(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** Schoolbook arithmetic on numbers of any length.

    Every function here walks arrays of {!Hacl.Secret.UInt32} limbs, least
    significant first, with the length given as a {!FStar.SizeT} the caller
    supplies.  There is no state, no allocation and no length limit beyond
    what the machine can address.

    {b What the postconditions say.}  Nothing here names a specification
    sequence.  Addition says

    {[ num vres + v c * wt n == num va + num vb ]}

    and that is the entire contract: the array denotes a number, and the
    number is the sum.  {!Spec.Bignum} explains the choice.

    {b Aliasing.}  Pulse's separation logic gives each argument its own
    permission, so the output of an operation is disjoint from its inputs by
    construction and nothing has to be said about it.  HACL* instead allows
    some arguments to be exactly equal; the replacements here are the
    in-place variants {!sub_from} and {!add_masked}, which take the
    accumulator and one operand rather than three arrays.  Those two are
    also what lets {!add_mod} and {!sub_mod} run without a temporary, which
    matters because the length is a run-time value and a temporary would
    therefore have to be a variable-length array.

    {b Constant time.}  The only decisions are on loop counters and on
    lengths, both public.  The conditional subtraction in {!add_mod} commits
    through a mask; no limb ever reaches an [if]. *)
module Hacl.Bignum.Base

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb32

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 The number an array denotes, and its prefixes}

    Every loop below has the same shape: after [j] steps the first [j] limbs
    of the output are right.  [pre v j] is the number those limbs denote, so
    that an invariant can talk about a prefix without a slice appearing in
    it. *)

let num (v: Seq.seq S32.t) : GTot nat = eval (vals v)

let pre (v: Seq.seq S32.t) (j: nat) : GTot nat =
  eval (Seq.slice (vals v) 0 (if j <= Seq.length v then j else Seq.length v))

let pre_zero (v: Seq.seq S32.t) : Lemma (pre v 0 == 0) = eval_empty (Seq.slice (vals v) 0 0)

let pre_full (v: Seq.seq S32.t) : Lemma (pre v (Seq.length v) == num v)
  = Seq.lemma_eq_intro (Seq.slice (vals v) 0 (Seq.length v)) (vals v)

(** One more limb weighs [wt j].  This is the step of every loop. *)
let pre_snoc (v: Seq.seq S32.t) (j: nat { j < Seq.length v })
  : Lemma (pre v (j + 1) == pre v j + wt j * S32.v (Seq.index v j))
  = eval_snoc (vals v) j

(** Writing limb [k] leaves every shorter prefix alone. *)
let pre_upd (v: Seq.seq S32.t) (k: nat { k < Seq.length v }) (x: S32.t) (j: nat { j <= k })
  : Lemma (pre (Seq.upd v k x) j == pre v j)
  = vals_upd v k x;
    eval_upd_above (vals v) k (S32.v x) j

(** A prefix is below its weight, because a limb is below the radix. *)
let pre_bnd (v: Seq.seq S32.t) (j: nat { j <= Seq.length v })
  : Lemma (pre v j < wt j)
  = eval_bnd_prefix (vals v) j

(** A zeroed prefix denotes zero. *)
let pre_zeros (v: Seq.seq S32.t) (j: nat { j <= Seq.length v })
  : Lemma (requires forall (i: nat). i < j ==> S32.v (Seq.index v i) == 0)
          (ensures pre v j == 0)
  = eval_zeros (Seq.slice (vals v) 0 j)

(** A prefix is the number modulo its weight: the low limbs are the low
    digits.  What a reduction loop needs in order to say that the limbs it
    has zeroed really did divide out. *)
let pre_mod (v: Seq.seq S32.t) (k: nat { k <= Seq.length v })
  : Lemma (pre v k == num v % wt k)
  = let n = Seq.length v in
    eval_split (vals v) k;
    eval_bnd_prefix (vals v) k;
    Math.lemma_mod_plus (eval (Seq.slice (vals v) 0 k))
      (eval (Seq.slice (vals v) k n)) (wt k);
    Math.small_mod (eval (Seq.slice (vals v) 0 k)) (wt k)

(** Writing one limb changes the number by the weight of that position
    times the difference.  Stated additively so both sides stay natural. *)
let num_upd (v: Seq.seq S32.t) (k: nat { k < Seq.length v }) (x: S32.t)
  : Lemma (num (Seq.upd v k x) + wt k * S32.v (Seq.index v k) ==
           num v + wt k * S32.v x)
  = vals_upd v k x;
    eval_upd (vals v) k (S32.v x)

(** Two arrays that agree above limb [k] denote numbers differing by exactly
    what their prefixes differ by.  Stated additively so both sides stay
    natural numbers. *)
let num_above (u v: Seq.seq S32.t) (k: nat { k <= Seq.length u })
  : Lemma (requires Seq.length u == Seq.length v /\
                    (forall (j: nat). k <= j /\ j < Seq.length u ==>
                       Seq.index v j == Seq.index u j))
          (ensures num v + pre u k == num u + pre v k)
  = let n = Seq.length u in
    eval_split (vals v) k;
    eval_split (vals u) k;
    Seq.lemma_eq_intro (Seq.slice v k n) (Seq.slice u k n);
    vals_slice v k n;
    vals_slice u k n

(** {2 The two step lemmas}

    Both are pure algebra about one column, stated separately because the
    solver does much better on them in isolation than inside a loop body
    that also carries three arrays. *)

let carry_bit (t: S64.t)
  : Lemma (requires S64.v t < 2 * base) (ensures S32.v (hi t) <= 1)
  = Math.lemma_div_le (S64.v t) (2 * base - 1) base;
    assert_norm ((2 * base - 1) / base == 1)

(** The two facts a column produces, restated in exactly the shape the step
    lemmas want.  Both are trivial; stating them separately keeps the
    solver from having to unfold [diff] and [lo]/[hi] inside a loop body
    that already carries three arrays and a quantifier. *)

let carry_fact (x y c r co: S32.t) (t: S64.t)
  : Lemma (requires S64.v t == S32.v x + S32.v y + S32.v c /\
                    S32.v r == S64.v t % base /\ S32.v co == S64.v t / base)
          (ensures S32.v r + base * S32.v co == S32.v x + S32.v y + S32.v c)
  = Math.euclidean_division_definition (S64.v t) base

let borrow_fact (x y c r h bo: S32.t)
  : Lemma (requires S32.v h <= 1 /\ S32.v bo == 1 - S32.v h /\
                    S32.v r == base * (1 - S32.v h) + S32.v x - S32.v y - S32.v c)
          (ensures S32.v r + S32.v y + S32.v c == base * S32.v bo + S32.v x)
  = ()

(** The column of an addition: the running sum grows by the new limb, and
    the carry moves up one weight. *)
let add_step (e ea eb: int) (ai bi ci ri co: int) (j: nat)
  : Lemma (requires e + ci * wt j == ea + eb /\ ri + base * co == ai + bi + ci)
          (ensures (e + wt j * ri) + co * wt (j + 1) == (ea + wt j * ai) + (eb + wt j * bi))
  = wt_succ j;
    Math.paren_mul_right co base (wt j);
    Math.distributivity_add_right (wt j) ri (base * co);
    Math.distributivity_add_right (wt j) (ai + bi) ci;
    Math.distributivity_add_right (wt j) ai bi

(** The column of a subtraction, with the borrow taken in advance so that
    every quantity in sight is a natural number. *)
let sub_step (e ea eb: int) (ai bi ci ri bo: int) (j: nat)
  : Lemma (requires ea + ci * wt j == e + eb /\ ri + bi + ci == base * bo + ai)
          (ensures (ea + wt j * ai) + bo * wt (j + 1) == (e + wt j * ri) + (eb + wt j * bi))
  = wt_succ j;
    Math.paren_mul_right bo base (wt j);
    Math.distributivity_add_right (wt j) (base * bo) ai;
    Math.distributivity_add_right (wt j) (ri + bi) ci;
    Math.distributivity_add_right (wt j) ri bi

(** {2 Filling} *)

(** [zero res n] sets all [n] limbs to zero. *)
fn zero (res: A.array S32.t) (n: SZ.t) (#vres: erased (Seq.seq S32.t))
requires A.pts_to res vres ** pure (Seq.length vres == SZ.v n)
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v **
  pure (Seq.length v == SZ.v n /\
        (forall (i: nat). i < Seq.length v ==> S32.v (Seq.index v i) == 0))
{
  A.pts_to_len res;
  let z = S32.zero;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
    pts_to i vi ** A.pts_to res v **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          (forall (k: nat). k < SZ.v vi ==> S32.v (Seq.index v k) == 0))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    A.((res.(vi) <- z));
    i := SZ.add vi 1sz;
  };
  ()
}

(** {2 Addition and subtraction} *)

#push-options "--z3rlimit 300"

(** [add res a b n] is [res = a + b] truncated to [n] limbs, returning the
    limb that did not fit.  That limb is zero or one. *)
fn add (res: A.array S32.t) (a b: A.array S32.t) (n: SZ.t)
       (#vres: erased (Seq.seq S32.t)) (#pa #pb: perm)
       (#va #vb: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns c: S32.t
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S32.v c <= 1 /\
        num v + S32.v c * wt (SZ.v n) == num va + num vb)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero va;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S32.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S32.t) (v: Seq.seq S32.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S32.v vc <= 1 /\
          pre v (SZ.v vi) + S32.v vc * wt (SZ.v vi) ==
            pre va (SZ.v vi) + pre vb (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    with v. assert (A.pts_to res v);
    let vi = !i;
    let vc = !c;
    let ai = A.(a.(vi));
    let bi = A.(b.(vi));
    let t = sum ai bi vc;
    carry_bit t;
    lo_hi t;
    let r = lo t;
    let co = hi t;
    carry_fact ai bi vc r co t;
    A.((res.(vi) <- r));
    pre_upd v (SZ.v vi) r (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) r) (SZ.v vi);
    pre_snoc va (SZ.v vi);
    pre_snoc vb (SZ.v vi);
    add_step (pre v (SZ.v vi)) (pre va (SZ.v vi)) (pre vb (SZ.v vi))
             (S32.v ai) (S32.v bi) (S32.v vc) (S32.v r) (S32.v co) (SZ.v vi);
    c := co;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full va;
  pre_full vb;
  !c
}

(** [sub res a b n] is [res = a - b] with a borrow: the returned limb is one
    exactly when [b] was the larger. *)
fn sub (res: A.array S32.t) (a b: A.array S32.t) (n: SZ.t)
       (#vres: erased (Seq.seq S32.t)) (#pa #pb: perm)
       (#va #vb: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns c: S32.t
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S32.v c <= 1 /\
        num va + S32.v c * wt (SZ.v n) == num v + num vb)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero va;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S32.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S32.t) (v: Seq.seq S32.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S32.v vc <= 1 /\
          pre va (SZ.v vi) + S32.v vc * wt (SZ.v vi) ==
            pre v (SZ.v vi) + pre vb (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    with v. assert (A.pts_to res v);
    let vi = !i;
    let vc = !c;
    let ai = A.(a.(vi));
    let bi = A.(b.(vi));
    diff_borrow ai bi vc;
    let d = diff ai bi vc;
    let r = lo d;
    let h = hi d;
    let bo = flip h;
    borrow_fact ai bi vc r h bo;
    A.((res.(vi) <- r));
    pre_upd v (SZ.v vi) r (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) r) (SZ.v vi);
    pre_snoc va (SZ.v vi);
    pre_snoc vb (SZ.v vi);
    sub_step (pre v (SZ.v vi)) (pre va (SZ.v vi)) (pre vb (SZ.v vi))
             (S32.v ai) (S32.v bi) (S32.v vc) (S32.v r) (S32.v bo) (SZ.v vi);
    c := bo;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full va;
  pre_full vb;
  !c
}

#pop-options


(** {2 In-place addition and subtraction}

    These two take an accumulator and one operand, which is what HACL*
    expresses by allowing [res] and [a] to be exactly equal.  They are what
    {!add_mod} and {!sub_mod} need in order to run in the caller's output
    array alone, with no temporary of run-time length. *)

#push-options "--z3rlimit 1000"

(** [sub_from res b n] is [res -= b], returning the borrow. *)
fn sub_from (res: A.array S32.t) (b: A.array S32.t) (n: SZ.t)
            (#vres: erased (Seq.seq S32.t)) (#pb: perm) (#vb: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == SZ.v n)
returns c: S32.t
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S32.v c <= 1 /\
        num vres + S32.v c * wt (SZ.v n) == num v + num vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S32.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S32.t) (v: Seq.seq S32.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S32.v vc <= 1 /\
          (forall (k: nat). SZ.v vi <= k /\ k < SZ.v n ==>
             Seq.index v k == Seq.index vres k) /\
          pre vres (SZ.v vi) + S32.v vc * wt (SZ.v vi) ==
            pre v (SZ.v vi) + pre vb (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    with v. assert (A.pts_to res v);
    let vi = !i;
    let vc = !c;
    let ai = A.(res.(vi));
    let bi = A.(b.(vi));
    diff_borrow ai bi vc;
    let d = diff ai bi vc;
    let r = lo d;
    let h = hi d;
    let bo = flip h;
    borrow_fact ai bi vc r h bo;
    A.((res.(vi) <- r));
    pre_upd v (SZ.v vi) r (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) r) (SZ.v vi);
    pre_snoc vres (SZ.v vi);
    pre_snoc vb (SZ.v vi);
    sub_step (pre v (SZ.v vi)) (pre vres (SZ.v vi)) (pre vb (SZ.v vi))
             (S32.v ai) (S32.v bi) (S32.v vc) (S32.v r) (S32.v bo) (SZ.v vi);
    c := bo;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full vres;
  pre_full vb;
  !c
}

(** A mask is all ones or all zeroes. *)
let is_mask (m: S32.t) : prop = S32.v m == 0 \/ S32.v m == pow2 32 - 1

(** The number a mask stands for, as a parameter rather than a definition.
    Writing [if v m = 0 then 0 else 1] inline would make every product in
    the loop below a conditional, and the solver splits on those; an opaque
    [k] bounded by one does not. *)
let stands_for (m: S32.t) (k: nat) : prop =
  k <= 1 /\ (S32.v m == 0 ==> k == 0) /\ (~(S32.v m == 0) ==> k == 1)

inline_for_extraction
let masked (m x: S32.t)
  : Pure S32.t (requires is_mask m) (ensures fun r -> r == (if S32.v m = 0 then S32.zero else x))
  = S32.select m x S32.zero

(** The multiplier a mask stands for, for the call sites to hand over. *)
let mask_bit (m: S32.t) : GTot nat = if S32.v m = 0 then 0 else 1

let mask_bit_ok (m: S32.t) : Lemma (stands_for m (mask_bit m)) = ()

let masked_val (m x: S32.t) (k: nat)
  : Lemma (requires is_mask m /\ stands_for m k)
          (ensures S32.v (masked m x) == k * S32.v x)
  = ()

(** Multiplying a running total by the same constant on both sides. *)
let scale_snoc (k e w x: int) : Lemma (k * (e + w * x) == k * e + w * (k * x))
  = Math.distributivity_add_right k e (w * x);
    Math.paren_mul_right k w x;
    Math.swap_mul k w;
    Math.paren_mul_right w k x

#push-options "--z3rlimit 1000"

(** [add_masked res b n m] is [res += b] if [m] is all ones and nothing at
    all if [m] is all zeroes, in the same time either way. *)
fn add_masked (res: A.array S32.t) (b: A.array S32.t) (n: SZ.t) (m: S32.t) (k: erased nat)
              (#vres: erased (Seq.seq S32.t)) (#pb: perm) (#vb: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == SZ.v n /\
        is_mask m /\ stands_for m (reveal k))
returns c: S32.t
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S32.v c <= 1 /\
        num v + S32.v c * wt (SZ.v n) == num vres + reveal k * num vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S32.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S32.t) (v: Seq.seq S32.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S32.v vc <= 1 /\
          (forall (j: nat). SZ.v vi <= j /\ j < SZ.v n ==>
             Seq.index v j == Seq.index vres j) /\
          pre v (SZ.v vi) + S32.v vc * wt (SZ.v vi) ==
            pre vres (SZ.v vi) + reveal k * pre vb (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    with v. assert (A.pts_to res v);
    let vi = !i;
    let vc = !c;
    let ai = A.(res.(vi));
    let bi = A.(b.(vi));
    masked_val m bi (reveal k);
    let mi = masked m bi;
    let t = sum ai mi vc;
    carry_bit t;
    lo_hi t;
    let r = lo t;
    let co = hi t;
    carry_fact ai mi vc r co t;
    A.((res.(vi) <- r));
    pre_upd v (SZ.v vi) r (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) r) (SZ.v vi);
    pre_snoc vres (SZ.v vi);
    pre_snoc vb (SZ.v vi);
    scale_snoc (reveal k) (pre vb (SZ.v vi)) (wt (SZ.v vi)) (S32.v bi);
    add_step (pre v (SZ.v vi)) (pre vres (SZ.v vi)) (reveal k * pre vb (SZ.v vi))
             (S32.v ai) (S32.v mi) (S32.v vc) (S32.v r) (S32.v co) (SZ.v vi);
    c := co;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full vres;
  pre_full vb;
  !c
}

#pop-options

#pop-options

(** {2 Modular addition and subtraction}

    Both are the plain operation followed by one conditional correction, and
    in both cases the mask that decides the correction is read off the
    carries rather than by comparing.  The arguments are required to be
    already reduced, which is the precondition HACL* states too. *)

(** [add_mod res a b m n] is [res = (a + b) mod m]. *)
fn add_mod (res: A.array S32.t) (a b m: A.array S32.t) (n: SZ.t)
           (#vres: erased (Seq.seq S32.t)) (#pa #pb #pm: perm)
           (#va #vb: erased (Seq.seq S32.t))
           (#vm: erased (s: Seq.seq S32.t { 0 < num s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to m #pm vm **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\
        Seq.length vb == SZ.v n /\ Seq.length vm == SZ.v n /\
        num va < num vm /\ num vb < num vm)
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to m #pm vm **
  pure (Seq.length v == SZ.v n /\ num v == (num va + num vb) % num vm)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  A.pts_to_len m;
  eval_bnd (vals vm);
  let c0 = add res a b n;
  with v1. assert (A.pts_to res v1);
  eval_bnd (vals v1);
  let c1 = sub_from res m n;
  with v2. assert (A.pts_to res v2);
  eval_bnd (vals v2);
  (* [c0 < c1] exactly when the sum was already reduced, in which case the
     modulus has to go back in.  The other impossible combination, a carry
     out of the sum but none out of the subtraction, is ruled out by the
     bound on [v2]. *)
  let mask = S32.lt_mask c0 c1;
  mask_bit_ok mask;
  let c2 = add_masked res m n mask (hide (mask_bit mask));
  with v3. assert (A.pts_to res v3);
  eval_bnd (vals v3);
  sum_mod_cases (num va) (num vb) (num vm);
  ()
}

(** [sub_mod res a b m n] is [res = (a - b) mod m]. *)
fn sub_mod (res: A.array S32.t) (a b m: A.array S32.t) (n: SZ.t)
           (#vres: erased (Seq.seq S32.t)) (#pa #pb #pm: perm)
           (#va #vb: erased (Seq.seq S32.t))
           (#vm: erased (s: Seq.seq S32.t { 0 < num s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to m #pm vm **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\
        Seq.length vb == SZ.v n /\ Seq.length vm == SZ.v n /\
        num va < num vm /\ num vb < num vm)
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to m #pm vm **
  pure (Seq.length v == SZ.v n /\ num v == (num va - num vb) % num vm)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  A.pts_to_len m;
  eval_bnd (vals vm);
  let c0 = sub res a b n;
  with v1. assert (A.pts_to res v1);
  eval_bnd (vals v1);
  (* A borrow means the difference went negative, and exactly one modulus
     brings it back. *)
  let mask = S32.eq_mask c0 (S32.classify 1ul);
  mask_bit_ok mask;
  let c2 = add_masked res m n mask (hide (mask_bit mask));
  with v2. assert (A.pts_to res v2);
  eval_bnd (vals v2);
  diff_mod_cases (num va) (num vb) (num vm);
  ()
}

(** {2 Comparison}

    Both scans run from the bottom and keep a single mask, so they look at
    every limb whatever the answer is. *)

(** All ones if [a < b], all zeroes otherwise. *)
fn lt_mask (a b: A.array S32.t) (n: SZ.t) (#pa #pb: perm)
           (#va #vb: erased (Seq.seq S32.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns r: S32.t
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (is_mask r /\ (num va < num vb <==> S32.v r == pow2 32 - 1))
{
  A.pts_to_len a;
  A.pts_to_len b;
  pre_zero va;
  pre_zero vb;
  let mut i = 0sz;
  let mut acc = S32.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vacc: S32.t).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ is_mask vacc /\
          (pre va (SZ.v vi) < pre vb (SZ.v vi) <==> S32.v vacc == pow2 32 - 1))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let vacc = !acc;
    let ai = A.(a.(vi));
    let bi = A.(b.(vi));
    eval_lt_snoc (vals va) (vals vb) (SZ.v vi);
    pre_snoc va (SZ.v vi);
    pre_snoc vb (SZ.v vi);
    acc := S32.select (S32.eq_mask ai bi) vacc (S32.lt_mask ai bi);
    i := SZ.add vi 1sz;
  };
  pre_full va;
  pre_full vb;
  !acc
}

(** All ones if [a == b], all zeroes otherwise. *)
fn eq_mask (a b: A.array S32.t) (n: SZ.t) (#pa #pb: perm)
           (#va #vb: erased (Seq.seq S32.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns r: S32.t
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (is_mask r /\ (num va == num vb <==> S32.v r == pow2 32 - 1))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  let mut acc = S32.ones;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vacc: S32.t).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ is_mask vacc /\
          ((forall (k: nat). k < SZ.v vi ==>
              S32.v (Seq.index va k) == S32.v (Seq.index vb k)) <==>
           S32.v vacc == pow2 32 - 1))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let vacc = !acc;
    let ai = A.(a.(vi));
    let bi = A.(b.(vi));
    acc := S32.select (S32.eq_mask ai bi) vacc S32.zero;
    i := SZ.add vi 1sz;
  };
  eval_eq (vals va) (vals vb);
  !acc
}

(** {2 Multiplication}

    The product of two [n]-limb numbers needs [2n] limbs.  The outer loop
    walks the limbs of [b] and the inner one adds [a] times that limb into
    the accumulator at the matching offset, so the whole product is computed
    in place with one pass over [res] per limb of [b] and never a carry
    longer than one limb. *)

(** The column of a row: one product accumulated at weight [off + j]. *)
let row_step (e er eva: int) (aj bi r ci ri co: int) (off j: nat)
  : Lemma (requires e + ci * wt (off + j) == er + (eva * bi) * wt off /\
                    ri + base * co == aj * bi + r + ci)
          (ensures (e + wt (off + j) * ri) + co * wt (off + j + 1) ==
                   (er + wt (off + j) * r) + ((eva + wt j * aj) * bi) * wt off)
  = wt_succ (off + j);
    wt_add off j;
    Math.paren_mul_right co base (wt (off + j));
    Math.distributivity_add_right (wt (off + j)) ri (base * co);
    Math.distributivity_add_left eva (wt j * aj) bi;
    Math.paren_mul_right (wt j) aj bi;
    Math.paren_mul_right (wt j * (aj * bi)) (wt off) 1;
    Math.swap_mul (wt j * (aj * bi)) (wt off);
    Math.paren_mul_right (wt off) (wt j) (aj * bi);
    Math.distributivity_add_left (eva * bi) (wt j * (aj * bi)) (wt off);
    Math.paren_mul_right (wt j * aj * bi) (wt off) 1;
    Math.distributivity_add_right (wt (off + j)) (aj * bi + r) ci;
    Math.distributivity_add_right (wt (off + j)) (aj * bi) r

#push-options "--z3rlimit 600"

(** [mul_row res a n bi off] is [res += a * bi * base^off], returning the
    limb that came out of the top of the window. *)
fn mul_row (res: A.array S32.t) (a: A.array S32.t) (n: SZ.t) (bi: S32.t) (off: SZ.t)
           (#vres: erased (Seq.seq S32.t)) (#pa: perm) (#va: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to a #pa va **
  pure (Seq.length va == SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vres /\
        SZ.fits (SZ.v off + SZ.v n))
returns c: S32.t
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va **
  pure (Seq.length v == Seq.length vres /\ S32.v c < base /\
        (forall (k: nat). SZ.v off + SZ.v n <= k /\ k < Seq.length v ==>
           Seq.index v k == Seq.index vres k) /\
        pre v (SZ.v off + SZ.v n) + S32.v c * wt (SZ.v off + SZ.v n) ==
          pre vres (SZ.v off + SZ.v n) + (num va * S32.v bi) * wt (SZ.v off))
{
  A.pts_to_len res;
  A.pts_to_len a;
  pre_zero va;
  let mut j = 0sz;
  let mut c = S32.zero;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (vc: S32.t) (v: Seq.seq S32.t).
    pts_to j vj ** pts_to c vc ** A.pts_to res v ** A.pts_to a #pa va **
    pure (SZ.v vj <= SZ.v n /\ Seq.length v == Seq.length vres /\
            (forall (k: nat). SZ.v off + SZ.v vj <= k /\ k < Seq.length v ==>
             Seq.index v k == Seq.index vres k) /\
          pre v (SZ.v off + SZ.v vj) + S32.v vc * wt (SZ.v off + SZ.v vj) ==
            pre vres (SZ.v off + SZ.v vj) + (pre va (SZ.v vj) * S32.v bi) * wt (SZ.v off))
  decreases (SZ.v n - SZ.v (!j))
  {
    with v. assert (A.pts_to res v);
    let vj = !j;
    let vc = !c;
    let pos = SZ.add off vj;
    let aj = A.(a.(vj));
    let rj = A.(res.(pos));
    let t = mac aj bi rj vc;
    lo_hi t;
    let r = lo t;
    let co = hi t;
    A.((res.(pos) <- r));
    pre_upd v (SZ.v pos) r (SZ.v pos);
    pre_snoc (Seq.upd v (SZ.v pos) r) (SZ.v pos);
    pre_snoc vres (SZ.v pos);
    pre_snoc va (SZ.v vj);
    row_step (pre v (SZ.v pos)) (pre vres (SZ.v pos)) (pre va (SZ.v vj))
             (S32.v aj) (S32.v bi) (S32.v rj) (S32.v vc) (S32.v r) (S32.v co)
             (SZ.v off) (SZ.v vj);
    c := co;
    j := SZ.add vj 1sz;
  };
  pre_full va;
  !c
}

#pop-options



(** Nothing above the cursor has been written yet, so the limb the carry is
    about to occupy is still zero. *)
let pre_carry (v: Seq.seq S32.t) (k: nat { k < Seq.length v }) (c: S32.t)
  : Lemma (requires S32.v (Seq.index v k) == 0)
          (ensures pre (Seq.upd v k c) (k + 1) == pre v k + wt k * S32.v c)
  = pre_upd v k c k;
    pre_snoc (Seq.upd v k c) k;
    pre_snoc v k

(** The outer step: one row, then the carry parked above it, is one more
    limb of the second operand multiplied in. *)
let mul_outer_step (p pold evb bi c nva wi wpos: int)
  : Lemma (requires p + c * wpos == pold + (nva * bi) * wi /\ pold == nva * evb)
          (ensures p + wpos * c == nva * (evb + wi * bi))
  = Math.swap_mul wpos c;
    Math.distributivity_add_right nva evb (wi * bi);
    Math.paren_mul_right nva wi bi;
    Math.swap_mul wi bi;
    Math.paren_mul_right nva bi wi

#push-options "--z3rlimit 600"

(** [mul res a b n] is the [2n]-limb product of two [n]-limb numbers. *)
fn mul (res: A.array S32.t) (a b: A.array S32.t) (n: SZ.t)
       (#vres: erased (Seq.seq S32.t)) (#pa #pb: perm)
       (#va #vb: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n + SZ.v n /\ Seq.length va == SZ.v n /\
        Seq.length vb == SZ.v n /\ SZ.fits (SZ.v n + SZ.v n))
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n + SZ.v n /\ num v == num va * num vb)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  zero res (SZ.add n n);
  with v0. assert (A.pts_to res v0);
  pre_zeros v0 (SZ.v n);
  pre_zero vb;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n + SZ.v n /\
          (forall (k: nat). SZ.v n + SZ.v vi <= k /\ k < Seq.length v ==>
             S32.v (Seq.index v k) == 0) /\
          pre v (SZ.v n + SZ.v vi) == num va * pre vb (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    with vold. assert (A.pts_to res vold);
    let vi = !i;
    let bi = A.(b.(vi));
    let c = mul_row res a n bi vi;
    with v. assert (A.pts_to res v);
    let pos = SZ.add n vi;
    A.((res.(pos) <- c));
    pre_carry v (SZ.v pos) c;
    pre_snoc vb (SZ.v vi);
    mul_outer_step (pre v (SZ.v pos)) (pre vold (SZ.v pos)) (pre vb (SZ.v vi))
                   (S32.v bi) (S32.v c) (num va) (wt (SZ.v vi)) (wt (SZ.v pos));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full vb;
  ()
}

(** [sqr res a n] is [a * a].  It is the same loop as {!mul} with both
    operands taken from the same array, which costs nothing extra here
    because no limb of [a] is written. *)
fn sqr (res: A.array S32.t) (a: A.array S32.t) (n: SZ.t)
       (#vres: erased (Seq.seq S32.t)) (#pa: perm) (#va: erased (Seq.seq S32.t))
requires A.pts_to res vres ** A.pts_to a #pa va **
  pure (Seq.length vres == SZ.v n + SZ.v n /\ Seq.length va == SZ.v n /\
        SZ.fits (SZ.v n + SZ.v n))
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to a #pa va **
  pure (Seq.length v == SZ.v n + SZ.v n /\ num v == num va * num va)
{
  A.pts_to_len res;
  A.pts_to_len a;
  zero res (SZ.add n n);
  with v0. assert (A.pts_to res v0);
  pre_zeros v0 (SZ.v n);
  pre_zero va;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n + SZ.v n /\
          (forall (k: nat). SZ.v n + SZ.v vi <= k /\ k < Seq.length v ==>
             S32.v (Seq.index v k) == 0) /\
          pre v (SZ.v n + SZ.v vi) == num va * pre va (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    with vold. assert (A.pts_to res vold);
    let vi = !i;
    let bi = A.(a.(vi));
    let c = mul_row res a n bi vi;
    with v. assert (A.pts_to res v);
    let pos = SZ.add n vi;
    A.((res.(pos) <- c));
    pre_carry v (SZ.v pos) c;
    pre_snoc va (SZ.v vi);
    mul_outer_step (pre v (SZ.v pos)) (pre vold (SZ.v pos)) (pre va (SZ.v vi))
                   (S32.v bi) (S32.v c) (num va) (wt (SZ.v vi)) (wt (SZ.v pos));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full va;
  ()
}

#pop-options


#pop-options
