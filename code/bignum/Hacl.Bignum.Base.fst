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

    Every function here walks arrays of {!Hacl.Secret.UInt64} limbs, least
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
open Hacl.Impl.Limb64

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128

module UInt = FStar.UInt
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 The number an array denotes, and its prefixes}

    Every loop below has the same shape: after [j] steps the first [j] limbs
    of the output are right.  [pre v j] is the number those limbs denote, so
    that an invariant can talk about a prefix without a slice appearing in
    it. *)

let num (v: Seq.seq S64.t) : GTot nat = eval (vals v)

let pre (v: Seq.seq S64.t) (j: nat) : GTot nat =
  eval (Seq.slice (vals v) 0 (if j <= Seq.length v then j else Seq.length v))

let pre_zero (v: Seq.seq S64.t) : Lemma (pre v 0 == 0) = eval_empty (Seq.slice (vals v) 0 0)

let pre_full (v: Seq.seq S64.t) : Lemma (pre v (Seq.length v) == num v)
  = Seq.lemma_eq_intro (Seq.slice (vals v) 0 (Seq.length v)) (vals v)

(** One more limb weighs [wt j].  This is the step of every loop. *)
let pre_snoc (v: Seq.seq S64.t) (j: nat { j < Seq.length v })
  : Lemma (pre v (j + 1) == pre v j + wt j * S64.v (Seq.index v j))
  = eval_snoc (vals v) j

(** Writing limb [k] leaves every shorter prefix alone. *)
let pre_upd (v: Seq.seq S64.t) (k: nat { k < Seq.length v }) (x: S64.t) (j: nat { j <= k })
  : Lemma (pre (Seq.upd v k x) j == pre v j)
  = vals_upd v k x;
    eval_upd_above (vals v) k (S64.v x) j

(** A prefix is below its weight, because a limb is below the radix. *)
let pre_bnd (v: Seq.seq S64.t) (j: nat { j <= Seq.length v })
  : Lemma (pre v j < wt j)
  = eval_bnd_prefix (vals v) j

(** A zeroed prefix denotes zero. *)
let pre_zeros (v: Seq.seq S64.t) (j: nat { j <= Seq.length v })
  : Lemma (requires forall (i: nat). i < j ==> S64.v (Seq.index v i) == 0)
          (ensures pre v j == 0)
  = eval_zeros (Seq.slice (vals v) 0 j)

(** A prefix is the number modulo its weight: the low limbs are the low
    digits.  What a reduction loop needs in order to say that the limbs it
    has zeroed really did divide out. *)
let pre_mod (v: Seq.seq S64.t) (k: nat { k <= Seq.length v })
  : Lemma (pre v k == num v % wt k)
  = let n = Seq.length v in
    eval_split (vals v) k;
    eval_bnd_prefix (vals v) k;
    Math.lemma_mod_plus (eval (Seq.slice (vals v) 0 k))
      (eval (Seq.slice (vals v) k n)) (wt k);
    Math.small_mod (eval (Seq.slice (vals v) 0 k)) (wt k)

(** Writing one limb changes the number by the weight of that position
    times the difference.  Stated additively so both sides stay natural. *)
let num_upd (v: Seq.seq S64.t) (k: nat { k < Seq.length v }) (x: S64.t)
  : Lemma (num (Seq.upd v k x) + wt k * S64.v (Seq.index v k) ==
           num v + wt k * S64.v x)
  = vals_upd v k x;
    eval_upd (vals v) k (S64.v x)

(** Two arrays that agree above limb [k] denote numbers differing by exactly
    what their prefixes differ by.  Stated additively so both sides stay
    natural numbers. *)
let num_above (u v: Seq.seq S64.t) (k: nat { k <= Seq.length u })
  : Lemma (requires Seq.length u == Seq.length v /\
                    (forall (j: nat). k <= j /\ j < Seq.length u ==>
                       Seq.index v j == Seq.index u j))
          (ensures num v + pre u k == num u + pre v k)
  = let n = Seq.length u in
    assert (Seq.length (vals u) == Seq.length u);
    assert (Seq.length (vals v) == Seq.length v);
    eval_split (vals v) k;
    eval_split (vals u) k;
    Seq.lemma_eq_intro (Seq.slice v k n) (Seq.slice u k n);
    vals_slice v k n;
    vals_slice u k n

(** Zeroes above limb [k] contribute nothing, so the number is its own
    prefix.  The dual of {!pre_zeros}. *)
let num_zeros_above (v: Seq.seq S64.t) (k: nat { k <= Seq.length v })
  : Lemma (requires forall (j: nat). k <= j /\ j < Seq.length v ==>
                      S64.v (Seq.index v j) == 0)
          (ensures num v == pre v k)
  = let n = Seq.length v in
    eval_split (vals v) k;
    eval_zeros (Seq.slice (vals v) k n)

(** A number is at least any one of its columns.  What a caller needs in
    order to conclude that a modulus with its top limb set is large, without
    evaluating the other two hundred and fifty-five limbs. *)
let num_top (v: Seq.seq S64.t) (k: nat { k < Seq.length v })
  : Lemma (num v >= wt k * S64.v (Seq.index v k))
  = pre_mod v (k + 1);
    pre_snoc v k;
    Math.lemma_div_mod (num v) (wt (k + 1));
    Math.lemma_mult_le_right (wt (k + 1)) 0 (num v / wt (k + 1))

(** {2 The two step lemmas}

    Both are pure algebra about one column, stated separately because the
    solver does much better on them in isolation than inside a loop body
    that also carries three arrays. *)

let carry_bit (t: S128.t)
  : Lemma (requires S128.v t < 2 * base) (ensures S64.v (hi t) <= 1)
  = Math.lemma_div_le (S128.v t) (2 * base - 1) base;
    assert_norm ((2 * base - 1) / base == 1)

(** The two facts a column produces, restated in exactly the shape the step
    lemmas want.  Both are trivial; stating them separately keeps the
    solver from having to unfold [diff] and [lo]/[hi] inside a loop body
    that already carries three arrays and a quantifier. *)

let carry_fact (x y c r co: S64.t) (t: S128.t)
  : Lemma (requires S128.v t == S64.v x + S64.v y + S64.v c /\
                    S64.v r == S128.v t % base /\ S64.v co == S128.v t / base)
          (ensures S64.v r + base * S64.v co == S64.v x + S64.v y + S64.v c)
  = Math.euclidean_division_definition (S128.v t) base

let borrow_fact (x y c r h bo: S64.t)
  : Lemma (requires S64.v h <= 1 /\ S64.v bo == 1 - S64.v h /\
                    S64.v r == base * (1 - S64.v h) + S64.v x - S64.v y - S64.v c)
          (ensures S64.v r + S64.v y + S64.v c == base * S64.v bo + S64.v x)
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
fn zero (res: A.array S64.t) (n: SZ.t) (#vres: erased (Seq.seq S64.t))
requires A.pts_to res vres ** pure (Seq.length vres == SZ.v n)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v **
  pure (Seq.length v == SZ.v n /\
        (forall (i: nat). i < Seq.length v ==> S64.v (Seq.index v i) == 0))
{
  A.pts_to_len res;
  let z = S64.zero;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          (forall (k: nat). k < SZ.v vi ==> S64.v (Seq.index v k) == 0))
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
fn add (res: A.array S64.t) (a b: A.array S64.t) (n: SZ.t)
       (#vres: erased (Seq.seq S64.t)) (#pa #pb: perm)
       (#va #vb: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns c: S64.t
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S64.v c <= 1 /\
        num v + S64.v c * wt (SZ.v n) == num va + num vb)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero va;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S64.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S64.t) (v: Seq.seq S64.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S64.v vc <= 1 /\
          pre v (SZ.v vi) + S64.v vc * wt (SZ.v vi) ==
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
             (S64.v ai) (S64.v bi) (S64.v vc) (S64.v r) (S64.v co) (SZ.v vi);
    c := co;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full va;
  pre_full vb;
  !c
}

(** [double res n] is [res += res], returning the limb that did not fit.
    In place, because that is what the doubling chain of {!precomp} wants
    and because the library never allocates. *)
fn double (res: A.array S64.t) (n: SZ.t) (#vres: erased (Seq.seq S64.t))
requires A.pts_to res vres ** pure (Seq.length vres == SZ.v n)
returns c: S64.t
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v **
  pure (Seq.length v == SZ.v n /\ S64.v c <= 1 /\
        num v + S64.v c * wt (SZ.v n) == num vres + num vres)
{
  A.pts_to_len res;
  pre_zero vres;
  let mut i = 0sz;
  let mut c = S64.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S64.t) (v: Seq.seq S64.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S64.v vc <= 1 /\
          (forall (k: nat). SZ.v vi <= k /\ k < Seq.length v ==>
             Seq.index v k == Seq.index vres k) /\
          pre v (SZ.v vi) + S64.v vc * wt (SZ.v vi) ==
            pre vres (SZ.v vi) + pre vres (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    with v. assert (A.pts_to res v);
    let vi = !i;
    let vc = !c;
    let xi = A.(res.(vi));
    let t = sum xi xi vc;
    carry_bit t;
    lo_hi t;
    let r = lo t;
    let co = hi t;
    carry_fact xi xi vc r co t;
    A.((res.(vi) <- r));
    pre_upd v (SZ.v vi) r (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) r) (SZ.v vi);
    pre_snoc vres (SZ.v vi);
    add_step (pre v (SZ.v vi)) (pre vres (SZ.v vi)) (pre vres (SZ.v vi))
             (S64.v xi) (S64.v xi) (S64.v vc) (S64.v r) (S64.v co) (SZ.v vi);
    c := co;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full vres;
  !c
}

(** [sub res a b n] is [res = a - b] with a borrow: the returned limb is one
    exactly when [b] was the larger. *)
fn sub (res: A.array S64.t) (a b: A.array S64.t) (n: SZ.t)
       (#vres: erased (Seq.seq S64.t)) (#pa #pb: perm)
       (#va #vb: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns c: S64.t
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S64.v c <= 1 /\
        num va + S64.v c * wt (SZ.v n) == num v + num vb)
{
  A.pts_to_len res;
  A.pts_to_len a;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero va;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S64.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S64.t) (v: Seq.seq S64.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S64.v vc <= 1 /\
          pre va (SZ.v vi) + S64.v vc * wt (SZ.v vi) ==
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
             (S64.v ai) (S64.v bi) (S64.v vc) (S64.v r) (S64.v bo) (SZ.v vi);
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
fn sub_from (res: A.array S64.t) (b: A.array S64.t) (n: SZ.t)
            (#vres: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == SZ.v n)
returns c: S64.t
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S64.v c <= 1 /\
        num vres + S64.v c * wt (SZ.v n) == num v + num vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S64.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S64.t) (v: Seq.seq S64.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S64.v vc <= 1 /\
          (forall (k: nat). SZ.v vi <= k /\ k < SZ.v n ==>
             Seq.index v k == Seq.index vres k) /\
          pre vres (SZ.v vi) + S64.v vc * wt (SZ.v vi) ==
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
             (S64.v ai) (S64.v bi) (S64.v vc) (S64.v r) (S64.v bo) (SZ.v vi);
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
let is_mask (m: S64.t) : prop = S64.v m == 0 \/ S64.v m == pow2 64 - 1

(** The number a mask stands for, as a parameter rather than a definition.
    Writing [if v m = 0 then 0 else 1] inline would make every product in
    the loop below a conditional, and the solver splits on those; an opaque
    [k] bounded by one does not. *)
let stands_for (m: S64.t) (k: nat) : prop =
  k <= 1 /\ (S64.v m == 0 ==> k == 0) /\ (~(S64.v m == 0) ==> k == 1)

inline_for_extraction
let masked (m x: S64.t)
  : Pure S64.t (requires is_mask m) (ensures fun r -> r == (if S64.v m = 0 then S64.zero else x))
  = S64.select m x S64.zero

(** The multiplier a mask stands for, for the call sites to hand over. *)
let mask_bit (m: S64.t) : GTot nat = if S64.v m = 0 then 0 else 1

let mask_bit_ok (m: S64.t) : Lemma (stands_for m (mask_bit m)) = ()

let masked_val (m x: S64.t) (k: nat)
  : Lemma (requires is_mask m /\ stands_for m k)
          (ensures S64.v (masked m x) == k * S64.v x)
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
fn add_masked (res: A.array S64.t) (b: A.array S64.t) (n: SZ.t) (m: S64.t) (k: erased nat)
              (#vres: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == SZ.v n /\
        is_mask m /\ stands_for m (reveal k))
returns c: S64.t
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to b #pb vb **
  pure (Seq.length v == SZ.v n /\ S64.v c <= 1 /\
        num v + S64.v c * wt (SZ.v n) == num vres + reveal k * num vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  pre_zero vres;
  pre_zero vb;
  let mut i = 0sz;
  let mut c = S64.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vc: S64.t) (v: Seq.seq S64.t).
    pts_to i vi ** pts_to c vc ** A.pts_to res v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\ S64.v vc <= 1 /\
          (forall (j: nat). SZ.v vi <= j /\ j < SZ.v n ==>
             Seq.index v j == Seq.index vres j) /\
          pre v (SZ.v vi) + S64.v vc * wt (SZ.v vi) ==
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
    scale_snoc (reveal k) (pre vb (SZ.v vi)) (wt (SZ.v vi)) (S64.v bi);
    add_step (pre v (SZ.v vi)) (pre vres (SZ.v vi)) (reveal k * pre vb (SZ.v vi))
             (S64.v ai) (S64.v mi) (S64.v vc) (S64.v r) (S64.v co) (SZ.v vi);
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
fn add_mod (res: A.array S64.t) (a b m: A.array S64.t) (n: SZ.t)
           (#vres: erased (Seq.seq S64.t)) (#pa #pb #pm: perm)
           (#va #vb: erased (Seq.seq S64.t))
           (#vm: erased (s: Seq.seq S64.t { 0 < num s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to m #pm vm **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\
        Seq.length vb == SZ.v n /\ Seq.length vm == SZ.v n /\
        num va < num vm /\ num vb < num vm)
ensures exists* (v: Seq.seq S64.t).
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
  let mask = S64.lt_mask c0 c1;
  mask_bit_ok mask;
  let c2 = add_masked res m n mask (hide (mask_bit mask));
  with v3. assert (A.pts_to res v3);
  eval_bnd (vals v3);
  sum_mod_cases (num va) (num vb) (num vm);
  ()
}

(** [double_mod res m n] is [res = (res + res) mod m], in place. *)
fn double_mod (res: A.array S64.t) (m: A.array S64.t) (n: SZ.t)
              (#vres: erased (Seq.seq S64.t)) (#pm: perm)
              (#vm: erased (s: Seq.seq S64.t { 0 < num s }))
requires A.pts_to res vres ** A.pts_to m #pm vm **
  pure (Seq.length vres == SZ.v n /\ Seq.length vm == SZ.v n /\ num vres < num vm)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to m #pm vm **
  pure (Seq.length v == SZ.v n /\ num v == (num vres + num vres) % num vm)
{
  A.pts_to_len res;
  A.pts_to_len m;
  eval_bnd (vals vm);
  let c0 = double res n;
  with v1. assert (A.pts_to res v1);
  eval_bnd (vals v1);
  let c1 = sub_from res m n;
  with v2. assert (A.pts_to res v2);
  eval_bnd (vals v2);
  let mask = S64.lt_mask c0 c1;
  mask_bit_ok mask;
  let c2 = add_masked res m n mask (hide (mask_bit mask));
  with v3. assert (A.pts_to res v3);
  eval_bnd (vals v3);
  sum_mod_cases (num vres) (num vres) (num vm);
  ()
}

(** [sub_mod res a b m n] is [res = (a - b) mod m]. *)
fn sub_mod (res: A.array S64.t) (a b m: A.array S64.t) (n: SZ.t)
           (#vres: erased (Seq.seq S64.t)) (#pa #pb #pm: perm)
           (#va #vb: erased (Seq.seq S64.t))
           (#vm: erased (s: Seq.seq S64.t { 0 < num s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to m #pm vm **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\
        Seq.length vb == SZ.v n /\ Seq.length vm == SZ.v n /\
        num va < num vm /\ num vb < num vm)
ensures exists* (v: Seq.seq S64.t).
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
  let mask = S64.eq_mask c0 (S64.classify 1uL);
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
fn lt_mask (a b: A.array S64.t) (n: SZ.t) (#pa #pb: perm)
           (#va #vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns r: S64.t
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (is_mask r /\ (num va < num vb <==> S64.v r == pow2 64 - 1))
{
  A.pts_to_len a;
  A.pts_to_len b;
  pre_zero va;
  pre_zero vb;
  let mut i = 0sz;
  let mut acc = S64.zero;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vacc: S64.t).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ is_mask vacc /\
          (pre va (SZ.v vi) < pre vb (SZ.v vi) <==> S64.v vacc == pow2 64 - 1))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let vacc = !acc;
    let ai = A.(a.(vi));
    let bi = A.(b.(vi));
    eval_lt_snoc (vals va) (vals vb) (SZ.v vi);
    pre_snoc va (SZ.v vi);
    pre_snoc vb (SZ.v vi);
    acc := S64.select (S64.eq_mask ai bi) vacc (S64.lt_mask ai bi);
    i := SZ.add vi 1sz;
  };
  pre_full va;
  pre_full vb;
  !acc
}

(** All ones if [a == b], all zeroes otherwise. *)
fn eq_mask (a b: A.array S64.t) (n: SZ.t) (#pa #pb: perm)
           (#va #vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns r: S64.t
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (is_mask r /\ (num va == num vb <==> S64.v r == pow2 64 - 1))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  let mut acc = S64.ones;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vacc: S64.t).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ is_mask vacc /\
          ((forall (k: nat). k < SZ.v vi ==>
              S64.v (Seq.index va k) == S64.v (Seq.index vb k)) <==>
           S64.v vacc == pow2 64 - 1))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let vacc = !acc;
    let ai = A.(a.(vi));
    let bi = A.(b.(vi));
    acc := S64.select (S64.eq_mask ai bi) vacc S64.zero;
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
fn mul_row (res: A.array S64.t) (a: A.array S64.t) (n: SZ.t) (bi: S64.t) (off: SZ.t)
           (#vres: erased (Seq.seq S64.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to a #pa va **
  pure (Seq.length va == SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vres /\
        SZ.fits (SZ.v off + SZ.v n))
returns c: S64.t
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va **
  pure (Seq.length v == Seq.length vres /\ S64.v c < base /\
        (forall (k: nat). SZ.v off + SZ.v n <= k /\ k < Seq.length v ==>
           Seq.index v k == Seq.index vres k) /\
        pre v (SZ.v off + SZ.v n) + S64.v c * wt (SZ.v off + SZ.v n) ==
          pre vres (SZ.v off + SZ.v n) + (num va * S64.v bi) * wt (SZ.v off))
{
  A.pts_to_len res;
  A.pts_to_len a;
  pre_zero va;
  let mut j = 0sz;
  let mut c = S64.zero;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (vc: S64.t) (v: Seq.seq S64.t).
    pts_to j vj ** pts_to c vc ** A.pts_to res v ** A.pts_to a #pa va **
    pure (SZ.v vj <= SZ.v n /\ Seq.length v == Seq.length vres /\
            (forall (k: nat). SZ.v off + SZ.v vj <= k /\ k < Seq.length v ==>
             Seq.index v k == Seq.index vres k) /\
          pre v (SZ.v off + SZ.v vj) + S64.v vc * wt (SZ.v off + SZ.v vj) ==
            pre vres (SZ.v off + SZ.v vj) + (pre va (SZ.v vj) * S64.v bi) * wt (SZ.v off))
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
             (S64.v aj) (S64.v bi) (S64.v rj) (S64.v vc) (S64.v r) (S64.v co)
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
let pre_carry (v: Seq.seq S64.t) (k: nat { k < Seq.length v }) (c: S64.t)
  : Lemma (requires S64.v (Seq.index v k) == 0)
          (ensures pre (Seq.upd v k c) (k + 1) == pre v k + wt k * S64.v c)
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
fn mul (res: A.array S64.t) (a b: A.array S64.t) (n: SZ.t)
       (#vres: erased (Seq.seq S64.t)) (#pa #pb: perm)
       (#va #vb: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vres == SZ.v n + SZ.v n /\ Seq.length va == SZ.v n /\
        Seq.length vb == SZ.v n /\ SZ.fits (SZ.v n + SZ.v n))
ensures exists* (v: Seq.seq S64.t).
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
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n + SZ.v n /\
          (forall (k: nat). SZ.v n + SZ.v vi <= k /\ k < Seq.length v ==>
             S64.v (Seq.index v k) == 0) /\
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
                   (S64.v bi) (S64.v c) (num va) (wt (SZ.v vi)) (wt (SZ.v pos));
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
fn sqr (res: A.array S64.t) (a: A.array S64.t) (n: SZ.t)
       (#vres: erased (Seq.seq S64.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to a #pa va **
  pure (Seq.length vres == SZ.v n + SZ.v n /\ Seq.length va == SZ.v n /\
        SZ.fits (SZ.v n + SZ.v n))
ensures exists* (v: Seq.seq S64.t).
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
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n + SZ.v n /\
          (forall (k: nat). SZ.v n + SZ.v vi <= k /\ k < Seq.length v ==>
             S64.v (Seq.index v k) == 0) /\
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
                   (S64.v bi) (S64.v c) (num va) (wt (SZ.v vi)) (wt (SZ.v pos));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  pre_full va;
  ()
}

#pop-options


#pop-options

(** {2 Copying, choosing, and reading a bit}

    What an exponentiation ladder needs on top of arithmetic: move a number,
    move it only if a mask says so, and look at one bit of the exponent
    without letting its value reach the control flow. *)

(** [copy res a n] is [res = a]. *)
fn copy (res: A.array S64.t) (a: A.array S64.t) (n: SZ.t)
        (#vres: erased (Seq.seq S64.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to a #pa va **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** pure (v == reveal va)
{
  A.pts_to_len res;
  A.pts_to_len a;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          (forall (k: nat). k < SZ.v vi /\ k < Seq.length v ==>
             Seq.index v k == Seq.index va k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let ai = A.(a.(vi));
    A.((res.(vi) <- ai));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  Seq.lemma_eq_intro v (reveal va);
  ()
}

let sel_eq (v va vres: Seq.seq S64.t) (k: nat)
  : Lemma (requires Seq.length v == Seq.length va /\
                    Seq.length v == Seq.length vres /\
                    (forall (j: nat). j < Seq.length v ==>
                       Seq.index v j ==
                         (if k = 1 then Seq.index va j else Seq.index vres j)))
          (ensures (k == 1 ==> v == va) /\ (k == 0 ==> v == vres))
  = if k = 1 then Seq.lemma_eq_intro v va else Seq.lemma_eq_intro v vres

(** [cselect res a n m k] is [res = a] if the mask is all ones and leaves
    [res] alone if it is all zeroes, in the same time either way. *)
fn cselect (res: A.array S64.t) (a: A.array S64.t) (n: SZ.t) (m: S64.t) (k: erased nat)
           (#vres: erased (Seq.seq S64.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to a #pa va **
  pure (Seq.length vres == SZ.v n /\ Seq.length va == SZ.v n /\
        is_mask m /\ stands_for m (reveal k))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va **
  pure ((reveal k == 1 ==> v == reveal va) /\
        (reveal k == 0 ==> v == reveal vres))
{
  A.pts_to_len res;
  A.pts_to_len a;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          (forall (k2: nat). k2 < SZ.v vi /\ k2 < Seq.length v ==>
             Seq.index v k2 ==
               (if reveal k = 1 then Seq.index va k2 else Seq.index vres k2)) /\
          (forall (k2: nat). SZ.v vi <= k2 /\ k2 < Seq.length v ==>
             Seq.index v k2 == Seq.index vres k2))
  decreases (SZ.v n - SZ.v (!i))
  {
    with v. assert (A.pts_to res v);
    let vi = !i;
    let ai = A.(a.(vi));
    let ri = A.(res.(vi));
    A.((res.(vi) <- S64.select m ai ri));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  sel_eq v va vres (reveal k);
  ()
}

(** Limb [q] is the number divided by that limb's weight, modulo the
    radix: exactly the digit it looks like. *)
let num_digit (v: Seq.seq S64.t) (q: nat { q < Seq.length v })
  : Lemma (num v / wt q % base == S64.v (Seq.index v q))
  = let n = Seq.length v in
    let hi = S64.v (Seq.index v q) + base * eval (Seq.slice (vals v) (q + 1) n) in
    eval_at (vals v) q;
    pre_bnd v q;
    Math.lemma_div_plus (pre v q) hi (wt q);
    Math.small_div (pre v q) (wt q);
    Math.lemma_mod_plus (S64.v (Seq.index v q))
      (eval (Seq.slice (vals v) (q + 1) n)) base;
    Math.small_mod (S64.v (Seq.index v q)) base

(** Shifting a limb out of the number and shifting inside the limb are
    the same shift. *)
let shift_in_limb (x: nat) (r: nat { r < 64 })
  : Lemma ((x % pow2 64) / pow2 r % 2 == x / pow2 r % 2)
  = assert_norm (pow2 1 == 2);
    Math.pow2_modulo_division_lemma_1 x r 64;
    Math.pow2_modulo_modulo_lemma_1 (x / pow2 r) 1 (64 - r)

(** Shifting down by [i] is shifting down to limb [i / 64] and then by the
    remainder. *)
let shift_num (n: nat) (q: nat) (r: nat)
  : Lemma (n / pow2 (rad * q + r) == (n / wt q) / pow2 r)
  = Math.pow2_plus (rad * q) r;
    Math.division_multiplication_lemma n (wt q) (pow2 r)

(** Bit [i] of the number is bit [i mod 64] of limb [i / 64]. *)
let num_bit (v: Seq.seq S64.t) (i: nat { i / 64 < Seq.length v })
  : Lemma (S64.v (Seq.index v (i / 64)) / pow2 (i % 64) % 2 == num v / pow2 i % 2)
  = let q = i / 64 in
    let r = i % 64 in
    num_digit v q;
    assert (num v / wt q % pow2 64 == S64.v (Seq.index v q));
    shift_in_limb (num v / wt q) r;
    assert (S64.v (Seq.index v q) / pow2 r % 2 == (num v / wt q) / pow2 r % 2);
    Math.euclidean_division_definition i 64;
    assert_norm (rad == 64);
    assert (rad * q + r == i);
    shift_num (num v) q r;
    assert (num v / pow2 i == (num v / wt q) / pow2 r)

(** Comparing a limb known to be zero or one against one turns it into a
    mask standing for that very value. *)
let bit_mask (bit one m: S64.t) (k: nat)
  : Lemma (requires k < 2 /\ S64.v bit == k /\ S64.v one == 1 /\
                    (S64.v bit == S64.v one ==> S64.v m == pow2 64 - 1) /\
                    (S64.v bit =!= S64.v one ==> S64.v m == 0))
          (ensures is_mask m /\ stands_for m k)
  = assert_norm (pow2 64 - 1 =!= 0)

(** [get_bit b i] is the all-ones mask when bit [i] of [b] is set.  The
    index is a loop counter and public; the bit itself never is. *)
fn get_bit (b: A.array S64.t) (i: SZ.t) (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to b #pb vb ** pure (SZ.v i / 64 < Seq.length vb)
returns m: S64.t
ensures A.pts_to b #pb vb **
  pure (is_mask m /\ stands_for m (num vb / pow2 (SZ.v i) % 2))
{
  A.pts_to_len b;
  let q = SZ.div i (SZ.uint_to_t 64);
  let r = SZ.rem i (SZ.uint_to_t 64);
  assert (pure (SZ.v q == SZ.v i / 64 /\ SZ.v r == SZ.v i % 64));
  let w = A.(b.(q));
  let rw = SZ.sizet_to_uint32 r;
  assert (pure (U32.v rw == SZ.v r));
  let x = S64.shift_right w rw;
  assert (pure (S64.v x == S64.v w / pow2 (SZ.v i % 64)));
  assert_norm (pow2 1 == 2);
  assert_norm (pow2 1 - 1 == 1);
  UInt.logand_mask #64 (S64.v x) 1;
  let one = S64.classify 1uL;
  assert (pure (S64.v one == 1));
  let bit = S64.logand x one;
  assert (pure (S64.v bit == S64.v x % 2));
  assert (pure (S64.v bit ==
    S64.v (Seq.index vb (SZ.v i / 64)) / pow2 (SZ.v i % 64) % 2));
  num_bit vb (SZ.v i);
  assert (pure (S64.v bit == num vb / pow2 (SZ.v i) % 2));
  let m = S64.eq_mask bit one;
  bit_mask bit one m (num vb / pow2 (SZ.v i) % 2);
  m
}


(** {2 Windows}

    The ladder in {!Hacl.Bignum.Exponentiation} consumes the exponent four
    bits at a time rather than one, which means reading a four-bit digit out
    of it and then picking one of sixteen precomputed powers without letting
    the choice reach the address bus.  Both halves are here, next to the
    single-bit versions they generalize. *)

(** Shifting inside a limb keeps the low [w] bits the number has there, as
    long as the window does not run off the top of the limb. *)
let shift_in_limb_w (x: nat) (r: nat) (w: nat { r + w <= 64 })
  : Lemma ((x % pow2 64) / pow2 r % pow2 w == x / pow2 r % pow2 w)
  = Math.pow2_modulo_division_lemma_1 x r 64;
    Math.pow2_modulo_modulo_lemma_1 (x / pow2 r) w (64 - r)

(** The [w] bits of the number at position [i] are the [w] bits of limb
    [i / 64] at position [i mod 64].  The side condition is that they do
    not straddle the limb boundary; a window whose width divides sixty-four
    and whose position is a multiple of that width never does. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"
let num_bits_at (v: Seq.seq S64.t) (i: nat { i / 64 < Seq.length v })
                (w: nat { i % 64 + w <= 64 })
  : Lemma (S64.v (Seq.index v (i / 64)) / pow2 (i % 64) % pow2 w ==
           num v / pow2 i % pow2 w)
  = let q = i / 64 in
    let r = i % 64 in
    num_digit v q;
    assert (num v / wt q % pow2 64 == S64.v (Seq.index v q));
    shift_in_limb_w (num v / wt q) r w;
    assert (S64.v (Seq.index v q) / pow2 r % pow2 w ==
            (num v / wt q) / pow2 r % pow2 w);
    Math.euclidean_division_definition i 64;
    assert_norm (rad == 64);
    assert (rad * q + r == i);
    shift_num (num v) q r;
    assert (num v / pow2 i == (num v / wt q) / pow2 r)
#pop-options

(** A position that is a multiple of four leaves room for four more bits in
    the same limb, because four divides sixty-four. *)
let window_fits (i: nat) : Lemma (requires i % 4 == 0) (ensures i % 64 + 4 <= 64)
  = assert_norm (pow2 2 == 4);
    assert_norm (pow2 6 == 64);
    Math.pow2_modulo_modulo_lemma_1 i 2 6

(** [get_digit b i] is the four-bit digit of [b] at position [i], which
    must be a multiple of four.  Unlike {!get_bit} this is a value, not a
    mask: it is consumed by {!table_select}, which is where it stops being
    something one could branch on. *)
inline_for_extraction
fn get_digit (b: A.array S64.t) (i: SZ.t) (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to b #pb vb ** pure (SZ.v i / 64 < Seq.length vb /\ SZ.v i % 4 == 0)
returns d: S64.t
ensures A.pts_to b #pb vb ** pure (S64.v d == num vb / pow2 (SZ.v i) % 16)
{
  A.pts_to_len b;
  window_fits (SZ.v i);
  let q = SZ.div i (SZ.uint_to_t 64);
  let r = SZ.rem i (SZ.uint_to_t 64);
  let w = A.(b.(q));
  assert (pure (w == Seq.index vb (SZ.v i / 64)));
  let x = S64.shift_right w (SZ.sizet_to_uint32 r);
  assert (pure (S64.v x == S64.v w / pow2 (SZ.v i % 64)));
  S64.logand_mask_low x 4ul;
  assert_norm (pow2 4 == 16);
  assert (pure (S64.v (S64.logand x (S64.mask_low 4ul)) == S64.v x % 16));
  num_bits_at vb (SZ.v i) 4;
  assert (pure (S64.v w / pow2 (SZ.v i % 64) % 16 ==
                num vb / pow2 (SZ.v i) % 16));
  S64.logand x (S64.mask_low 4ul)
}

(** Reading a table entry out of a flat array, as a sequence slice. *)
let sel_eq_at (v vt vres: Seq.seq S64.t) (off n: nat) (k: nat)
  : Lemma (requires Seq.length v == n /\ Seq.length vres == n /\
                    off + n <= Seq.length vt /\
                    (forall (j: nat). j < n ==>
                       Seq.index v j ==
                         (if k = 1 then Seq.index vt (off + j)
                          else Seq.index vres j)))
          (ensures (k == 1 ==> v == Seq.slice vt off (off + n)) /\
                   (k == 0 ==> v == vres))
  = if k = 1 then Seq.lemma_eq_intro v (Seq.slice vt off (off + n))
    else Seq.lemma_eq_intro v vres

(** [cselect_at res tbl n off m k] is {!cselect} reading the [n] limbs of
    [tbl] that begin at [off]. *)
fn cselect_at (res: A.array S64.t) (tbl: A.array S64.t) (n: SZ.t) (off: SZ.t)
              (m: S64.t) (k: erased nat)
              (#vres: erased (Seq.seq S64.t)) (#pt: perm)
              (#vt: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to tbl #pt vt **
  pure (Seq.length vres == SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vt /\
        SZ.fits (SZ.v off + SZ.v n) /\ is_mask m /\ stands_for m (reveal k))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to tbl #pt vt **
  pure (Seq.length v == SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vt /\
        (reveal k == 1 ==>
           v == Seq.slice vt (SZ.v off) (SZ.v off + SZ.v n)) /\
        (reveal k == 0 ==> v == reveal vres))
{
  A.pts_to_len res;
  A.pts_to_len tbl;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to tbl #pt vt **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          SZ.v off + SZ.v n <= Seq.length vt /\
          (forall (k2: nat). k2 < SZ.v vi ==>
             Seq.index v k2 ==
               (if reveal k = 1 then Seq.index vt (SZ.v off + k2)
                else Seq.index vres k2)) /\
          (forall (k2: nat). SZ.v vi <= k2 /\ k2 < SZ.v n ==>
             Seq.index v k2 == Seq.index vres k2))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let ai = A.(tbl.(SZ.add off vi));
    let ri = A.(res.(vi));
    A.((res.(vi) <- S64.select m ai ri));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  sel_eq_at v vt vres (SZ.v off) (SZ.v n) (reveal k);
  ()
}

(** [table_select res tbl n d] copies entry [d] of a sixteen-entry table of
    [n]-limb numbers into [res].  Every entry is read and fifteen of them
    are discarded, so neither the time nor the addresses touched depend on
    [d] -- which is a secret, being four bits of the exponent. *)
fn table_select (res: A.array S64.t) (tbl: A.array S64.t) (n: SZ.t)
                (d: S64.t) (k: erased nat)
                (#vres: erased (Seq.seq S64.t)) (#pt: perm)
                (#vt: erased (Seq.seq S64.t))
requires A.pts_to res vres ** A.pts_to tbl #pt vt **
  pure (Seq.length vres == SZ.v n /\ Seq.length vt == 16 * SZ.v n /\
        SZ.fits (16 * SZ.v n) /\ S64.v d == reveal k /\ reveal k < 16)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to tbl #pt vt **
  pure (Seq.length v == SZ.v n /\ Seq.length vt == 16 * SZ.v n /\
        reveal k < 16 /\
        v == Seq.slice vt (reveal k * SZ.v n) (reveal k * SZ.v n + SZ.v n))
{
  A.pts_to_len res;
  A.pts_to_len tbl;
  assert_norm (pow2 64 - 1 =!= 0);
  let mut e = 0sz;
  let mut ec = S64.classify 0uL;
  while (let ve = !e; SZ.lt ve (SZ.uint_to_t 16))
  invariant exists* (ve: SZ.t) (vec: S64.t) (v: Seq.seq S64.t).
    pts_to e ve ** pts_to ec vec ** A.pts_to res v ** A.pts_to tbl #pt vt **
    pure (SZ.v ve <= 16 /\ S64.v vec == SZ.v ve /\ Seq.length v == SZ.v n /\
          Seq.length vt == 16 * SZ.v n /\ reveal k < 16 /\
          (reveal k < SZ.v ve ==>
             v == Seq.slice vt (reveal k * SZ.v n)
                              (reveal k * SZ.v n + SZ.v n)))
  decreases (16 - SZ.v (!e))
  {
    let ve = !e;
    let vec = !ec;
    let m = S64.eq_mask d vec;
    cselect_at res tbl n (SZ.mul ve n) m (if SZ.v ve = reveal k then 1 else 0);
    ec := S64.add_mod vec (S64.classify 1uL);
    e := SZ.add ve 1sz;
  }
}

(** [table_store tbl src n off] writes the [n] limbs of [src] into [tbl] at
    [off] and leaves the rest of [tbl] alone.  Only the table's construction
    uses this, where the offset is a public loop counter; the secret-indexed
    read is {!table_select}. *)
fn table_store (tbl: A.array S64.t) (src: A.array S64.t) (n: SZ.t) (off: SZ.t)
               (#vt: erased (Seq.seq S64.t)) (#ps: perm)
               (#vs: erased (Seq.seq S64.t))
requires A.pts_to tbl vt ** A.pts_to src #ps vs **
  pure (Seq.length vs == SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vt /\
        SZ.fits (SZ.v off + SZ.v n))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to tbl v ** A.pts_to src #ps vs **
  pure (Seq.length v == Seq.length vt /\ Seq.length vs == SZ.v n /\
        SZ.v off + SZ.v n <= Seq.length vt /\
        (forall (j: nat). j < SZ.v n ==>
           Seq.index v (SZ.v off + j) == Seq.index vs j) /\
        (forall (j: nat). j < Seq.length v ==>
           (j < SZ.v off \/ SZ.v off + SZ.v n <= j) ==>
           Seq.index v j == Seq.index vt j))
{
  A.pts_to_len tbl;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to tbl v ** A.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == Seq.length vt /\
          Seq.length vs == SZ.v n /\
          SZ.v off + SZ.v n <= Seq.length vt /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index v (SZ.v off + j) == Seq.index vs j) /\
          (forall (j: nat). j < Seq.length v ==>
             (j < SZ.v off \/ SZ.v off + SZ.v vi <= j) ==>
             Seq.index v j == Seq.index vt j))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let si = A.(src.(vi));
    A.((tbl.(SZ.add off vi) <- si));
    i := SZ.add vi 1sz;
  }
}

(** The all-ones mask, for the table reads whose index is public. *)
inline_for_extraction
let ones () : m: S64.t { is_mask m /\ stands_for m 1 }
  = assert_norm (pow2 64 - 1 =!= 0); S64.mask_low 64ul
