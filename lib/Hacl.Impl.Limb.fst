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

(** Sixteen-bit limbs in sixty-four-bit secret words.

    [Spec.Bignum256] says what a sequence of limbs means; this module is the
    small machine layer underneath it, shared by everything that uses that
    representation.  There is nothing modulus-specific here and nothing
    curve-specific: a word is a [uint64] holding a value that the caller has
    bounded, a limb is one of those under [2^16], and the two loops are the
    carry pass with and without its carry out.

    {b Why sixteen bits.}  Custard compiles F* straight to C and the only
    machine integers it knows are the eight-, sixteen-, thirty-two- and
    sixty-four-bit ones.  With no hundred-and-twenty-eight-bit type there is
    no room for a radix-[2^51] product, so the radix has to come down far
    enough that sixteen products of two limbs still fit in a [uint64] with
    room for a reduction on top.  Sixteen is the largest such radix that
    also makes a limb exactly two bytes.

    Every operation below is a sixty-four-bit add, subtract, multiply, shift,
    mask or select on secret integers.  Nothing branches on a secret.

    [Hacl.Curve25519.Field] predates this module and still carries its own
    copy of the word operations; it is otherwise identical, and folding the
    two together is a refactor waiting for a quiet afternoon. *)
module Hacl.Impl.Limb

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 Viewing a slice of secrets as a sequence of numbers} *)

let vals (v: Seq.seq S64.t)
  : GTot (s: Seq.seq nat { Seq.length s == Seq.length v /\
                           (forall (i: nat). i < Seq.length v ==>
                              Seq.index s i == S64.v (Seq.index v i)) })
  = Seq.init_ghost (Seq.length v) (fun i -> (S64.v (Seq.index v i) <: nat))

let vals_upd (v: Seq.seq S64.t) (k: nat { k < Seq.length v }) (x: S64.t)
  : Lemma (vals (Seq.upd v k x) == Seq.upd (vals v) k (S64.v x))
  = Seq.lemma_eq_intro (vals (Seq.upd v k x)) (Seq.upd (vals v) k (S64.v x))

(** {2 The machine operations}

    Each is the [uint64] instruction plus the argument that it did not wrap.
    Keeping them here means the modular-arithmetic side condition is
    discharged once, against a two-line context, rather than inside a loop
    body that also carries the heap. *)

inline_for_extraction
let mask16 : m: S64.t { S64.v m == base - 1 } =
  assert_norm (base - 1 == 0xffff);
  S64.classify 0xffffuL

inline_for_extraction
let lo16 (x: S64.t) : r: S64.t { S64.v r == S64.v x % base } =
  UInt.logand_mask #64 (S64.v x) 16;
  S64.logand x mask16

inline_for_extraction
let hi16 (x: S64.t) : r: S64.t { S64.v r == S64.v x / base } =
  S64.shift_right x 16ul

inline_for_extraction
let addw (x y: S64.t)
  : Pure S64.t (requires S64.v x + S64.v y < pow2 64)
               (ensures fun z -> S64.v z == S64.v x + S64.v y)
  = Math.small_mod (S64.v x + S64.v y) (pow2 64);
    S64.add_mod x y

inline_for_extraction
let subw (x y: S64.t)
  : Pure S64.t (requires S64.v y <= S64.v x)
               (ensures fun z -> S64.v z == S64.v x - S64.v y)
  = Math.small_mod (S64.v x - S64.v y) (pow2 64);
    S64.sub_mod x y

inline_for_extraction
let mulw (x y: S64.t)
  : Pure S64.t (requires S64.v x * S64.v y < pow2 64)
               (ensures fun z -> S64.v z == S64.v x * S64.v y)
  = Math.small_mod (S64.v x * S64.v y) (pow2 64);
    S64.mul_mod x y

inline_for_extraction
let mulk (k: U64.t) (x: S64.t)
  : Pure S64.t (requires U64.v k * S64.v x < pow2 64)
               (ensures fun z -> S64.v z == U64.v k * S64.v x)
  = Math.small_mod (U64.v k * S64.v x) (pow2 64);
    S64.mul_mod (S64.classify k) x

(** {2 The carry pass}

    Limbs [0] to [14] carry into their neighbour and the top limb keeps its
    low sixteen bits.  [c] bounds the limbs on entry and [d] the carry; the
    caller supplies both, and [Spec.Bignum256.carry_run_chained] turns them
    into the bound that makes each division small.

    The two versions differ only in what becomes of the overflow out of the
    top limb: {!carry_out_op} returns it and {!carry_low_op} drops it. *)

#push-options "--z3rlimit 300"

(** The pass itself, over any width: limbs [0] to [n - 1] each hand their
    top bits to their neighbour.  [n] must leave a neighbour to carry into,
    so it is strictly below the length. *)
fn carry_run_op (a: A.array S64.t) (n: SZ.t) (c: erased nat) (d: erased nat)
                (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (SZ.v n < Seq.length va /\ ble (vals va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 64)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == Seq.length va /\
        vals va' == carry_run (vals va) (SZ.v n))
{
  A.pts_to_len a;
  div_le_of_lt (reveal c + reveal d) base d;
  Loops.repeati_zero carry_step (vals va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk n)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= SZ.v n /\ Seq.length v == Seq.length va /\
          vals v == carry_run (vals va) (SZ.v vk))
  decreases (SZ.v n - SZ.v (!k))
  {
    with v. assert (A.pts_to a v);
    let vk = !k;
    carry_run_chained (vals va) c d (SZ.v vk);
    carry_run_len (vals va) (SZ.v vk);
    let t = A.(a.(vk));
    let u = A.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S64.v t) (reveal c + reveal d) base;
    let lo = lo16 t;
    let up = addw u (hi16 t);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    vals_upd v (SZ.v vk) lo;
    vals_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (vals va);
    k := SZ.add vk 1sz;
  };
  ()
}

(** Sixteen limbs: the pass, then the top limb's overflow, returned. *)
fn carry_out_op (a: A.array S64.t) (c: erased nat) (d: erased nat)
                (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\ ble (vals va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 64)
returns r: S64.t
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == carry_low (vals va) /\
        S64.v r == carry_out (vals va))
{
  A.pts_to_len a;
  carry_run_op a 15sz c d;
  with v. assert (A.pts_to a v);
  carry_run_chained (vals va) c d 15;
  carry_run_len (vals va) 15;
  let t = A.(a.(15sz));
  let lo = lo16 t;
  let hi = hi16 t;
  A.((a.(15sz) <- lo));
  vals_upd v 15 lo;
  assert (pure (vals (Seq.upd v 15 lo) == carry_low (vals va)));
  hi
}

fn carry_low_op (a: A.array S64.t) (c: erased nat) (d: erased nat)
                (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\ ble (vals va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 64)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == carry_low (vals va))
{
  let _ = carry_out_op a c d;
  ()
}

#pop-options

(** {2 The schoolbook product}

    [nl * nl] limb products accumulated into [nw] lazy columns, no carries
    anywhere: [Spec.Bignum256.part] says exactly this, one row at a time,
    and the two loops here are its two indices.  Column [i + j] can receive
    at most [nl] products of two limbs, so the caller's bound
    [nl * lim^2 + lim^2 < 2^64] is what keeps a column inside a word.

    Deferring every carry to a single pass afterwards is the whole reason
    the radix is below half a word: it buys [64 - 2 * 16 = 32] bits of
    headroom, which is four more than the [nl = 16] rows need. *)

let ble_mono (s: Seq.seq nat) (c c': nat)
  : Lemma (requires ble s c /\ c <= c') (ensures ble s c') = ()

let addw_zerow (x: Seq.seq nat)
  : Lemma (requires Seq.length x == nw) (ensures addw x zerow == x)
  = Seq.lemma_eq_intro (addw x zerow) x

let acc_ble (a b acc: Seq.seq nat) (lim: nat) (i j: nat)
  : Lemma (requires ble a lim /\ ble b lim /\
                    acc == addw (part a b i) (rowj a b i j) /\ i < nl)
          (ensures ble acc (nl * (lim * lim)))
  = part_ble a b lim lim i;
    rowj_ble a b lim lim i j;
    addw_ble (part a b i) (rowj a b i j) (i * (lim * lim)) (lim * lim);
    Math.distributivity_add_left i 1 (lim * lim);
    Math.lemma_mult_le_right (lim * lim) (i + 1) nl;
    ble_mono acc (i * (lim * lim) + lim * lim) (nl * (lim * lim))

#push-options "--z3rlimit 300"

fn mul_columns (t a b: A.array S64.t) (lim: erased nat)
               (#vt: erased (Seq.seq S64.t))
               (#pa: perm) (#va: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == nw /\ Seq.length va == nl /\ Seq.length vb == nl /\
        ble (vals va) lim /\ ble (vals vb) lim /\
        nl * (reveal lim * reveal lim) + reveal lim * reveal lim < pow2 64)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ ble (vals vt') (nl * (reveal lim * reveal lim)) /\
        vals vt' == part (vals va) (vals vb) nl)
{
  A.pts_to_len t;
  A.pts_to_len a;
  A.pts_to_len b;
  let z = S64.zero;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 31sz)
  invariant exists* (vc: SZ.t) (v: Seq.seq S64.t).
    pts_to c vc ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vc <= 31 /\ Seq.length v == nw /\
          (forall (k: nat). k < SZ.v vc ==> Seq.index (vals v) k == 0))
  decreases (31 - SZ.v (!c))
  {
    let vc = !c;
    A.((t.(vc) <- z));
    c := SZ.add vc 1sz;
  };
  with v0. assert (A.pts_to t v0);
  assert (pure (vals v0 `Seq.equal` zerow));
  Loops.repeati_zero (mul_step (vals va) (vals vb)) zerow;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length v == nw /\
          vals v == part (vals va) (vals vb) (SZ.v vi))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let ai = A.(a.(vi));
    part_len (vals va) (vals vb) (SZ.v vi);
    rowj_zero (vals va) (vals vb) (SZ.v vi);
    addw_zerow (part (vals va) (vals vb) (SZ.v vi));
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj 16sz)
    invariant exists* (vj: SZ.t) (v: Seq.seq S64.t).
      pts_to j vj ** pts_to i vi ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      pure (SZ.v vj <= 16 /\ Seq.length v == nw /\ SZ.v vi < 16 /\
            vals v == addw (part (vals va) (vals vb) (SZ.v vi))
                           (rowj (vals va) (vals vb) (SZ.v vi) (SZ.v vj)))
    decreases (16 - SZ.v (!j))
    {
      with v. assert (A.pts_to t v);
      let vj = !j;
      acc_ble (vals va) (vals vb) (vals v) lim (SZ.v vi) (SZ.v vj);
      let bj = A.(b.(vj));
      let pos = SZ.add vi vj;
      let cur = A.(t.(pos));
      Math.lemma_mult_le_left (S64.v ai) (S64.v bj) lim;
      Math.lemma_mult_le_right lim (S64.v ai) lim;
      let nw' = addw cur (mulw ai bj);
      A.((t.(pos) <- nw'));
      vals_upd v (SZ.v vi + SZ.v vj) nw';
      addw_rowj_step (part (vals va) (vals vb) (SZ.v vi)) (vals va) (vals vb)
                     (SZ.v vi) (SZ.v vj);
      j := SZ.add vj 1sz;
    };
    part_step (vals va) (vals vb) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  part_ble (vals va) (vals vb) lim lim nl;
  ()
}

#pop-options

(** {2 A branch-free conditional}

    [m] is all ones or all zeroes -- the output of an [eq_mask] or a
    [gte_mask] -- and the whole slice takes one side or the other.  The
    caller has already turned the question into a mask, so this is the last
    place a secret could have become a branch, and it does not. *)

#push-options "--z3rlimit 200"

fn cselect (a b: A.array S64.t) (m: S64.t)
           (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == nl /\
        (S64.v m == 0 \/ S64.v m == pow2 64 - 1))
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b #pb vb **
  pure (Seq.length va' == nl /\
        vals va' == (if S64.v m = 0 then vals va else vals vb))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               (if S64.v m = 0 then Seq.index (vals va) k else Seq.index (vals vb) k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < nl ==>
             Seq.index (vals v) k == Seq.index (vals va) k))
  decreases (16 - SZ.v (!i))
  {
    with v. assert (A.pts_to a v);
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let z = S64.select m y x;
    A.((a.(vi) <- z));
    vals_upd v (SZ.v vi) z;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  assert (pure (vals v `Seq.equal` (if S64.v m = 0 then vals va else vals vb)));
}

#pop-options

#pop-options
