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

(** Sixty-four-bit limbs in sixty-four-bit secret words.

    [Spec.Bignum4] says what a sequence of limbs means; this module is the
    small machine layer underneath it, the twin of {!Hacl.Impl.Limb} one
    radix up.  A word is a [uint64] and a limb is the whole of it, so there
    is no masking anywhere and the splitting all happens on the wide type.

    {b What changes at sixty-four bits.}  A limb no longer has spare room,
    so a lazy sum does not fit in a word and a product does not fit in a
    column.  Both are handled the same way: the value is computed in a
    [uint128] and put back as two halves.  For the carry pass that is the
    ordinary [lo]/[hi] split; for the schoolbook multiplier it is the
    column split that {!Spec.Bignum4.srow} describes, with the low half of
    [a_i b_j] going to column [i + j] and the high half to column
    [i + j + 1].

    Every operation below is a sixty-four- or hundred-and-twenty-eight-bit
    add, multiply, shift or select on secret integers.  Nothing branches on
    a secret. *)
module Hacl.Impl.Limb4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Cast = Hacl.Secret.Cast
module Classical = FStar.Classical
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

(** A word is always a proper limb now, which the callers of the carry pass
    would otherwise have to say by hand. *)
let vals_bnd (v: Seq.seq S64.t) : Lemma (bnd (vals v) base)
  = assert_norm (base == pow2 64)

(** The columns of a product do not fit in a word, so they get their own
    view. *)

let vals128 (v: Seq.seq S128.t)
  : GTot (s: Seq.seq nat { Seq.length s == Seq.length v /\
                           (forall (i: nat). i < Seq.length v ==>
                              Seq.index s i == S128.v (Seq.index v i)) })
  = Seq.init_ghost (Seq.length v) (fun i -> (S128.v (Seq.index v i) <: nat))

let vals128_upd (v: Seq.seq S128.t) (k: nat { k < Seq.length v }) (x: S128.t)
  : Lemma (vals128 (Seq.upd v k x) == Seq.upd (vals128 v) k (S128.v x))
  = Seq.lemma_eq_intro (vals128 (Seq.upd v k x)) (Seq.upd (vals128 v) k (S128.v x))

(** {2 The machine operations}

    Each is the instruction plus the argument that it did not wrap. *)

inline_for_extraction
let widen (x: S64.t) : r: S128.t { S128.v r == S64.v x } = Cast.u64_to_u128 x

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

(** The product of two limbs is a wide value now, so there is no word
    multiply; [mulw] is the wrapping one, which is exactly what the
    Montgomery digit wants. *)
inline_for_extraction
let mulw (x y: S64.t) : r: S64.t { S64.v r == (S64.v x * S64.v y) % base } =
  assert_norm (base == pow2 64);
  S64.mul_mod x y

inline_for_extraction
let addd (x y: S128.t)
  : Pure S128.t (requires S128.v x + S128.v y < pow2 128)
                (ensures fun z -> S128.v z == S128.v x + S128.v y)
  = Math.small_mod (S128.v x + S128.v y) (pow2 128);
    S128.add_mod x y

(** The two halves of a wide value.  [lo64d] is a truncation and [hi64d] a
    shift; together they are {!Spec.Bignum4.plo} and {!Spec.Bignum4.phi}. *)

inline_for_extraction
let lo64d (x: S128.t) : r: S64.t { S64.v r == S128.v x % base } =
  assert_norm (base == pow2 64);
  Cast.u128_to_u64 x

inline_for_extraction
let hi64d (x: S128.t) : r: S128.t { S128.v r == S128.v x / base } =
  assert_norm (base == pow2 64);
  S128.shift_right x 64ul

(** The high half of a product of two limbs is itself a limb, so it can go
    back in a word. *)
inline_for_extraction
let hi64w (x: S128.t)
  : Pure S64.t (requires S128.v x < pow2 128)
               (ensures fun z -> S64.v z == S128.v x / base)
  = assert_norm (base == pow2 64);
    Math.lemma_div_lt (S128.v x) 128 64;
    Math.small_mod (S128.v x / base) (pow2 64);
    Cast.u128_to_u64 (S128.shift_right x 64ul)

inline_for_extraction
let narrow128 (x: S128.t)
  : Pure S64.t (requires S128.v x < pow2 64)
               (ensures fun z -> S64.v z == S128.v x)
  = Math.small_mod (S128.v x) (pow2 64);
    Cast.u128_to_u64 x

(** The digit of a wide column, modulo the radix: only the bottom limb of
    the column takes part, which is what keeps this a word multiply. *)
let mod_mul_lo (a mu: nat)
  : Lemma ((a * mu) % base == ((a % base) * mu) % base)
  = Math.lemma_mod_mul_distr_l a mu base

(** {2 The carry pass}

    Only the wide version survives at this radix: a word is already a
    proper limb, so a carry pass over words would have nothing to do.  The
    columns of a product and of the reduction are what need normalising,
    and [c] bounds them on entry while [d] bounds the carry.  The caller
    supplies both, and [Spec.Bignum4.carry_run_chained] turns them into the
    bound that makes each division small. *)

#push-options "--z3rlimit 300"

fn carry_run128_op (a: A.array S128.t) (n: SZ.t) (c: erased nat) (d: erased nat)
                   (#va: erased (Seq.seq S128.t))
requires A.pts_to a va **
  pure (SZ.v n < Seq.length va /\ ble (vals128 va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 128)
ensures exists* (va': Seq.seq S128.t).
  A.pts_to a va' **
  pure (Seq.length va' == Seq.length va /\
        vals128 va' == carry_run (vals128 va) (SZ.v n))
{
  A.pts_to_len a;
  div_le_of_lt (reveal c + reveal d) base d;
  Loops.repeati_zero carry_step (vals128 va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk n)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= SZ.v n /\ Seq.length v == Seq.length va /\
          vals128 v == carry_run (vals128 va) (SZ.v vk))
  decreases (SZ.v n - SZ.v (!k))
  {
    with v. assert (A.pts_to a v);
    let vk = !k;
    carry_run_chained (vals128 va) c d (SZ.v vk);
    carry_run_len (vals128 va) (SZ.v vk);
    let t = A.(a.(vk));
    let u = A.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S128.v t) (reveal c + reveal d) base;
    let lo = Cast.u64_to_u128 (lo64d t);
    let up = addd u (hi64d t);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    vals128_upd v (SZ.v vk) lo;
    vals128_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (vals128 va);
    k := SZ.add vk 1sz;
  };
  ()
}

#pop-options

(** {2 The schoolbook product}

    Sixteen limb products accumulated into eight lazy columns, no carries
    anywhere: [Spec.Bignum4.part] says exactly this, one row at a time, and
    the two loops here are its two indices.  What is new at this radix is
    that a product does not fit in a column, so each one is added twice --
    its low half at [i + j] and its high half at [i + j + 1] -- which is
    what {!Spec.Bignum4.srow} is defined to do.

    A column therefore receives at most [nl] low halves and [nl] high
    halves, all below [base], so it stays under [2^67] and there is no
    bound for the caller to supply. *)

let ble_mono (s: Seq.seq nat) (c c': nat)
  : Lemma (requires ble s c /\ c <= c') (ensures ble s c') = ()

let addw_zerow (x: Seq.seq nat)
  : Lemma (requires Seq.length x == nw) (ensures addw x zerow == x)
  = Seq.lemma_eq_intro (addw x zerow) x

let acc_ble (a b acc: Seq.seq nat) (i j: nat)
  : Lemma (requires ble a (base - 1) /\ ble b (base - 1) /\
                    acc == addw (part a b i) (rowj a b i j) /\ i < nl)
          (ensures ble acc (nl * (2 * (base - 1))))
  = part_ble a b i;
    rowj_ble a b i j;
    part_len a b i;
    addw_ble (part a b i) (rowj a b i j) (i * (2 * (base - 1))) (2 * (base - 1));
    Math.distributivity_add_left i 1 (2 * (base - 1));
    Math.lemma_mult_le_right (2 * (base - 1)) (i + 1) nl;
    ble_mono acc (i * (2 * (base - 1)) + 2 * (base - 1)) (nl * (2 * (base - 1)))

#push-options "--z3rlimit 400"

fn mul_columns (t: A.array S128.t) (a b: A.array S64.t)
               (#vt: erased (Seq.seq S128.t))
               (#pa: perm) (#va: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == nw /\ Seq.length va == nl /\ Seq.length vb == nl)
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ ble (vals128 vt') (nl * (2 * (base - 1))) /\
        vals128 vt' == part (vals va) (vals vb) nl)
{
  A.pts_to_len t;
  A.pts_to_len a;
  A.pts_to_len b;
  vals_bnd va;
  vals_bnd vb;
  assert_norm (nl * (2 * (base - 1)) + base < pow2 128);
  let z = S128.zero;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (v: Seq.seq S128.t).
    pts_to c vc ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vc <= 8 /\ Seq.length v == nw /\
          (forall (k: nat). k < SZ.v vc ==> Seq.index (vals128 v) k == 0))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    A.((t.(vc) <- z));
    c := SZ.add vc 1sz;
  };
  with v0. assert (A.pts_to t v0);
  assert (pure (vals128 v0 `Seq.equal` zerow));
  Loops.repeati_zero (mul_step (vals va) (vals vb)) zerow;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 4 /\ Seq.length v == nw /\
          vals128 v == part (vals va) (vals vb) (SZ.v vi))
  decreases (4 - SZ.v (!i))
  {
    let vi = !i;
    let ai = A.(a.(vi));
    part_len (vals va) (vals vb) (SZ.v vi);
    rowj_zero (vals va) (vals vb) (SZ.v vi);
    addw_zerow (part (vals va) (vals vb) (SZ.v vi));
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj 4sz)
    invariant exists* (vj: SZ.t) (v: Seq.seq S128.t).
      pts_to j vj ** pts_to i vi ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      pure (SZ.v vj <= 4 /\ Seq.length v == nw /\ SZ.v vi < 4 /\
            vals128 v == addw (part (vals va) (vals vb) (SZ.v vi))
                              (rowj (vals va) (vals vb) (SZ.v vi) (SZ.v vj)))
    decreases (4 - SZ.v (!j))
    {
      with v. assert (A.pts_to t v);
      let vj = !j;
      acc_ble (vals va) (vals vb) (vals128 v) (SZ.v vi) (SZ.v vj);
      let bj = A.(b.(vj));
      let pos = SZ.add vi vj;
      let pos1 = SZ.add pos 1sz;
      let p = S128.mul_wide ai bj;
      let pl = Cast.u64_to_u128 (lo64d p);
      let ph = hi64d p;
      Math.lemma_mult_le_left (S64.v ai) (S64.v bj) (base - 1);
      Math.lemma_mult_le_right (base - 1) (S64.v ai) (base - 1);
      phi_le (S64.v ai * S64.v bj) (base - 1);
      let cur = A.(t.(pos));
      let nv = addd cur pl;
      A.((t.(pos) <- nv));
      vals128_upd v (SZ.v vi + SZ.v vj) nv;
      with v1. assert (A.pts_to t v1);
      let cur1 = A.(t.(pos1));
      let nv1 = addd cur1 ph;
      A.((t.(pos1) <- nv1));
      vals128_upd v1 (SZ.v vi + SZ.v vj + 1) nv1;
      addw_rowj_step (part (vals va) (vals vb) (SZ.v vi)) (vals va) (vals vb)
                     (SZ.v vi) (SZ.v vj);
      j := SZ.add vj 1sz;
    };
    part_step (vals va) (vals vb) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  part_ble (vals va) (vals vb) nl;
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
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               (if S64.v m = 0 then Seq.index (vals va) k else Seq.index (vals vb) k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < nl ==>
             Seq.index (vals v) k == Seq.index (vals va) k))
  decreases (4 - SZ.v (!i))
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
