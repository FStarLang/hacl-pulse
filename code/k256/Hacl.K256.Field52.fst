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

(** secp256k1's field, on five sixty-four-bit secret integers.

    A field element is a five-element slice; limb [k] carries bits [52k] to
    [52k+52], and the operations keep every limb at or below [2^53 - 1].
    This replaces the four-limb Montgomery representation the curve shared
    with P-256, which held the prime exactly and therefore had no room to
    accumulate: every limb product there had to be split into a low and a
    high column and added into two separate accumulators, and
    [Hacl_K256_Field_fmul] came out at four hundred and forty-seven
    instructions for sixteen multiplications.

    Five fifty-two-bit limbs waste twenty bits of space and buy all of it
    back.  A column of the schoolbook product is a sum of five products of
    numbers below [2^53], so it is below [2^108.4] and it simply
    accumulates: twenty-five [mul_wide]s and twenty-five adds, no split and
    no carry between limbs.  The reduction is not Montgomery at all --
    [2^260 = 16 * prime + 2^36 + 15632] -- so the Montgomery factor
    disappears from the representation, and with it [fto], [ffrom], the
    four constant tables that held [R], [R^2] and the rest, and the
    conditional subtraction every operation used to end with.

    All the arithmetic lives in [Spec.K256.Field52], which states each
    operation as one function on [Seq.seq nat] and one lemma; the job here
    is to compute the sequence that lemma names.  The limbs are secret
    integers throughout, and there is no branch on a secret anywhere.

    The shape of this module is [Hacl.Curve25519.Field]'s, which does the
    same at radix [2^51], and the two should be read side by side. *)
module Hacl.K256.Field52

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.K256.Freeze

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Cast = Hacl.Secret.Cast
module Loops = Hacl.Spec.Loops
module K = Spec.K256
module F52 = Spec.K256.Field52
module S8 = Hacl.Secret.UInt8
module Declassify = Hacl.Secret.Declassify
module B4 = Spec.Bignum4
module F4 = Spec.Field4
module SKF = Spec.K256.Field
module L4 = Hacl.Impl.Limb4
module IB4 = Hacl.Impl.Bignum4
module IM4 = Hacl.Impl.Mont4
module KT = Hacl.K256.Tables
module KT52 = Hacl.K256.Tables52
module Tbl = Hacl.Impl.Table
module By = Hacl.Spec.Bytes
module RP = Spec.K256.Repack
module G = Pulse.Lib.GlobalArray

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

let vals128 (v: Seq.seq S128.t)
  : GTot (s: Seq.seq nat { Seq.length s == Seq.length v /\
                           (forall (i: nat). i < Seq.length v ==>
                              Seq.index s i == S128.v (Seq.index v i)) })
  = Seq.init_ghost (Seq.length v) (fun i -> (S128.v (Seq.index v i) <: nat))

let vals128_upd (v: Seq.seq S128.t) (k: nat { k < Seq.length v }) (x: S128.t)
  : Lemma (vals128 (Seq.upd v k x) == Seq.upd (vals128 v) k (S128.v x))
  = Seq.lemma_eq_intro (vals128 (Seq.upd v k x)) (Seq.upd (vals128 v) k (S128.v x))

(** {2 The machine operations}

    Each is the [uint64] instruction plus the argument that it did not
    wrap.  Keeping them here means the modular-arithmetic side condition is
    discharged once, against a two-line context, rather than inside a loop
    body that also carries the heap. *)

inline_for_extraction
let mask52 : m: S64.t { S64.v m == base - 1 } =
  assert_norm (base - 1 == 0xfffffffffffff);
  S64.classify 0xfffffffffffffuL

inline_for_extraction
let lo52 (x: S64.t) : r: S64.t { S64.v r == S64.v x % base } =
  assert_norm (base == pow2 52);
  UInt.logand_mask #64 (S64.v x) 52;
  S64.logand x mask52

inline_for_extraction
let hi52 (x: S64.t) : r: S64.t { S64.v r == S64.v x / base } =
  assert_norm (base == pow2 52);
  S64.shift_right x 52ul

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
let mulk (k: U64.t) (x: S64.t)
  : Pure S64.t (requires U64.v k * S64.v x < pow2 64)
               (ensures fun z -> S64.v z == U64.v k * S64.v x)
  = Math.small_mod (U64.v k * S64.v x) (pow2 64);
    S64.mul_mod (S64.classify k) x

(** The reduction constant as a word.  Curve25519's is nineteen and fits in
    a shift and two adds; [2^36 + 15632] does not, so it is multiplied for
    real -- which costs nothing, because the operand it multiplies is always
    a single narrowed carry and the result always wanted at full width. *)
inline_for_extraction
let cfw : (k: U64.t { U64.v k == cf }) = 0x1000003d10uL

(** {2 The same instructions one width up} *)

inline_for_extraction
let addd (x y: S128.t)
  : Pure S128.t (requires S128.v x + S128.v y < pow2 128)
                (ensures fun z -> S128.v z == S128.v x + S128.v y)
  = Math.small_mod (S128.v x + S128.v y) (pow2 128);
    S128.add_mod x y

inline_for_extraction
let lo52d (x: S128.t) : r: S64.t { S64.v r == S128.v x % base } =
  assert_norm (base == pow2 52);
  Math.pow2_modulo_modulo_lemma_1 (S128.v x) 52 64;
  UInt.logand_mask #64 (S128.v x % pow2 64) 52;
  S64.logand (Cast.u128_to_u64 x) mask52

inline_for_extraction
let hi52d (x: S128.t) : r: S128.t { S128.v r == S128.v x / base } =
  assert_norm (base == pow2 52);
  S128.shift_right x 52ul

inline_for_extraction
let narrow128 (x: S128.t)
  : Pure S64.t (requires S128.v x < pow2 64)
               (ensures fun z -> S64.v z == S128.v x)
  = Math.small_mod (S128.v x) (pow2 64);
    Cast.u128_to_u64 x

(** A limb product.  No splitting: a column is a sum of five of these and
    a sum of five numbers below [2^106] is below [2^109], which is the
    whole reason the field moved off sixty-four-bit limbs. *)
inline_for_extraction
let mul52 (x y: S64.t)
  : Pure S128.t (requires S64.v x <= lim /\ S64.v y <= lim)
                (ensures fun z -> S128.v z == S64.v x * S64.v y /\
                                  S128.v z <= lim * lim)
  = Math.lemma_mult_le_left (S64.v x) (S64.v y) lim;
    Math.lemma_mult_le_right lim (S64.v x) lim;
    S128.mul_wide x y

(** [cf] times a carried digit.  The operand is always a digit or a carry,
    never a limb of an argument, so one widening multiply does it. *)
inline_for_extraction
let mulcf (x: S64.t) : (z: S128.t { S128.v z == cf * S64.v x }) =
  Math.swap_mul (U64.v cfw) (S64.v x);
  S128.mul_wide (S64.classify cfw) x

(** {2 The constants and masks freezing needs} *)

inline_for_extraction
let cf1w : (k: U64.t { U64.v k == cf1 }) = 4294968273uL

inline_for_extraction
let mask48 : m: S64.t { S64.v m == hib - 1 } =
  assert_norm (hib - 1 == 0xffffffffffff);
  S64.classify 0xffffffffffffuL

inline_for_extraction
let lo48 (x: S64.t) : r: S64.t { S64.v r == S64.v x % hib } =
  assert_norm (hib == pow2 48);
  UInt.logand_mask #64 (S64.v x) 48;
  S64.logand x mask48

inline_for_extraction
let hi48 (x: S64.t) : r: S64.t { S64.v r == S64.v x / hib } =
  assert_norm (hib == pow2 48);
  S64.shift_right x 48ul

(** A mask is all ones or all zeroes, and stays that way under [logand]
    and [logor].  The two lemmas are the four bitwise facts the SMT solver
    cannot see through a [logand] symbol. *)
inline_for_extraction
let mand (x y: S64.t)
  : Pure S64.t (requires (S64.v x == 0 \/ S64.v x == pow2 64 - 1) /\
                         (S64.v y == 0 \/ S64.v y == pow2 64 - 1))
               (ensures fun r -> (S64.v r == 0 \/ S64.v r == pow2 64 - 1) /\
                                 (S64.v r == pow2 64 - 1 <==>
                                  (S64.v x == pow2 64 - 1 /\ S64.v y == pow2 64 - 1)))
  = UInt.logand_lemma_1 #64 (S64.v x);
    UInt.logand_lemma_2 #64 (S64.v x);
    UInt.logand_commutative #64 (S64.v x) (S64.v y);
    UInt.logand_lemma_1 #64 (S64.v y);
    UInt.logand_lemma_2 #64 (S64.v y);
    assert_norm (pow2 64 - 1 =!= 0);
    S64.logand x y

inline_for_extraction
let mor (x y: S64.t)
  : Pure S64.t (requires (S64.v x == 0 \/ S64.v x == pow2 64 - 1) /\
                         (S64.v y == 0 \/ S64.v y == pow2 64 - 1))
               (ensures fun r -> (S64.v r == 0 \/ S64.v r == pow2 64 - 1) /\
                                 (S64.v r == pow2 64 - 1 <==>
                                  (S64.v x == pow2 64 - 1 \/ S64.v y == pow2 64 - 1)))
  = UInt.logor_lemma_1 #64 (S64.v x);
    UInt.logor_lemma_2 #64 (S64.v x);
    UInt.logor_commutative #64 (S64.v x) (S64.v y);
    UInt.logor_lemma_1 #64 (S64.v y);
    UInt.logor_lemma_2 #64 (S64.v y);
    assert_norm (pow2 64 - 1 =!= 0);
    S64.logor x y

(** {2 The carry pass on words}

    Limbs [0] to [3] carry into their neighbour, and the top limb carries
    round into limb [0] multiplied by the reduction constant.  [c] bounds
    the limbs on entry and [d] the carry; the caller supplies both, and
    [Spec.K256.Field52.pass] turns them into the bound on exit.

    This is the pass an addition, a subtraction or a negation uses, where
    every intermediate is a word.  A multiplication's is one width up, in
    {!carry_chain128}. *)

#push-options "--z3rlimit 200"

[@@ FStar.Attributes.CInline]
fn carry_chain (a: A.array S64.t) (c: erased nat) (d: erased nat)
               (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\ ble (vals va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 64 /\ base + cf * reveal d < pow2 64)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == carry_pass (vals va))
{
  A.pts_to_len a;
  div_le_of_lt (reveal c + reveal d) base d;
  Loops.repeati_zero carry_step (vals va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 4sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= 4 /\ Seq.length v == nl /\
          vals v == carry_run (vals va) (SZ.v vk))
  decreases (4 - SZ.v (!k))
  {
    with v. assert (A.pts_to a v);
    let vk = !k;
    carry_run_chained (vals va) c d (SZ.v vk);
    carry_run_len (vals va) (SZ.v vk);
    let t = A.(a.(vk));
    let u = A.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S64.v t) (reveal c + reveal d) base;
    let lo = lo52 t;
    let up = addw u (hi52 t);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    vals_upd v (SZ.v vk) lo;
    vals_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (vals va);
    k := SZ.add vk 1sz;
  };
  with v. assert (A.pts_to a v);
  carry_run_chained (vals va) c d 4;
  carry_run_len (vals va) 4;
  let t = A.(a.(4sz));
  let z = A.(a.(0sz));
  Math.lemma_div_le (S64.v t) (reveal c + reveal d) base;
  let lo = lo52 t;
  let z' = addw z (mulk cfw (hi52 t));
  A.((a.(4sz) <- lo));
  A.((a.(0sz) <- z'));
  vals_upd v 4 lo;
  vals_upd (Seq.upd v 4 lo) 0 z';
  assert (pure (vals (Seq.upd (Seq.upd v 4 lo) 0 z') == carry_pass (vals va)));
}

#pop-options

(** {2 Addition} *)

#push-options "--z3rlimit 120"

[@@ FStar.Attributes.CInline]
fn fadd (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem (vals vout') /\
        fev (vals vout') == K.fadd (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 5 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vb) k))
  decreases (5 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    assert_norm (lim + lim < pow2 64);
    A.((out.(vi) <- addw x y));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  assert (pure (vals v `Seq.equal` Spec.Bignum52.addw (vals va) (vals vb)));
  addw_ble (vals va) (vals vb) lim lim;
  assert_norm (lim + lim + 5 < base * 6);
  assert_norm (lim + lim + 5 < pow2 64);
  assert_norm (base + cf * 5 < pow2 64);
  carry_chain out (2 * lim) 5;
  with v'. assert (A.pts_to out v');
  assert (pure (vals v' == fadd_spec (vals va) (vals vb)));
  fadd_spec_ok (vals va) (vals vb);
  assert (pure (felem (vals v')));
}

(** {2 Subtraction}

    [p64] is [64 * prime] written in limbs; every one of its limbs
    dominates every limb of the subtrahend, so the difference is taken limb
    by limb with no borrow.  Curve25519 needs only eight primes, and the
    difference is the four bits [2^260] has over [2^256]: the top limb of
    this prime is [2^48 - 1] where an element's is [2^53]. *)

[@@ FStar.Attributes.CInline]
fn fsub (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem (vals vout') /\
        fev (vals vout') == K.fsub (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (lim < 18014398509481920);
  assert_norm (lim + 288230376151711680 < pow2 64);
  p64_index 0;
  let x0 = A.(a.(0sz));
  let y0 = A.(b.(0sz));
  A.((out.(0sz) <- subw (addw x0 (S64.classify 288230101273742272uL)) y0));
  let mut i = 1sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (1 <= SZ.v vi /\ SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               Seq.index (vals va) k + Seq.index p64 k - Seq.index (vals vb) k))
  decreases (4 - SZ.v (!i))
  {
    let vi = !i;
    p64_index (SZ.v vi);
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((out.(vi) <- subw (addw x (S64.classify 288230376151711680uL)) y));
    i := SZ.add vi 1sz;
  };
  p64_index 4;
  let x4 = A.(a.(4sz));
  let y4 = A.(b.(4sz));
  A.((out.(4sz) <- subw (addw x4 (S64.classify 18014398509481920uL)) y4));
  with v. assert (A.pts_to out v);
  p64_ok ();
  assert (pure (vals v `Seq.equal` Spec.K256.Field52.subw (vals va) (vals vb)));
  subw_ok (vals va) (vals vb);
  assert_norm (lim + 64 * (base - 1) + 66 < base * 67);
  assert_norm (lim + 64 * (base - 1) + 66 < pow2 64);
  assert_norm (base + cf * 66 < pow2 64);
  carry_chain out (lim + 64 * (base - 1)) 66;
  with v'. assert (A.pts_to out v');
  assert (pure (vals v' == fsub_spec (vals va) (vals vb)));
  fsub_spec_ok (vals va) (vals vb);
  assert (pure (felem (vals v')));
}

(** {2 Negation}

    The same with nothing to subtract from: [p64]'s limbs are the whole of
    the minuend. *)

[@@ FStar.Attributes.CInline]
fn fneg (out a: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == nl /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (felem (vals vout') /\ fev (vals vout') == K.fneg (fev (vals va)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  assert_norm (lim < 18014398509481920);
  p64_index 0;
  let x0 = A.(a.(0sz));
  A.((out.(0sz) <- subw (S64.classify 288230101273742272uL) x0));
  let mut i = 1sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va **
    pure (1 <= SZ.v vi /\ SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index p64 k - Seq.index (vals va) k))
  decreases (4 - SZ.v (!i))
  {
    let vi = !i;
    p64_index (SZ.v vi);
    let x = A.(a.(vi));
    A.((out.(vi) <- subw (S64.classify 288230376151711680uL) x));
    i := SZ.add vi 1sz;
  };
  p64_index 4;
  let x4 = A.(a.(4sz));
  A.((out.(4sz) <- subw (S64.classify 18014398509481920uL) x4));
  with v. assert (A.pts_to out v);
  p64_ok ();
  assert (pure (vals v `Seq.equal` Spec.K256.Field52.negw (vals va)));
  negw_ok (vals va);
  assert_norm (64 * (base - 1) + 64 < base * 65);
  assert_norm (64 * (base - 1) + 64 < pow2 64);
  assert_norm (base + cf * 64 < pow2 64);
  carry_chain out (64 * (base - 1)) 64;
  with v'. assert (A.pts_to out v');
  assert (pure (vals v' == fneg_spec (vals va)));
  fneg_spec_ok (vals va);
  assert (pure (felem (vals v')));
}

#pop-options

(** {2 Multiplication}

    Twenty-five widening multiplies into nine columns, a four-step chain
    that turns the top four into proper digits, five folds against [cf],
    and two carry passes.

    The bounds run: a column is at most [colb = 5 * (2^53 - 1)^2], just
    over [2^108]; a carry out of anything that size is at most [dhi =
    2^57]; a folded column is at most [colb + cf * dhi], still just over
    [2^108]; the first pass leaves limb zero at [base - 1 + cf * 2^57],
    just under [2^94]; so the second pass carries at most [2^42] out of
    limb zero, at most one out of every other limb, and needs only words.
    [Spec.K256.Field52.fmul_spec_ok] turns that into the invariant.

    The nine columns go through a nine-element scratch array rather than
    through nine local variables.  That is a proof decision and not a code
    one -- it cuts the verification condition in half, and both compilers
    scalarise a local array whose every subscript is a literal -- but it
    is the reason this is two functions instead of one. *)

#push-options "--z3rlimit 400"

(** {3 The twenty-five products} *)

[@@ FStar.Attributes.CInline]
fn mkcols (t: A.array S128.t) (a b: A.array S64.t)
          (#vt: erased (Seq.seq S128.t))
          (#pa: perm) (#va: erased (Seq.seq S64.t))
          (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == nw /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ vals128 vt' == part (vals va) (vals vb) nl /\
        ble (vals128 vt') colb)
{
  A.pts_to_len t;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (nl == 5);
  assert_norm (nw == 9);
  assert_norm (colb == nl * (lim * lim));
  assert_norm (nl * (lim * lim) < pow2 128);

  let a0 = A.(a.(0sz)); let a1 = A.(a.(1sz)); let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz)); let a4 = A.(a.(4sz));
  let b0 = A.(b.(0sz)); let b1 = A.(b.(1sz)); let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz)); let b4 = A.(b.(4sz));

  let c0 = mul52 a0 b0;
  let c1 = addd (mul52 a0 b1) (mul52 a1 b0);
  let c2 = addd (addd (mul52 a0 b2) (mul52 a1 b1)) (mul52 a2 b0);
  let c3 = addd (addd (addd (mul52 a0 b3) (mul52 a1 b2)) (mul52 a2 b1)) (mul52 a3 b0);
  let c4 = addd (addd (addd (addd (mul52 a0 b4) (mul52 a1 b3)) (mul52 a2 b2))
                      (mul52 a3 b1)) (mul52 a4 b0);
  let c5 = addd (addd (addd (mul52 a1 b4) (mul52 a2 b3)) (mul52 a3 b2)) (mul52 a4 b1);
  let c6 = addd (addd (mul52 a2 b4) (mul52 a3 b3)) (mul52 a4 b2);
  let c7 = addd (mul52 a3 b4) (mul52 a4 b3);
  let c8 = mul52 a4 b4;

  A.((t.(0sz) <- c0)); A.((t.(1sz) <- c1)); A.((t.(2sz) <- c2));
  A.((t.(3sz) <- c3)); A.((t.(4sz) <- c4)); A.((t.(5sz) <- c5));
  A.((t.(6sz) <- c6)); A.((t.(7sz) <- c7)); A.((t.(8sz) <- c8));

  with vt'. assert (A.pts_to t vt');
  part_len (vals va) (vals vb) nl;
  p0 (vals va) (vals vb); p1 (vals va) (vals vb); p2 (vals va) (vals vb);
  p3 (vals va) (vals vb); p4 (vals va) (vals vb); p5 (vals va) (vals vb);
  p6 (vals va) (vals vb); p7 (vals va) (vals vb); p8 (vals va) (vals vb);
  nine_eq (vals128 vt') (part (vals va) (vals vb) nl);
  ()
}

(** {3 The chain, the fold and the two passes} *)

[@@ FStar.Attributes.CInline]
fn reduce (out: A.array S64.t) (t: A.array S128.t)
          (#vout: erased (Seq.seq S64.t))
          (#pt: perm) (#vt: erased (Seq.seq S128.t))
requires A.pts_to out vout ** A.pts_to t #pt vt **
  pure (Seq.length vout == nl /\ Seq.length vt == nw /\ ble (vals128 vt) colb)
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to t #pt vt **
  pure (Seq.length vout' == nl /\
        vals vout' == carry_pass (carry_pass (folded (vals128 vt))))
{
  A.pts_to_len out;
  A.pts_to_len t;
  assert_norm (nl == 5);
  assert_norm (nw == 9);
  assert_norm (colb + dhi < base * (dhi + 1));
  assert_norm (colb + cf * dhi + dhi < base * (dhi + 1));
  assert_norm (colb + cf * dhi + dhi < pow2 128);
  assert_norm (dhi < pow2 64);

  let c0 = A.(t.(0sz)); let c1 = A.(t.(1sz)); let c2 = A.(t.(2sz));
  let c3 = A.(t.(3sz)); let c4 = A.(t.(4sz)); let c5 = A.(t.(5sz));
  let c6 = A.(t.(6sz)); let c7 = A.(t.(7sz)); let c8 = A.(t.(8sz));

  (* The top four columns, carried into proper digits. *)
  div_le_of_lt (colb + dhi) base dhi;
  Math.lemma_div_le (S128.v c5) (colb + dhi) base;
  let o5 = lo52d c5;
  let v6 = addd c6 (hi52d c5);
  Math.lemma_div_le (S128.v v6) (colb + dhi) base;
  let o6 = lo52d v6;
  let v7 = addd c7 (hi52d v6);
  Math.lemma_div_le (S128.v v7) (colb + dhi) base;
  let o7 = lo52d v7;
  let v8 = addd c8 (hi52d v7);
  Math.lemma_div_le (S128.v v8) (colb + dhi) base;
  let o8 = lo52d v8;
  let t8 = narrow128 (hi52d v8);

  (* The fold. *)
  let f0 = addd c0 (mulcf o5);
  let f1 = addd c1 (mulcf o6);
  let f2 = addd c2 (mulcf o7);
  let f3 = addd c3 (mulcf o8);
  let f4 = addd c4 (mulcf t8);

  assert_norm (cf * (base - 1) <= cf * dhi);
  let ff = hide (folded (vals128 vt));
  fcols (vals128 vt);
  assert (pure (Seq.length ff == nl));
  assert (pure (Seq.index ff 0 == S128.v f0 /\ Seq.index ff 1 == S128.v f1 /\
                Seq.index ff 2 == S128.v f2 /\ Seq.index ff 3 == S128.v f3 /\
                Seq.index ff 4 == S128.v f4));

  (* The first pass, one width up. *)
  div_le_of_lt (colb + cf * dhi + dhi) base dhi;
  Math.lemma_div_le (S128.v f0) (colb + cf * dhi + dhi) base;
  let g0 = lo52d f0;
  let u1 = addd f1 (hi52d f0);
  Math.lemma_div_le (S128.v u1) (colb + cf * dhi + dhi) base;
  let g1 = lo52d u1;
  let u2 = addd f2 (hi52d u1);
  Math.lemma_div_le (S128.v u2) (colb + cf * dhi + dhi) base;
  let g2 = lo52d u2;
  let u3 = addd f3 (hi52d u2);
  Math.lemma_div_le (S128.v u3) (colb + cf * dhi + dhi) base;
  let g3 = lo52d u3;
  let u4 = addd f4 (hi52d u3);
  Math.lemma_div_le (S128.v u4) (colb + cf * dhi + dhi) base;
  let g4 = lo52d u4;
  let t4 = narrow128 (hi52d u4);
  assert_norm (base - 1 + cf * dhi < pow2 128);
  let r0 = addd (Cast.u64_to_u128 g0) (mulcf t4);

  let s1 = hide (carry_pass ff);
  wpass ff;
  assert (pure (Seq.length s1 == nl));
  assert (pure (Seq.index s1 0 == S128.v r0 /\ Seq.index s1 1 == S64.v g1 /\
                Seq.index s1 2 == S64.v g2 /\ Seq.index s1 3 == S64.v g3 /\
                Seq.index s1 4 == S64.v g4));

  (* The second pass.  Only limb zero is large, so only its step needs a
     hundred and twenty-eight bits. *)
  assert_norm (base - 1 + cf * dhi < base * (pow2 42 + 1));
  div_le_of_lt (base - 1 + cf * dhi) base (pow2 42);
  Math.lemma_div_le (S128.v r0) (base - 1 + cf * dhi) base;
  assert_norm (pow2 42 < pow2 64);
  let p0 = lo52d r0;
  let y0 = narrow128 (hi52d r0);
  assert_norm (base - 1 + pow2 42 < base * 2);
  assert_norm (base - 1 + pow2 42 < pow2 64);
  div_le_of_lt (base - 1 + pow2 42) base 1;
  let w1 = addw g1 y0;
  Math.lemma_div_le (S64.v w1) (base - 1 + pow2 42) base;
  let h1 = lo52 w1;
  let w2 = addw g2 (hi52 w1);
  Math.lemma_div_le (S64.v w2) (base - 1 + pow2 42) base;
  let h2 = lo52 w2;
  let w3 = addw g3 (hi52 w2);
  Math.lemma_div_le (S64.v w3) (base - 1 + pow2 42) base;
  let h3 = lo52 w3;
  let w4 = addw g4 (hi52 w3);
  Math.lemma_div_le (S64.v w4) (base - 1 + pow2 42) base;
  let h4 = lo52 w4;
  assert_norm (cf * 1 < pow2 64);
  assert_norm (base - 1 + cf < pow2 64);
  let n0 = addw p0 (mulk cfw (hi52 w4));

  wpass s1;
  A.((out.(0sz) <- n0)); A.((out.(1sz) <- h1)); A.((out.(2sz) <- h2));
  A.((out.(3sz) <- h3)); A.((out.(4sz) <- h4));
  with w. assert (A.pts_to out w);
  assert (pure (Seq.length (vals w) == nl));
  assert (pure (Seq.index (vals w) 0 == S64.v n0 /\ Seq.index (vals w) 1 == S64.v h1 /\
                Seq.index (vals w) 2 == S64.v h2 /\ Seq.index (vals w) 3 == S64.v h3 /\
                Seq.index (vals w) 4 == S64.v h4));
  five_eq (vals w) (carry_pass s1);
  ()
}

(** {3 The two halves together} *)

[@@ FStar.Attributes.CInline]
fn fmul (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem (vals vout') /\
        fev (vals vout') == K.fmul (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  let z = S128.zero;
  let mut t = [| z; 9sz |];
  A.pts_to_len t;
  mkcols t a b;
  reduce out t;
  fmul_spec_ok (vals va) (vals vb);
  ()
}

#pop-options

(** {2 Freezing}

    The one operation that produces the representative below the prime.
    Three straight chains and a branch-free conditional subtraction, all
    of it stated in [Spec.K256.Freeze]: a carry, a fold of everything
    above bit 256 back against [cf1], a second carry, then the mask that
    is all ones exactly when the number has reached the modulus, either by
    overflowing [2^256] or by matching the prime limb for limb.

    Nothing here branches on a secret.  The subtraction is [select]ing
    [cf1] or zero into limb zero, carrying unconditionally -- which is a
    no-op when zero was selected, because the limbs are already proper --
    and masking the top limb back to forty-eight bits. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn freeze (out a: A.array S64.t)
          (#vout: erased (Seq.seq S64.t))
          (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == nl /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (vals vout' == freeze_spec (vals va) /\ felem (vals vout') /\
        eval (vals vout') == fev (vals va) /\ eval (vals vout') < prime)
{
  A.pts_to_len out;
  A.pts_to_len a;
  assert_norm (nl == 5);
  assert_norm (lim + 2 < base * 3);
  assert_norm (lim + 2 < pow2 64);
  div_le_of_lt (lim + 2) base 2;

  let x0 = A.(a.(0sz)); let x1 = A.(a.(1sz)); let x2 = A.(a.(2sz));
  let x3 = A.(a.(3sz)); let x4 = A.(a.(4sz));

  (* The first chain. *)
  Math.lemma_div_le (S64.v x0) (lim + 2) base;
  let o0 = lo52 x0;
  let v1 = addw x1 (hi52 x0);
  Math.lemma_div_le (S64.v v1) (lim + 2) base;
  let o1 = lo52 v1;
  let v2 = addw x2 (hi52 v1);
  Math.lemma_div_le (S64.v v2) (lim + 2) base;
  let o2 = lo52 v2;
  let v3 = addw x3 (hi52 v2);
  Math.lemma_div_le (S64.v v3) (lim + 2) base;
  let o3 = lo52 v3;
  let v4 = addw x4 (hi52 v3);

  let s1 = hide (step1 (vals va));
  run4 (vals va);
  carry_run_len (vals va) (nl - 1);
  assert (pure (Seq.length s1 == nl));
  assert (pure (Seq.index s1 0 == S64.v o0 /\ Seq.index s1 1 == S64.v o1 /\
                Seq.index s1 2 == S64.v o2 /\ Seq.index s1 3 == S64.v o3 /\
                Seq.index s1 4 == S64.v v4));

  (* The fold of everything above bit 256. *)
  assert_norm (lim + 2 < hib * 33);
  div_le_of_lt (lim + 2) hib 32;
  Math.lemma_div_le (S64.v v4) (lim + 2) hib;
  let q = hi48 v4;
  let t4 = lo48 v4;
  assert_norm (cf1 * 32 < pow2 64);
  Math.lemma_mult_le_right cf1 (S64.v q) 32;
  assert_norm (base - 1 + cf1 * 32 < pow2 64);
  let t0 = addw o0 (mulk cf1w q);

  let s2 = hide (step2 (vals va));
  assert (pure (Seq.length s2 == nl));
  assert (pure (Seq.index s2 0 == S64.v t0 /\ Seq.index s2 1 == S64.v o1 /\
                Seq.index s2 2 == S64.v o2 /\ Seq.index s2 3 == S64.v o3 /\
                Seq.index s2 4 == S64.v t4));

  (* The second chain. *)
  assert_norm (base - 1 + cf1 * 32 < base * 2);
  div_le_of_lt (base - 1 + cf1 * 32) base 1;
  Math.lemma_div_le (S64.v t0) (base - 1 + cf1 * 32) base;
  let u0 = lo52 t0;
  let n1 = addw o1 (hi52 t0);
  Math.lemma_div_le (S64.v n1) (base - 1 + cf1 * 32) base;
  let u1 = lo52 n1;
  let n2 = addw o2 (hi52 n1);
  Math.lemma_div_le (S64.v n2) (base - 1 + cf1 * 32) base;
  let u2 = lo52 n2;
  let n3 = addw o3 (hi52 n2);
  Math.lemma_div_le (S64.v n3) (base - 1 + cf1 * 32) base;
  let u3 = lo52 n3;
  let u4 = addw t4 (hi52 n3);

  let s3 = hide (step3 (vals va));
  run4 s2;
  carry_run_len s2 (nl - 1);
  step3_ble (vals va);
  assert (pure (Seq.length s3 == nl /\ proper s3));
  assert (pure (Seq.index s3 0 == S64.v u0 /\ Seq.index s3 1 == S64.v u1 /\
                Seq.index s3 2 == S64.v u2 /\ Seq.index s3 3 == S64.v u3 /\
                Seq.index s3 4 == S64.v u4));

  (* Has it reached the modulus? *)
  assert_norm (hib < pow2 64);
  assert_norm (pl0 == 4503595332402223);
  let m = mor (S64.gte_mask u4 (S64.classify 281474976710656uL))
              (mand (S64.eq_mask u4 mask48)
                    (mand (S64.eq_mask u3 mask52)
                          (mand (S64.eq_mask u2 mask52)
                                (mand (S64.eq_mask u1 mask52)
                                      (S64.gte_mask u0 (S64.classify 4503595332402223uL))))));
  assert (pure ((S64.v m == pow2 64 - 1) <==> over s3));

  (* The conditional subtraction. *)
  let d = S64.select m (S64.classify cf1w) S64.zero;
  let xx = hide (if over s3 then 1 else 0);
  assert (pure (S64.v d == cf1 * reveal xx));
  assert_norm (base - 1 + cf1 < base * 2);
  assert_norm (base - 1 + cf1 < pow2 64);
  div_le_of_lt (base - 1 + cf1) base 1;
  let y0 = addw u0 d;
  Math.lemma_div_le (S64.v y0) (base - 1 + cf1) base;
  let p0 = lo52 y0;
  let g1 = addw u1 (hi52 y0);
  Math.lemma_div_le (S64.v g1) (base - 1 + cf1) base;
  let p1 = lo52 g1;
  let g2 = addw u2 (hi52 g1);
  Math.lemma_div_le (S64.v g2) (base - 1 + cf1) base;
  let p2 = lo52 g2;
  let g3 = addw u3 (hi52 g2);
  Math.lemma_div_le (S64.v g3) (base - 1 + cf1) base;
  let p3 = lo52 g3;
  assert_norm (hib + 1 < pow2 64);
  let g4 = addw u4 (hi52 g3);
  let p4 = lo48 g4;

  let bb = hide (Seq.upd s3 0 (vat s3 0 + cf1 * reveal xx));
  run4 bb;
  carry_run_len bb (nl - 1);
  fin_uniform s3 (reveal xx);
  assert (pure (Seq.length (freeze_spec (vals va)) == nl));
  assert (pure (Seq.index (freeze_spec (vals va)) 0 == S64.v p0 /\
                Seq.index (freeze_spec (vals va)) 1 == S64.v p1 /\
                Seq.index (freeze_spec (vals va)) 2 == S64.v p2 /\
                Seq.index (freeze_spec (vals va)) 3 == S64.v p3 /\
                Seq.index (freeze_spec (vals va)) 4 == S64.v p4));

  A.((out.(0sz) <- p0)); A.((out.(1sz) <- p1)); A.((out.(2sz) <- p2));
  A.((out.(3sz) <- p3)); A.((out.(4sz) <- p4));
  with w. assert (A.pts_to out w);
  assert (pure (Seq.length (vals w) == nl));
  assert (pure (Seq.index (vals w) 0 == S64.v p0 /\ Seq.index (vals w) 1 == S64.v p1 /\
                Seq.index (vals w) 2 == S64.v p2 /\ Seq.index (vals w) 3 == S64.v p3 /\
                Seq.index (vals w) 4 == S64.v p4));
  five_eq (vals w) (freeze_spec (vals va));
  freeze_ok (vals va);
  ()
}

#pop-options

#pop-options

(** {2 Bytes}

    A fifty-two-bit limb is not a whole number of bytes, so neither
    direction touches bytes and limbs at the same time.  Loading decodes
    the four sixty-four-bit limbs, whose big-endian layer is proved in
    [Spec.Bignum4], checks them against the prime with the comparison the
    Montgomery code already had, and then reads the five fifty-two-bit
    limbs off them as bit windows.  Storing freezes, runs the same
    repacking the other way, and hands four sixty-four-bit limbs to the
    same byte layer.  The repacking itself is [Spec.K256.Repack]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** The two views of a slice of secrets agree; [Hacl.Impl.Limb4] has its
    own copy, and the byte and comparison code below is stated in terms of
    that one. *)
let vals_l4 (v: Seq.seq S64.t) : Lemma (vals v == L4.vals v)
  = Seq.lemma_eq_intro (vals v) (L4.vals v)

(** Adding two windows and keeping [w] bits: the machine wraps at [2^64]
    and the mask throws the wrap away. *)
let win_mod (a b: nat) (w: nat { w <= 64 })
  : Lemma (((a + b % pow2 64) % pow2 64) % pow2 w == (a + b) % pow2 w)
  = Math.lemma_mod_plus_distr_r a b (pow2 64);
    Math.pow2_modulo_modulo_lemma_1 (a + b) w 64

(** A window that spans two limbs, kept to fifty-two bits. *)
inline_for_extraction
let win2_52 (x y: S64.t) (s1 s2: U32.t { U32.v s1 < 64 /\ U32.v s2 < 64 })
  : r: S64.t { S64.v r == (S64.v x / pow2 (U32.v s1) +
                           pow2 (U32.v s2) * S64.v y) % pow2 52 }
  = let p = S64.shift_right x s1 in
    let q = S64.shift_left y s2 in
    let u = S64.add_mod p q in
    Math.swap_mul (S64.v y) (pow2 (U32.v s2));
    win_mod (S64.v x / pow2 (U32.v s1)) (pow2 (U32.v s2) * S64.v y) 52;
    UInt.logand_mask #64 (S64.v u) 52;
    assert_norm (base - 1 == pow2 52 - 1);
    S64.logand u mask52

(** The same kept to sixty-four bits: no mask, because the wrap the machine
    performs is already the window. *)
inline_for_extraction
let win2_64 (x y: S64.t) (s1 s2: U32.t { U32.v s1 < 64 /\ U32.v s2 < 64 })
  : r: S64.t { S64.v r == (S64.v x / pow2 (U32.v s1) +
                           pow2 (U32.v s2) * S64.v y) % pow2 64 }
  = let p = S64.shift_right x s1 in
    let q = S64.shift_left y s2 in
    let u = S64.add_mod p q in
    Math.swap_mul (S64.v y) (pow2 (U32.v s2));
    win_mod (S64.v x / pow2 (U32.v s1)) (pow2 (U32.v s2) * S64.v y) 64;
    Math.small_mod (S64.v u) (pow2 64);
    u

(** Four sixty-four-bit limbs to five fifty-two-bit ones.  The bottom
    window is a mask and the top one is a shift; the three in between
    straddle a limb boundary. *)
fn load (a h: A.array S64.t)
        (#va: erased (Seq.seq S64.t)) (#ph: perm) (#vh: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to h #ph vh **
  pure (Seq.length va == nl /\ Seq.length vh == B4.nl /\ B4.bnd (vals vh) B4.base)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to h #ph vh **
  pure (Seq.length va' == nl /\ bnd (vals va') base /\
        eval (vals va') == B4.eval (vals vh))
{
  A.pts_to_len a; A.pts_to_len h;
  assert_norm (nl == 5); assert_norm (B4.nl == 4);
  assert_norm (base == pow2 52);
  let h0 = A.(h.(0sz)); let h1 = A.(h.(1sz));
  let h2 = A.(h.(2sz)); let h3 = A.(h.(3sz));
  let a0 = lo52 h0;
  let a1 = win2_52 h0 h1 52ul 12ul;
  let a2 = win2_52 h1 h2 40ul 24ul;
  let a3 = win2_52 h2 h3 28ul 36ul;
  let a4 = S64.shift_right h3 16ul;
  A.((a.(0sz) <- a0)); A.((a.(1sz) <- a1)); A.((a.(2sz) <- a2));
  A.((a.(3sz) <- a3)); A.((a.(4sz) <- a4));
  with s. assert (A.pts_to a s);
  assert (pure (Seq.length (vals s) == nl));
  assert (pure (B4.vat (vals vh) 0 == S64.v h0 /\ B4.vat (vals vh) 1 == S64.v h1 /\
                B4.vat (vals vh) 2 == S64.v h2 /\ B4.vat (vals vh) 3 == S64.v h3));
  assert (pure (Seq.index (vals s) 0 == B4.vat (vals vh) 0 % pow2 52));
  assert (pure (Seq.index (vals s) 1 ==
                (B4.vat (vals vh) 0 / pow2 52 + pow2 12 * B4.vat (vals vh) 1) % pow2 52));
  assert (pure (Seq.index (vals s) 2 ==
                (B4.vat (vals vh) 1 / pow2 40 + pow2 24 * B4.vat (vals vh) 2) % pow2 52));
  assert (pure (Seq.index (vals s) 3 ==
                (B4.vat (vals vh) 2 / pow2 28 + pow2 36 * B4.vat (vals vh) 3) % pow2 52));
  assert (pure (Seq.index (vals s) 4 == B4.vat (vals vh) 3 / pow2 16));
  RP.load_all (vals vh) (vals s);
  ()
}

(** And back: five fifty-two-bit limbs to four sixty-four-bit ones. *)
fn store (u a: A.array S64.t)
         (#vu: erased (Seq.seq S64.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to u vu ** A.pts_to a #pa va **
  pure (Seq.length vu == B4.nl /\ Seq.length va == nl /\
        bnd (vals va) base /\ eval (vals va) < pow2 256)
ensures exists* (vu': Seq.seq S64.t).
  A.pts_to u vu' ** A.pts_to a #pa va **
  pure (Seq.length vu' == B4.nl /\ B4.bnd (vals vu') B4.base /\
        B4.eval (vals vu') == eval (vals va))
{
  A.pts_to_len u; A.pts_to_len a;
  assert_norm (nl == 5); assert_norm (B4.nl == 4);
  let s0 = A.(a.(0sz)); let s1 = A.(a.(1sz)); let s2 = A.(a.(2sz));
  let s3 = A.(a.(3sz)); let s4 = A.(a.(4sz));
  let u0 = win2_64 s0 s1 0ul 52ul;
  let u1 = win2_64 s1 s2 12ul 40ul;
  let u2 = win2_64 s2 s3 24ul 28ul;
  let u3 = win2_64 s3 s4 36ul 16ul;
  A.((u.(0sz) <- u0)); A.((u.(1sz) <- u1));
  A.((u.(2sz) <- u2)); A.((u.(3sz) <- u3));
  with w. assert (A.pts_to u w);
  assert (pure (Seq.length (vals w) == B4.nl));
  assert (pure (vat (vals va) 0 == S64.v s0 /\ vat (vals va) 1 == S64.v s1 /\
                vat (vals va) 2 == S64.v s2 /\ vat (vals va) 3 == S64.v s3 /\
                vat (vals va) 4 == S64.v s4));
  assert (pure (Seq.index (vals w) 0 ==
                (vat (vals va) 0 / pow2 0 + pow2 52 * vat (vals va) 1) % pow2 64));
  assert (pure (Seq.index (vals w) 1 ==
                (vat (vals va) 1 / pow2 12 + pow2 40 * vat (vals va) 2) % pow2 64));
  assert (pure (Seq.index (vals w) 2 ==
                (vat (vals va) 2 / pow2 24 + pow2 28 * vat (vals va) 3) % pow2 64));
  assert (pure (Seq.index (vals w) 3 ==
                (vat (vals va) 3 / pow2 36 + pow2 16 * vat (vals va) 4) % pow2 64));
  RP.store_all (vals va) (vals w);
  ()
}

(** Big-endian, thirty-two bytes, as every standard that mentions
    secp256k1 says.  Decoding is also the range check: a coordinate at or
    above the prime is not a coordinate, and the comparison runs on the
    sixty-four-bit limbs, where the modulus table already is. *)
fn fload (out: A.array S64.t) (b: A.array S8.t)
         (#vo: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
returns r: bool
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (felem (vals vo') /\ r == (By.be_nat vb < K.prime) /\
        (r ==> fev (vals vo') == By.be_nat vb))
{
  SKF.fmod_ok ();
  assert_norm (SKF.fmod.m == K.prime);
  assert_norm (pow2 256 < 2 * K.prime);
  assert_norm (base - 1 <= lim);
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at;
  let mut asv = [| z128; 4sz |]; A.pts_to_len asv;
  A.pts_to_len at; A.pts_to_len asv;
  IB4.load_be at b;
  let nm = KT.fnm ();
  let r = IM4.abelow at asv nm SKF.fmod;
  Tbl.drop_table nm;
  with t. assert (A.pts_to at t);
  vals_l4 t;
  load out at;
  with s. assert (A.pts_to out s);
  Math.small_mod (eval (vals s)) prime;
  r
}

fn fstore (b: A.array S8.t) (a: A.array S64.t)
          (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ felem (vals va))
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == By.nat_to_be 32 (fev (vals va)))
{
  assert_norm (prime < pow2 256);
  let z = S64.zero;
  let mut fa = [| z; 5sz |]; A.pts_to_len fa;
  let mut at = [| z; 4sz |]; A.pts_to_len at;
  A.pts_to_len fa; A.pts_to_len at;
  freeze fa a;
  with f. assert (A.pts_to fa f);
  freeze_ok (vals va);
  proper_bnd (vals f);
  store at fa;
  with t. assert (A.pts_to at t);
  vals_l4 t;
  IB4.store_be b at;
  ()
}

#pop-options

(** {2 Constants, copies and comparison}

    Nothing here is Montgomery any more, so a constant is the number
    itself written out in five limbs and [fone] is a literal one rather
    than a table lookup. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn fcopy (dst src: A.array S64.t)
         (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == nl /\ felem (vals vs))
ensures exists* (vd': Seq.seq S64.t).
  A.pts_to dst vd' ** A.pts_to src #ps vs **
  pure (felem (vals vd') /\ fev (vals vd') == fev (vals vs))
{
  A.pts_to_len dst; A.pts_to_len src;
  assert_norm (nl == 5);
  let x0 = A.(src.(0sz)); let x1 = A.(src.(1sz)); let x2 = A.(src.(2sz));
  let x3 = A.(src.(3sz)); let x4 = A.(src.(4sz));
  A.((dst.(0sz) <- x0)); A.((dst.(1sz) <- x1)); A.((dst.(2sz) <- x2));
  A.((dst.(3sz) <- x3)); A.((dst.(4sz) <- x4));
  with w. assert (A.pts_to dst w);
  five_eq (vals w) (vals vs);
  ()
}

fn fzero (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == nl)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (felem (vals vo') /\ fev (vals vo') == K.fzero)
{
  A.pts_to_len out;
  assert_norm (nl == 5);
  A.((out.(0sz) <- S64.zero)); A.((out.(1sz) <- S64.zero));
  A.((out.(2sz) <- S64.zero)); A.((out.(3sz) <- S64.zero));
  A.((out.(4sz) <- S64.zero));
  with w. assert (A.pts_to out w);
  limbs_index 0 0; limbs_index 0 1; limbs_index 0 2;
  limbs_index 0 3; limbs_index 0 4;
  five_eq (vals w) (limbs_of 0);
  limbs_of_ok 0;
  ()
}

fn fone (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == nl)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (felem (vals vo') /\ fev (vals vo') == K.fone)
{
  A.pts_to_len out;
  assert_norm (nl == 5);
  assert_norm (1 < base);
  assert_norm (1 < pow2 (rad * 1) /\ 1 < pow2 (rad * 2) /\
               1 < pow2 (rad * 3) /\ 1 < pow2 (rad * 4));
  assert_norm (1 < prime);
  let one = S64.classify 1uL;
  A.((out.(0sz) <- one)); A.((out.(1sz) <- S64.zero));
  A.((out.(2sz) <- S64.zero)); A.((out.(3sz) <- S64.zero));
  A.((out.(4sz) <- S64.zero));
  with w. assert (A.pts_to out w);
  limbs_index 1 0; limbs_index 1 1; limbs_index 1 2;
  limbs_index 1 3; limbs_index 1 4;
  five_eq (vals w) (limbs_of 1);
  limbs_of_ok 1;
  Math.small_mod 1 prime;
  ()
}

(** Squaring needs a second reference to its argument and the multiplier
    wants the three buffers distinct: five moves against twenty-five
    multiplies. *)
fn fsqr (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem (vals va))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem (vals vo') /\ fev (vals vo') == K.fmul (fev (vals va)) (fev (vals va)))
{
  let z = S64.zero;
  let mut ac = [| z; 5sz |]; A.pts_to_len ac; A.pts_to_len ac;
  fcopy ac a;
  fmul out a ac;
  ()
}

(** Two field elements are equal when their canonical forms are equal limb
    for limb: [proper_uniq] is what says a canonical form is unique.  The
    mask is folded rather than branched on, and only the final answer --
    public in every caller -- is declassified. *)
fn feq (a b: A.array S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem (vals va) /\ felem (vals vb))
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (fev (vals va) = fev (vals vb)))
{
  assert_norm (nl == 5);
  let z = S64.zero;
  let mut fa = [| z; 5sz |]; A.pts_to_len fa;
  let mut fb = [| z; 5sz |]; A.pts_to_len fb;
  A.pts_to_len fa; A.pts_to_len fb;
  freeze fa a;
  freeze fb b;
  freeze_ok (vals va); freeze_ok (vals vb);
  with sa. assert (A.pts_to fa sa);
  with sb. assert (A.pts_to fb sb);
  let a0 = A.(fa.(0sz)); let a1 = A.(fa.(1sz)); let a2 = A.(fa.(2sz));
  let a3 = A.(fa.(3sz)); let a4 = A.(fa.(4sz));
  let b0 = A.(fb.(0sz)); let b1 = A.(fb.(1sz)); let b2 = A.(fb.(2sz));
  let b3 = A.(fb.(3sz)); let b4 = A.(fb.(4sz));
  let m = mand (mand (mand (S64.eq_mask a0 b0) (S64.eq_mask a1 b1))
                     (mand (S64.eq_mask a2 b2) (S64.eq_mask a3 b3)))
               (S64.eq_mask a4 b4);
  assert_norm ((pow2 64 - 1) % pow2 8 == pow2 8 - 1);
  let m8 = Cast.u64_to_u8 m;
  let r = Declassify.bool_of_mask m8;
  Classical.move_requires (Seq.lemma_eq_intro (vals sa)) (vals sb);
  Classical.move_requires (proper_uniq (vals sa)) (vals sb);
  r
}

fn fis_zero (a: A.array S64.t) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** pure (felem (vals va))
returns r: bool
ensures A.pts_to a #pa va ** pure (r == (fev (vals va) = K.fzero))
{
  let z = S64.zero;
  let mut az = [| z; 5sz |]; A.pts_to_len az; A.pts_to_len az;
  fzero az;
  let r = feq a az;
  r
}

(** A curve constant is the number itself in five limbs; [limbs_of_ok] is
    what says the literals in [Hacl.K256.Tables] denote the number they
    should. *)
inline_for_extraction
fn fconst (a: G.static_array S64.t) (x: erased K.felem)
requires pure (Seq.length (G.static_array_elems a) == nl /\
               vals (G.static_array_elems a) == limbs_of (reveal x))
returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem (vals v) /\ fev (vals v) == reveal x)
{
  assert_norm (prime < pow2 256);
  limbs_of_ok (reveal x);
  Math.small_mod (reveal x) prime;
  Tbl.table a 5sz
}

#pop-options

(** {2 Curve constants}

    Not in Montgomery form any more, so reading one is reading the table
    and nothing else. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

inline_for_extraction
fn fb () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem (vals v) /\ fev (vals v) == K.b_coeff)
{ fconst KT52.b_arr K.b_coeff }

(** [3b = 21], which is the only coefficient the complete formulas need. *)
inline_for_extraction
fn fb3 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem (vals v) /\ fev (vals v) == K.b3)
{ fconst KT52.b3_arr K.b3 }

inline_for_extraction
fn fgx () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem (vals v) /\ fev (vals v) == K.g_x)
{ fconst KT52.gx_arr K.g_x }

inline_for_extraction
fn fgy () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem (vals v) /\ fev (vals v) == K.g_y)
{ fconst KT52.gy_arr K.g_y }

#pop-options
