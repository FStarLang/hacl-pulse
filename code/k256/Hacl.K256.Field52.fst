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
open Spec.K256.Columns

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

#pop-options
