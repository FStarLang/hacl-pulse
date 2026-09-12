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

(** Curve25519's field, on sixteen sixty-four-bit secret integers.

    A field element is a sixteen-element slice; limb [k] carries bits [16k]
    to [16k+16], and the operations keep every limb at or below [2^17 - 1].
    Sixteen bits is small -- HACL* uses fifty-one -- and the reason is the
    pipeline: Custard compiles F* straight to C, and the only machine
    integers it knows are the eight-, sixteen-, thirty-two- and sixty-four-bit
    ones.  Without a hundred-and-twenty-eight-bit type there is no room for a
    radix-[2^51] product, so the radix has to come down far enough that
    sixteen products of two limbs still fit in a [uint64] with room for the
    reduction.  Sixteen is the largest such radix that also makes a limb
    exactly two bytes, which makes loading and storing trivial, and makes the
    modulus wrap around the top of the array at [2^256 = 2 * prime + 38].

    The cost is arithmetic: a multiplication is two hundred and fifty-six
    word multiplies rather than twenty-five.  The benefit is that the whole
    of X25519 is portable C with no compiler extension anywhere.

    All the arithmetic lives in [Spec.Curve25519.Field], which states each
    operation as one function on [Seq.seq nat] and one lemma.  The job here
    is to compute the sequence that lemma names.  The limbs are secret
    integers throughout: every operation below is a sixty-four-bit add,
    subtract, multiply, shift, mask or select, and there is no branch on a
    secret anywhere in the module. *)
module Hacl.Curve25519.Field

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Curve25519.Field
open Hacl.Spec.Bytes

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module Loops = Hacl.Spec.Loops
module C = Spec.Curve25519

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
let mask15 : m: S64.t { S64.v m == pow2 15 - 1 } =
  assert_norm (pow2 15 - 1 == 0x7fff);
  S64.classify 0x7fffuL

inline_for_extraction
let lo16 (x: S64.t) : r: S64.t { S64.v r == S64.v x % base } =
  UInt.logand_mask #64 (S64.v x) 16;
  S64.logand x mask16

inline_for_extraction
let hi16 (x: S64.t) : r: S64.t { S64.v r == S64.v x / base } =
  S64.shift_right x 16ul

inline_for_extraction
let lo15 (x: S64.t) : r: S64.t { S64.v r == S64.v x % pow2 15 } =
  UInt.logand_mask #64 (S64.v x) 15;
  S64.logand x mask15

inline_for_extraction
let hi15 (x: S64.t) : r: S64.t { S64.v r == S64.v x / pow2 15 } =
  S64.shift_right x 15ul

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

    Limbs [0] to [14] carry into their neighbour, and the top limb carries
    round into limb [0] multiplied by [38].  [c] bounds the limbs on entry
    and [d] the carry; the caller supplies both, and
    [Spec.Curve25519.Field.pass] turns them into the bound on exit. *)

#push-options "--z3rlimit 200"

fn carry_chain (a: A.array S64.t) (c: erased nat) (d: erased nat)
               (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\ ble (vals va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 64 /\ base + 38 * reveal d < pow2 64)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == carry_pass (vals va))
{
  A.pts_to_len a;
  div_le_of_lt (reveal c + reveal d) base d;
  Loops.repeati_zero carry_step (vals va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 15sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= 15 /\ Seq.length v == nl /\
          vals v == carry_run (vals va) (SZ.v vk))
  decreases (15 - SZ.v (!k))
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
  with v. assert (A.pts_to a v);
  carry_run_chained (vals va) c d 15;
  carry_run_len (vals va) 15;
  let t = A.(a.(15sz));
  let z = A.(a.(0sz));
  Math.lemma_div_le (S64.v t) (reveal c + reveal d) base;
  let lo = lo16 t;
  let z' = addw z (mulk 38uL (hi16 t));
  A.((a.(15sz) <- lo));
  A.((a.(0sz) <- z'));
  vals_upd v 15 lo;
  vals_upd (Seq.upd v 15 lo) 0 z';
  assert (pure (vals (Seq.upd (Seq.upd v 15 lo) 0 z') == carry_pass (vals va)));
}

(** The same chain without the wrap-around: the top limb keeps only its low
    sixteen bits and the overflow is dropped, which is [carry_low]. *)
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
  A.pts_to_len a;
  div_le_of_lt (reveal c + reveal d) base d;
  Loops.repeati_zero carry_step (vals va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 15sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= 15 /\ Seq.length v == nl /\
          vals v == carry_run (vals va) (SZ.v vk))
  decreases (15 - SZ.v (!k))
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
  with v. assert (A.pts_to a v);
  carry_run_len (vals va) 15;
  let t = A.(a.(15sz));
  let lo = lo16 t;
  A.((a.(15sz) <- lo));
  vals_upd v 15 lo;
  assert (pure (vals (Seq.upd v 15 lo) == carry_low (vals va)));
}

#pop-options

(** {2 Addition} *)

#push-options "--z3rlimit 120"

fn fadd (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem (vals vout') /\
        fev (vals vout') == C.fadd (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vb) k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    assert_norm (lim + lim < pow2 64);
    A.((out.(vi) <- addw x y));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  assert (pure (vals v `Seq.equal` Spec.Curve25519.Field.addw (vals va) (vals vb)));
  addw_ble (vals va) (vals vb) lim lim;
  assert_norm (lim + lim + 4 < base * 5);
  assert_norm (lim + lim + 4 < pow2 64);
  assert_norm (base + 38 * 4 < pow2 64);
  carry_chain out (2 * lim) 4;
  with v'. assert (A.pts_to out v');
  assert (pure (vals v' == carry_pass (vals v)));
  assert (pure (vals v == Spec.Curve25519.Field.addw (vals va) (vals vb)));
  assert (pure (vals v' == fadd_spec (vals va) (vals vb)));
  fadd_spec_ok (vals va) (vals vb);
  assert (pure (felem (vals v')));
}

(** {2 Subtraction}

    [eightp] is [8 * prime] written in limbs; every one of its limbs
    dominates every limb of the subtrahend, so the difference is taken limb
    by limb with no borrow. *)

let eightp_index (i: nat { i < nl })
  : Lemma (Seq.index eightp i == (if i = 0 then 261992 else 262140))
  = assert_norm (4 * (base - 38) == 261992);
    assert_norm (4 * (base - 1) == 262140)

fn fsub (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem (vals vout') /\
        fev (vals vout') == C.fsub (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (lim < 261992);
  assert_norm (lim + 262140 < pow2 64);
  eightp_index 0;
  let x0 = A.(a.(0sz));
  let y0 = A.(b.(0sz));
  A.((out.(0sz) <- subw (addw x0 (S64.classify 261992uL)) y0));
  let mut i = 1sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (1 <= SZ.v vi /\ SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               Seq.index (vals va) k + Seq.index eightp k - Seq.index (vals vb) k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    eightp_index (SZ.v vi);
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((out.(vi) <- subw (addw x (S64.classify 262140uL)) y));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  eightp_ok ();
  assert (pure (vals v `Seq.equal` Spec.Curve25519.Field.subw (vals va) (vals vb)));
  subw_ok (vals va) (vals vb);
  assert_norm (lim + 4 * (base - 1) + 6 < base * 7);
  assert_norm (lim + 4 * (base - 1) + 6 < pow2 64);
  assert_norm (base + 38 * 6 < pow2 64);
  carry_chain out (lim + 4 * (base - 1)) 6;
  with v'. assert (A.pts_to out v');
  assert (pure (vals v' == carry_pass (vals v)));
  assert (pure (vals v == Spec.Curve25519.Field.subw (vals va) (vals vb)));
  assert (pure (vals v' == fsub_spec (vals va) (vals vb)));
  fsub_spec_ok (vals va) (vals vb);
  assert (pure (felem (vals v')));
}

#pop-options

(** {2 Multiplication by a small constant} *)

#push-options "--z3rlimit 120"

fn fscale (out a: A.array S64.t) (m: U64.t { U64.v m <= 121665 })
          (#vout: erased (Seq.seq S64.t))
          (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == nl /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (felem (vals vout') /\
        fev (vals vout') == (U64.v m * eval (vals va)) % prime)
{
  A.pts_to_len out;
  A.pts_to_len a;
  assert_norm (121665 * lim < pow2 64);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == U64.v m * Seq.index (vals va) k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    Math.lemma_mult_le_left (U64.v m) (S64.v x) lim;
    Math.lemma_mult_le_right lim (U64.v m) 121665;
    A.((out.(vi) <- mulk m x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  assert (pure (vals v `Seq.equal` scale (U64.v m) (vals va)));
  scale_ble (U64.v m) (vals va) lim;
  Math.lemma_mult_le_right lim (U64.v m) 121665;
  ble_mono (vals v) (U64.v m * lim) (121665 * lim);
  assert_norm (121665 * lim <= pow2 34);
  assert_norm (pow2 34 + (pow2 18 + pow2 4) < base * (pow2 18 + pow2 4 + 1));
  assert_norm (pow2 34 + (pow2 18 + pow2 4) < pow2 64);
  assert_norm (base + 38 * (pow2 18 + pow2 4) < pow2 64);
  ble_mono (vals v) (121665 * lim) (pow2 34);
  carry_chain out (pow2 34) (pow2 18 + pow2 4);
  with v1. assert (A.pts_to out v1);
  assert_norm (base - 1 + 38 * ((pow2 34 + (pow2 18 + pow2 4)) / base) <= pow2 24);
  carry_pass_len (vals v);
  carry_pass_ble (vals v) (pow2 34) (pow2 18 + pow2 4);
  ble_mono (vals v1) (base - 1 + 38 * ((pow2 34 + (pow2 18 + pow2 4)) / base)) (pow2 24);
  assert_norm (pow2 24 + 257 < base * 258);
  assert_norm (pow2 24 + 257 < pow2 64);
  assert_norm (base + 38 * 257 < pow2 64);
  carry_chain out (pow2 24) 257;
  with v2. assert (A.pts_to out v2);
  assert (pure (vals v2 == carry_pass (carry_pass (scale (U64.v m) (vals va)))));
  assert (pure (vals v2 == fscale_spec (U64.v m) (vals va)));
  fscale_spec_ok (U64.v m) (vals va);
  assert (pure (felem (vals v2)));
}

#pop-options

(** {2 Multiplication}

    Three loops: the thirty-one wide columns of the schoolbook product, the
    fold of the top fifteen columns down by [38], and three carry passes.
    The columns live in a thirty-one-word scratch slice, which the caller
    supplies; a column is at most sixteen products of two limbs under
    [2^17], so it stays under [2^40]. *)

let addw_zerow (x: Seq.seq nat)
  : Lemma (requires Seq.length x == nw)
          (ensures Spec.Curve25519.Field.addw x zerow == x)
  = Seq.lemma_eq_intro (Spec.Curve25519.Field.addw x zerow) x

let acc_ble (a b acc: Seq.seq nat) (i j: nat)
  : Lemma (requires ble a lim /\ ble b lim /\
                    acc == Spec.Curve25519.Field.addw (part a b i) (rowj a b i j) /\ i < nl)
          (ensures ble acc (nl * (lim * lim)))
  = part_ble a b lim lim i;
    rowj_ble a b lim lim i j;
    addw_ble (part a b i) (rowj a b i j) (i * (lim * lim)) (lim * lim);
    Math.distributivity_add_left i 1 (lim * lim);
    Math.lemma_mult_le_right (lim * lim) (i + 1) nl;
    ble_mono acc (i * (lim * lim) + lim * lim) (nl * (lim * lim))

#push-options "--z3rlimit 300"

fn mul_columns (t a b: A.array S64.t)
               (#vt: erased (Seq.seq S64.t))
               (#pa: perm) (#va: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == nw /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ vals vt' == part (vals va) (vals vb) nl)
{
  A.pts_to_len t;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (nl * (lim * lim) + lim * lim < pow2 64);
  assert_norm (lim * lim < pow2 64);
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
            vals v == Spec.Curve25519.Field.addw
                        (part (vals va) (vals vb) (SZ.v vi))
                        (rowj (vals va) (vals vb) (SZ.v vi) (SZ.v vj)))
    decreases (16 - SZ.v (!j))
    {
      with v. assert (A.pts_to t v);
      let vj = !j;
      acc_ble (vals va) (vals vb) (vals v) (SZ.v vi) (SZ.v vj);
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
  ()
}

#pop-options

#push-options "--z3rlimit 300"

fn fmul (out a b t: A.array S64.t)
        (#vout: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ Seq.length vt == nw /\
        felem (vals va) /\ felem (vals vb))
ensures exists* (vout': Seq.seq S64.t) (vt': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ felem (vals vout') /\
        fev (vals vout') == C.fmul (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len t;
  mul_columns t a b;
  with vp. assert (A.pts_to t vp);
  part_ble (vals va) (vals vb) lim lim nl;
  assert_norm (39 * (nl * (lim * lim)) < pow2 64);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 15sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to out v ** A.pts_to t vp ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vk <= 15 /\ Seq.length v == nl /\
          (forall (c: nat). c < SZ.v vk ==>
             Seq.index (vals v) c ==
               Seq.index (vals vp) c + 38 * Seq.index (vals vp) (c + nl)))
  decreases (15 - SZ.v (!k))
  {
    let vk = !k;
    let x = A.(t.(vk));
    let y = A.(t.(SZ.add vk 16sz));
    A.((out.(vk) <- addw x (mulk 38uL y)));
    k := SZ.add vk 1sz;
  };
  let top = A.(t.(15sz));
  A.((out.(15sz) <- top));
  with v. assert (A.pts_to out v);
  assert (pure (vals v `Seq.equal` fold38 (vals vp)));
  fold_ble (vals vp) (nl * (lim * lim));
  assert_norm (39 * (nl * (lim * lim)) <= pow2 44);
  ble_mono (vals v) (39 * (nl * (lim * lim))) (pow2 44);
  assert_norm (pow2 44 + (pow2 28 + pow2 13) < base * (pow2 28 + pow2 13 + 1));
  assert_norm (pow2 44 + (pow2 28 + pow2 13) < pow2 64);
  assert_norm (base + 38 * (pow2 28 + pow2 13) < pow2 64);
  carry_chain out (pow2 44) (pow2 28 + pow2 13);
  with v1. assert (A.pts_to out v1);
  carry_pass_len (vals v);
  carry_pass_ble (vals v) (pow2 44) (pow2 28 + pow2 13);
  assert_norm (base - 1 + 38 * ((pow2 44 + (pow2 28 + pow2 13)) / base) <= pow2 34);
  ble_mono (vals v1) (base - 1 + 38 * ((pow2 44 + (pow2 28 + pow2 13)) / base)) (pow2 34);
  assert_norm (pow2 34 + (pow2 18 + pow2 4) < base * (pow2 18 + pow2 4 + 1));
  assert_norm (pow2 34 + (pow2 18 + pow2 4) < pow2 64);
  assert_norm (base + 38 * (pow2 18 + pow2 4) < pow2 64);
  carry_chain out (pow2 34) (pow2 18 + pow2 4);
  with v2. assert (A.pts_to out v2);
  carry_pass_len (vals v1);
  carry_pass_ble (vals v1) (pow2 34) (pow2 18 + pow2 4);
  assert_norm (base - 1 + 38 * ((pow2 34 + (pow2 18 + pow2 4)) / base) <= pow2 24);
  ble_mono (vals v2) (base - 1 + 38 * ((pow2 34 + (pow2 18 + pow2 4)) / base)) (pow2 24);
  assert_norm (pow2 24 + 257 < base * 258);
  assert_norm (pow2 24 + 257 < pow2 64);
  assert_norm (base + 38 * 257 < pow2 64);
  carry_chain out (pow2 24) 257;
  with v3. assert (A.pts_to out v3);
  assert (pure (vals v == fold38 (part (vals va) (vals vb) nl)));
  assert (pure (vals v3 ==
                carry_pass (carry_pass (carry_pass (fold38 (part (vals va) (vals vb) nl))))));
  assert (pure (vals v3 == fmul_spec (vals va) (vals vb)));
  fmul_spec_ok (vals va) (vals vb);
  assert (pure (felem (vals v3)));
}

#pop-options

(** {2 Bytes} *)

#push-options "--z3rlimit 120"

(** Two little-endian bytes make a limb. *)
fn load (a: A.array S64.t) (b: A.array S8.t)
        (#va: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == 32)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b #pb vb **
  pure (Seq.length va' == nl /\ bnd (vals va') base /\ eval (vals va') == le_nat vb)
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
               S8.v (Seq.index vb (2 * k)) + 256 * S8.v (Seq.index vb (2 * k + 1))))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let lo = A.(b.(SZ.mul vi 2sz));
    let hi = A.(b.(SZ.add (SZ.mul vi 2sz) 1sz));
    assert_norm (256 * (pow2 8 - 1) + (pow2 8 - 1) < pow2 64);
    let w = addw (Cast.u8_to_u64 lo) (mulk 256uL (Cast.u8_to_u64 hi));
    A.((a.(vi) <- w));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  assert (pure (forall (k: nat). k < nl ==>
                  Seq.index (vals v) k ==
                    S8.v (Seq.index vb (2 * k)) + 256 * S8.v (Seq.index vb (2 * k + 1))));
  eval_bytes vb (vals v);
  assert_norm (256 * (pow2 8 - 1) + (pow2 8 - 1) < base);
}

(** Bit [255] is not part of the number a public key encodes. *)
fn mask_top (a: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == nl /\ bnd (vals va) base)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ bnd (vals va') base /\
        eval (vals va') == eval (vals va) % pow2 255)
{
  A.pts_to_len a;
  let t = A.(a.(15sz));
  let m = lo15 t;
  A.((a.(15sz) <- m));
  vals_upd va 15 m;
  mask255_ok (vals va);
  assert (pure (vals (Seq.upd va 15 m) == mask255 (vals va)));
}

(** A limb is exactly two bytes, so storing is a truncation and a shift. *)
fn store (b: A.array S8.t) (a: A.array S64.t)
         (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ Seq.length va == nl /\ bnd (vals va) base)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == nat_to_le 32 (eval (vals va)))
{
  A.pts_to_len b;
  A.pts_to_len a;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 16 /\ Seq.length v == 32 /\
          (forall (k: nat). k < SZ.v vi ==>
             S8.v (Seq.index v (2 * k)) == Seq.index (vals va) k % 256 /\
             S8.v (Seq.index v (2 * k + 1)) == Seq.index (vals va) k / 256))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    Math.pow2_plus 8 8;
    Math.lemma_div_lt_nat (S64.v x) 16 8;
    Math.small_mod (S64.v x / 256) (pow2 8);
    A.((b.(SZ.mul vi 2sz) <- Cast.u64_to_u8 x));
    A.((b.(SZ.add (SZ.mul vi 2sz) 1sz) <- Cast.u64_to_u8 (S64.shift_right x 8ul)));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  assert (pure (Seq.length v == 32 /\ bnd (vals va) base));
  assert (pure (forall (k: nat). k < nl ==>
                  S8.v (Seq.index v (2 * k)) == Seq.index (vals va) k % 256 /\
                  S8.v (Seq.index v (2 * k + 1)) == Seq.index (vals va) k / 256));
  store_ok (vals va) v;
  assert (pure (v == nat_to_le 32 (eval (vals va))));
}

#pop-options

(** {2 Freezing}

    The unique representative below the prime.  Four carry passes bring the
    limbs into base [2^16] and the number below [2^256], two subtractions of
    the prime bring it below [2^255], and the last conditional subtraction is
    selected on the top bit of the number plus nineteen. *)

#push-options "--z3rlimit 300"

(** [a] becomes [fold255 a]: bit [255] is cleared and nineteen times what it
    held is added back at the bottom, which subtracts one prime. *)
fn fold255_op (a: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == nl /\ bnd (vals va) base)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == fold255 (vals va))
{
  A.pts_to_len a;
  let t = A.(a.(15sz));
  let z = A.(a.(0sz));
  let m = lo15 t;
  assert_norm (base + 19 * 2 < pow2 64);
  Math.lemma_div_lt_nat (S64.v t) 16 15;
  assert_norm (pow2 (16 - 15) == 2);
  let z' = addw z (mulk 19uL (hi15 t));
  A.((a.(15sz) <- m));
  A.((a.(0sz) <- z'));
  vals_upd va 15 m;
  vals_upd (Seq.upd va 15 m) 0 z';
  assert (pure (vals (Seq.upd (Seq.upd va 15 m) 0 z') == fold255 (vals va)));
}

fn red255_op (a: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\ bnd (vals va) base /\ eval (vals va) < pow2 256)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == red255 (vals va))
{
  fold255_op a;
  with v. assert (A.pts_to a v);
  Math.lemma_div_lt_nat (Seq.index (vals va) 15) 16 15;
  assert_norm (pow2 (16 - 15) == 2);
  assert_norm (pow2 15 < base + 19);
  assert (pure (hi255 (vals va) <= 1));
  assert (pure (ble (vals v) (base + 18)));
  assert_norm (base + 18 + 1 < base * 2);
  assert_norm (base + 18 + 1 < pow2 64);
  carry_low_op a (base + 18) 1;
  with v'. assert (A.pts_to a v');
  assert (pure (vals v == fold255 (vals va)));
  assert (pure (vals v' == carry_low (fold255 (vals va))));
  assert (pure (vals v' == red255 (vals va)));
}

(** Four passes, and then the number is a genuine base-[2^16] one. *)
fn narrow (a: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == nl /\ felem (vals va))
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == freeze_a (vals va))
{
  freeze_a_bounds (vals va);
  assert_norm (lim + 2 < base * 3);
  assert_norm (lim + 2 < pow2 64);
  assert_norm (base + 38 * 2 < pow2 64);
  carry_chain a lim 2;
  with x1. assert (A.pts_to a x1);
  assert (pure (vals x1 == carry_pass (vals va)));
  assert_norm (65611 + 1 < base * 2);
  assert_norm (65611 + 1 < pow2 64);
  assert_norm (base + 38 * 1 < pow2 64);
  carry_chain a 65611 1;
  with x2. assert (A.pts_to a x2);
  assert (pure (vals x2 == carry_pass (carry_pass (vals va))));
  assert_norm (65573 + 1 < base * 2);
  assert_norm (65573 + 1 < pow2 64);
  carry_chain a 65573 1;
  with x3. assert (A.pts_to a x3);
  assert (pure (vals x3 == carry_pass (carry_pass (carry_pass (vals va)))));
  carry_chain a 65573 1;
  with x4. assert (A.pts_to a x4);
  assert (pure (vals x4 ==
                carry_pass (carry_pass (carry_pass (carry_pass (vals va))))));
  freeze_a_alt (vals va);
  assert (pure (vals x4 == freeze_a (vals va)));
}

(** [a] becomes its unique representative below the prime.  [t] is scratch. *)
fn freeze (a t: A.array S64.t)
          (#va: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to t vt **
  pure (Seq.length va == nl /\ Seq.length vt == nl /\ felem (vals va))
ensures exists* (va': Seq.seq S64.t) (vt': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to t vt' **
  pure (Seq.length va' == nl /\ Seq.length vt' == nl /\
        bnd (vals va') base /\ eval (vals va') == eval (vals va) % prime)
{
  A.pts_to_len a;
  A.pts_to_len t;
  narrow a;
  with v0. assert (A.pts_to a v0);
  assert (pure (vals v0 == freeze_a (vals va)));
  freeze_a_ok (vals va);
  red255_op a;
  with v1. assert (A.pts_to a v1);
  assert (pure (vals v1 == red255 (vals v0)));
  red255_ok (vals v0);
  Math.lemma_div_lt_nat (eval (vals v0)) 256 255;
  assert_norm (pow2 (256 - 255) == 2);
  assert (pure (eval (vals v1) < pow2 256));
  red255_op a;
  with y. assert (A.pts_to a y);
  assert (pure (vals y == red255 (vals v1)));
  assert (pure (vals y == freeze_b (vals v0)));
  freeze_b_ok (vals v0);
  assert (pure (bnd (vals y) base /\ eval (vals y) < pow2 255));
  (* w = carry_low (add19 y), in the scratch slice *)
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a y ** A.pts_to t v **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index y k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    A.((t.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with w0. assert (A.pts_to t w0);
  assert (pure (w0 `Seq.equal` reveal y));
  let z = A.(t.(0sz));
  assert_norm (base + 19 < pow2 64);
  let z' = addw z (S64.classify 19uL);
  A.((t.(0sz) <- z'));
  with w1. assert (A.pts_to t w1);
  vals_upd w0 0 z';
  assert (pure (vals w1 == add19 (vals y)));
  assert (pure (ble (vals w1) (base + 18)));
  assert_norm (base + 18 + 1 < base * 2);
  assert_norm (base + 18 + 1 < pow2 64);
  carry_low_op t (base + 18) 1;
  with w. assert (A.pts_to t w);
  freeze_w_ok (vals y);
  assert (pure (vals w == freeze_w (vals y)));
  (* the top bit decides whether the last prime comes off *)
  let wt = A.(t.(15sz));
  let bit = hi15 wt;
  Math.lemma_div_lt_nat (S64.v wt) 16 15;
  assert_norm (pow2 (16 - 15) == 2);
  let sel = S64.eq_mask bit (S64.classify 1uL);
  let mt = lo15 wt;
  A.((t.(15sz) <- mt));
  with wm. assert (A.pts_to t wm);
  vals_upd w 15 mt;
  assert (pure (vals wm == mask255 (vals w)));
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 16sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S64.t).
    pts_to j vj ** A.pts_to a v ** A.pts_to t wm **
    pure (SZ.v vj <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index v k == (if hi255 (vals w) = 1 then Seq.index wm k else Seq.index y k)) /\
          (forall (k: nat). SZ.v vj <= k /\ k < nl ==> Seq.index v k == Seq.index y k))
  decreases (16 - SZ.v (!j))
  {
    let vj = !j;
    let x = A.(t.(vj));
    let u = A.(a.(vj));
    A.((a.(vj) <- S64.select sel x u));
    j := SZ.add vj 1sz;
  };
  with r. assert (A.pts_to a r);
  freeze_spec_ok (vals va);
  assert (pure (vals r `Seq.equal` freeze_spec (vals va)));
}

#pop-options

(** {2 Conditional swap}

    The ladder's only data-dependent choice, made with a mask. *)

#push-options "--z3rlimit 120"

fn cswap (sel: S64.t) (a b: A.array S64.t)
         (#va: erased (Seq.seq S64.t)) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to b vb **
  pure (Seq.length va == nl /\ Seq.length vb == nl /\
        (S64.v sel == 0 \/ S64.v sel == pow2 64 - 1))
ensures exists* (va': Seq.seq S64.t) (vb': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b vb' **
  pure (Seq.length va' == nl /\ Seq.length vb' == nl /\
        (if S64.v sel = 0 then va' == reveal va /\ vb' == reveal vb
                          else va' == reveal vb /\ vb' == reveal va))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (x: Seq.seq S64.t) (y: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a x ** A.pts_to b y **
    pure (SZ.v vi <= 16 /\ Seq.length x == nl /\ Seq.length y == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index x k == (if S64.v sel = 0 then Seq.index va k else Seq.index vb k) /\
             Seq.index y k == (if S64.v sel = 0 then Seq.index vb k else Seq.index va k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < nl ==>
             Seq.index x k == Seq.index va k /\ Seq.index y k == Seq.index vb k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((a.(vi) <- S64.select sel y x));
    A.((b.(vi) <- S64.select sel x y));
    i := SZ.add vi 1sz;
  };
  with x. assert (A.pts_to a x);
  with y. assert (A.pts_to b y);
  assert (pure (if S64.v sel = 0 then x `Seq.equal` reveal va /\ y `Seq.equal` reveal vb
                                 else x `Seq.equal` reveal vb /\ y `Seq.equal` reveal va));
}

(** A straight copy, for the ladder's temporaries. *)
fn copy (dst src: A.array S64.t)
        (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == nl /\ Seq.length vs == nl)
ensures exists* (vd': Seq.seq S64.t).
  A.pts_to dst vd' ** A.pts_to src #ps vs ** pure (vd' == reveal vs)
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #ps vs **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index vs k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  assert (pure (v `Seq.equal` reveal vs));
}

#pop-options

#pop-options
