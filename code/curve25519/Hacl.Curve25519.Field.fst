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

(** Curve25519's field, on eight sixty-four-bit secret integers.

    A field element is an eight-element slice; limb [k] carries bits [32k]
    to [32k+32], and the operations keep every limb at or below [2^33 - 1].
    Thirty-two bits is small -- HACL* uses fifty-one -- and the reason is
    the schoolbook product: a column of it holds eight limb products with no
    intermediate reduction, which is what makes
    [Spec.Curve25519.Field.part] carry-free and its proof tractable.  At
    radix [2^32] a column is under [2^69] and thirty-eight times a column is
    under [2^75], so the columns live in [Hacl.Secret.UInt128] until the
    first carry pass brings them back under [2^49]; at radix [2^64] four
    products would already reach [2^130] and there would be nowhere to put
    them.  Thirty-two also makes a limb exactly four bytes, which makes
    loading and storing trivial, and keeps [nl * rad = 256], so the modulus
    still wraps around the top of the array at [2^256 = 2 * prime + 38].

    A multiplication is sixty-four word multiplies.  Every one of them is a
    [uint64 * uint64 -> uint128], which is what the hardware does anyway.

    All the arithmetic lives in [Spec.Curve25519.Field], which states each
    operation as one function on [Seq.seq nat] and one lemma.  The job here
    is to compute the sequence that lemma names.  The limbs are secret
    integers throughout: every operation below is a sixty-four- or
    hundred-and-twenty-eight-bit add, subtract, multiply, shift, mask or
    select, and there is no branch on a secret anywhere in the module. *)
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
module Classical = FStar.Classical
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
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

(** The columns of a product do not fit in a word, so they get their own
    view.  [pre] is the first [nl] of the [nw] columns: once the fold has
    wrapped the top half round, that prefix is the field element. *)

let vals128 (v: Seq.seq S128.t)
  : GTot (s: Seq.seq nat { Seq.length s == Seq.length v /\
                           (forall (i: nat). i < Seq.length v ==>
                              Seq.index s i == S128.v (Seq.index v i)) })
  = Seq.init_ghost (Seq.length v) (fun i -> (S128.v (Seq.index v i) <: nat))

let vals128_upd (v: Seq.seq S128.t) (k: nat { k < Seq.length v }) (x: S128.t)
  : Lemma (vals128 (Seq.upd v k x) == Seq.upd (vals128 v) k (S128.v x))
  = Seq.lemma_eq_intro (vals128 (Seq.upd v k x)) (Seq.upd (vals128 v) k (S128.v x))

let pre (v: Seq.seq S128.t) : GTot (Seq.seq nat) =
  if nl <= Seq.length v then Seq.slice (vals128 v) 0 nl else Seq.empty

let pre_index (v: Seq.seq S128.t)
  : Lemma (requires Seq.length v == nw)
          (ensures Seq.length (pre v) == nl /\
                   (forall (c: nat). c < nl ==>
                      Seq.index (pre v) c == Seq.index (vals128 v) c))
  = let aux (c: nat { c < nl })
      : Lemma (Seq.index (pre v) c == Seq.index (vals128 v) c)
      = Seq.lemma_index_slice (vals128 v) 0 nl c in
    Classical.forall_intro aux

let pre_upd (v: Seq.seq S128.t) (k: nat { k < nl }) (x: S128.t)
  : Lemma (requires Seq.length v == nw)
          (ensures pre (Seq.upd v k x) == Seq.upd (pre v) k (S128.v x))
  = vals128_upd v k x;
    Seq.lemma_eq_intro (pre (Seq.upd v k x)) (Seq.upd (pre v) k (S128.v x))

(** The four byte weights inside a limb, as literals. *)
let pow2_bytes (_: unit)
  : Lemma (pow2 8 == 256 /\ pow2 16 == 65536 /\ pow2 24 == 16777216)
  = assert_norm (pow2 8 == 256);
    assert_norm (pow2 16 == 65536);
    assert_norm (pow2 24 == 16777216)

(** {2 The machine operations}

    Each is the [uint64] instruction plus the argument that it did not wrap.
    Keeping them here means the modular-arithmetic side condition is
    discharged once, against a two-line context, rather than inside a loop
    body that also carries the heap. *)

inline_for_extraction
let mask32 : m: S64.t { S64.v m == base - 1 } =
  assert_norm (base - 1 == 0xffffffff);
  S64.classify 0xffffffffuL

inline_for_extraction
let mask31 : m: S64.t { S64.v m == pow2 31 - 1 } =
  assert_norm (pow2 31 - 1 == 0x7fffffff);
  S64.classify 0x7fffffffuL

inline_for_extraction
let lo32 (x: S64.t) : r: S64.t { S64.v r == S64.v x % base } =
  UInt.logand_mask #64 (S64.v x) 32;
  S64.logand x mask32

inline_for_extraction
let hi32 (x: S64.t) : r: S64.t { S64.v r == S64.v x / base } =
  S64.shift_right x 32ul

inline_for_extraction
let lo31 (x: S64.t) : r: S64.t { S64.v r == S64.v x % pow2 31 } =
  UInt.logand_mask #64 (S64.v x) 31;
  S64.logand x mask31

inline_for_extraction
let hi31 (x: S64.t) : r: S64.t { S64.v r == S64.v x / pow2 31 } =
  S64.shift_right x 31ul

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

(** The same handful of instructions one width up.  A column of the
    schoolbook product is at most [8 * (2^33 - 1)^2 < 2^69], and the fold
    multiplies it by thirty-eight, so the accumulator has to be a
    hundred-and-twenty-eight-bit integer until the first carry pass has
    brought it back under [2^49]. *)

inline_for_extraction
let addd (x y: S128.t)
  : Pure S128.t (requires S128.v x + S128.v y < pow2 128)
                (ensures fun z -> S128.v z == S128.v x + S128.v y)
  = Math.small_mod (S128.v x + S128.v y) (pow2 128);
    S128.add_mod x y

(** [Hacl.Secret.UInt128] has no multiplication, but [38 = 32 + 4 + 2]. *)
inline_for_extraction
let mul38 (x: S128.t)
  : Pure S128.t (requires 38 * S128.v x < pow2 128)
                (ensures fun z -> S128.v z == 38 * S128.v x)
  = assert_norm (pow2 5 == 32);
    assert_norm (pow2 2 == 4);
    assert_norm (pow2 1 == 2);
    Math.lemma_mult_le_right (S128.v x) 32 38;
    Math.lemma_mult_le_right (S128.v x) 4 38;
    Math.lemma_mult_le_right (S128.v x) 2 38;
    Math.small_mod (S128.v x * pow2 5) (pow2 128);
    Math.small_mod (S128.v x * pow2 2) (pow2 128);
    Math.small_mod (S128.v x * pow2 1) (pow2 128);
    addd (addd (S128.shift_left x 5ul) (S128.shift_left x 2ul)) (S128.shift_left x 1ul)

inline_for_extraction
let lo32d (x: S128.t) : r: S64.t { S64.v r == S128.v x % base } =
  assert_norm (base == pow2 32);
  Math.pow2_modulo_modulo_lemma_1 (S128.v x) 32 64;
  UInt.logand_mask #64 (S128.v x % pow2 64) 32;
  S64.logand (Cast.u128_to_u64 x) mask32

inline_for_extraction
let hi32d (x: S128.t) : r: S128.t { S128.v r == S128.v x / base } =
  assert_norm (base == pow2 32);
  S128.shift_right x 32ul

inline_for_extraction
let narrow128 (x: S128.t)
  : Pure S64.t (requires S128.v x < pow2 64)
               (ensures fun z -> S64.v z == S128.v x)
  = Math.small_mod (S128.v x) (pow2 64);
    Cast.u128_to_u64 x

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
  while (let vk = !k; SZ.lt vk 7sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= 7 /\ Seq.length v == nl /\
          vals v == carry_run (vals va) (SZ.v vk))
  decreases (7 - SZ.v (!k))
  {
    with v. assert (A.pts_to a v);
    let vk = !k;
    carry_run_chained (vals va) c d (SZ.v vk);
    carry_run_len (vals va) (SZ.v vk);
    let t = A.(a.(vk));
    let u = A.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S64.v t) (reveal c + reveal d) base;
    let lo = lo32 t;
    let up = addw u (hi32 t);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    vals_upd v (SZ.v vk) lo;
    vals_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (vals va);
    k := SZ.add vk 1sz;
  };
  with v. assert (A.pts_to a v);
  carry_run_chained (vals va) c d 7;
  carry_run_len (vals va) 7;
  let t = A.(a.(7sz));
  let z = A.(a.(0sz));
  Math.lemma_div_le (S64.v t) (reveal c + reveal d) base;
  let lo = lo32 t;
  let z' = addw z (mulk 38uL (hi32 t));
  A.((a.(7sz) <- lo));
  A.((a.(0sz) <- z'));
  vals_upd v 7 lo;
  vals_upd (Seq.upd v 7 lo) 0 z';
  assert (pure (vals (Seq.upd (Seq.upd v 7 lo) 0 z') == carry_pass (vals va)));
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
  while (let vk = !k; SZ.lt vk 7sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= 7 /\ Seq.length v == nl /\
          vals v == carry_run (vals va) (SZ.v vk))
  decreases (7 - SZ.v (!k))
  {
    with v. assert (A.pts_to a v);
    let vk = !k;
    carry_run_chained (vals va) c d (SZ.v vk);
    carry_run_len (vals va) (SZ.v vk);
    let t = A.(a.(vk));
    let u = A.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S64.v t) (reveal c + reveal d) base;
    let lo = lo32 t;
    let up = addw u (hi32 t);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    vals_upd v (SZ.v vk) lo;
    vals_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (vals va);
    k := SZ.add vk 1sz;
  };
  with v. assert (A.pts_to a v);
  carry_run_len (vals va) 7;
  let t = A.(a.(7sz));
  let lo = lo32 t;
  A.((a.(7sz) <- lo));
  vals_upd v 7 lo;
  assert (pure (vals (Seq.upd v 7 lo) == carry_low (vals va)));
}

(** The same chain one width up, on the first [nl] of the [nw] columns.
    This is the pass that brings a folded product back under [2^49], which
    is where it becomes a word again. *)
fn carry_chain128 (a: A.array S128.t) (c: erased nat) (d: erased nat)
                  (#va: erased (Seq.seq S128.t))
requires A.pts_to a va **
  pure (Seq.length va == nw /\ ble (pre va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 128 /\ base + 38 * reveal d < pow2 128)
ensures exists* (va': Seq.seq S128.t).
  A.pts_to a va' **
  pure (Seq.length va' == nw /\ pre va' == carry_pass (pre va))
{
  A.pts_to_len a;
  div_le_of_lt (reveal c + reveal d) base d;
  Loops.repeati_zero carry_step (pre va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 7sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= 7 /\ Seq.length v == nw /\
          pre v == carry_run (pre va) (SZ.v vk))
  decreases (7 - SZ.v (!k))
  {
    with v. assert (A.pts_to a v);
    let vk = !k;
    carry_run_chained (pre va) c d (SZ.v vk);
    carry_run_len (pre va) (SZ.v vk);
    let x = A.(a.(vk));
    let u = A.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S128.v x) (reveal c + reveal d) base;
    let lo = Cast.u64_to_u128 (lo32d x);
    let up = addd u (hi32d x);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    pre_upd v (SZ.v vk) lo;
    pre_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (pre va);
    k := SZ.add vk 1sz;
  };
  with v. assert (A.pts_to a v);
  carry_run_chained (pre va) c d 7;
  carry_run_len (pre va) 7;
  let x = A.(a.(7sz));
  let z = A.(a.(0sz));
  Math.lemma_div_le (S128.v x) (reveal c + reveal d) base;
  let lo = Cast.u64_to_u128 (lo32d x);
  let z' = addd z (mul38 (hi32d x));
  A.((a.(7sz) <- lo));
  A.((a.(0sz) <- z'));
  pre_upd v 7 lo;
  pre_upd (Seq.upd v 7 lo) 0 z';
  assert (pure (pre (Seq.upd (Seq.upd v 7 lo) 0 z') == carry_pass (pre va)));
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vb) k))
  decreases (8 - SZ.v (!i))
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
  : Lemma (Seq.index eightp i == (if i = 0 then 17179869032 else 17179869180))
  = assert_norm (4 * (base - 38) == 17179869032);
    assert_norm (4 * (base - 1) == 17179869180)

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
  assert_norm (lim < 17179869032);
  assert_norm (lim + 17179869180 < pow2 64);
  eightp_index 0;
  let x0 = A.(a.(0sz));
  let y0 = A.(b.(0sz));
  A.((out.(0sz) <- subw (addw x0 (S64.classify 17179869032uL)) y0));
  let mut i = 1sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (1 <= SZ.v vi /\ SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               Seq.index (vals va) k + Seq.index eightp k - Seq.index (vals vb) k))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    eightp_index (SZ.v vi);
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((out.(vi) <- subw (addw x (S64.classify 17179869180uL)) y));
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == U64.v m * Seq.index (vals va) k))
  decreases (8 - SZ.v (!i))
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
  assert_norm (121665 * lim <= pow2 50);
  assert_norm (pow2 50 + (pow2 18 + pow2 3) < base * (pow2 18 + pow2 3 + 1));
  assert_norm (pow2 50 + (pow2 18 + pow2 3) < pow2 64);
  assert_norm (base + 38 * (pow2 18 + pow2 3) < pow2 64);
  ble_mono (vals v) (121665 * lim) (pow2 50);
  carry_chain out (pow2 50) (pow2 18 + pow2 3);
  with v2. assert (A.pts_to out v2);
  assert (pure (vals v2 == carry_pass (scale (U64.v m) (vals va))));
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

fn mul_columns (t: A.array S128.t) (a b: A.array S64.t)
               (#vt: erased (Seq.seq S128.t))
               (#pa: perm) (#va: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == nw /\ felem (vals va) /\ felem (vals vb))
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ vals128 vt' == part (vals va) (vals vb) nl)
{
  A.pts_to_len t;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (nl * (lim * lim) + lim * lim < pow2 128);
  assert_norm (lim * lim < pow2 128);
  let z = S128.zero;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 15sz)
  invariant exists* (vc: SZ.t) (v: Seq.seq S128.t).
    pts_to c vc ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vc <= 15 /\ Seq.length v == nw /\
          (forall (k: nat). k < SZ.v vc ==> Seq.index (vals128 v) k == 0))
  decreases (15 - SZ.v (!c))
  {
    let vc = !c;
    A.((t.(vc) <- z));
    c := SZ.add vc 1sz;
  };
  with v0. assert (A.pts_to t v0);
  assert (pure (vals128 v0 `Seq.equal` zerow));
  Loops.repeati_zero (mul_step (vals va) (vals vb)) zerow;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == nw /\
          vals128 v == part (vals va) (vals vb) (SZ.v vi))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let ai = A.(a.(vi));
    part_len (vals va) (vals vb) (SZ.v vi);
    rowj_zero (vals va) (vals vb) (SZ.v vi);
    addw_zerow (part (vals va) (vals vb) (SZ.v vi));
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj 8sz)
    invariant exists* (vj: SZ.t) (v: Seq.seq S128.t).
      pts_to j vj ** pts_to i vi ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      pure (SZ.v vj <= 8 /\ Seq.length v == nw /\ SZ.v vi < 8 /\
            vals128 v == Spec.Curve25519.Field.addw
                           (part (vals va) (vals vb) (SZ.v vi))
                           (rowj (vals va) (vals vb) (SZ.v vi) (SZ.v vj)))
    decreases (8 - SZ.v (!j))
    {
      with v. assert (A.pts_to t v);
      let vj = !j;
      acc_ble (vals va) (vals vb) (vals128 v) (SZ.v vi) (SZ.v vj);
      let bj = A.(b.(vj));
      let pos = SZ.add vi vj;
      let cur = A.(t.(pos));
      Math.lemma_mult_le_left (S64.v ai) (S64.v bj) lim;
      Math.lemma_mult_le_right lim (S64.v ai) lim;
      let nw' = addd cur (S128.mul_wide ai bj);
      A.((t.(pos) <- nw'));
      vals128_upd v (SZ.v vi + SZ.v vj) nw';
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

(** One step of the fold, on the sequences alone: [g] is [f] with the first
    [k] columns already folded, and [x] is the folded column [k]. *)
let fold_step (f g: Seq.seq nat) (k: nat { k < 7 }) (x: nat)
  : Lemma (requires Seq.length f == nw /\ Seq.length g == nw /\
                    x == Seq.index f k + 38 * Seq.index f (k + 8) /\
                    (forall (c: nat). c < k ==>
                       Seq.index g c == Seq.index f c + 38 * Seq.index f (c + 8)) /\
                    (forall (c: nat). k <= c /\ c < nw ==> Seq.index g c == Seq.index f c))
          (ensures (let h = Seq.upd g k x in
                    Seq.length h == nw /\
                    (forall (c: nat). c < k + 1 ==>
                       Seq.index h c == Seq.index f c + 38 * Seq.index f (c + 8)) /\
                    (forall (c: nat). k + 1 <= c /\ c < nw ==> Seq.index h c == Seq.index f c)))
  = ()

(** One step of the narrowing copy, on the sequences alone. *)
let copy_step (f g: Seq.seq nat) (k: nat { k < Seq.length g }) (x: nat)
  : Lemma (requires Seq.length f == Seq.length g /\ x == Seq.index f k /\
                    (forall (c: nat). c < k ==> Seq.index g c == Seq.index f c))
          (ensures (forall (c: nat). c < k + 1 ==>
                      Seq.index (Seq.upd g k x) c == Seq.index f c))
  = ()

#push-options "--z3rlimit 600"

fn fmul (out a b: A.array S64.t) (t: A.array S128.t)
        (#vout: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S128.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ Seq.length vt == nw /\
        felem (vals va) /\ felem (vals vb))
ensures exists* (vout': Seq.seq S64.t) (vt': Seq.seq S128.t).
  A.pts_to out vout' ** A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ felem (vals vout') /\
        fev (vals vout') == C.fmul (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len t;
  mul_columns t a b;
  with vp. assert (A.pts_to t vp);
  part_ble (vals va) (vals vb) lim lim nl;
  assert_norm (39 * (nl * (lim * lim)) < pow2 128);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 7sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to t v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vk <= 7 /\ Seq.length v == nw /\
          (forall (c: nat). c < SZ.v vk ==>
             Seq.index (vals128 v) c ==
               Seq.index (vals128 vp) c + 38 * Seq.index (vals128 vp) (c + 8)) /\
          (forall (c: nat). SZ.v vk <= c /\ c < nw ==>
             Seq.index (vals128 v) c == Seq.index (vals128 vp) c))
  decreases (7 - SZ.v (!k))
  {
    with v. assert (A.pts_to t v);
    let vk = !k;
    let x = A.(t.(vk));
    let y = A.(t.(SZ.add vk 8sz));
    assert (pure (S128.v x == Seq.index (vals128 vp) (SZ.v vk)));
    assert (pure (S128.v y == Seq.index (vals128 vp) (SZ.v vk + 8)));
    assert (pure (38 * S128.v y < pow2 128));
    let s = addd x (mul38 y);
    A.((t.(vk) <- s));
    vals128_upd v (SZ.v vk) s;
    fold_step (vals128 vp) (vals128 v) (SZ.v vk) (S128.v s);
    k := SZ.add vk 1sz;
  };
  with v. assert (A.pts_to t v);
  pre_index v;
  assert (pure (pre v `Seq.equal` fold38 (vals128 vp)));
  fold_ble (vals128 vp) (nl * (lim * lim));
  assert_norm (39 * (nl * (lim * lim)) <= pow2 75);
  ble_mono (pre v) (39 * (nl * (lim * lim))) (pow2 75);
  assert_norm (pow2 75 + (pow2 43 + pow2 28) < base * (pow2 43 + pow2 28 + 1));
  assert_norm (pow2 75 + (pow2 43 + pow2 28) < pow2 128);
  assert_norm (base + 38 * (pow2 43 + pow2 28) < pow2 128);
  carry_chain128 t (pow2 75) (pow2 43 + pow2 28);
  with v1. assert (A.pts_to t v1);
  carry_pass_len (pre v);
  carry_pass_ble (pre v) (pow2 75) (pow2 43 + pow2 28);
  assert_norm (base - 1 + 38 * ((pow2 75 + (pow2 43 + pow2 28)) / base) <= pow2 49);
  ble_mono (pre v1) (base - 1 + 38 * ((pow2 75 + (pow2 43 + pow2 28)) / base)) (pow2 49);
  assert_norm (pow2 49 < pow2 64);
  let mut n = 0sz;
  while (let vn = !n; SZ.lt vn 8sz)
  invariant exists* (vn: SZ.t) (w: Seq.seq S64.t).
    pts_to n vn ** A.pts_to out w ** A.pts_to t v1 ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vn <= 8 /\ Seq.length w == nl /\
          (forall (c: nat). c < SZ.v vn ==>
             Seq.index (vals w) c == Seq.index (pre v1) c))
  decreases (8 - SZ.v (!n))
  {
    with w. assert (A.pts_to out w);
    let vn = !n;
    let x = A.(t.(vn));
    Seq.lemma_index_slice (vals128 v1) 0 nl (SZ.v vn);
    assert (pure (Seq.index (pre v1) (SZ.v vn) == S128.v x));
    assert (pure (S128.v x <= pow2 49));
    assert (pure (S128.v x < pow2 64));
    let y = narrow128 x;
    A.((out.(vn) <- y));
    vals_upd w (SZ.v vn) y;
    copy_step (pre v1) (vals w) (SZ.v vn) (S64.v y);
    n := SZ.add vn 1sz;
  };
  with w. assert (A.pts_to out w);
  assert (pure (vals w `Seq.equal` pre v1));
  assert_norm (pow2 49 + (pow2 17 + pow2 2) < base * (pow2 17 + pow2 2 + 1));
  assert_norm (pow2 49 + (pow2 17 + pow2 2) < pow2 64);
  assert_norm (base + 38 * (pow2 17 + pow2 2) < pow2 64);
  carry_chain out (pow2 49) (pow2 17 + pow2 2);
  with v3. assert (A.pts_to out v3);
  assert (pure (pre v == fold38 (part (vals va) (vals vb) nl)));
  assert (pure (vals v3 ==
                carry_pass (carry_pass (fold38 (part (vals va) (vals vb) nl)))));
  assert (pure (vals v3 == fmul_spec (vals va) (vals vb)));
  fmul_spec_ok (vals va) (vals vb);
  assert (pure (felem (vals v3)));
}

#pop-options

(** {2 Bytes} *)

#push-options "--z3rlimit 120"

(** Four little-endian bytes make a limb. *)
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               S8.v (Seq.index vb (4 * k)) + 256 * S8.v (Seq.index vb (4 * k + 1)) +
               65536 * S8.v (Seq.index vb (4 * k + 2)) +
               16777216 * S8.v (Seq.index vb (4 * k + 3))))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let o = SZ.mul vi 4sz;
    let b0 = A.(b.(o));
    let b1 = A.(b.(SZ.add o 1sz));
    let b2 = A.(b.(SZ.add o 2sz));
    let b3 = A.(b.(SZ.add o 3sz));
    assert_norm (16777216 * (pow2 8 - 1) < pow2 64);
    assert_norm (65536 * (pow2 8 - 1) < pow2 64);
    assert_norm (256 * (pow2 8 - 1) < pow2 64);
    assert_norm ((pow2 8 - 1) + 256 * (pow2 8 - 1) +
                 65536 * (pow2 8 - 1) + 16777216 * (pow2 8 - 1) < pow2 64);
    let w = addw (addw (Cast.u8_to_u64 b0) (mulk 256uL (Cast.u8_to_u64 b1)))
                 (addw (mulk 65536uL (Cast.u8_to_u64 b2))
                       (mulk 16777216uL (Cast.u8_to_u64 b3)));
    A.((a.(vi) <- w));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  assert (pure (forall (k: nat). k < nl ==>
                  Seq.index (vals v) k ==
                    S8.v (Seq.index vb (4 * k)) + 256 * S8.v (Seq.index vb (4 * k + 1)) +
                    65536 * S8.v (Seq.index vb (4 * k + 2)) +
                    16777216 * S8.v (Seq.index vb (4 * k + 3))));
  eval_bytes vb (vals v);
  assert_norm ((pow2 8 - 1) + 256 * (pow2 8 - 1) +
               65536 * (pow2 8 - 1) + 16777216 * (pow2 8 - 1) < base);
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
  let t = A.(a.(7sz));
  let m = lo31 t;
  A.((a.(7sz) <- m));
  vals_upd va 7 m;
  mask255_ok (vals va);
  assert (pure (vals (Seq.upd va 7 m) == mask255 (vals va)));
}

(** A limb is exactly four bytes, so storing is a truncation and three
    shifts. *)
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 8 /\ Seq.length v == 32 /\
          (forall (k: nat). k < SZ.v vi ==>
             S8.v (Seq.index v (4 * k)) == Seq.index (vals va) k % 256 /\
             S8.v (Seq.index v (4 * k + 1)) == Seq.index (vals va) k / 256 % 256 /\
             S8.v (Seq.index v (4 * k + 2)) == Seq.index (vals va) k / 65536 % 256 /\
             S8.v (Seq.index v (4 * k + 3)) == Seq.index (vals va) k / 16777216 % 256))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let o = SZ.mul vi 4sz;
    pow2_bytes ();
    A.((b.(o) <- Cast.u64_to_u8 x));
    A.((b.(SZ.add o 1sz) <- Cast.u64_to_u8 (S64.shift_right x 8ul)));
    A.((b.(SZ.add o 2sz) <- Cast.u64_to_u8 (S64.shift_right x 16ul)));
    A.((b.(SZ.add o 3sz) <- Cast.u64_to_u8 (S64.shift_right x 24ul)));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  assert (pure (Seq.length v == 32 /\ bnd (vals va) base));
  assert (pure (forall (k: nat). k < nl ==>
                  S8.v (Seq.index v (4 * k)) == Seq.index (vals va) k % 256 /\
                  S8.v (Seq.index v (4 * k + 1)) == Seq.index (vals va) k / 256 % 256 /\
                  S8.v (Seq.index v (4 * k + 2)) == Seq.index (vals va) k / 65536 % 256 /\
                  S8.v (Seq.index v (4 * k + 3)) == Seq.index (vals va) k / 16777216 % 256));
  store_digits (vals va) v;
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
  let t = A.(a.(7sz));
  let z = A.(a.(0sz));
  let m = lo31 t;
  assert_norm (base + 19 * 2 < pow2 64);
  Math.lemma_div_lt_nat (S64.v t) 32 31;
  assert_norm (pow2 (32 - 31) == 2);
  let z' = addw z (mulk 19uL (hi31 t));
  A.((a.(7sz) <- m));
  A.((a.(0sz) <- z'));
  vals_upd va 7 m;
  vals_upd (Seq.upd va 7 m) 0 z';
  assert (pure (vals (Seq.upd (Seq.upd va 7 m) 0 z') == fold255 (vals va)));
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
  Math.lemma_div_lt_nat (Seq.index (vals va) 7) 32 31;
  assert_norm (pow2 (32 - 31) == 2);
  assert_norm (pow2 31 < base + 19);
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
  assert_norm (4294967371 + 1 < base * 2);
  assert_norm (4294967371 + 1 < pow2 64);
  assert_norm (base + 38 * 1 < pow2 64);
  carry_chain a 4294967371 1;
  with x2. assert (A.pts_to a x2);
  assert (pure (vals x2 == carry_pass (carry_pass (vals va))));
  assert_norm (4294967333 + 1 < base * 2);
  assert_norm (4294967333 + 1 < pow2 64);
  carry_chain a 4294967333 1;
  with x3. assert (A.pts_to a x3);
  assert (pure (vals x3 == carry_pass (carry_pass (carry_pass (vals va)))));
  carry_chain a 4294967333 1;
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a y ** A.pts_to t v **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index y k))
  decreases (8 - SZ.v (!i))
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
  let wt = A.(t.(7sz));
  let bit = hi31 wt;
  Math.lemma_div_lt_nat (S64.v wt) 32 31;
  assert_norm (pow2 (32 - 31) == 2);
  let sel = S64.eq_mask bit (S64.classify 1uL);
  let mt = lo31 wt;
  A.((t.(7sz) <- mt));
  with wm. assert (A.pts_to t wm);
  vals_upd w 7 mt;
  assert (pure (vals wm == mask255 (vals w)));
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 8sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S64.t).
    pts_to j vj ** A.pts_to a v ** A.pts_to t wm **
    pure (SZ.v vj <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index v k == (if hi255 (vals w) = 1 then Seq.index wm k else Seq.index y k)) /\
          (forall (k: nat). SZ.v vj <= k /\ k < nl ==> Seq.index v k == Seq.index y k))
  decreases (8 - SZ.v (!j))
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (x: Seq.seq S64.t) (y: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a x ** A.pts_to b y **
    pure (SZ.v vi <= 8 /\ Seq.length x == nl /\ Seq.length y == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index x k == (if S64.v sel = 0 then Seq.index va k else Seq.index vb k) /\
             Seq.index y k == (if S64.v sel = 0 then Seq.index vb k else Seq.index va k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < nl ==>
             Seq.index x k == Seq.index va k /\ Seq.index y k == Seq.index vb k))
  decreases (8 - SZ.v (!i))
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #ps vs **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index vs k))
  decreases (8 - SZ.v (!i))
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
