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

(** Curve25519's field, on five sixty-four-bit secret integers.

    A field element is a five-element slice; limb [k] carries bits [51k] to
    [51k+51], and the operations keep every limb at or below [2^52 - 1].
    Fifty-one bits is the classical choice for this curve and the one HACL*
    makes: [5 * 51 = 255], so the wrap-around of the top limb is a
    multiplication by [19] rather than [38], and the whole schoolbook
    product is twenty-five word multiplies rather than sixty-four.

    The headroom works out.  A column of the product holds at most five
    limb products, each below [2^104], so a column is below [2^107]; the
    fold multiplies it by twenty and it is still below [2^111], which is
    comfortably inside a hundred and twenty-eight bits.  Two carry passes
    in that width bring it back under [2^52], which is where it becomes a
    word again.

    What fifty-one bits costs is the byte layer: a limb is no longer a
    whole number of bytes.  Rather than prove a second one, {!load} and
    {!store} go through the thirty-two-bit representation of
    [Spec.Bignum256] -- whose byte layer is a shuffle and already proved --
    and repack the bits with a handful of shifts.  The repacking is
    straight-line and its correctness is two lemmas in
    [Spec.Curve25519.Field].

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
module B32 = Spec.Bignum256
module W = Spec.Bignum51.Window
module W32 = Spec.Bignum256.Window
module R = Spec.Curve25519.Repack
module Cols = Spec.Curve25519.Columns
module Mem = Hacl.Mem

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

(** The four byte weights inside a thirty-two-bit limb, as literals. *)
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
let mask51 : m: S64.t { S64.v m == base - 1 } =
  assert_norm (base - 1 == 0x7ffffffffffff);
  S64.classify 0x7ffffffffffffuL

inline_for_extraction
let mask32 : m: S64.t { S64.v m == pow2 32 - 1 } =
  assert_norm (pow2 32 - 1 == 0xffffffff);
  S64.classify 0xffffffffuL

inline_for_extraction
let mask31 : m: S64.t { S64.v m == pow2 31 - 1 } =
  assert_norm (pow2 31 - 1 == 0x7fffffff);
  S64.classify 0x7fffffffuL

inline_for_extraction
let lo51 (x: S64.t) : r: S64.t { S64.v r == S64.v x % base } =
  assert_norm (base == pow2 51);
  UInt.logand_mask #64 (S64.v x) 51;
  S64.logand x mask51

inline_for_extraction
let hi51 (x: S64.t) : r: S64.t { S64.v r == S64.v x / base } =
  assert_norm (base == pow2 51);
  S64.shift_right x 51ul

inline_for_extraction
let lo31 (x: S64.t) : r: S64.t { S64.v r == S64.v x % pow2 31 } =
  UInt.logand_mask #64 (S64.v x) 31;
  S64.logand x mask31

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

(** The same handful of instructions one width up.  A column of the
    schoolbook product is at most [5 * (2^52 - 1)^2 < 2^107], and the fold
    multiplies it by twenty, so the accumulator has to be a
    hundred-and-twenty-eight-bit integer until two carry passes have
    brought it back under [2^52]. *)

inline_for_extraction
let addd (x y: S128.t)
  : Pure S128.t (requires S128.v x + S128.v y < pow2 128)
                (ensures fun z -> S128.v z == S128.v x + S128.v y)
  = Math.small_mod (S128.v x + S128.v y) (pow2 128);
    S128.add_mod x y

(** [Hacl.Secret.UInt128] has no multiplication, but [19 = 16 + 2 + 1]. *)
inline_for_extraction
let mul19 (x: S128.t)
  : Pure S128.t (requires 19 * S128.v x < pow2 128)
                (ensures fun z -> S128.v z == 19 * S128.v x)
  = assert_norm (pow2 4 == 16);
    assert_norm (pow2 1 == 2);
    Math.lemma_mult_le_right (S128.v x) 16 19;
    Math.lemma_mult_le_right (S128.v x) 2 19;
    Math.small_mod (S128.v x * pow2 4) (pow2 128);
    Math.small_mod (S128.v x * pow2 1) (pow2 128);
    addd (addd (S128.shift_left x 4ul) (S128.shift_left x 1ul)) x

inline_for_extraction
let lo51d (x: S128.t) : r: S64.t { S64.v r == S128.v x % base } =
  assert_norm (base == pow2 51);
  Math.pow2_modulo_modulo_lemma_1 (S128.v x) 51 64;
  UInt.logand_mask #64 (S128.v x % pow2 64) 51;
  S64.logand (Cast.u128_to_u64 x) mask51

inline_for_extraction
let hi51d (x: S128.t) : r: S128.t { S128.v r == S128.v x / base } =
  assert_norm (base == pow2 51);
  S128.shift_right x 51ul

inline_for_extraction
let narrow128 (x: S128.t)
  : Pure S64.t (requires S128.v x < pow2 64)
               (ensures fun z -> S64.v z == S128.v x)
  = Math.small_mod (S128.v x) (pow2 64);
    Cast.u128_to_u64 x

(** {2 The carry pass}

    Limbs [0] to [3] carry into their neighbour, and the top limb carries
    round into limb [0] multiplied by [19].  [c] bounds the limbs on entry
    and [d] the carry; the caller supplies both, and
    [Spec.Curve25519.Field.pass] turns them into the bound on exit. *)

#push-options "--z3rlimit 200"

[@@ FStar.Attributes.CInline]
fn carry_chain (a: A.array S64.t) (c: erased nat) (d: erased nat)
               (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\ ble (vals va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 64 /\ base + 19 * reveal d < pow2 64)
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
    let lo = lo51 t;
    let up = addw u (hi51 t);
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
  let lo = lo51 t;
  let z' = addw z (mulk 19uL (hi51 t));
  A.((a.(4sz) <- lo));
  A.((a.(0sz) <- z'));
  vals_upd v 4 lo;
  vals_upd (Seq.upd v 4 lo) 0 z';
  assert (pure (vals (Seq.upd (Seq.upd v 4 lo) 0 z') == carry_pass (vals va)));
}

(** The same chain without the wrap-around: the top limb keeps only its low
    fifty-one bits and the overflow is returned rather than folded, which is
    [carry_low] together with [carry_out]. *)
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
    let lo = lo51 t;
    let up = addw u (hi51 t);
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
  let lo = lo51 t;
  let hi = hi51 t;
  A.((a.(4sz) <- lo));
  vals_upd v 4 lo;
  assert (pure (vals (Seq.upd v 4 lo) == carry_low (vals va)));
  hi
}

(** The same chain one width up, on the first [nl] of the [nw] columns.
    This is the pass that brings a folded product back towards a word. *)
[@@ FStar.Attributes.CInline]
fn carry_chain128 (a: A.array S128.t) (c: erased nat) (d: erased nat)
                  (#va: erased (Seq.seq S128.t))
requires A.pts_to a va **
  pure (Seq.length va == nw /\ ble (pre va) c /\
        reveal c + reveal d < base * (reveal d + 1) /\
        reveal c + reveal d < pow2 128 /\ base + 19 * reveal d < pow2 128)
ensures exists* (va': Seq.seq S128.t).
  A.pts_to a va' **
  pure (Seq.length va' == nw /\ pre va' == carry_pass (pre va))
{
  A.pts_to_len a;
  div_le_of_lt (reveal c + reveal d) base d;
  Loops.repeati_zero carry_step (pre va);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 4sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to a v **
    pure (SZ.v vk <= 4 /\ Seq.length v == nw /\
          pre v == carry_run (pre va) (SZ.v vk))
  decreases (4 - SZ.v (!k))
  {
    with v. assert (A.pts_to a v);
    let vk = !k;
    carry_run_chained (pre va) c d (SZ.v vk);
    carry_run_len (pre va) (SZ.v vk);
    let x = A.(a.(vk));
    let u = A.(a.(SZ.add vk 1sz));
    Math.lemma_div_le (S128.v x) (reveal c + reveal d) base;
    let lo = Cast.u64_to_u128 (lo51d x);
    let up = addd u (hi51d x);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    pre_upd v (SZ.v vk) lo;
    pre_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (pre va);
    k := SZ.add vk 1sz;
  };
  with v. assert (A.pts_to a v);
  carry_run_chained (pre va) c d 4;
  carry_run_len (pre va) 4;
  let x = A.(a.(4sz));
  let z = A.(a.(0sz));
  Math.lemma_div_le (S128.v x) (reveal c + reveal d) base;
  let lo = Cast.u64_to_u128 (lo51d x);
  let z' = addd z (mul19 (hi51d x));
  A.((a.(4sz) <- lo));
  A.((a.(0sz) <- z'));
  pre_upd v 4 lo;
  pre_upd (Seq.upd v 4 lo) 0 z';
  assert (pure (pre (Seq.upd (Seq.upd v 4 lo) 0 z') == carry_pass (pre va)));
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
        fev (vals vout') == C.fadd (fev (vals va)) (fev (vals vb)))
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
  assert (pure (vals v `Seq.equal` Spec.Curve25519.Field.addw (vals va) (vals vb)));
  addw_ble (vals va) (vals vb) lim lim;
  assert_norm (lim + lim + 4 < base * 5);
  assert_norm (lim + lim + 4 < pow2 64);
  assert_norm (base + 19 * 4 < pow2 64);
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
  : Lemma (Seq.index eightp i ==
             (if i = 0 then 18014398509481832 else 18014398509481976))
  = assert_norm (8 * (base - 19) == 18014398509481832);
    assert_norm (8 * (base - 1) == 18014398509481976)

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
        fev (vals vout') == C.fsub (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (lim < 18014398509481832);
  assert_norm (lim + 18014398509481976 < pow2 64);
  eightp_index 0;
  let x0 = A.(a.(0sz));
  let y0 = A.(b.(0sz));
  A.((out.(0sz) <- subw (addw x0 (S64.classify 18014398509481832uL)) y0));
  let mut i = 1sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (1 <= SZ.v vi /\ SZ.v vi <= 5 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               Seq.index (vals va) k + Seq.index eightp k - Seq.index (vals vb) k))
  decreases (5 - SZ.v (!i))
  {
    let vi = !i;
    eightp_index (SZ.v vi);
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((out.(vi) <- subw (addw x (S64.classify 18014398509481976uL)) y));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  eightp_ok ();
  assert (pure (vals v `Seq.equal` Spec.Curve25519.Field.subw (vals va) (vals vb)));
  subw_ok (vals va) (vals vb);
  assert_norm (lim + 8 * (base - 1) + 10 < base * 11);
  assert_norm (lim + 8 * (base - 1) + 10 < pow2 64);
  assert_norm (base + 19 * 10 < pow2 64);
  carry_chain out (lim + 8 * (base - 1)) 10;
  with v'. assert (A.pts_to out v');
  assert (pure (vals v' == carry_pass (vals v)));
  assert (pure (vals v == Spec.Curve25519.Field.subw (vals va) (vals vb)));
  assert (pure (vals v' == fsub_spec (vals va) (vals vb)));
  fsub_spec_ok (vals va) (vals vb);
  assert (pure (felem (vals v')));
}

#pop-options

(** One step of the narrowing copy, on the sequences alone. *)
let copy_step (f g: Seq.seq nat) (k: nat { k < Seq.length g }) (x: nat)
  : Lemma (requires Seq.length f == Seq.length g /\ x == Seq.index f k /\
                    (forall (c: nat). c < k ==> Seq.index g c == Seq.index f c))
          (ensures (forall (c: nat). c < k + 1 ==>
                      Seq.index (Seq.upd g k x) c == Seq.index f c))
  = ()

(** {2 Multiplication by a small constant}

    [121665] times a limb reaches [2^69], so unlike at radix [2^32] this one
    does not fit in a word either: the products go into the wide scratch
    slice and come back through one carry pass. *)

#push-options "--z3rlimit 200"

[@@ FStar.Attributes.CInline]
fn fscale (out a: A.array S64.t) (m: U64.t { U64.v m <= 121665 }) (t: A.array S128.t)
          (#vout: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S128.t))
          (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to t vt ** A.pts_to a #pa va **
  pure (Seq.length vout == nl /\ Seq.length vt == nw /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t) (vt': Seq.seq S128.t).
  A.pts_to out vout' ** A.pts_to t vt' ** A.pts_to a #pa va **
  pure (Seq.length vt' == nw /\ felem (vals vout') /\
        fev (vals vout') == (U64.v m * eval (vals va)) % prime)
{
  A.pts_to_len out;
  A.pts_to_len t;
  A.pts_to_len a;
  let ms = S64.classify m;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to t v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 5 /\ Seq.length v == nw /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals128 v) k == U64.v m * Seq.index (vals va) k))
  decreases (5 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    A.((t.(vi) <- S128.mul_wide ms x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to t v);
  pre_index v;
  assert (pure (pre v `Seq.equal` scale (U64.v m) (vals va)));
  scale_ble (U64.v m) (vals va) lim;
  Math.lemma_mult_le_right lim (U64.v m) 121665;
  ble_mono (pre v) (U64.v m * lim) (121665 * lim);
  assert_norm (121665 * lim <= pow2 69);
  ble_mono (pre v) (121665 * lim) (pow2 69);
  assert_norm (pow2 69 + (pow2 18 + pow2 6) < base * (pow2 18 + pow2 6 + 1));
  assert_norm (pow2 69 + (pow2 18 + pow2 6) < pow2 128);
  assert_norm (base + 19 * (pow2 18 + pow2 6) < pow2 128);
  carry_chain128 t (pow2 69) (pow2 18 + pow2 6);
  with v1. assert (A.pts_to t v1);
  carry_pass_len (pre v);
  carry_pass_ble (pre v) (pow2 69) (pow2 18 + pow2 6);
  assert_norm (base - 1 + 19 * ((pow2 69 + (pow2 18 + pow2 6)) / base) <= lim);
  ble_mono (pre v1) (base - 1 + 19 * ((pow2 69 + (pow2 18 + pow2 6)) / base)) lim;
  assert_norm (lim < pow2 64);
  let mut n = 0sz;
  while (let vn = !n; SZ.lt vn 5sz)
  invariant exists* (vn: SZ.t) (w: Seq.seq S64.t).
    pts_to n vn ** A.pts_to out w ** A.pts_to t v1 ** A.pts_to a #pa va **
    pure (SZ.v vn <= 5 /\ Seq.length w == nl /\
          (forall (c: nat). c < SZ.v vn ==>
             Seq.index (vals w) c == Seq.index (pre v1) c))
  decreases (5 - SZ.v (!n))
  {
    with w. assert (A.pts_to out w);
    let vn = !n;
    let x = A.(t.(vn));
    Seq.lemma_index_slice (vals128 v1) 0 nl (SZ.v vn);
    assert (pure (Seq.index (pre v1) (SZ.v vn) == S128.v x));
    assert (pure (S128.v x < pow2 64));
    let y = narrow128 x;
    A.((out.(vn) <- y));
    vals_upd w (SZ.v vn) y;
    copy_step (pre v1) (vals w) (SZ.v vn) (S64.v y);
    n := SZ.add vn 1sz;
  };
  with w. assert (A.pts_to out w);
  assert (pure (vals w `Seq.equal` pre v1));
  assert (pure (vals w == fscale_spec (U64.v m) (vals va)));
  fscale_spec_ok (U64.v m) (vals va);
  assert (pure (felem (vals w)));
}

#pop-options

(** {2 Multiplication}

    Twenty-five products, five columns, one carry chain -- and not one
    array.  [Spec.Curve25519.Columns] says the five columns of
    [fold19 (part a b nl)] are these five explicit sums and that
    [carry_fix (carry_pass .)] is this straight line, so the whole of
    [fmul] can be written in local variables and Custard emits it as
    such.  The nine-column accumulator and the second carry pass that the
    specification describes are proof scaffolding; they never run.

    The two ideas that make it fit.  The reduction constant is folded
    into [b] up front -- [19 * lim] still fits a word, so four
    multiplications buy nine columns collapsed to five.  And the carry
    between columns is a {e word}: a column is under [95 * lim^2], so its
    quotient by the base is under [2^60] and nineteen times the last one
    is still under [2^64].  That is what turns two hundred-and-twenty-eight-bit
    carry passes into one chain of five. *)

unfold let colb : nat = 5 * (19 * (lim * lim))
unfold let carb : nat = (colb + pow2 60) / base

(** A limb product with the nineteen already in the right factor. *)
inline_for_extraction
let mulw19 (x y: S64.t)
  : Pure S128.t (requires S64.v x <= lim /\ S64.v y <= 19 * lim)
                (ensures fun z -> S128.v z == S64.v x * S64.v y /\
                                  S128.v z <= 19 * (lim * lim))
  = Math.lemma_mult_le_left (S64.v x) (S64.v y) (19 * lim);
    Math.lemma_mult_le_right (19 * lim) (S64.v x) lim;
    Math.paren_mul_right lim 19 lim;
    Math.swap_mul lim 19;
    Math.paren_mul_right 19 lim lim;
    S128.mul_wide x y

(** One column: five of those, summed left to right. *)
inline_for_extraction
let col5 (p0 p1 p2 p3 p4: S128.t)
  : Pure S128.t
         (requires S128.v p0 <= 19 * (lim * lim) /\ S128.v p1 <= 19 * (lim * lim) /\
                   S128.v p2 <= 19 * (lim * lim) /\ S128.v p3 <= 19 * (lim * lim) /\
                   S128.v p4 <= 19 * (lim * lim))
         (ensures fun z ->
            S128.v z == S128.v p0 + S128.v p1 + S128.v p2 + S128.v p3 + S128.v p4 /\
            S128.v z <= colb)
  = assert_norm (colb < pow2 128);
    addd (addd (addd (addd p0 p1) p2) p3) p4

(** The incoming carry, widened onto a column. *)
inline_for_extraction
let cadd (x: S128.t) (c: S64.t)
  : Pure S128.t (requires S128.v x <= colb /\ S64.v c <= carb)
                (ensures fun z -> S128.v z == S128.v x + S64.v c /\
                                  S128.v z <= colb + pow2 60)
  = assert_norm (carb <= pow2 60);
    assert_norm (colb + pow2 60 < pow2 128);
    addd x (Cast.u64_to_u128 c)

(** The outgoing carry, narrowed back to a word. *)
inline_for_extraction
let chi (x: S128.t)
  : Pure S64.t (requires S128.v x <= colb + pow2 60)
               (ensures fun k -> S64.v k == S128.v x / base /\ S64.v k <= carb)
  = assert_norm (carb < pow2 64);
    Math.lemma_div_le (S128.v x) (colb + pow2 60) base;
    narrow128 (hi51d x)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

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
        fev (vals vout') == C.fmul (fev (vals va)) (fev (vals vb)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (nl == 5);
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let a4 = A.(a.(4sz));
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  let b4 = A.(b.(4sz));

  (* The four scaled limbs of [b]. *)
  assert_norm (19 * lim < pow2 64);
  let r1 = mulk 19uL b1;
  let r2 = mulk 19uL b2;
  let r3 = mulk 19uL b3;
  let r4 = mulk 19uL b4;
  assert (pure (S64.v b0 <= 19 * lim /\ S64.v b1 <= 19 * lim /\
                S64.v b2 <= 19 * lim /\ S64.v b3 <= 19 * lim /\
                S64.v b4 <= 19 * lim));

  let c0 = col5 (mulw19 a0 b0) (mulw19 a1 r4) (mulw19 a2 r3) (mulw19 a3 r2) (mulw19 a4 r1);
  let c1 = col5 (mulw19 a0 b1) (mulw19 a1 b0) (mulw19 a2 r4) (mulw19 a3 r3) (mulw19 a4 r2);
  let c2 = col5 (mulw19 a0 b2) (mulw19 a1 b1) (mulw19 a2 b0) (mulw19 a3 r4) (mulw19 a4 r3);
  let c3 = col5 (mulw19 a0 b3) (mulw19 a1 b2) (mulw19 a2 b1) (mulw19 a3 b0) (mulw19 a4 r4);
  let c4 = col5 (mulw19 a0 b4) (mulw19 a1 b3) (mulw19 a2 b2) (mulw19 a3 b1) (mulw19 a4 b0);

  (* The columns are the five entries of [fold19 (part a b nl)]. *)
  Cols.col0 (vals va) (vals vb);
  Cols.col1 (vals va) (vals vb);
  Cols.col2 (vals va) (vals vb);
  Cols.col3 (vals va) (vals vb);
  Cols.col4 (vals va) (vals vb);
  assert (pure (Seq.length (fold19 (part (vals va) (vals vb) nl)) == nl /\
                vat (fold19 (part (vals va) (vals vb) nl)) 0 == S128.v c0 /\
                vat (fold19 (part (vals va) (vals vb) nl)) 1 == S128.v c1 /\
                vat (fold19 (part (vals va) (vals vb) nl)) 2 == S128.v c2 /\
                vat (fold19 (part (vals va) (vals vb) nl)) 3 == S128.v c3 /\
                vat (fold19 (part (vals va) (vals vb) nl)) 4 == S128.v c4));

  (* One chain up the limbs, carrying a word. *)
  let o0 = lo51d c0;
  let k0 = chi c0;
  let l1 = cadd c1 k0;
  let o1 = lo51d l1;
  let k1 = chi l1;
  let l2 = cadd c2 k1;
  let o2 = lo51d l2;
  let k2 = chi l2;
  let l3 = cadd c3 k2;
  let o3 = lo51d l3;
  let k3 = chi l3;
  let l4 = cadd c4 k3;
  let o4 = lo51d l4;
  let k4 = chi l4;

  (* The wrap: [2^255 == prime + 19], then one more step into limb one. *)
  assert_norm (19 * carb < pow2 64);
  assert_norm (base + 19 * carb < pow2 64);
  let t0 = addw o0 (mulk 19uL k4);
  let w0 = lo51 t0;
  let w1 = addw o1 (hi51 t0);

  Cols.chain (fold19 (part (vals va) (vals vb) nl));

  A.((out.(0sz) <- w0));
  A.((out.(1sz) <- w1));
  A.((out.(2sz) <- o2));
  A.((out.(3sz) <- o3));
  A.((out.(4sz) <- o4));

  with w. assert (A.pts_to out w);
  assert (pure (Seq.length w == nl));
  assert (pure (Seq.index w 0 == w0 /\ Seq.index w 1 == w1 /\
                Seq.index w 2 == o2 /\ Seq.index w 3 == o3 /\
                Seq.index w 4 == o4));
  assert (pure (Seq.length (fmul_spec (vals va) (vals vb)) == nl));
  assert (pure (Seq.index (fmul_spec (vals va) (vals vb)) 0 == S64.v w0));
  assert (pure (Seq.index (fmul_spec (vals va) (vals vb)) 1 == S64.v w1));
  assert (pure (Seq.index (fmul_spec (vals va) (vals vb)) 2 == S64.v o2));
  assert (pure (Seq.index (fmul_spec (vals va) (vals vb)) 3 == S64.v o3));
  assert (pure (Seq.index (fmul_spec (vals va) (vals vb)) 4 == S64.v o4));
  Cols.five_eq (vals w) (fmul_spec (vals va) (vals vb));
  fmul_spec_ok (vals va) (vals vb);
  ()
}

#pop-options

(** {2 Squaring}

    A square is a product whose two factors are the same, and the
    schoolbook product of a sequence with itself is symmetric: [a_i * a_j]
    and [a_j * a_i] land in the same column.  Pairing them up front and
    carrying the factor of two in the {e word} -- where it costs one
    addition -- leaves three limb products to a column instead of five,
    with the diagonal term standing alone in columns zero, two and four.
    Fifteen multiplications, not twenty-five.

    Nothing else changes.  [Spec.Curve25519.Columns.sq0] to [sq4] say the
    three-product columns are the same five numbers as [fmul]'s
    five-product ones, so the carry chain, the wrap and {!Cols.chain} are
    reused letter for letter, and the postcondition is [fmul] applied
    twice to the same argument -- which is what every caller wanted when
    it copied an array and called {!fmul}.

    The six scaled words are [2 a0], [2 a1], [38 a2], [19 a3], [19 a4] and
    [38 a4]; [38 * lim] is still under [2^64], so they are words.  The
    heaviest column is the zeroth, at [(1 + 38 + 38) * lim^2]: well inside
    the [95 * lim^2] that {!chi} and {!cadd} were proved against, so the
    carry stays a word too. *)

(** A limb product against a scaled limb: [k] times the plain bound. *)
let mulb (k: pos) (x y: nat)
  : Lemma (requires x <= k * lim /\ y <= lim)
          (ensures x * y <= k * (lim * lim))
  = Math.lemma_mult_le_left x y lim;
    Math.lemma_mult_le_right lim x (k * lim);
    Math.paren_mul_right k lim lim

inline_for_extraction
let mw1 (x y: S64.t)
  : Pure S128.t (requires S64.v x <= lim /\ S64.v y <= lim)
                (ensures fun z -> S128.v z == S64.v x * S64.v y /\
                                  S128.v z <= 1 * (lim * lim))
  = mulb 1 (S64.v x) (S64.v y); S128.mul_wide x y

inline_for_extraction
let mw2 (x y: S64.t)
  : Pure S128.t (requires S64.v x <= 2 * lim /\ S64.v y <= lim)
                (ensures fun z -> S128.v z == S64.v x * S64.v y /\
                                  S128.v z <= 2 * (lim * lim))
  = mulb 2 (S64.v x) (S64.v y); S128.mul_wide x y

inline_for_extraction
let mw19 (x y: S64.t)
  : Pure S128.t (requires S64.v x <= 19 * lim /\ S64.v y <= lim)
                (ensures fun z -> S128.v z == S64.v x * S64.v y /\
                                  S128.v z <= 19 * (lim * lim))
  = mulb 19 (S64.v x) (S64.v y); S128.mul_wide x y

inline_for_extraction
let mw38 (x y: S64.t)
  : Pure S128.t (requires S64.v x <= 38 * lim /\ S64.v y <= lim)
                (ensures fun z -> S128.v z == S64.v x * S64.v y /\
                                  S128.v z <= 38 * (lim * lim))
  = mulb 38 (S64.v x) (S64.v y); S128.mul_wide x y

(** Three products with multipliers summing to at most ninety-five stay
    inside a column. *)
let colb3 (i j k: pos) (x y z: nat)
  : Lemma (requires x <= i * (lim * lim) /\ y <= j * (lim * lim) /\
                    z <= k * (lim * lim) /\ i + j + k <= 95)
          (ensures x + y + z <= colb)
  = Math.distributivity_add_left i j (lim * lim);
    Math.distributivity_add_left (i + j) k (lim * lim);
    Math.lemma_mult_le_right (lim * lim) (i + j + k) 95;
    Math.paren_mul_right 5 19 (lim * lim)

(** The same from the word bounds, which is the form the call sites have. *)
let colw3 (i j k: pos) (x0 y0 x1 y1 x2 y2: nat)
  : Lemma (requires x0 <= i * lim /\ y0 <= lim /\ x1 <= j * lim /\ y1 <= lim /\
                    x2 <= k * lim /\ y2 <= lim /\ i + j + k <= 95)
          (ensures x0 * y0 + x1 * y1 + x2 * y2 <= colb)
  = mulb i x0 y0; mulb j x1 y1; mulb k x2 y2;
    colb3 i j k (x0 * y0) (x1 * y1) (x2 * y2)

(** One column of a square: three of those, summed left to right. *)
inline_for_extraction
let col3s (p0 p1 p2: S128.t)
  : Pure S128.t
         (requires S128.v p0 + S128.v p1 + S128.v p2 <= colb)
         (ensures fun z -> S128.v z == S128.v p0 + S128.v p1 + S128.v p2 /\
                           S128.v z <= colb)
  = assert_norm (colb < pow2 128);
    addd (addd p0 p1) p2

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

[@@ FStar.Attributes.CInline]
fn fsqr (out a: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == nl /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (felem (vals vout') /\
        fev (vals vout') == C.fmul (fev (vals va)) (fev (vals va)))
{
  A.pts_to_len out;
  A.pts_to_len a;
  assert_norm (nl == 5);
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let a4 = A.(a.(4sz));

  (* The six scaled limbs: the twos pair the off-diagonal products, the
     nineteens and thirty-eights fold the top of the column. *)
  assert_norm (38 * lim < pow2 64);
  let d0 = mulk 2uL a0;
  let d1 = mulk 2uL a1;
  let r2 = mulk 38uL a2;
  let r3 = mulk 19uL a3;
  let s4 = mulk 19uL a4;
  let r4 = mulk 38uL a4;

  colw3 1 38 38 (S64.v a0) (S64.v a0) (S64.v r4) (S64.v a1) (S64.v r2) (S64.v a3);
  let c0 = col3s (mw1 a0 a0) (mw38 r4 a1) (mw38 r2 a3);
  colw3 2 38 19 (S64.v d0) (S64.v a1) (S64.v r4) (S64.v a2) (S64.v r3) (S64.v a3);
  let c1 = col3s (mw2 d0 a1) (mw38 r4 a2) (mw19 r3 a3);
  colw3 2 1 38 (S64.v d0) (S64.v a2) (S64.v a1) (S64.v a1) (S64.v r4) (S64.v a3);
  let c2 = col3s (mw2 d0 a2) (mw1 a1 a1) (mw38 r4 a3);
  colw3 2 2 19 (S64.v d0) (S64.v a3) (S64.v d1) (S64.v a2) (S64.v s4) (S64.v a4);
  let c3 = col3s (mw2 d0 a3) (mw2 d1 a2) (mw19 s4 a4);
  colw3 2 2 1 (S64.v d0) (S64.v a4) (S64.v d1) (S64.v a3) (S64.v a2) (S64.v a2);
  let c4 = col3s (mw2 d0 a4) (mw2 d1 a3) (mw1 a2 a2);

  (* The same five columns as [fmul] on two copies of [a]. *)
  Cols.sq0 (vals va);
  Cols.sq1 (vals va);
  Cols.sq2 (vals va);
  Cols.sq3 (vals va);
  Cols.sq4 (vals va);
  assert (pure (Seq.length (fold19 (part (vals va) (vals va) nl)) == nl /\
                vat (fold19 (part (vals va) (vals va) nl)) 0 == S128.v c0 /\
                vat (fold19 (part (vals va) (vals va) nl)) 1 == S128.v c1 /\
                vat (fold19 (part (vals va) (vals va) nl)) 2 == S128.v c2 /\
                vat (fold19 (part (vals va) (vals va) nl)) 3 == S128.v c3 /\
                vat (fold19 (part (vals va) (vals va) nl)) 4 == S128.v c4));

  (* From here on, letter for letter the end of [fmul]. *)
  let o0 = lo51d c0;
  let k0 = chi c0;
  let l1 = cadd c1 k0;
  let o1 = lo51d l1;
  let k1 = chi l1;
  let l2 = cadd c2 k1;
  let o2 = lo51d l2;
  let k2 = chi l2;
  let l3 = cadd c3 k2;
  let o3 = lo51d l3;
  let k3 = chi l3;
  let l4 = cadd c4 k3;
  let o4 = lo51d l4;
  let k4 = chi l4;

  assert_norm (19 * carb < pow2 64);
  assert_norm (base + 19 * carb < pow2 64);
  let t0 = addw o0 (mulk 19uL k4);
  let w0 = lo51 t0;
  let w1 = addw o1 (hi51 t0);

  Cols.chain (fold19 (part (vals va) (vals va) nl));

  A.((out.(0sz) <- w0));
  A.((out.(1sz) <- w1));
  A.((out.(2sz) <- o2));
  A.((out.(3sz) <- o3));
  A.((out.(4sz) <- o4));

  with w. assert (A.pts_to out w);
  assert (pure (Seq.length w == nl));
  assert (pure (Seq.index w 0 == w0 /\ Seq.index w 1 == w1 /\
                Seq.index w 2 == o2 /\ Seq.index w 3 == o3 /\
                Seq.index w 4 == o4));
  assert (pure (Seq.length (fmul_spec (vals va) (vals va)) == nl));
  assert (pure (Seq.index (fmul_spec (vals va) (vals va)) 0 == S64.v w0));
  assert (pure (Seq.index (fmul_spec (vals va) (vals va)) 1 == S64.v w1));
  assert (pure (Seq.index (fmul_spec (vals va) (vals va)) 2 == S64.v o2));
  assert (pure (Seq.index (fmul_spec (vals va) (vals va)) 3 == S64.v o3));
  assert (pure (Seq.index (fmul_spec (vals va) (vals va)) 4 == S64.v o4));
  Cols.five_eq (vals w) (fmul_spec (vals va) (vals va));
  fmul_spec_ok (vals va) (vals va);
  ()
}

#pop-options

(** {2 Bytes}

    A fifty-one-bit limb is not a whole number of bytes, so neither
    direction touches bytes and limbs at the same time.  Loading decodes
    the thirty-two-bit representation, whose byte layer is proved in
    [Spec.Bignum256], clears bit [255] there, and then reads the five
    fifty-one-bit limbs off it as bit windows.  Storing runs the same
    repacking the other way and hands eight thirty-two-bit limbs to the
    same byte layer. *)

#push-options "--z3rlimit 300"

(** Adding two windows and keeping [w] bits: the machine wraps at [2^64]
    and the mask throws the wrap away. *)
let win_mod (a b: nat) (w: nat { w <= 64 })
  : Lemma (((a + b % pow2 64) % pow2 64) % pow2 w == (a + b) % pow2 w)
  = Math.lemma_mod_plus_distr_r a b (pow2 64);
    Math.pow2_modulo_modulo_lemma_1 (a + b) w 64

let win_mod3 (a b c: nat) (w: nat { w <= 64 })
  : Lemma ((((a + b % pow2 64) % pow2 64 + c % pow2 64) % pow2 64) % pow2 w ==
           (a + b + c) % pow2 w)
  = Math.lemma_mod_plus_distr_r a b (pow2 64);
    Math.lemma_mod_plus_distr_l (a + b) (c % pow2 64) (pow2 64);
    Math.lemma_mod_plus_distr_r (a + b) c (pow2 64);
    Math.pow2_modulo_modulo_lemma_1 (a + b + c) w 64

(** A window that spans two limbs, kept to fifty-one bits. *)
inline_for_extraction
let win2_51 (x y: S64.t) (s1 s2: U32.t { U32.v s1 < 64 /\ U32.v s2 < 64 })
  : r: S64.t { S64.v r == (S64.v x / pow2 (U32.v s1) +
                           pow2 (U32.v s2) * S64.v y) % pow2 51 }
  = let p = S64.shift_right x s1 in
    let q = S64.shift_left y s2 in
    let u = S64.add_mod p q in
    Math.swap_mul (S64.v y) (pow2 (U32.v s2));
    win_mod (S64.v x / pow2 (U32.v s1)) (pow2 (U32.v s2) * S64.v y) 51;
    UInt.logand_mask #64 (S64.v u) 51;
    assert_norm (base - 1 == pow2 51 - 1);
    S64.logand u mask51

(** A window that spans three, kept to fifty-one bits. *)
inline_for_extraction
let win3_51 (x y z: S64.t) (s1 s2 s3: U32.t { U32.v s1 < 64 /\ U32.v s2 < 64 /\ U32.v s3 < 64 })
  : r: S64.t { S64.v r == (S64.v x / pow2 (U32.v s1) +
                           pow2 (U32.v s2) * S64.v y +
                           pow2 (U32.v s3) * S64.v z) % pow2 51 }
  = let p = S64.shift_right x s1 in
    let q = S64.shift_left y s2 in
    let r = S64.shift_left z s3 in
    let u = S64.add_mod (S64.add_mod p q) r in
    Math.swap_mul (S64.v y) (pow2 (U32.v s2));
    Math.swap_mul (S64.v z) (pow2 (U32.v s3));
    win_mod3 (S64.v x / pow2 (U32.v s1)) (pow2 (U32.v s2) * S64.v y)
             (pow2 (U32.v s3) * S64.v z) 51;
    UInt.logand_mask #64 (S64.v u) 51;
    assert_norm (base - 1 == pow2 51 - 1);
    S64.logand u mask51

(** The same, kept to thirty-two. *)
inline_for_extraction
let win2_32 (x y: S64.t) (s1 s2: U32.t { U32.v s1 < 64 /\ U32.v s2 < 64 })
  : r: S64.t { S64.v r == (S64.v x / pow2 (U32.v s1) +
                           pow2 (U32.v s2) * S64.v y) % pow2 32 }
  = let p = S64.shift_right x s1 in
    let q = S64.shift_left y s2 in
    let u = S64.add_mod p q in
    Math.swap_mul (S64.v y) (pow2 (U32.v s2));
    win_mod (S64.v x / pow2 (U32.v s1)) (pow2 (U32.v s2) * S64.v y) 32;
    UInt.logand_mask #64 (S64.v u) 32;
    S64.logand u mask32

(** The thirty-two-bit half of a load: eight little-endian four-byte limbs,
    with bit [255] cleared. *)
fn load32 (u: A.array S64.t) (b: A.array S8.t)
          (#vu: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to u vu ** A.pts_to b #pb vb **
  pure (Seq.length vu == 8 /\ Seq.length vb == 32)
ensures exists* (vu': Seq.seq S64.t).
  A.pts_to u vu' ** A.pts_to b #pb vb **
  pure (Seq.length vu' == 8 /\ B32.bnd (vals vu') B32.base /\
        B32.eval (vals vu') == le_nat vb % pow2 255)
{
  A.pts_to_len u;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to u v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == 8 /\
          (forall (k: nat). k < SZ.v vi ==>
             S64.v (Seq.index v k) ==
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
    A.((u.(vi) <- w));
    i := SZ.add vi 1sz;
  };
  with g. assert (A.pts_to u g);
  B32.eval_bytes vb (vals g);
  assert_norm ((pow2 8 - 1) + 256 * (pow2 8 - 1) +
               65536 * (pow2 8 - 1) + 16777216 * (pow2 8 - 1) < B32.base);
  assert (pure (B32.bnd (vals g) B32.base /\ B32.eval (vals g) == le_nat vb));
  let t7 = A.(u.(7sz));
  let m7 = lo31 t7;
  A.((u.(7sz) <- m7));
  with h. assert (A.pts_to u h);
  vals_upd g 7 m7;
  assert (pure (vals h == mask255_32 (vals g)));
  mask255_32_ok (vals g);
  assert (pure (B32.eval (vals h) == B32.eval (vals g) % pow2 255));
  assert (pure (B32.eval (vals h) == le_nat vb % pow2 255));
}

(** The thirty-two-bit half of a store. *)
fn store32 (b: A.array S8.t) (u: A.array S64.t)
           (#vb: erased (Seq.seq S8.t)) (#pu: perm) (#vu: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to u #pu vu **
  pure (Seq.length vb == 32 /\ Seq.length vu == 8 /\ B32.bnd (vals vu) B32.base)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to u #pu vu **
  pure (vb' == nat_to_le 32 (B32.eval (vals vu)))
{
  A.pts_to_len b;
  A.pts_to_len u;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to u #pu vu **
    pure (SZ.v vi <= 8 /\ Seq.length v == 32 /\
          (forall (k: nat). k < SZ.v vi ==>
             S8.v (Seq.index v (4 * k)) == Seq.index (vals vu) k % 256 /\
             S8.v (Seq.index v (4 * k + 1)) == Seq.index (vals vu) k / 256 % 256 /\
             S8.v (Seq.index v (4 * k + 2)) == Seq.index (vals vu) k / 65536 % 256 /\
             S8.v (Seq.index v (4 * k + 3)) == Seq.index (vals vu) k / 16777216 % 256))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(u.(vi));
    let o = SZ.mul vi 4sz;
    pow2_bytes ();
    A.((b.(o) <- Cast.u64_to_u8 x));
    A.((b.(SZ.add o 1sz) <- Cast.u64_to_u8 (S64.shift_right x 8ul)));
    A.((b.(SZ.add o 2sz) <- Cast.u64_to_u8 (S64.shift_right x 16ul)));
    A.((b.(SZ.add o 3sz) <- Cast.u64_to_u8 (S64.shift_right x 24ul)));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  assert (pure (Seq.length v == 32 /\ B32.bnd (vals vu) B32.base));
  assert (pure (forall (k: nat). k < 8 ==>
                  S8.v (Seq.index v (4 * k)) == Seq.index (vals vu) k % 256 /\
                  S8.v (Seq.index v (4 * k + 1)) == Seq.index (vals vu) k / 256 % 256 /\
                  S8.v (Seq.index v (4 * k + 2)) == Seq.index (vals vu) k / 65536 % 256 /\
                  S8.v (Seq.index v (4 * k + 3)) == Seq.index (vals vu) k / 16777216 % 256));
  B32.store_digits (vals vu) v;
  assert (pure (v == nat_to_le 32 (B32.eval (vals vu))));
}

(** Loading: decode to thirty-two-bit limbs, then read the five fifty-one-bit
    limbs off them as bit windows.  The five offsets are [(0,0)], [(1,19)],
    [(3,6)], [(4,25)] and [(6,12)] -- limb and bit within it -- and the two
    that straddle three thirty-two-bit limbs are the ones whose offset plus
    fifty-one exceeds sixty-four. *)
fn load (a: A.array S64.t) (b: A.array S8.t)
        (#va: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == 32)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b #pb vb **
  pure (Seq.length va' == nl /\ bnd (vals va') base /\
        eval (vals va') == le_nat vb % pow2 255)
{
  A.pts_to_len a;
  A.pts_to_len b;
  let zz = S64.zero;
  let mut u = [| zz; 8sz |];
  Mem.track u;
  A.pts_to_len u;
  load32 u b;
  with h. assert (A.pts_to u h);
  A.pts_to_len u;
  let u0 = A.(u.(0sz));
  let u1 = A.(u.(1sz));
  let u2 = A.(u.(2sz));
  let u3 = A.(u.(3sz));
  let u4 = A.(u.(4sz));
  let u5 = A.(u.(5sz));
  let u6 = A.(u.(6sz));
  let u7 = A.(u.(7sz));
  let a0 = win2_51 u0 u1 0ul 32ul;
  let a1 = win3_51 u1 u2 u3 19ul 13ul 45ul;
  let a2 = win2_51 u3 u4 6ul 26ul;
  let a3 = win3_51 u4 u5 u6 25ul 7ul 39ul;
  let a4 = win2_51 u6 u7 12ul 20ul;
  A.((a.(0sz) <- a0));
  A.((a.(1sz) <- a1));
  A.((a.(2sz) <- a2));
  A.((a.(3sz) <- a3));
  A.((a.(4sz) <- a4));
  with s. assert (A.pts_to a s);
  R.load_windows (vals h) (vals s);
  assert (pure (B32.eval (vals h) == le_nat vb % pow2 255));
  Math.pow2_lt_compat 256 255;
  load_ok (B32.eval (vals h)) (vals s);
  assert (pure (eval (vals s) == le_nat vb % pow2 255 /\ bnd (vals s) base));
  Mem.wipe u 8sz;
}

(** Storing: the same repacking the other way.  The eight offsets into the
    fifty-one-bit limbs are [(0,0)], [(0,32)], [(1,13)], [(1,45)], [(2,26)],
    [(3,7)], [(3,39)] and [(4,20)]; a thirty-two-bit window never needs a
    third limb. *)
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
  let zz = S64.zero;
  let mut u = [| zz; 8sz |];
  Mem.track u;
  A.pts_to_len u;
  let s0 = A.(a.(0sz));
  let s1 = A.(a.(1sz));
  let s2 = A.(a.(2sz));
  let s3 = A.(a.(3sz));
  let s4 = A.(a.(4sz));
  let c0 = win2_32 s0 s1 0ul 51ul;
  let c1 = win2_32 s0 s1 32ul 19ul;
  let c2 = win2_32 s1 s2 13ul 38ul;
  let c3 = win2_32 s1 s2 45ul 6ul;
  let c4 = win2_32 s2 s3 26ul 25ul;
  let c5 = win2_32 s3 s4 7ul 44ul;
  let c6 = win2_32 s3 s4 39ul 12ul;
  let c7 = win2_32 s4 zz 20ul 31ul;
  A.((u.(0sz) <- c0));
  A.((u.(1sz) <- c1));
  A.((u.(2sz) <- c2));
  A.((u.(3sz) <- c3));
  A.((u.(4sz) <- c4));
  A.((u.(5sz) <- c5));
  A.((u.(6sz) <- c6));
  A.((u.(7sz) <- c7));
  eval_bnd (vals va);
  assert_norm (rad * nl == 255);
  Math.pow2_lt_compat 256 255;
  with g. assert (A.pts_to u g);
  R.store_windows (vals va) (vals g);
  store_ok (eval (vals va)) (vals g);
  store32 b u;
  Mem.wipe u 8sz;
}

#pop-options

(** {2 Freezing}

    The unique representative below the prime.  Four carry passes bring the
    limbs into base [2^51], at which point the value is below [2^255]
    because [nl * rad] is [255]; then adding nineteen and carrying decides
    the single conditional subtraction, since the carry out of the top limb
    is one exactly when the value had reached the prime. *)

#push-options "--z3rlimit 300"

(** Four passes, and then the number is a genuine base-[2^51] one. *)
fn narrow (a: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == nl /\ felem (vals va))
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == nl /\ vals va' == freeze_a (vals va))
{
  freeze_a_bounds (vals va);
  assert_norm (lim + 2 < base * 3);
  assert_norm (lim + 2 < pow2 64);
  assert_norm (base + 19 * 2 < pow2 64);
  carry_chain a lim 2;
  with x1. assert (A.pts_to a x1);
  assert (pure (vals x1 == carry_pass (vals va)));
  assert_norm (base + 37 + 1 < base * 2);
  assert_norm (base + 37 + 1 < pow2 64);
  assert_norm (base + 19 * 1 < pow2 64);
  carry_chain a (base + 37) 1;
  with x2. assert (A.pts_to a x2);
  assert (pure (vals x2 == carry_pass (carry_pass (vals va))));
  assert_norm (base + 18 + 1 < base * 2);
  assert_norm (base + 18 + 1 < pow2 64);
  carry_chain a (base + 18) 1;
  with x3. assert (A.pts_to a x3);
  assert (pure (vals x3 == carry_pass (carry_pass (carry_pass (vals va)))));
  carry_chain a (base + 18) 1;
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
  with y. assert (A.pts_to a y);
  freeze_a_ok (vals va);
  assert (pure (vals y == freeze_a (vals va)));
  assert (pure (bnd (vals y) base /\ eval (vals y) < pow2 255));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a y ** A.pts_to t v **
    pure (SZ.v vi <= 5 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index y k))
  decreases (5 - SZ.v (!i))
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
  let r = carry_out_op t (base + 18) 1;
  with w. assert (A.pts_to t w);
  freeze_step (vals y);
  assert (pure (vals w == freeze_w (vals y)));
  assert (pure (S64.v r == carry_out (add19 (vals y))));
  assert (pure (S64.v r <= 1));
  let sel = S64.eq_mask r (S64.classify 1uL);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 5sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S64.t).
    pts_to j vj ** A.pts_to a v ** A.pts_to t w **
    pure (SZ.v vj <= 5 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index v k ==
               (if carry_out (add19 (vals y)) = 1 then Seq.index w k else Seq.index y k)) /\
          (forall (k: nat). SZ.v vj <= k /\ k < nl ==> Seq.index v k == Seq.index y k))
  decreases (5 - SZ.v (!j))
  {
    let vj = !j;
    let x = A.(t.(vj));
    let uu = A.(a.(vj));
    A.((a.(vj) <- S64.select sel x uu));
    j := SZ.add vj 1sz;
  };
  with res. assert (A.pts_to a res);
  freeze_spec_ok (vals va);
  assert (pure (vals res `Seq.equal` freeze_spec (vals va)));
}

#pop-options

(** {2 Conditional swap}

    The ladder's only data-dependent choice, made with a mask. *)

#push-options "--z3rlimit 120"

[@@ FStar.Attributes.CInline]
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
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (x: Seq.seq S64.t) (y: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a x ** A.pts_to b y **
    pure (SZ.v vi <= 5 /\ Seq.length x == nl /\ Seq.length y == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index x k == (if S64.v sel = 0 then Seq.index va k else Seq.index vb k) /\
             Seq.index y k == (if S64.v sel = 0 then Seq.index vb k else Seq.index va k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < nl ==>
             Seq.index x k == Seq.index va k /\ Seq.index y k == Seq.index vb k))
  decreases (5 - SZ.v (!i))
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
[@@ FStar.Attributes.CInline]
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
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #ps vs **
    pure (SZ.v vi <= 5 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index vs k))
  decreases (5 - SZ.v (!i))
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
