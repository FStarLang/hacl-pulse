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

(** Thirty-two-bit limbs in sixty-four-bit secret words.

    [Spec.Bignum256] says what a sequence of limbs means; this module is the
    small machine layer underneath it, shared by everything that uses that
    representation.  There is nothing modulus-specific here and nothing
    curve-specific: a word is a [uint64] holding a value that the caller has
    bounded, a limb is one of those under [2^32], and the loops are the
    carry pass -- with and without its carry out, over words and over the
    wide columns of a product -- and the schoolbook multiplier.

    {b Why thirty-two bits.}  Custard now emits [unsigned __int128], so a
    limb product of two thirty-two-bit limbs has somewhere to go: eight
    limbs of thirty-two bits multiply in sixty-four word multiplies rather
    than the two hundred and fifty-six that sixteen-bit limbs needed.
    Thirty-two is also the largest radix that keeps a limb a whole number
    of bytes and a column of [nl] products inside a hundred-and-twenty-eight
    bit integer with room for the Montgomery reduction on top.

    {b Two widths.}  Limbs live in [uint64]: a proper limb is under [2^32],
    and the lazy sums an addition or a subtraction produces stay far below
    [2^64], so those loops never need the wide type.  Only the columns of a
    product do, and they get their own view ({!vals128}) and their own
    carry pass ({!carry_run128_op}).

    Every operation below is a sixty-four- or hundred-and-twenty-eight-bit
    add, subtract, multiply, shift, mask or select on secret integers.
    Nothing branches on a secret.

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

    Each is the [uint64] instruction plus the argument that it did not wrap.
    Keeping them here means the modular-arithmetic side condition is
    discharged once, against a two-line context, rather than inside a loop
    body that also carries the heap. *)

inline_for_extraction
let mask32 : m: S64.t { S64.v m == base - 1 } =
  assert_norm (base - 1 == 0xffffffff);
  S64.classify 0xffffffffuL

inline_for_extraction
let lo32 (x: S64.t) : r: S64.t { S64.v r == S64.v x % base } =
  UInt.logand_mask #64 (S64.v x) 32;
  S64.logand x mask32

inline_for_extraction
let hi32 (x: S64.t) : r: S64.t { S64.v r == S64.v x / base } =
  S64.shift_right x 32ul

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

(** {2 The wide operations}

    The same four, one width up.  [Hacl.Secret.UInt128] offers the widening
    multiply and nothing else that is needed here: a column is built by
    [mul_wide] and [addd], and taken apart again by [lo32d] and [hi32d]. *)

inline_for_extraction
let addd (x y: S128.t)
  : Pure S128.t (requires S128.v x + S128.v y < pow2 128)
                (ensures fun z -> S128.v z == S128.v x + S128.v y)
  = Math.small_mod (S128.v x + S128.v y) (pow2 128);
    S128.add_mod x y

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

(** The digit of a wide column, modulo the radix: only the bottom limb of
    the column takes part, which is what keeps this a word multiply. *)
let mod_mul_lo (a mu: nat)
  : Lemma ((a * mu) % base == ((a % base) * mu) % base)
  = Math.lemma_mod_mul_distr_l a mu base

(** {2 The carry pass}

    Limbs [0] to [nl - 2] carry into their neighbour and the top limb keeps
    its low thirty-two bits.  [c] bounds the limbs on entry and [d] the carry; the
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
    let lo = lo32 t;
    let up = addw u (hi32 t);
    A.((a.(vk) <- lo));
    A.((a.(SZ.add vk 1sz) <- up));
    vals_upd v (SZ.v vk) lo;
    vals_upd (Seq.upd v (SZ.v vk) lo) (SZ.v vk + 1) up;
    Loops.unfold_repeati (SZ.v vk) carry_step (vals va);
    k := SZ.add vk 1sz;
  };
  ()
}

(** Eight limbs: the pass, then the top limb's overflow, returned. *)
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
  carry_run_op a 7sz c d;
  with v. assert (A.pts_to a v);
  carry_run_chained (vals va) c d 7;
  carry_run_len (vals va) 7;
  let t = A.(a.(7sz));
  let lo = lo32 t;
  let hi = hi32 t;
  A.((a.(7sz) <- lo));
  vals_upd v 7 lo;
  assert (pure (vals (Seq.upd v 7 lo) == carry_low (vals va)));
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

(** The same pass one width up, over the wide columns the reduction leaves
    behind.  It is stated over any length and any number of steps, so the
    caller can use it both for a full [carry_low] and for
    [Spec.Field256.normalize], which runs [nl] steps over [nl + 1]
    columns. *)
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
    let lo = Cast.u64_to_u128 (lo32d t);
    let up = addd u (hi32d t);
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

    [nl * nl] limb products accumulated into [nw] lazy columns, no carries
    anywhere: [Spec.Bignum256.part] says exactly this, one row at a time,
    and the two loops here are its two indices.  Column [i + j] can receive
    at most [nl] products of two limbs, so the caller's bound
    [nl * lim^2 + lim^2 < 2^128] is what keeps a column inside a wide word.

    Deferring every carry to a single pass afterwards is what the wide
    column buys: with [lim = 2^32 - 1] a column is under [2^67], leaving
    sixty-one bits of headroom -- far more than the Montgomery reduction
    that runs on top of it will ever use. *)

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

fn mul_columns (t: A.array S128.t) (a b: A.array S64.t) (lim: erased nat)
               (#vt: erased (Seq.seq S128.t))
               (#pa: perm) (#va: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == nw /\ Seq.length va == nl /\ Seq.length vb == nl /\
        ble (vals va) lim /\ ble (vals vb) lim /\
        nl * (reveal lim * reveal lim) + reveal lim * reveal lim < pow2 128)
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == nw /\ ble (vals128 vt') (nl * (reveal lim * reveal lim)) /\
        vals128 vt' == part (vals va) (vals vb) nl)
{
  A.pts_to_len t;
  A.pts_to_len a;
  A.pts_to_len b;
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
            vals128 v == addw (part (vals va) (vals vb) (SZ.v vi))
                              (rowj (vals va) (vals vb) (SZ.v vi) (SZ.v vj)))
    decreases (8 - SZ.v (!j))
    {
      with v. assert (A.pts_to t v);
      let vj = !j;
      acc_ble (vals va) (vals vb) (vals128 v) lim (SZ.v vi) (SZ.v vj);
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
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               (if S64.v m = 0 then Seq.index (vals va) k else Seq.index (vals vb) k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < nl ==>
             Seq.index (vals v) k == Seq.index (vals va) k))
  decreases (8 - SZ.v (!i))
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
