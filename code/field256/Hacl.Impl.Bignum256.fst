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

(** Montgomery arithmetic modulo a generic 256-bit modulus.

    [Spec.Field256] says what the four operations are; this module runs
    them.  Everything is parameterised by the modulus bundle, which arrives
    as two eight-limb slices -- the modulus [ms] and its two's complement
    [nm] -- and one word [mu].  P-256 has two such bundles, the field prime
    and the group order, and both go through the same code.

    {b Shape of the workspace.}  Nothing here allocates.  A multiplication
    needs fifteen wide columns for the schoolbook product, seventeen for
    the reduction to run in, nine for the normalisation that follows it,
    and eight words for the conditional subtraction to keep its second
    candidate; an addition or a subtraction needs only the last of those
    four.  They are passed in, and {!Hacl.P256.Field} and {!Hacl.K256.Field}
    is where they acquire names.

    {b Two widths.}  The product and the reduction run on
    hundred-and-twenty-eight-bit columns, because a column holds eight
    products of thirty-two-bit limbs and the reduction adds eight more
    multiples of the modulus on top.  Everything else -- the additions, the
    conditional subtractions, the byte conversions -- stays in words.

    {b Constant time.}  The only decisions are on loop counters.  The
    conditional subtractions compare with [gte_mask] and commit with
    [Hacl.Impl.Limb.cselect]; no secret ever reaches an [if]. *)
module Hacl.Impl.Bignum256

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.Montgomery256
open Spec.Field256
open Hacl.Impl.Limb
open Hacl.Spec.Bytes

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Cast = Hacl.Secret.Cast
module Loops = Hacl.Spec.Loops

(** This module is arithmetic-heavy, and the default SMT encoding boxes
    every integer operation, which hides the structure of the products from
    Z3's arithmetic solver.  Encoding linear arithmetic natively and leaving
    only the nonlinear operators wrapped is measurably faster here. *)
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 One Montgomery step}

    [Spec.Montgomery256.mstep] adds [u * m] at limb [i] and then carries
    limb [i] into its neighbour, where [u] is the digit that makes limb [i]
    vanish.  The inner loop adds one product at a time, so it needs the
    partial row: [mrow t ms u i j] is [t] plus [u] times the first [j]
    limbs of the modulus, placed at offset [i]. *)

let mrow (t ms: Seq.seq nat) (u: nat) (i: nat) (j: nat { j <= Seq.length ms })
  : Seq.seq nat
  = addw t (emb (Seq.length t) i (scale u (Seq.slice ms 0 j)))

let mrow_len (t ms: Seq.seq nat) (u: nat) (i: nat) (j: nat { j <= Seq.length ms })
  : Lemma (Seq.length (mrow t ms u i j) == Seq.length t) = ()

let mrow_zero (t ms: Seq.seq nat) (u: nat) (i: nat)
  : Lemma (mrow t ms u i 0 == t)
  = Seq.lemma_eq_intro (mrow t ms u i 0) t

let mrow_full (t ms: Seq.seq nat) (u: nat) (i: nat)
  : Lemma (mrow t ms u i (Seq.length ms) ==
           addw t (emb (Seq.length t) i (scale u ms)))
  = Seq.lemma_eq_intro (Seq.slice ms 0 (Seq.length ms)) ms

(** Adding the [j]-th product is an update of column [i + j], because that
    column has not been touched yet. *)
let mrow_step (t ms: Seq.seq nat) (u: nat) (i: nat) (j: nat { j < Seq.length ms })
  : Lemma (requires i + Seq.length ms <= Seq.length t)
          (ensures mrow t ms u i (j + 1) ==
                   Seq.upd (mrow t ms u i j) (i + j)
                           (Seq.index t (i + j) + u * Seq.index ms j))
  = Seq.lemma_eq_intro (mrow t ms u i (j + 1))
      (Seq.upd (mrow t ms u i j) (i + j)
               (Seq.index t (i + j) + u * Seq.index ms j))

let mrow_ble (t ms: Seq.seq nat) (u: nat) (i: nat) (j: nat { j <= Seq.length ms })
             (c: nat)
  : Lemma (requires ble t c /\ u < base /\ ble ms (base - 1))
          (ensures ble (mrow t ms u i j) (c + (base - 1) * (base - 1)))
  = let p = Seq.slice ms 0 j in
    assert (ble p (base - 1));
    scale_ble u p (base - 1);
    Math.lemma_mult_le_right (base - 1) u (base - 1);
    emb_ble (Seq.length t) i (scale u p) (u * (base - 1));
    addw_ble t (emb (Seq.length t) i (scale u p)) c ((base - 1) * (base - 1))

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn mstep_op (t: A.array S128.t) (ms: A.array S64.t) (mu: S64.t) (i: SZ.t) (c: erased nat)
            (#vt: erased (Seq.seq S128.t))
            (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to ms #pm vms **
  pure (Seq.length vms == nl /\ SZ.v i + nl <= Seq.length vt /\
        mont_ok (vals vms) (S64.v mu) /\ ble (vals128 vt) c /\ c <= pow2 72)
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to ms #pm vms **
  pure (Seq.length vt' == Seq.length vt /\
        vals128 vt' == mstep (vals vms) (S64.v mu) (SZ.v i) (vals128 vt))
{
  A.pts_to_len t;
  A.pts_to_len ms;
  assert_norm ((base - 1) * (base - 1) < pow2 64);
  assert_norm (pow2 72 + pow2 64 < pow2 128);
  assert_norm (pow2 72 + pow2 64 + pow2 72 < pow2 128);
  let ti = A.(t.(i));
  let tl = lo32d ti;
  Math.lemma_mult_le_left (S64.v tl) (S64.v mu) (base - 1);
  Math.lemma_mult_le_right (base - 1) (S64.v tl) (base - 1);
  mod_mul_lo (S128.v ti) (S64.v mu);
  let u = lo32 (mulw tl mu);
  mrow_zero (vals128 vt) (vals vms) (S64.v u) (SZ.v i);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 8sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S128.t).
    pts_to j vj ** A.pts_to t v ** A.pts_to ms #pm vms **
    pure (SZ.v vj <= 8 /\ Seq.length v == Seq.length vt /\
          vals128 v == mrow (vals128 vt) (vals vms) (S64.v u) (SZ.v i) (SZ.v vj))
  decreases (8 - SZ.v (!j))
  {
    with v. assert (A.pts_to t v);
    let vj = !j;
    mrow_ble (vals128 vt) (vals vms) (S64.v u) (SZ.v i) (SZ.v vj) c;
    let msj = A.(ms.(vj));
    let pos = SZ.add i vj;
    let cur = A.(t.(pos));
    Math.lemma_mult_le_right (S64.v msj) (S64.v u) (base - 1);
    Math.lemma_mult_le_left (base - 1) (S64.v msj) (base - 1);
    let nv = addd cur (S128.mul_wide u msj);
    A.((t.(pos) <- nv));
    vals128_upd v (SZ.v i + SZ.v vj) nv;
    mrow_step (vals128 vt) (vals vms) (S64.v u) (SZ.v i) (SZ.v vj);
    j := SZ.add vj 1sz;
  };
  mrow_full (vals128 vt) (vals vms) (S64.v u) (SZ.v i);
  with v. assert (A.pts_to t v);
  assert (pure (vals128 v == addw (vals128 vt)
                                  (emb (Seq.length vt) (SZ.v i)
                                       (scale (S64.v u) (vals vms)))));
  mrow_ble (vals128 vt) (vals vms) (S64.v u) (SZ.v i) nl c;
  let x = A.(t.(i));
  let lo = Cast.u64_to_u128 (lo32d x);
  let hi = hi32d x;
  A.((t.(i) <- lo));
  vals128_upd v (SZ.v i) lo;
  with v1. assert (A.pts_to t v1);
  let ip = SZ.add i 1sz;
  let y = A.(t.(ip));
  let up = addd y hi;
  A.((t.(ip) <- up));
  vals128_upd v1 (SZ.v i + 1) up;
  ()
}

#pop-options

(** {2 The eight steps}

    Each step raises a column by less than [2^65], so a product's [2^67]
    reaches at most [2^69] and stays inside a wide word with room to
    spare. *)

(** The exit of the loop in [mreduce_op]: the counter is [nl]. *)
let mreduce_fin (v t ms: Seq.seq nat) (mu: nat) (c: nat) (k: nat)
  : Lemma (requires k == nl /\ v == mrun ms mu k t /\ ble v (c + k * pow2 65))
          (ensures v == mrun ms mu nl t /\ ble v (c + nl * pow2 65))
  = ()

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn mreduce_op (t: A.array S128.t) (ms: A.array S64.t) (mu: S64.t) (c: erased nat)
              (#vt: erased (Seq.seq S128.t))
              (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to ms #pm vms **
  pure (Seq.length vms == nl /\ Seq.length vt == ncol /\
        mont_ok (vals vms) (S64.v mu) /\ ble (vals128 vt) c /\
        reveal c + nl * pow2 65 <= pow2 72)
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to ms #pm vms **
  pure (Seq.length vt' == ncol /\
        ble (vals128 vt') (reveal c + nl * pow2 65) /\
        vals128 vt' == mrun (vals vms) (S64.v mu) nl (vals128 vt))
{
  A.pts_to_len t;
  A.pts_to_len ms;
  Loops.repeati_zero (mstep (vals vms) (S64.v mu)) (vals128 vt);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 8sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to t v ** A.pts_to ms #pm vms **
    pure (SZ.v vk <= 8 /\ Seq.length v == ncol /\
          vals128 v == mrun (vals vms) (S64.v mu) (SZ.v vk) (vals128 vt) /\
          ble (vals128 v) (reveal c + SZ.v vk * pow2 65))
  decreases (8 - SZ.v (!k))
  {
    with v. assert (A.pts_to t v);
    let vk = !k;
    Math.lemma_mult_le_right (pow2 65) (SZ.v vk) nl;
    mstep_op t ms mu vk (reveal c + SZ.v vk * pow2 65);
    mstep_ble (vals vms) (S64.v mu) (SZ.v vk) (vals128 v) (reveal c + SZ.v vk * pow2 65);
    Loops.unfold_repeati (SZ.v vk) (mstep (vals vms) (S64.v mu)) (vals128 vt);
    Math.distributivity_add_left (SZ.v vk) 1 (pow2 65);
    k := SZ.add vk 1sz;
  };
  with vk v. assert (pts_to k vk ** A.pts_to t v);
  mreduce_fin (vals128 v) (vals128 vt) (vals vms) (S64.v mu) c (SZ.v vk);
  ()
}

#pop-options

(** {2 Loop steps}

    Each limb-wise loop below grows a prefix on which the buffer agrees with
    its target by one limb per pass.  Stating the pass once, at top level,
    keeps the quantifier out of the loop's own query. *)

let sum_step (v: Seq.seq S64.t) (x y: Seq.seq nat) (k: nat) (z: S64.t)
  : Lemma (requires Seq.length v == nl /\ k < nl /\
                    k < Seq.length x /\ k < Seq.length y /\
                    S64.v z == Seq.index x k + Seq.index y k /\
                    (forall (j: nat). j < k ==>
                       Seq.index (vals v) j == Seq.index x j + Seq.index y j))
          (ensures Seq.length (Seq.upd v k z) == nl /\
                   (forall (j: nat). j < k + 1 ==>
                      Seq.index (vals (Seq.upd v k z)) j == Seq.index x j + Seq.index y j))
  = vals_upd v k z

let copy128_step (v: Seq.seq S128.t) (n: nat) (w: Seq.seq nat) (o k: nat) (z: S128.t)
  : Lemma (requires Seq.length v == n /\ k < n /\ o + k < Seq.length w /\
                    S128.v z == Seq.index w (o + k) /\
                    (forall (j: nat). j < k ==> Seq.index (vals128 v) j == Seq.index w (o + j)))
          (ensures Seq.length (Seq.upd v k z) == n /\
                   (forall (j: nat). j < k + 1 ==>
                      Seq.index (vals128 (Seq.upd v k z)) j == Seq.index w (o + j)))
  = vals128_upd v k z

(** {2 The conditional subtraction}

    Add [2^256 - m] into the spare buffer.  The carry out of that addition,
    together with any carry the caller already had above bit 256, says
    whether the value was at least [m]; when it was, the spare buffer
    already holds the difference. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn csub_op (a s nm: A.array S64.t) (top: S64.t) (d: erased modulus)
           (#va: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to s vs ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length va == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        bnd (vals va) base /\ S64.v top <= 1 /\
        eval (vals va) + pow2 256 * S64.v top < 2 * d.m)
ensures exists* (va': Seq.seq S64.t) (vs': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to s vs' ** A.pts_to nm #pn vnm **
  pure (Seq.length va' == nl /\ Seq.length vs' == nl /\
        res d (vals va') /\ vals va' == csub d (vals va) (S64.v top))
{
  A.pts_to_len a;
  A.pts_to_len s;
  A.pts_to_len nm;
  assert_norm (2 * base < pow2 64);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a va ** A.pts_to s v ** A.pts_to nm #pn vnm **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vnm) k))
  decreases (8 - SZ.v (!i))
  {
    with v. assert (A.pts_to s v);
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(nm.(vi));
    A.((s.(vi) <- addw x y));
    vals_upd v (SZ.v vi) (addw x y);
    sum_step v (vals va) (vals vnm) (SZ.v vi) (addw x y);
    i := SZ.add vi 1sz;
    assert pure (SZ.v (SZ.add vi 1sz) == SZ.v vi + 1);
  };
  with v. assert (A.pts_to s v);
  addw_len (vals va) (vals vnm);
  assert (pure (vals v `Seq.equal` addw (vals va) (vals vnm)));
  addw_ble (vals va) (vals vnm) (base - 1) (base - 1);
  assert_norm (2 * (base - 1) + 1 < base * 2);
  assert_norm (2 * (base - 1) + 1 < pow2 64);
  carry_split_bnd (addw (vals va) (vals vnm)) (2 * (base - 1)) 1;
  let co = carry_out_op s (2 * (base - 1)) 1;
  let m = S64.gte_mask (addw top co) (S64.classify 1uL);
  cselect a s m;
  csub_ok d (vals va) (S64.v top);
  with va'. assert (A.pts_to a va');
  assert (pure (vals va' == csub d (vals va) (S64.v top)));
}

#pop-options

(** {2 Addition, subtraction, negation}

    Both operands are already below the modulus, so a sum is below twice it
    and one conditional subtraction is enough.  A difference is computed as
    a sum with the two's complement: the carry out is one exactly when the
    subtraction did not go negative, and when it did, adding the modulus
    back is the correction. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn madd_op (out a b s nm: A.array S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to a #pa va **
  A.pts_to b #pb vb ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to s vs' ** A.pts_to a #pa va **
  A.pts_to b #pb vb ** A.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        res d (vals vo') /\ vals vo' == madd d (vals va) (vals vb))
{
  A.pts_to_len out;
  A.pts_to_len s;
  A.pts_to_len nm;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (2 * base < pow2 64);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to s vs ** A.pts_to a #pa va **
    A.pts_to b #pb vb ** A.pts_to nm #pn vnm **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vb) k))
  decreases (8 - SZ.v (!i))
  {
    with v. assert (A.pts_to out v);
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((out.(vi) <- addw x y));
    vals_upd v (SZ.v vi) (addw x y);
    sum_step v (vals va) (vals vb) (SZ.v vi) (addw x y);
    i := SZ.add vi 1sz;
    assert pure (SZ.v (SZ.add vi 1sz) == SZ.v vi + 1);
  };
  with v. assert (A.pts_to out v);
  addw_len (vals va) (vals vb);
  assert (pure (vals v `Seq.equal` addw (vals va) (vals vb)));
  addw_ble (vals va) (vals vb) (base - 1) (base - 1);
  assert_norm (2 * (base - 1) + 1 < base * 2);
  assert_norm (2 * (base - 1) + 1 < pow2 64);
  let co = carry_out_op out (2 * (base - 1)) 1;
  carry_split_bnd (addw (vals va) (vals vb)) (2 * (base - 1)) 1;
  carry_split_ok (addw (vals va) (vals vb));
  carry_low_len (addw (vals va) (vals vb));
  eval_addw (vals va) (vals vb);
  csub_op out s nm co d;
  madd_ok d (vals va) (vals vb);
  with vo'. assert (A.pts_to out vo');
  assert (pure (vals vo' == madd d (vals va) (vals vb)));
}

#pop-options

(** {2 Subtraction}

    [a - b] is [a + (2^256 - b)], and the two's complement is built one
    limb at a time: every limb gets [2^32 - 1 - b_i], and limb zero gets the
    extra one.  The carry out of the sum is one exactly when [a >= b]. *)

let negw_shape (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl /\ bnd b base)
          (ensures Seq.length (compl b) == nl /\
                   addw a (negw b) ==
                     Seq.upd (addw a (compl b)) 0
                             (Seq.index a 0 + Seq.index (compl b) 0 + 1))
  = unit1_ok ();
    Seq.lemma_eq_intro (addw a (negw b))
      (Seq.upd (addw a (compl b)) 0
               (Seq.index a 0 + Seq.index (compl b) 0 + 1))

#push-options "--z3rlimit 300"

[@@ FStar.Attributes.CInline]
fn negsub_op (out a b: A.array S64.t)
             (#vo: erased (Seq.seq S64.t))
             (#pa: perm) (#va: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
returns co: S64.t
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo' == nl /\ bnd (vals vo') base /\
        vals vo' == carry_low (addw (vals va) (negw (vals vb))) /\
        S64.v co == carry_out (addw (vals va) (negw (vals vb))))
{
  A.pts_to_len out;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (2 * base < pow2 64);
  compl_ok (vals vb);
  let top = S64.classify 0xffffffffuL;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               Seq.index (vals va) k + Seq.index (compl (vals vb)) k))
  decreases (8 - SZ.v (!i))
  {
    with v. assert (A.pts_to out v);
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let nv = addw x (subw top y);
    A.((out.(vi) <- nv));
    vals_upd v (SZ.v vi) nv;
    sum_step v (vals va) (compl (vals vb)) (SZ.v vi) nv;
    i := SZ.add vi 1sz;
    assert pure (SZ.v (SZ.add vi 1sz) == SZ.v vi + 1);
  };
  with v. assert (A.pts_to out v);
  addw_len (vals va) (compl (vals vb));
  assert (pure (vals v `Seq.equal` addw (vals va) (compl (vals vb))));
  let x0 = A.(out.(0sz));
  let nv0 = addw x0 (S64.classify 1uL);
  A.((out.(0sz) <- nv0));
  vals_upd v 0 nv0;
  negw_shape (vals va) (vals vb);
  with v1. assert (A.pts_to out v1);
  assert (pure (vals v1 == addw (vals va) (negw (vals vb))));
  negw_ok (vals vb);
  addw_ble (vals va) (negw (vals vb)) (base - 1) base;
  assert_norm (base - 1 + base + 2 < base * 3);
  assert_norm (base - 1 + base + 2 < pow2 64);
  carry_split_bnd (addw (vals va) (negw (vals vb))) (base - 1 + base) 2;
  carry_low_len (addw (vals va) (negw (vals vb)));
  let co = carry_out_op out (base - 1 + base) 2;
  co
}

#pop-options

(** The correction, computed whether or not it is wanted: when the
    subtraction went negative, adding the modulus back and dropping the
    overflow is the answer. *)

#push-options "--z3rlimit 300"

[@@ FStar.Attributes.CInline]
fn addm_op (out s ms: A.array S64.t) (m: S64.t)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to ms #pm vms **
  pure (Seq.length vo == nl /\ Seq.length vs == nl /\ Seq.length vms == nl /\
        bnd (vals vo) base /\ bnd (vals vms) base /\
        (S64.v m == 0 \/ S64.v m == pow2 64 - 1))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to s vs' ** A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        vals vo' == (if S64.v m = 0 then vals vo
                     else carry_low (addw (vals vo) (vals vms))))
{
  A.pts_to_len out;
  A.pts_to_len s;
  A.pts_to_len ms;
  assert_norm (2 * base < pow2 64);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 8sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S64.t).
    pts_to j vj ** A.pts_to out vo ** A.pts_to s v ** A.pts_to ms #pm vms **
    pure (SZ.v vj <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index (vals v) k == Seq.index (vals vo) k + Seq.index (vals vms) k))
  decreases (8 - SZ.v (!j))
  {
    with v. assert (A.pts_to s v);
    let vj = !j;
    let x = A.(out.(vj));
    let y = A.(ms.(vj));
    A.((s.(vj) <- addw x y));
    vals_upd v (SZ.v vj) (addw x y);
    sum_step v (vals vo) (vals vms) (SZ.v vj) (addw x y);
    j := SZ.add vj 1sz;
    assert pure (SZ.v (SZ.add vj 1sz) == SZ.v vj + 1);
  };
  with w. assert (A.pts_to s w);
  addw_len (vals vo) (vals vms);
  assert (pure (vals w `Seq.equal` addw (vals vo) (vals vms)));
  addw_ble (vals vo) (vals vms) (base - 1) (base - 1);
  assert_norm (2 * (base - 1) + 1 < base * 2);
  assert_norm (2 * (base - 1) + 1 < pow2 64);
  carry_low_op s (2 * (base - 1)) 1;
  cselect out s m;
  ()
}

#pop-options

(** What the mask built from a carry says, as a proposition. *)
let mask_flag (co m: S64.t)
  : Lemma (requires m == S64.eq_mask co S64.zero)
          (ensures (S64.v m == 0) == (S64.v co =!= 0) /\
                   (S64.v m = 0 <==> S64.v co <> 0) /\
                   (S64.v m == 0 \/ S64.v m == pow2 64 - 1))
  = assert_norm (pow2 64 - 1 =!= 0);
    FStar.PropositionalExtensionality.apply (S64.v m == 0) (S64.v co =!= 0)

(** The two branches of [msub_op] are the two branches of [msub]. *)
let msub_shape (d: modulus) (a b lo r ms: Seq.seq nat) (co m: nat)
  : Lemma (requires lo == carry_low (addw a (negw b)) /\
                    co == carry_out (addw a (negw b)) /\ co <= 1 /\
                    ms == d.ms /\ (m = 0 <==> co <> 0) /\
                    r == (if m = 0 then lo else carry_low (addw lo ms)))
          (ensures r == msub d a b)
  = ()

#push-options "--z3rlimit 1200"

[@@ FStar.Attributes.CInline]
fn msub_op (out a b s ms: A.array S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to a #pa va **
  A.pts_to b #pb vb ** A.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
        Seq.length vms == nl /\ vals vms == d.ms /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to s vs' ** A.pts_to a #pa va **
  A.pts_to b #pb vb ** A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        res d (vals vo') /\ vals vo' == msub d (vals va) (vals vb))
{
  A.pts_to_len out;
  A.pts_to_len s;
  A.pts_to_len ms;
  let co = negsub_op out a b;
  msub_pre d (vals va) (vals vb);
  with lo. assert (A.pts_to out lo);
  assert (pure (S64.v co <= 1));
  let m = S64.eq_mask co S64.zero;
  mask_flag co m;
  assert (pure ((S64.v m == 0) == (S64.v co =!= 0)));
  addm_op out s ms m;
  with vo'. assert (A.pts_to out vo');
  assert (pure (vals vo' == (if S64.v m = 0 then vals lo
                             else carry_low (addw (vals lo) (vals vms)))));
  msub_ok d (vals va) (vals vb);
  msub_shape d (vals va) (vals vb) (vals lo) (vals vo') (vals vms) (S64.v co) (S64.v m);
  assert (pure (vals vo' == msub d (vals va) (vals vb)));
}

#pop-options

(** {2 Multiplication}

    The schoolbook product into fifteen wide columns, copied into the
    seventeen the reduction runs in with the top two cleared. *)

#push-options "--z3rlimit 300"

[@@ FStar.Attributes.CInline]
fn prod_op (t p: A.array S128.t) (a b: A.array S64.t)
           (#vt: erased (Seq.seq S128.t)) (#vp: erased (Seq.seq S128.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to p vp ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == ncol /\ Seq.length vp == nw /\
        Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
ensures exists* (vt': Seq.seq S128.t) (vp': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to p vp' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == ncol /\ Seq.length vp' == nw /\
        vals128 vt' == prod (vals va) (vals vb))
{
  A.pts_to_len t;
  A.pts_to_len p;
  A.pts_to_len a;
  A.pts_to_len b;
  assert_norm (nl * ((base - 1) * (base - 1)) + (base - 1) * (base - 1) < pow2 128);
  mul_columns p a b (base - 1);
  with vp1. assert (A.pts_to p vp1);
  let z = S128.zero;
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 15sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to t v ** A.pts_to p vp1 ** A.pts_to a #pa va **
    A.pts_to b #pb vb **
    pure (SZ.v vk <= 15 /\ Seq.length v == ncol /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index (vals128 v) j == Seq.index (vals128 vp1) j))
  decreases (15 - SZ.v (!k))
  {
    with v. assert (A.pts_to t v);
    let vk = !k;
    let x = A.(p.(vk));
    A.((t.(vk) <- x));
    vals128_upd v (SZ.v vk) x;
    copy128_step v ncol (vals128 vp1) 0 (SZ.v vk) x;
    k := SZ.add vk 1sz;
    assert pure (SZ.v (SZ.add vk 1sz) == SZ.v vk + 1);
  };
  with v. assert (A.pts_to t v);
  A.((t.(15sz) <- z));
  vals128_upd v 15 z;
  with v2. assert (A.pts_to t v2);
  A.((t.(16sz) <- z));
  vals128_upd v2 16 z;
  with v3. assert (A.pts_to t v3);
  assert (pure (vals128 v3 `Seq.equal` prod (vals va) (vals vb)));
}

#pop-options

(** [Spec.Field256.redc] only makes sense on a full-width accumulator,
    and a Pulse [ensures] is elaborated with no [requires] in scope, so the
    postcondition below goes through a total version of it. *)
let redcn (d: modulus) (t: Seq.seq nat) : (r: Seq.seq nat { Seq.length r == nl + 1 }) =
  if Seq.length t = ncol then redc d t else Seq.create (nl + 1) 0

(** A proper limb of the normalised reduction fits back in a word.  Stated
    on its own because the bound arrives as a [bnd] on a slice and the
    narrowing needs it on an index. *)
(** One pass of the narrowing loop in [redc_op]: the prefix agreement
    grows by the limb just written. *)
let narrow_step (v: Seq.seq S64.t) (w: Seq.seq S128.t) (k: nat) (y: S64.t)
  : Lemma (requires Seq.length v == nl /\ k < nl /\ k < Seq.length w /\
                    S64.v y == S128.v (Seq.index w k) /\
                    (forall (j: nat). j < k ==> Seq.index (vals v) j == Seq.index (vals128 w) j))
          (ensures Seq.length (Seq.upd v k y) == nl /\
                   (forall (j: nat). j < k + 1 ==>
                      Seq.index (vals (Seq.upd v k y)) j == Seq.index (vals128 w) j))
  = vals_upd v k y

let narrow_ok (s: Seq.seq nat) (k: nat)
  : Lemma (requires Seq.length s == nl + 1 /\ bnd (Seq.slice s 0 nl) base /\ k < nl)
          (ensures Seq.index s k < base)
  = Seq.lemma_index_slice s 0 nl k

(** The reduction proper: eight Montgomery steps, then the upper half
    normalised into eight proper limbs and a top carry.  The normalisation
    happens in [r], nine wide columns of its own, because the reduction's
    accumulator has no room below the half being normalised; the narrowing
    into words is the last thing that happens, once [redc_ok] has said the
    limbs are proper. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn redc_op (out: A.array S64.t) (t r: A.array S128.t) (ms: A.array S64.t)
           (mu: S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S128.t))
           (#vr: erased (Seq.seq S128.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t vt ** A.pts_to r vr ** A.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vt == ncol /\
        Seq.length vr == nl + 1 /\
        Seq.length vms == nl /\ vals vms == d.ms /\ S64.v mu == d.mu /\
        ble (vals128 vt) cmax /\ eval (vals128 vt) < d.m * pow2 256)
returns top: S64.t
ensures exists* (vo': Seq.seq S64.t) (vt': Seq.seq S128.t) (vr': Seq.seq S128.t).
  A.pts_to out vo' ** A.pts_to t vt' ** A.pts_to r vr' ** A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vt' == ncol /\
        Seq.length vr' == nl + 1 /\
        vals vo' == Seq.slice (redcn d (vals128 vt)) 0 nl /\
        S64.v top == vat (redcn d (vals128 vt)) nl)
{
  A.pts_to_len out;
  A.pts_to_len t;
  A.pts_to_len r;
  A.pts_to_len ms;
  cmax_fits ();
  mreduce_op t ms mu cmax;
  with u. assert (A.pts_to t u);
  mrun_len d.ms d.mu nl (vals128 vt);
  assert (pure (Seq.slice (vals128 u) nl ncol == mreduce d.ms d.mu (vals128 vt)));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 9sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to r v ** A.pts_to t u ** A.pts_to out vo **
    A.pts_to ms #pm vms **
    pure (SZ.v vi <= 9 /\ Seq.length v == nl + 1 /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index (vals128 v) j == Seq.index (vals128 u) (8 + j)))
  decreases (9 - SZ.v (!i))
  {
    with v. assert (A.pts_to r v);
    let vi = !i;
    let x = A.(t.(SZ.add 8sz vi));
    A.((r.(vi) <- x));
    vals128_upd v (SZ.v vi) x;
    copy128_step v (nl + 1) (vals128 u) 8 (SZ.v vi) x;
    i := SZ.add vi 1sz;
    assert pure (SZ.v (SZ.add vi 1sz) == SZ.v vi + 1);
  };
  with w. assert (A.pts_to r w);
  assert (pure (vals128 w `Seq.equal` mreduce d.ms d.mu (vals128 vt)));
  mreduce_ble d.ms d.mu (vals128 vt) cmax;
  assert_norm (cmax + nl * pow2 65 + pow2 41 < base * (pow2 41 + 1));
  assert_norm (cmax + nl * pow2 65 + pow2 41 < pow2 128);
  carry_run128_op r 8sz (cmax + nl * pow2 65) (pow2 41);
  with w2. assert (A.pts_to r w2);
  assert (pure (vals128 w2 == redcn d (vals128 vt)));
  redc_ok d (vals128 vt);
  assert (pure (bnd (Seq.slice (redcn d (vals128 vt)) 0 nl) base));
  assert_norm (base < pow2 64);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 8sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to out v ** A.pts_to r w2 ** A.pts_to t u **
    A.pts_to ms #pm vms **
    pure (SZ.v vk <= 8 /\ Seq.length v == nl /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index (vals v) j == Seq.index (vals128 w2) j))
  decreases (8 - SZ.v (!k))
  {
    with v. assert (A.pts_to out v);
    let vk = !k;
    let x = A.(r.(vk));
    narrow_ok (vals128 w2) (SZ.v vk);
    let y = narrow128 x;
    A.((out.(vk) <- y));
    vals_upd v (SZ.v vk) y;
    narrow_step v w2 (SZ.v vk) y;
    k := SZ.add vk 1sz;
    assert pure (SZ.v (SZ.add vk 1sz) == SZ.v vk + 1);
  };
  with vo2. assert (A.pts_to out vo2);
  assert (pure (vals vo2 `Seq.equal` Seq.slice (redcn d (vals128 vt)) 0 nl));
  let hi = A.(r.(8sz));
  narrow128 hi
}

#pop-options

#push-options "--z3rlimit 300"

[@@ FStar.Attributes.CInline]
fn mmul_op (out: A.array S64.t) (a b: A.array S64.t) (p t r: A.array S128.t)
           (s ms nm: A.array S64.t) (mu: S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vp: erased (Seq.seq S128.t))
           (#vt: erased (Seq.seq S128.t)) (#vr: erased (Seq.seq S128.t))
           (#vs: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to p vp ** A.pts_to t vt ** A.pts_to r vr **
  A.pts_to s vs ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vp == nw /\
        Seq.length vt == ncol /\ Seq.length vr == nl + 1 /\
        Seq.length vs == nl /\
        Seq.length vms == nl /\ Seq.length vnm == nl /\
        vals vms == d.ms /\ vals vnm == d.nm /\ S64.v mu == d.mu /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vp': Seq.seq S128.t)
                (vt': Seq.seq S128.t) (vr': Seq.seq S128.t) (vs': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to p vp' ** A.pts_to t vt' ** A.pts_to r vr' **
  A.pts_to s vs' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\ Seq.length vp' == nw /\
        Seq.length vt' == ncol /\ Seq.length vr' == nl + 1 /\
        Seq.length vs' == nl /\
        res d (vals vo') /\ vals vo' == mmul d (vals va) (vals vb))
{
  prod_op t p a b;
  prod_ok (vals va) (vals vb);
  Math.lemma_mult_le_right (eval (vals vb)) (eval (vals va)) (d.m - 1);
  Math.lemma_mult_le_left d.m (eval (vals vb)) (pow2 256);
  let top = redc_op out t r ms mu d;
  redc_ok d (prod (vals va) (vals vb));
  csub_op out s nm top d;
  mmul_ok d (vals va) (vals vb);
  with vo'. assert (A.pts_to out vo');
  assert (pure (vals vo' == mmul d (vals va) (vals vb)));
}

#pop-options

(** {2 Big-endian bytes}

    P-256 serialises most significant byte first, so limb [k] -- the [k]-th
    least significant -- is the four-byte group at distance [4 (7 - k)]
    from the start, most significant byte of the limb first.  That
    mirroring is the only difference from Curve25519's little-endian
    quadruple. *)

(** The byte offset of limb [vi], computed in [SZ.t], is linear in [vi]. *)
let quad_pos (vi: SZ.t)
  : Lemma (requires SZ.v vi < 8)
          (ensures SZ.v 4sz * SZ.v (SZ.sub 7sz vi) == 4 * (7 - SZ.v vi) /\
                   SZ.fits (SZ.v 4sz * SZ.v (SZ.sub 7sz vi)))
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 (4 * (7 - SZ.v vi))

(** A byte scaled by a word constant is a linear term in the byte. *)
let byte_mul (k: FStar.UInt64.t) (c: nat) (x: S8.t)
  : Lemma (requires FStar.UInt64.v k == c)
          (ensures FStar.UInt64.v k * S64.v (Cast.u8_to_u64 x) == c * S8.v x /\
                   S64.v (Cast.u8_to_u64 x) == S8.v x /\ S8.v x < 256)
  = assert_norm (pow2 8 == 256)

(** One pass of the loop in [load_be]: the four bytes read are limb [k]'s
    big-endian bytes, and the word built from them is that limb. *)
let bat_at (vb: Seq.seq S8.t) (o: nat) (x: S8.t)
  : Lemma (requires Seq.length vb == 32 /\ o < 32 /\ x == Seq.index vb o)
          (ensures bat vb o == S8.v x)
  = ()

#push-options "--z3rlimit 40"
let load_word (vb: Seq.seq S8.t) (k: nat)
              (b0 b1 b2 b3: S8.t) (w: S64.t)
  : Lemma (requires Seq.length vb == 32 /\ k < nl /\
                    b0 == Seq.index vb (4 * (7 - k) + 0) /\
                    b1 == Seq.index vb (4 * (7 - k) + 1) /\
                    b2 == Seq.index vb (4 * (7 - k) + 2) /\
                    b3 == Seq.index vb (4 * (7 - k) + 3) /\
                    S64.v w ==
                    16777216 * S8.v b0 +
                    65536 * S8.v b1 +
                    256 * S8.v b2 +
                    S8.v b3)
          (ensures S64.v w == be_quad vb nl k)
  = let o = 4 * (7 - k) in
    assert (4 * (nl - 1 - k) == o);
    assert (o + 3 < 32);
    bat_at vb (o + 0) b0;
    bat_at vb (o + 1) b1;
    bat_at vb (o + 2) b2;
    bat_at vb (o + 3) b3;
    assert (S64.v w == be_quad vb nl k)

let load_step (v: Seq.seq S64.t) (vb: Seq.seq S8.t) (k: nat)
              (b0 b1 b2 b3: S8.t) (w: S64.t)
  : Lemma (requires Seq.length v == nl /\ Seq.length vb == 32 /\ k < nl /\
                    b0 == Seq.index vb (4 * (7 - k) + 0) /\
                    b1 == Seq.index vb (4 * (7 - k) + 1) /\
                    b2 == Seq.index vb (4 * (7 - k) + 2) /\
                    b3 == Seq.index vb (4 * (7 - k) + 3) /\
                    S64.v w ==
                    16777216 * S8.v b0 +
                    65536 * S8.v b1 +
                    256 * S8.v b2 +
                    S8.v b3 /\
                    (forall (j: nat). j < k ==> Seq.index (vals v) j == be_quad vb nl j))
          (ensures Seq.length (Seq.upd v k w) == nl /\
                   (forall (j: nat). j < k + 1 ==>
                      Seq.index (vals (Seq.upd v k w)) j == be_quad vb nl j))
  = load_word vb k b0 b1 b2 b3 w;
    vals_upd v k w
#pop-options

#push-options "--z3rlimit 300"

[@@ FStar.Attributes.CInline]
fn load_be (a: A.array S64.t) (b: A.array S8.t)
           (#va: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == 32)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b #pb vb **
  pure (Seq.length va' == nl /\ bnd (vals va') base /\
        eval (vals va') == be_nat vb)
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 8 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == be_quad vb nl k))
  decreases (8 - SZ.v (!i))
  {
    with v. assert (A.pts_to a v);
    let vi = !i;
    quad_pos vi;
    let pos = SZ.mul 4sz (SZ.sub 7sz vi);
    let b0 = A.(b.(pos));
    let b1 = A.(b.(SZ.add pos 1sz));
    let b2 = A.(b.(SZ.add pos 2sz));
    let b3 = A.(b.(SZ.add pos 3sz));
    byte_mul 16777216uL 16777216 b0;
    byte_mul 65536uL 65536 b1;
    byte_mul 256uL 256 b2;
    byte_mul 1uL 1 b3;
    assert_norm (pow2 64 == 18446744073709551616);
    assert_norm (16777216 * (pow2 8 - 1) < pow2 64);
    assert_norm (65536 * (pow2 8 - 1) < pow2 64);
    assert_norm (256 * (pow2 8 - 1) < pow2 64);
    assert_norm (16777216 * (pow2 8 - 1) + 65536 * (pow2 8 - 1) +
                 256 * (pow2 8 - 1) + (pow2 8 - 1) < pow2 64);
    let w = addw (addw (mulk 16777216uL (Cast.u8_to_u64 b0))
                       (mulk 65536uL (Cast.u8_to_u64 b1)))
                 (addw (mulk 256uL (Cast.u8_to_u64 b2)) (Cast.u8_to_u64 b3));
    A.((a.(vi) <- w));
    load_step v vb (SZ.v vi) b0 b1 b2 b3 w;
    i := SZ.add vi 1sz;
    assert pure (SZ.v (SZ.add vi 1sz) == SZ.v vi + 1);
  };
  with v. assert (A.pts_to a v);
  assert (pure (forall (k: nat). k < nl ==> Seq.index (vals v) k == be_quad vb nl k));
  eval_bytes_be vb (vals v);
  assert_norm (16777216 * (pow2 8 - 1) + 65536 * (pow2 8 - 1) +
               256 * (pow2 8 - 1) + (pow2 8 - 1) < base);
}

[@@ FStar.Attributes.CInline]
fn store_be (b: A.array S8.t) (a: A.array S64.t)
            (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ Seq.length va == nl /\ bnd (vals va) base)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == nat_to_be 32 (eval (vals va)))
{
  A.pts_to_len b;
  A.pts_to_len a;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 8 /\ Seq.length v == 32 /\
          (forall (k: nat). k < SZ.v vi ==>
             S8.v (Seq.index v (4 * (nl - 1 - k))) == Seq.index (vals va) k / 16777216 % 256 /\
             S8.v (Seq.index v (4 * (nl - 1 - k) + 1)) == Seq.index (vals va) k / 65536 % 256 /\
             S8.v (Seq.index v (4 * (nl - 1 - k) + 2)) == Seq.index (vals va) k / 256 % 256 /\
             S8.v (Seq.index v (4 * (nl - 1 - k) + 3)) == Seq.index (vals va) k % 256))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    quad_pos vi;
    let pos = SZ.mul 4sz (SZ.sub 7sz vi);
    assert_norm (pow2 24 == 16777216);
    assert_norm (pow2 16 == 65536);
    assert_norm (pow2 8 == 256);
    Math.lemma_div_lt_nat (S64.v x) 32 24;
    Math.lemma_div_lt_nat (S64.v x) 32 16;
    Math.lemma_div_lt_nat (S64.v x) 32 8;
    Math.small_mod (S64.v x / 16777216) (pow2 8);
    Math.pow2_modulo_division_lemma_1 (S64.v x) 16 24;
    Math.pow2_modulo_division_lemma_1 (S64.v x) 8 16;
    Math.pow2_modulo_modulo_lemma_1 (S64.v x) 8 32;
    A.((b.(pos) <- Cast.u64_to_u8 (S64.shift_right x 24ul)));
    A.((b.(SZ.add pos 1sz) <- Cast.u64_to_u8 (S64.shift_right x 16ul)));
    A.((b.(SZ.add pos 2sz) <- Cast.u64_to_u8 (S64.shift_right x 8ul)));
    A.((b.(SZ.add pos 3sz) <- Cast.u64_to_u8 x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  assert (pure (Seq.length v == 32 /\ bnd (vals va) base));
  assert (pure (forall (k: nat). k < nl ==>
                  bat v (4 * (nl - 1 - k)) == Seq.index (vals va) k / 16777216 % 256 /\
                  bat v (4 * (nl - 1 - k) + 1) == Seq.index (vals va) k / 65536 % 256 /\
                  bat v (4 * (nl - 1 - k) + 2) == Seq.index (vals va) k / 256 % 256 /\
                  bat v (4 * (nl - 1 - k) + 3) == Seq.index (vals va) k % 256));
  store_be_ok (vals va) v;
  assert (pure (v == nat_to_be 32 (eval (vals va))));
}

#pop-options

#pop-options
