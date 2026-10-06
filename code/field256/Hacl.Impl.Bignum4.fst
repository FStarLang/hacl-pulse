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

(** Montgomery arithmetic modulo a generic 256-bit modulus, at four limbs
    of sixty-four bits.

    The twin of {!Hacl.Impl.Bignum256}, against {!Spec.Bignum4},
    {!Spec.Montgomery4} and {!Spec.Field4} instead of their thirty-two-bit
    originals, and on {!Hacl.Impl.Limb4} instead of {!Hacl.Impl.Limb}.
    Everything a client sees is the same; what changes is underneath.

    {b A product is two columns.}  At this radix [a_i b_j] does not fit in
    a column, so it is added as two halves, the low one at column [i + j]
    and the high one at [i + j + 1].  {!Spec.Bignum4.srow} says this once
    and both the schoolbook multiplier and the Montgomery reduction use it,
    so the loops here each write two columns per multiply and nothing else
    about them changed.

    {b A lazy sum is a column too.}  A word used to have thirty-two bits of
    slack, so an addition could be done lazily in words and carried
    afterwards.  It has none now, so the conditional subtraction builds its
    sum one width up and narrows it as it selects.

    The workspace shapes: eight columns for a product, nine for the
    reduction to run in, five for the normalisation of its upper half, and
    four columns for the conditional subtraction. *)
module Hacl.Impl.Bignum4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.Montgomery4
open Spec.Field4
open Hacl.Impl.Limb4
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

    [Spec.Montgomery4.mstep] adds [u * m] at limb [i] and then carries limb
    [i] into its neighbour, where [u] is the digit that makes limb [i]
    vanish.  The inner loop adds one product at a time, and each product is
    the two halves {!Spec.Bignum4.srow} places. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn mstep_op (t: A.array S128.t) (ms: A.array S64.t) (mu: S64.t) (i: SZ.t) (c: erased nat)
            (#vt: erased (Seq.seq S128.t))
            (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to ms #pm vms **
  pure (Seq.length vms == nl /\ SZ.v i + nl + 1 <= Seq.length vt /\
        mont_ok (vals vms) (S64.v mu) /\ ble (vals128 vt) c /\ c <= pow2 72)
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to ms #pm vms **
  pure (Seq.length vt' == Seq.length vt /\
        vals128 vt' == mstep (vals vms) (S64.v mu) (SZ.v i) (vals128 vt))
{
  A.pts_to_len t;
  A.pts_to_len ms;
  vals_bnd vms;
  assert_norm (pow2 72 + 2 * (base - 1) + base < pow2 128);
  assert_norm (pow2 72 + 2 * (base - 1) < pow2 128);
  let ti = A.(t.(i));
  let tl = lo64d ti;
  mod_mul_lo (S128.v ti) (S64.v mu);
  let u = mulw tl mu;
  addw_srow_zero (vals128 vt) (Seq.length vt) (S64.v u) (vals vms) (SZ.v i);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 4sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S128.t).
    pts_to j vj ** A.pts_to t v ** A.pts_to ms #pm vms **
    pure (SZ.v vj <= 4 /\ Seq.length v == Seq.length vt /\
          vals128 v == addw (vals128 vt)
                            (srow (Seq.length vt) (S64.v u) (vals vms) (SZ.v i) (SZ.v vj)))
  decreases (4 - SZ.v (!j))
  {
    with v. assert (A.pts_to t v);
    let vj = !j;
    addw_srow_ble (vals128 vt) (vals vms) (Seq.length vt) (S64.v u) (SZ.v i) (SZ.v vj) c;
    let msj = A.(ms.(vj));
    let pos = SZ.add i vj;
    let pos1 = SZ.add pos 1sz;
    let p = S128.mul_wide u msj;
    let pl = Cast.u64_to_u128 (lo64d p);
    let ph = hi64d p;
    Math.lemma_mult_le_left (S64.v u) (S64.v msj) (base - 1);
    Math.lemma_mult_le_right (base - 1) (S64.v u) (base - 1);
    phi_le (S64.v u * S64.v msj) (base - 1);
    let cur = A.(t.(pos));
    let nv = addd cur pl;
    A.((t.(pos) <- nv));
    vals128_upd v (SZ.v i + SZ.v vj) nv;
    with v1. assert (A.pts_to t v1);
    let cur1 = A.(t.(pos1));
    let nv1 = addd cur1 ph;
    A.((t.(pos1) <- nv1));
    vals128_upd v1 (SZ.v i + SZ.v vj + 1) nv1;
    addw_srow_step (vals128 vt) (Seq.length vt) (S64.v u) (vals vms) (SZ.v i) (SZ.v vj);
    j := SZ.add vj 1sz;
  };
  with v. assert (A.pts_to t v);
  addw_srow_ble (vals128 vt) (vals vms) (Seq.length vt) (S64.v u) (SZ.v i) nl c;
  assert (pure (vals128 v ==
                  addw (vals128 vt)
                       (srow (Seq.length vt) (S64.v u) (vals vms) (SZ.v i) nl)));
  assert (pure (S64.v u == mdigit (S64.v mu) (SZ.v i) (vals128 vt)));
  let x = A.(t.(i));
  let lo = Cast.u64_to_u128 (lo64d x);
  let hi = hi64d x;
  A.((t.(i) <- lo));
  vals128_upd v (SZ.v i) lo;
  with v1. assert (A.pts_to t v1);
  assert (pure (vals128 v1 ==
                  Seq.upd (vals128 v) (SZ.v i) (vat (vals128 v) (SZ.v i) % base)));
  let ip = SZ.add i 1sz;
  let y = A.(t.(ip));
  let up = addd y hi;
  A.((t.(ip) <- up));
  vals128_upd v1 (SZ.v i + 1) up;
  with v2. assert (A.pts_to t v2);
  (* The two writes above are exactly [carry_step i], and [mstep] is that
     applied to the row the loop built. *)
  assert (pure (vals128 v2 ==
                  Seq.upd (vals128 v1) (SZ.v i + 1)
                          (vat (vals128 v1) (SZ.v i + 1) +
                           vat (vals128 v) (SZ.v i) / base)));
  assert (pure (SZ.v i + 1 < Seq.length (vals128 v)));
  assert (pure (vals128 v2 == carry_step (SZ.v i) (vals128 v)));
  assert (pure (vals128 v2 == mstep (vals vms) (S64.v mu) (SZ.v i) (vals128 vt)));
  ()
}

#pop-options

(** {2 The four steps}

    Each step raises a column by less than [2^66], so a product's [2^67]
    reaches at most [2^69] and stays inside a wide word with room to
    spare. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn mreduce_op (t: A.array S128.t) (ms: A.array S64.t) (mu: S64.t) (c: erased nat)
              (#vt: erased (Seq.seq S128.t))
              (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to ms #pm vms **
  pure (Seq.length vms == nl /\ Seq.length vt == ncol /\
        mont_ok (vals vms) (S64.v mu) /\ ble (vals128 vt) c /\
        reveal c + nl * pow2 66 <= pow2 72)
ensures exists* (vt': Seq.seq S128.t).
  A.pts_to t vt' ** A.pts_to ms #pm vms **
  pure (Seq.length vt' == ncol /\
        ble (vals128 vt') (reveal c + nl * pow2 66) /\
        vals128 vt' == mrun (vals vms) (S64.v mu) nl (vals128 vt))
{
  A.pts_to_len t;
  A.pts_to_len ms;
  Loops.repeati_zero (mstep (vals vms) (S64.v mu)) (vals128 vt);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 4sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to t v ** A.pts_to ms #pm vms **
    pure (SZ.v vk <= 4 /\ Seq.length v == ncol /\
          vals128 v == mrun (vals vms) (S64.v mu) (SZ.v vk) (vals128 vt) /\
          ble (vals128 v) (reveal c + SZ.v vk * pow2 66))
  decreases (4 - SZ.v (!k))
  {
    with v. assert (A.pts_to t v);
    let vk = !k;
    Math.lemma_mult_le_right (pow2 66) (SZ.v vk) nl;
    mstep_op t ms mu vk (reveal c + SZ.v vk * pow2 66);
    mstep_ble (vals vms) (S64.v mu) (SZ.v vk) (vals128 v) (reveal c + SZ.v vk * pow2 66);
    Loops.unfold_repeati (SZ.v vk) (mstep (vals vms) (S64.v mu)) (vals128 vt);
    Math.distributivity_add_left (SZ.v vk) 1 (pow2 66);
    k := SZ.add vk 1sz;
  };
  ()
}

#pop-options


(** {2 Narrowing}

    A carried column array holds proper limbs, so it can be copied back
    into words.  Every lazy sum in this module is built one width up now,
    and this is how it comes back down. *)

#push-options "--z3rlimit 300"

[@@ FStar.Attributes.CInline]
fn narrow_copy (out: A.array S64.t) (b: A.array S128.t)
               (#vo: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S128.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == nl /\ bnd (vals128 vb) base)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (Seq.length vo' == nl /\ vals vo' == vals128 vb)
{
  A.pts_to_len out;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals128 vb) k))
  decreases (4 - SZ.v (!i))
  {
    with v. assert (A.pts_to out v);
    let vi = !i;
    let x = A.(b.(vi));
    let y = narrow128 x;
    A.((out.(vi) <- y));
    vals_upd v (SZ.v vi) y;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  assert (pure (vals v `Seq.equal` vals128 vb));
}

#pop-options

(** {2 The conditional subtraction}

    Add the modulus's complement, look at the carry out to learn whether
    the value was at least the modulus, and select.  The sum of two limbs
    no longer fits in a word, so it is built in [s], which is a column
    array, and the select narrows on its way out. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn csub_op (a: A.array S64.t) (s: A.array S128.t) (nm: A.array S64.t)
           (top: S64.t) (d: erased modulus)
           (#va: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S128.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to s vs ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length va == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        bnd (vals va) base /\ S64.v top <= 1 /\
        eval (vals va) + pow2 256 * S64.v top < 2 * d.m)
ensures exists* (va': Seq.seq S64.t) (vs': Seq.seq S128.t).
  A.pts_to a va' ** A.pts_to s vs' ** A.pts_to nm #pn vnm **
  pure (Seq.length va' == nl /\ Seq.length vs' == nl /\
        res d (vals va') /\ vals va' == csub d (vals va) (S64.v top))
{
  A.pts_to_len a;
  A.pts_to_len s;
  A.pts_to_len nm;
  vals_bnd va;
  vals_bnd vnm;
  assert_norm (2 * (base - 1) < pow2 128);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to a va ** A.pts_to s v ** A.pts_to nm #pn vnm **
    pure (SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals128 v) k == Seq.index (vals va) k + Seq.index (vals vnm) k))
  decreases (4 - SZ.v (!i))
  {
    with v. assert (A.pts_to s v);
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(nm.(vi));
    let z = addd (widen x) (widen y);
    A.((s.(vi) <- z));
    vals128_upd v (SZ.v vi) z;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to s v);
  addw_len (vals va) (vals vnm);
  assert (pure (vals128 v `Seq.equal` addw (vals va) (vals vnm)));
  addw_ble (vals va) (vals vnm) (base - 1) (base - 1);
  assert_norm (2 * (base - 1) + 1 < base * 2);
  assert_norm (2 * (base - 1) + 1 < pow2 128);
  assert_norm (1 < pow2 64);
  carry_split_bnd (addw (vals va) (vals vnm)) (2 * (base - 1)) 1;
  let co = carry_out128_op s (2 * (base - 1)) 1;
  assert (pure (S64.v co <= 1));
  assert_norm (2 < pow2 64);
  let m = S64.gte_mask (addw top co) (S64.classify 1uL);
  cselect_narrow a s m;
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
    back is the correction.

    The column array [s] is used twice here, first for the sum and then as
    the conditional subtraction's own workspace; nothing it holds outlives
    the narrowing. *)

#push-options "--z3rlimit 800"

[@@ FStar.Attributes.CInline]
fn madd_op (out a b: A.array S64.t) (s: A.array S128.t) (nm: A.array S64.t)
           (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S128.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to a #pa va **
  A.pts_to b #pb vb ** A.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S128.t).
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
  vals_bnd va;
  vals_bnd vb;
  assert_norm (2 * (base - 1) < pow2 128);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to out vo ** A.pts_to s v ** A.pts_to a #pa va **
    A.pts_to b #pb vb ** A.pts_to nm #pn vnm **
    pure (SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals128 v) k == Seq.index (vals va) k + Seq.index (vals vb) k))
  decreases (4 - SZ.v (!i))
  {
    with v. assert (A.pts_to s v);
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let z = addd (widen x) (widen y);
    A.((s.(vi) <- z));
    vals128_upd v (SZ.v vi) z;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to s v);
  addw_len (vals va) (vals vb);
  assert (pure (vals128 v `Seq.equal` addw (vals va) (vals vb)));
  addw_ble (vals va) (vals vb) (base - 1) (base - 1);
  assert_norm (2 * (base - 1) + 1 < base * 2);
  assert_norm (2 * (base - 1) + 1 < pow2 128);
  assert_norm (1 < pow2 64);
  carry_split_bnd (addw (vals va) (vals vb)) (2 * (base - 1)) 1;
  let co = carry_out128_op s (2 * (base - 1)) 1;
  carry_split_ok (addw (vals va) (vals vb));
  carry_low_len (addw (vals va) (vals vb));
  eval_addw (vals va) (vals vb);
  narrow_copy out s;
  csub_op out s nm co d;
  madd_ok d (vals va) (vals vb);
  with vo'. assert (A.pts_to out vo');
  assert (pure (vals vo' == madd d (vals va) (vals vb)));
}

#pop-options

(** {2 Subtraction}

    [a - b] is [a + (2^256 - b)], and the two's complement is built one
    limb at a time: every limb gets [2^64 - 1 - b_i], and limb zero gets
    the extra one.  The carry out of the sum is one exactly when [a >= b].
    A limb of the complement can be as large as [2^64 - 1], so this sum is
    a column array too. *)

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

(** The one spec-level step the loop below takes after it has filled the
    complement: bumping limb zero turns [compl] into [negw].  Kept out of
    the Pulse body, where the surrounding context makes it expensive. *)
let negsub_shape (a b v v1: Seq.seq nat) (z: nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl /\ bnd b base /\
                    v == addw a (compl b) /\
                    z == Seq.index a 0 + Seq.index (compl b) 0 + 1 /\
                    v1 == Seq.upd v 0 z)
          (ensures v1 == addw a (negw b))
  = negw_shape a b

#push-options "--z3rlimit 1200"

[@@ FStar.Attributes.CInline]
fn negsub_op (w: A.array S128.t) (a b: A.array S64.t)
             (#vw: erased (Seq.seq S128.t))
             (#pa: perm) (#va: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to w vw ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vw == nl /\ Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
returns co: S64.t
ensures exists* (vw': Seq.seq S128.t).
  A.pts_to w vw' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vw' == nl /\ bnd (vals128 vw') base /\
        vals128 vw' == carry_low (addw (vals va) (negw (vals vb))) /\
        S64.v co == carry_out (addw (vals va) (negw (vals vb))))
{
  A.pts_to_len w;
  A.pts_to_len a;
  A.pts_to_len b;
  compl_ok (vals vb);
  assert_norm (2 * (base - 1) + 1 < pow2 128);
  let top = S64.classify 0xffffffffffffffffuL;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to w v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals128 v) k ==
               Seq.index (vals va) k + Seq.index (compl (vals vb)) k))
  decreases (4 - SZ.v (!i))
  {
    with v. assert (A.pts_to w v);
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let nv = addd (widen x) (widen (subw top y));
    A.((w.(vi) <- nv));
    vals128_upd v (SZ.v vi) nv;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to w v);
  addw_len (vals va) (compl (vals vb));
  assert (pure (vals128 v `Seq.equal` addw (vals va) (compl (vals vb))));
  let a0 = A.(a.(0sz));
  let b0 = A.(b.(0sz));
  (* The two limbs and the carried one are each below the radix, so the sum
     is nowhere near a wide word; say so, rather than leaving it to the
     solver among the sequence facts above. *)
  assert (pure (S64.v a0 < base /\ S64.v (subw top b0) < base));
  assert (pure (S128.v (widen a0) < base /\
                S128.v (widen (subw top b0)) < base /\
                S128.v (widen (S64.classify 1uL)) == 1));
  assert_norm (base + base + 1 < pow2 128);
  let s0 = addd (widen a0) (widen (subw top b0));
  assert (pure (S128.v s0 < base + base));
  let nv0 = addd s0 (widen (S64.classify 1uL));
  A.((w.(0sz) <- nv0));
  vals128_upd v 0 nv0;
  with v1. assert (A.pts_to w v1);
  negsub_shape (vals va) (vals vb) (vals128 v) (vals128 v1) (S128.v nv0);
  assert (pure (vals128 v1 == addw (vals va) (negw (vals vb))));
  negw_ok (vals vb);
  addw_ble (vals va) (negw (vals vb)) (base - 1) base;
  assert_norm (base - 1 + base + 2 < base * 3);
  assert_norm (base - 1 + base + 2 < pow2 128);
  assert_norm (2 < pow2 64);
  carry_split_bnd (addw (vals va) (negw (vals vb))) (base - 1 + base) 2;
  carry_low_len (addw (vals va) (negw (vals vb)));
  let co = carry_out128_op w (base - 1 + base) 2;
  co
}

#pop-options

(** The correction, computed whether or not it is wanted: when the
    subtraction went negative, adding the modulus back and dropping the
    overflow is the answer. *)

#push-options "--z3rlimit 400"

[@@ FStar.Attributes.CInline]
fn addm_op (out: A.array S64.t) (s: A.array S128.t) (ms: A.array S64.t) (m: S64.t)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S128.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to ms #pm vms **
  pure (Seq.length vo == nl /\ Seq.length vs == nl /\ Seq.length vms == nl /\
        bnd (vals vo) base /\ bnd (vals vms) base /\
        (S64.v m == 0 \/ S64.v m == pow2 64 - 1))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S128.t).
  A.pts_to out vo' ** A.pts_to s vs' ** A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        vals vo' == (if S64.v m = 0 then vals vo
                     else carry_low (addw (vals vo) (vals vms))))
{
  A.pts_to_len out;
  A.pts_to_len s;
  A.pts_to_len ms;
  assert_norm (2 * (base - 1) < pow2 128);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 4sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S128.t).
    pts_to j vj ** A.pts_to out vo ** A.pts_to s v ** A.pts_to ms #pm vms **
    pure (SZ.v vj <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index (vals128 v) k == Seq.index (vals vo) k + Seq.index (vals vms) k))
  decreases (4 - SZ.v (!j))
  {
    with v. assert (A.pts_to s v);
    let vj = !j;
    let x = A.(out.(vj));
    let y = A.(ms.(vj));
    let z = addd (widen x) (widen y);
    A.((s.(vj) <- z));
    vals128_upd v (SZ.v vj) z;
    j := SZ.add vj 1sz;
  };
  with w. assert (A.pts_to s w);
  addw_len (vals vo) (vals vms);
  assert (pure (vals128 w `Seq.equal` addw (vals vo) (vals vms)));
  addw_ble (vals vo) (vals vms) (base - 1) (base - 1);
  assert_norm (2 * (base - 1) + 1 < base * 2);
  assert_norm (2 * (base - 1) + 1 < pow2 128);
  assert_norm (1 < pow2 64);
  carry_split_bnd (addw (vals vo) (vals vms)) (2 * (base - 1)) 1;
  let ignored = carry_out128_op s (2 * (base - 1)) 1;
  cselect_narrow out s m;
  ()
}

#pop-options

#push-options "--z3rlimit 1200"

[@@ FStar.Attributes.CInline]
fn msub_op (out a b: A.array S64.t) (s: A.array S128.t) (ms: A.array S64.t)
           (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S128.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to a #pa va **
  A.pts_to b #pb vb ** A.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
        Seq.length vms == nl /\ vals vms == d.ms /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S128.t).
  A.pts_to out vo' ** A.pts_to s vs' ** A.pts_to a #pa va **
  A.pts_to b #pb vb ** A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        res d (vals vo') /\ vals vo' == msub d (vals va) (vals vb))
{
  A.pts_to_len out;
  A.pts_to_len s;
  A.pts_to_len ms;
  let co = negsub_op s a b;
  assert_norm (pow2 64 - 1 =!= 0);
  let m = S64.eq_mask co S64.zero;
  assert (pure ((S64.v m == 0) == (S64.v co =!= 0)));
  msub_pre d (vals va) (vals vb);
  narrow_copy out s;
  with lo. assert (A.pts_to out lo);
  assert (pure (vals lo == carry_low (addw (vals va) (negw (vals vb)))));
  addm_op out s ms m;
  with vo'. assert (A.pts_to out vo');
  assert (pure (vals vo' == (if S64.v m = 0 then vals lo
                             else carry_low (addw (vals lo) (vals vms)))));
  msub_ok d (vals va) (vals vb);
  assert (pure (vals vo' == msub d (vals va) (vals vb)));
}

#pop-options

(** {2 Multiplication}

    The schoolbook product into eight wide columns, copied into the nine
    the reduction runs in with the top one cleared. *)

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
  mul_columns p a b;
  with vp1. assert (A.pts_to p vp1);
  let z = S128.zero;
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 8sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S128.t).
    pts_to k vk ** A.pts_to t v ** A.pts_to p vp1 ** A.pts_to a #pa va **
    A.pts_to b #pb vb **
    pure (SZ.v vk <= 8 /\ Seq.length v == ncol /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index (vals128 v) j == Seq.index (vals128 vp1) j))
  decreases (8 - SZ.v (!k))
  {
    with v. assert (A.pts_to t v);
    let vk = !k;
    let x = A.(p.(vk));
    A.((t.(vk) <- x));
    vals128_upd v (SZ.v vk) x;
    k := SZ.add vk 1sz;
  };
  with v. assert (A.pts_to t v);
  A.((t.(8sz) <- z));
  vals128_upd v 8 z;
  with v2. assert (A.pts_to t v2);
  assert (pure (vals128 v2 `Seq.equal` prod (vals va) (vals vb)));
}

#pop-options

(** [Spec.Field4.redc] only makes sense on a full-width accumulator,
    and a Pulse [ensures] is elaborated with no [requires] in scope, so the
    postcondition below goes through a total version of it. *)
let redcn (d: modulus) (t: Seq.seq nat) : (r: Seq.seq nat { Seq.length r == nl + 1 }) =
  if Seq.length t = ncol then redc d t else Seq.create (nl + 1) 0

(** A proper limb of the normalised reduction fits back in a word.  Stated
    on its own because the bound arrives as a [bnd] on a slice and the
    narrowing needs it on an index. *)
let narrow_ok (s: Seq.seq nat) (k: nat)
  : Lemma (requires Seq.length s == nl + 1 /\ bnd (Seq.slice s 0 nl) base /\ k < nl)
          (ensures Seq.index s k < base)
  = Seq.lemma_index_slice s 0 nl k

(** The reduction proper: four Montgomery steps, then the upper half
    normalised into four proper limbs and a top carry.  The normalisation
    happens in [r], five wide columns of its own, because the reduction's
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
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S128.t).
    pts_to i vi ** A.pts_to r v ** A.pts_to t u ** A.pts_to out vo **
    A.pts_to ms #pm vms **
    pure (SZ.v vi <= 5 /\ Seq.length v == nl + 1 /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index (vals128 v) j == Seq.index (vals128 u) (4 + j)))
  decreases (5 - SZ.v (!i))
  {
    with v. assert (A.pts_to r v);
    let vi = !i;
    let x = A.(t.(SZ.add 4sz vi));
    A.((r.(vi) <- x));
    vals128_upd v (SZ.v vi) x;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to r w);
  assert (pure (vals128 w `Seq.equal` mreduce d.ms d.mu (vals128 vt)));
  mreduce_ble d.ms d.mu (vals128 vt) cmax;
  assert_norm (cmax + nl * pow2 66 + pow2 9 < base * (pow2 9 + 1));
  assert_norm (cmax + nl * pow2 66 + pow2 9 < pow2 128);
  carry_run128_op r 4sz (cmax + nl * pow2 66) (pow2 9);
  with w2. assert (A.pts_to r w2);
  assert (pure (vals128 w2 == redcn d (vals128 vt)));
  redc_ok d (vals128 vt);
  assert (pure (bnd (Seq.slice (redcn d (vals128 vt)) 0 nl) base));
  assert_norm (base <= pow2 64);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 4sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** A.pts_to out v ** A.pts_to r w2 ** A.pts_to t u **
    A.pts_to ms #pm vms **
    pure (SZ.v vk <= 4 /\ Seq.length v == nl /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index (vals v) j == Seq.index (vals128 w2) j))
  decreases (4 - SZ.v (!k))
  {
    with v. assert (A.pts_to out v);
    let vk = !k;
    let x = A.(r.(vk));
    narrow_ok (vals128 w2) (SZ.v vk);
    let y = narrow128 x;
    A.((out.(vk) <- y));
    vals_upd v (SZ.v vk) y;
    k := SZ.add vk 1sz;
  };
  with vo2. assert (A.pts_to out vo2);
  assert (pure (vals vo2 `Seq.equal` Seq.slice (redcn d (vals128 vt)) 0 nl));
  assert (pure (vat (redcn d (vals128 vt)) nl <= 1));
  assert_norm (1 < pow2 64);
  let hi = A.(r.(4sz));
  narrow128 hi
}

#pop-options

#push-options "--z3rlimit 300"

[@@ FStar.Attributes.CInline]
fn mmul_op (out: A.array S64.t) (a b: A.array S64.t) (p t r s: A.array S128.t)
           (ms nm: A.array S64.t) (mu: S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vp: erased (Seq.seq S128.t))
           (#vt: erased (Seq.seq S128.t)) (#vr: erased (Seq.seq S128.t))
           (#vs: erased (Seq.seq S128.t))
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
                (vt': Seq.seq S128.t) (vr': Seq.seq S128.t) (vs': Seq.seq S128.t).
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
    least significant -- is the eight-byte group at distance [8 (3 - k)]
    from the start, most significant byte of the limb first. *)

(** The store loop below proves one byte at a time, in the shape the
    writes have; {!Spec.Field4.store_be_ok} wants a single statement
    quantified over both indices.  The bridge is a case analysis on the
    byte's position within its limb, which Z3 will not do on its own, and
    it is done one limb at a time so that the eight facts in play are
    about one value and not about four. *)

#push-options "--z3rlimit 200"

let store_be_byte (s: Seq.seq nat) (b: Seq.seq S8.t)
                  (k: nat { k < nl }) (m: nat { m < 8 })
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\
                    bat b (8 * (nl - 1 - k)) == (Seq.index s k / pow2 56) % 256 /\
                    bat b (8 * (nl - 1 - k) + 1) == (Seq.index s k / pow2 48) % 256 /\
                    bat b (8 * (nl - 1 - k) + 2) == (Seq.index s k / pow2 40) % 256 /\
                    bat b (8 * (nl - 1 - k) + 3) == (Seq.index s k / pow2 32) % 256 /\
                    bat b (8 * (nl - 1 - k) + 4) == (Seq.index s k / pow2 24) % 256 /\
                    bat b (8 * (nl - 1 - k) + 5) == (Seq.index s k / pow2 16) % 256 /\
                    bat b (8 * (nl - 1 - k) + 6) == (Seq.index s k / pow2 8) % 256 /\
                    bat b (8 * (nl - 1 - k) + 7) == (Seq.index s k / pow2 0) % 256)
          (ensures bat b (8 * (nl - 1 - k) + m) ==
                     (Seq.index s k / pow2 (8 * (7 - m))) % 256)
  = if m = 0 then assert (8 * (7 - m) == 56)
    else if m = 1 then assert (8 * (7 - m) == 48)
    else if m = 2 then assert (8 * (7 - m) == 40)
    else if m = 3 then assert (8 * (7 - m) == 32)
    else if m = 4 then assert (8 * (7 - m) == 24)
    else if m = 5 then assert (8 * (7 - m) == 16)
    else if m = 6 then assert (8 * (7 - m) == 8)
    else assert (8 * (7 - m) == 0)

let store_be_bridge (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\
                    (forall (k: nat). k < nl ==>
                       bat b (8 * (nl - 1 - k)) == (Seq.index s k / pow2 56) % 256 /\
                       bat b (8 * (nl - 1 - k) + 1) == (Seq.index s k / pow2 48) % 256 /\
                       bat b (8 * (nl - 1 - k) + 2) == (Seq.index s k / pow2 40) % 256 /\
                       bat b (8 * (nl - 1 - k) + 3) == (Seq.index s k / pow2 32) % 256 /\
                       bat b (8 * (nl - 1 - k) + 4) == (Seq.index s k / pow2 24) % 256 /\
                       bat b (8 * (nl - 1 - k) + 5) == (Seq.index s k / pow2 16) % 256 /\
                       bat b (8 * (nl - 1 - k) + 6) == (Seq.index s k / pow2 8) % 256 /\
                       bat b (8 * (nl - 1 - k) + 7) == (Seq.index s k / pow2 0) % 256))
          (ensures (forall (k: nat) (m: nat). k < nl /\ m < 8 ==>
                      bat b (8 * (nl - 1 - k) + m) ==
                        (Seq.index s k / pow2 (8 * (7 - m))) % 256))
  = introduce forall (k: nat) (m: nat). (k < nl /\ m < 8) ==>
      bat b (8 * (nl - 1 - k) + m) == (Seq.index s k / pow2 (8 * (7 - m))) % 256
    with introduce _ ==> _
    with store_be_byte s b k m

#pop-options

#push-options "--z3rlimit 400"

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
  assert_norm (72057594037927936 * (pow2 8 - 1) + 281474976710656 * (pow2 8 - 1) +
               1099511627776 * (pow2 8 - 1) + 4294967296 * (pow2 8 - 1) +
               16777216 * (pow2 8 - 1) + 65536 * (pow2 8 - 1) +
               256 * (pow2 8 - 1) + (pow2 8 - 1) < pow2 64);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 4 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == be_oct vb nl k))
  decreases (4 - SZ.v (!i))
  {
    let vi = !i;
    let pos = SZ.mul 8sz (SZ.sub 3sz vi);
    let b0 = A.(b.(pos));
    let b1 = A.(b.(SZ.add pos 1sz));
    let b2 = A.(b.(SZ.add pos 2sz));
    let b3 = A.(b.(SZ.add pos 3sz));
    let b4 = A.(b.(SZ.add pos 4sz));
    let b5 = A.(b.(SZ.add pos 5sz));
    let b6 = A.(b.(SZ.add pos 6sz));
    let b7 = A.(b.(SZ.add pos 7sz));
    let w = addw (addw (addw (mulk 72057594037927936uL (Cast.u8_to_u64 b0))
                             (mulk 281474976710656uL (Cast.u8_to_u64 b1)))
                       (addw (mulk 1099511627776uL (Cast.u8_to_u64 b2))
                             (mulk 4294967296uL (Cast.u8_to_u64 b3))))
                 (addw (addw (mulk 16777216uL (Cast.u8_to_u64 b4))
                             (mulk 65536uL (Cast.u8_to_u64 b5)))
                       (addw (mulk 256uL (Cast.u8_to_u64 b6))
                             (Cast.u8_to_u64 b7)));
    A.((a.(vi) <- w));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  assert (pure (forall (k: nat). k < nl ==> Seq.index (vals v) k == be_oct vb nl k));
  eval_bytes_be vb (vals v);
  assert_norm (72057594037927936 * (pow2 8 - 1) + 281474976710656 * (pow2 8 - 1) +
               1099511627776 * (pow2 8 - 1) + 4294967296 * (pow2 8 - 1) +
               16777216 * (pow2 8 - 1) + 65536 * (pow2 8 - 1) +
               256 * (pow2 8 - 1) + (pow2 8 - 1) < base);
}

#pop-options

#push-options "--z3rlimit 600"

[@@ FStar.Attributes.CInline]
(** One more limb's worth of bytes in the loop invariant of {!store_be}: the
    trichotomy is trivial, but it is the kind of step the solver will not
    reach once the eight writes of the body are in scope. *)
let store_be_extend (v: Seq.seq S8.t) (s: Seq.seq nat) (n: nat { n < nl })
  : Lemma (requires Seq.length v == 32 /\ Seq.length s == nl /\
                    (forall (k: nat). k < n ==>
                       S8.v (Seq.index v (8 * (nl - 1 - k))) == Seq.index s k / pow2 56 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 1)) == Seq.index s k / pow2 48 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 2)) == Seq.index s k / pow2 40 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 3)) == Seq.index s k / pow2 32 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 4)) == Seq.index s k / pow2 24 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 5)) == Seq.index s k / pow2 16 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 6)) == Seq.index s k / pow2 8 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 7)) == Seq.index s k / pow2 0 % 256) /\
                    S8.v (Seq.index v (8 * (nl - 1 - n))) == Seq.index s n / pow2 56 % 256 /\
                    S8.v (Seq.index v (8 * (nl - 1 - n) + 1)) == Seq.index s n / pow2 48 % 256 /\
                    S8.v (Seq.index v (8 * (nl - 1 - n) + 2)) == Seq.index s n / pow2 40 % 256 /\
                    S8.v (Seq.index v (8 * (nl - 1 - n) + 3)) == Seq.index s n / pow2 32 % 256 /\
                    S8.v (Seq.index v (8 * (nl - 1 - n) + 4)) == Seq.index s n / pow2 24 % 256 /\
                    S8.v (Seq.index v (8 * (nl - 1 - n) + 5)) == Seq.index s n / pow2 16 % 256 /\
                    S8.v (Seq.index v (8 * (nl - 1 - n) + 6)) == Seq.index s n / pow2 8 % 256 /\
                    S8.v (Seq.index v (8 * (nl - 1 - n) + 7)) == Seq.index s n / pow2 0 % 256)
          (ensures (forall (k: nat). k < n + 1 ==>
                       S8.v (Seq.index v (8 * (nl - 1 - k))) == Seq.index s k / pow2 56 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 1)) == Seq.index s k / pow2 48 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 2)) == Seq.index s k / pow2 40 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 3)) == Seq.index s k / pow2 32 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 4)) == Seq.index s k / pow2 24 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 5)) == Seq.index s k / pow2 16 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 6)) == Seq.index s k / pow2 8 % 256 /\
                       S8.v (Seq.index v (8 * (nl - 1 - k) + 7)) == Seq.index s k / pow2 0 % 256))
  = ()

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
  assert_norm (pow2 8 == 256);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 4 /\ Seq.length v == 32 /\
          (forall (k: nat). k < SZ.v vi ==>
             S8.v (Seq.index v (8 * (nl - 1 - k))) == Seq.index (vals va) k / pow2 56 % 256 /\
             S8.v (Seq.index v (8 * (nl - 1 - k) + 1)) == Seq.index (vals va) k / pow2 48 % 256 /\
             S8.v (Seq.index v (8 * (nl - 1 - k) + 2)) == Seq.index (vals va) k / pow2 40 % 256 /\
             S8.v (Seq.index v (8 * (nl - 1 - k) + 3)) == Seq.index (vals va) k / pow2 32 % 256 /\
             S8.v (Seq.index v (8 * (nl - 1 - k) + 4)) == Seq.index (vals va) k / pow2 24 % 256 /\
             S8.v (Seq.index v (8 * (nl - 1 - k) + 5)) == Seq.index (vals va) k / pow2 16 % 256 /\
             S8.v (Seq.index v (8 * (nl - 1 - k) + 6)) == Seq.index (vals va) k / pow2 8 % 256 /\
             S8.v (Seq.index v (8 * (nl - 1 - k) + 7)) == Seq.index (vals va) k / pow2 0 % 256))
  decreases (4 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let pos = SZ.mul 8sz (SZ.sub 3sz vi);
    A.((b.(pos) <- Cast.u64_to_u8 (S64.shift_right x 56ul)));
    A.((b.(SZ.add pos 1sz) <- Cast.u64_to_u8 (S64.shift_right x 48ul)));
    A.((b.(SZ.add pos 2sz) <- Cast.u64_to_u8 (S64.shift_right x 40ul)));
    A.((b.(SZ.add pos 3sz) <- Cast.u64_to_u8 (S64.shift_right x 32ul)));
    A.((b.(SZ.add pos 4sz) <- Cast.u64_to_u8 (S64.shift_right x 24ul)));
    A.((b.(SZ.add pos 5sz) <- Cast.u64_to_u8 (S64.shift_right x 16ul)));
    A.((b.(SZ.add pos 6sz) <- Cast.u64_to_u8 (S64.shift_right x 8ul)));
    A.((b.(SZ.add pos 7sz) <- Cast.u64_to_u8 x));
    with v. assert (A.pts_to b v);
    assert (pure (
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)))) == Seq.index (vals va) (SZ.v vi) / pow2 56 % 256 /\
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)) + 1)) == Seq.index (vals va) (SZ.v vi) / pow2 48 % 256 /\
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)) + 2)) == Seq.index (vals va) (SZ.v vi) / pow2 40 % 256 /\
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)) + 3)) == Seq.index (vals va) (SZ.v vi) / pow2 32 % 256 /\
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)) + 4)) == Seq.index (vals va) (SZ.v vi) / pow2 24 % 256 /\
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)) + 5)) == Seq.index (vals va) (SZ.v vi) / pow2 16 % 256 /\
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)) + 6)) == Seq.index (vals va) (SZ.v vi) / pow2 8 % 256 /\
      S8.v (Seq.index v (8 * (nl - 1 - (SZ.v vi)) + 7)) == Seq.index (vals va) (SZ.v vi) / pow2 0 % 256));
    store_be_extend v (vals va) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  assert (pure (Seq.length v == 32 /\ bnd (vals va) base));
  store_be_bridge (vals va) v;
  store_be_ok (vals va) v;
  assert (pure (v == nat_to_be 32 (eval (vals va))));
}

#pop-options

#pop-options
