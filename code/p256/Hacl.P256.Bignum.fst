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

    [Spec.P256.Field] says what the four operations are; this module runs
    them.  Everything is parameterised by the modulus bundle, which arrives
    as two sixteen-limb slices -- the modulus [ms] and its two's complement
    [nm] -- and one word [mu].  P-256 has two such bundles, the field prime
    and the group order, and both go through the same code.

    {b Shape of the workspace.}  Nothing here allocates.  A multiplication
    needs thirty-one columns for the schoolbook product, thirty-three for
    the reduction to run in, and sixteen for the conditional subtraction to
    keep its second candidate; an addition or a subtraction needs only the
    last of those three.  They are passed in, and {!Hacl.P256.Field} is
    where they acquire names.

    {b Constant time.}  The only decisions are on loop counters.  The
    conditional subtractions compare with [gte_mask] and commit with
    [Hacl.Impl.Limb.cselect]; no secret ever reaches an [if]. *)
module Hacl.P256.Bignum

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.Montgomery256
open Spec.P256.Field
open Hacl.Impl.Limb

module S = Pulse.Lib.Slice
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module S64 = Hacl.Secret.UInt64
module Loops = Hacl.Spec.Loops

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

fn mstep_op (t ms: S.slice S64.t) (mu: S64.t) (i: SZ.t) (c: erased nat)
            (#vt: erased (Seq.seq S64.t))
            (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires S.pts_to t vt ** S.pts_to ms #pm vms **
  pure (Seq.length vms == nl /\ SZ.v i + nl <= Seq.length vt /\
        mont_ok (vals vms) (S64.v mu) /\ ble (vals vt) c /\ c <= pow2 40)
ensures exists* (vt': Seq.seq S64.t).
  S.pts_to t vt' ** S.pts_to ms #pm vms **
  pure (Seq.length vt' == Seq.length vt /\
        vals vt' == mstep (vals vms) (S64.v mu) (SZ.v i) (vals vt))
{
  S.pts_to_len t;
  S.pts_to_len ms;
  assert_norm ((base - 1) * (base - 1) < pow2 32);
  assert_norm (pow2 40 + pow2 32 < pow2 64);
  assert_norm (pow2 40 + pow2 32 + pow2 40 < pow2 64);
  assert_norm (pow2 40 * (base - 1) < pow2 64);
  let ti = S.(t.(i));
  Math.lemma_mult_le_left (S64.v ti) (S64.v mu) (base - 1);
  Math.lemma_mult_le_right (base - 1) (S64.v ti) c;
  let u = lo16 (mulw ti mu);
  mrow_zero (vals vt) (vals vms) (S64.v u) (SZ.v i);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 16sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S64.t).
    pts_to j vj ** S.pts_to t v ** S.pts_to ms #pm vms **
    pure (SZ.v vj <= 16 /\ Seq.length v == Seq.length vt /\
          vals v == mrow (vals vt) (vals vms) (S64.v u) (SZ.v i) (SZ.v vj))
  decreases (16 - SZ.v (!j))
  {
    with v. assert (S.pts_to t v);
    let vj = !j;
    mrow_ble (vals vt) (vals vms) (S64.v u) (SZ.v i) (SZ.v vj) c;
    let msj = S.(ms.(vj));
    let pos = SZ.add i vj;
    let cur = S.(t.(pos));
    Math.lemma_mult_le_right (S64.v msj) (S64.v u) (base - 1);
    Math.lemma_mult_le_left (base - 1) (S64.v msj) (base - 1);
    let nv = addw cur (mulw u msj);
    S.((t.(pos) <- nv));
    vals_upd v (SZ.v i + SZ.v vj) nv;
    mrow_step (vals vt) (vals vms) (S64.v u) (SZ.v i) (SZ.v vj);
    j := SZ.add vj 1sz;
  };
  mrow_full (vals vt) (vals vms) (S64.v u) (SZ.v i);
  with v. assert (S.pts_to t v);
  assert (pure (vals v == addw (vals vt)
                                (emb (Seq.length vt) (SZ.v i)
                                     (scale (S64.v u) (vals vms)))));
  mrow_ble (vals vt) (vals vms) (S64.v u) (SZ.v i) nl c;
  let x = S.(t.(i));
  let lo = lo16 x;
  let hi = hi16 x;
  S.((t.(i) <- lo));
  vals_upd v (SZ.v i) lo;
  with v1. assert (S.pts_to t v1);
  let ip = SZ.add i 1sz;
  let y = S.(t.(ip));
  let up = addw y hi;
  S.((t.(ip) <- up));
  vals_upd v1 (SZ.v i + 1) up;
  ()
}

#pop-options

(** {2 The sixteen steps}

    Each step raises a column by less than [2^33], so a product's [2^36]
    reaches at most [2^40] and stays inside a word with room to spare. *)

#push-options "--z3rlimit 400"

fn mreduce_op (t ms: S.slice S64.t) (mu: S64.t) (c: erased nat)
              (#vt: erased (Seq.seq S64.t))
              (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires S.pts_to t vt ** S.pts_to ms #pm vms **
  pure (Seq.length vms == nl /\ Seq.length vt == ncol /\
        mont_ok (vals vms) (S64.v mu) /\ ble (vals vt) c /\
        reveal c + nl * pow2 33 <= pow2 40)
ensures exists* (vt': Seq.seq S64.t).
  S.pts_to t vt' ** S.pts_to ms #pm vms **
  pure (Seq.length vt' == ncol /\
        ble (vals vt') (reveal c + nl * pow2 33) /\
        vals vt' == mrun (vals vms) (S64.v mu) nl (vals vt))
{
  S.pts_to_len t;
  S.pts_to_len ms;
  Loops.repeati_zero (mstep (vals vms) (S64.v mu)) (vals vt);
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 16sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** S.pts_to t v ** S.pts_to ms #pm vms **
    pure (SZ.v vk <= 16 /\ Seq.length v == ncol /\
          vals v == mrun (vals vms) (S64.v mu) (SZ.v vk) (vals vt) /\
          ble (vals v) (reveal c + SZ.v vk * pow2 33))
  decreases (16 - SZ.v (!k))
  {
    with v. assert (S.pts_to t v);
    let vk = !k;
    Math.lemma_mult_le_right (pow2 33) (SZ.v vk) nl;
    mstep_op t ms mu vk (reveal c + SZ.v vk * pow2 33);
    mstep_ble (vals vms) (S64.v mu) (SZ.v vk) (vals v) (reveal c + SZ.v vk * pow2 33);
    Loops.unfold_repeati (SZ.v vk) (mstep (vals vms) (S64.v mu)) (vals vt);
    Math.distributivity_add_left (SZ.v vk) 1 (pow2 33);
    k := SZ.add vk 1sz;
  };
  ()
}

#pop-options

(** {2 The conditional subtraction}

    Add [2^256 - m] into the spare buffer.  The carry out of that addition,
    together with any carry the caller already had above bit 256, says
    whether the value was at least [m]; when it was, the spare buffer
    already holds the difference. *)

#push-options "--z3rlimit 400"

fn csub_op (a s nm: S.slice S64.t) (top: S64.t) (d: erased modulus)
           (#va: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires S.pts_to a va ** S.pts_to s vs ** S.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length va == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        bnd (vals va) base /\ S64.v top <= 1 /\
        eval (vals va) + pow2 256 * S64.v top < 2 * d.m)
ensures exists* (va': Seq.seq S64.t) (vs': Seq.seq S64.t).
  S.pts_to a va' ** S.pts_to s vs' ** S.pts_to nm #pn vnm **
  pure (Seq.length va' == nl /\ Seq.length vs' == nl /\
        res d (vals va') /\ vals va' == csub d (vals va) (S64.v top))
{
  S.pts_to_len a;
  S.pts_to_len s;
  S.pts_to_len nm;
  assert_norm (2 * base < pow2 64);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to a va ** S.pts_to s v ** S.pts_to nm #pn vnm **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vnm) k))
  decreases (16 - SZ.v (!i))
  {
    with v. assert (S.pts_to s v);
    let vi = !i;
    let x = S.(a.(vi));
    let y = S.(nm.(vi));
    S.((s.(vi) <- addw x y));
    vals_upd v (SZ.v vi) (addw x y);
    i := SZ.add vi 1sz;
  };
  with v. assert (S.pts_to s v);
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
  with va'. assert (S.pts_to a va');
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

fn madd_op (out a b s nm: S.slice S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to s vs ** S.pts_to a #pa va **
  S.pts_to b #pb vb ** S.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
        Seq.length vnm == nl /\ vals vnm == d.nm /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to s vs' ** S.pts_to a #pa va **
  S.pts_to b #pb vb ** S.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        res d (vals vo') /\ vals vo' == madd d (vals va) (vals vb))
{
  S.pts_to_len out;
  S.pts_to_len s;
  S.pts_to_len nm;
  S.pts_to_len a;
  S.pts_to_len b;
  assert_norm (2 * base < pow2 64);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to out v ** S.pts_to s vs ** S.pts_to a #pa va **
    S.pts_to b #pb vb ** S.pts_to nm #pn vnm **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k == Seq.index (vals va) k + Seq.index (vals vb) k))
  decreases (16 - SZ.v (!i))
  {
    with v. assert (S.pts_to out v);
    let vi = !i;
    let x = S.(a.(vi));
    let y = S.(b.(vi));
    S.((out.(vi) <- addw x y));
    vals_upd v (SZ.v vi) (addw x y);
    i := SZ.add vi 1sz;
  };
  with v. assert (S.pts_to out v);
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
  with vo'. assert (S.pts_to out vo');
  assert (pure (vals vo' == madd d (vals va) (vals vb)));
}

#pop-options


(** {2 Subtraction}

    [a - b] is [a + (2^256 - b)], and the two's complement is built one
    limb at a time: every limb gets [2^16 - 1 - b_i], and limb zero gets the
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

fn negsub_op (out a b: S.slice S64.t)
             (#vo: erased (Seq.seq S64.t))
             (#pa: perm) (#va: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
returns co: S64.t
ensures exists* (vo': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (Seq.length vo' == nl /\ bnd (vals vo') base /\
        vals vo' == carry_low (addw (vals va) (negw (vals vb))) /\
        S64.v co == carry_out (addw (vals va) (negw (vals vb))))
{
  S.pts_to_len out;
  S.pts_to_len a;
  S.pts_to_len b;
  assert_norm (2 * base < pow2 64);
  compl_ok (vals vb);
  let top = S64.classify 0xffffuL;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to out v ** S.pts_to a #pa va ** S.pts_to b #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index (vals v) k ==
               Seq.index (vals va) k + Seq.index (compl (vals vb)) k))
  decreases (16 - SZ.v (!i))
  {
    with v. assert (S.pts_to out v);
    let vi = !i;
    let x = S.(a.(vi));
    let y = S.(b.(vi));
    let nv = addw x (subw top y);
    S.((out.(vi) <- nv));
    vals_upd v (SZ.v vi) nv;
    i := SZ.add vi 1sz;
  };
  with v. assert (S.pts_to out v);
  addw_len (vals va) (compl (vals vb));
  assert (pure (vals v `Seq.equal` addw (vals va) (compl (vals vb))));
  let x0 = S.(out.(0sz));
  let nv0 = addw x0 (S64.classify 1uL);
  S.((out.(0sz) <- nv0));
  vals_upd v 0 nv0;
  negw_shape (vals va) (vals vb);
  with v1. assert (S.pts_to out v1);
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

fn addm_op (out s ms: S.slice S64.t) (m: S64.t)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to s vs ** S.pts_to ms #pm vms **
  pure (Seq.length vo == nl /\ Seq.length vs == nl /\ Seq.length vms == nl /\
        bnd (vals vo) base /\ bnd (vals vms) base /\
        (S64.v m == 0 \/ S64.v m == pow2 64 - 1))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to s vs' ** S.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        vals vo' == (if S64.v m = 0 then vals vo
                     else carry_low (addw (vals vo) (vals vms))))
{
  S.pts_to_len out;
  S.pts_to_len s;
  S.pts_to_len ms;
  assert_norm (2 * base < pow2 64);
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 16sz)
  invariant exists* (vj: SZ.t) (v: Seq.seq S64.t).
    pts_to j vj ** S.pts_to out vo ** S.pts_to s v ** S.pts_to ms #pm vms **
    pure (SZ.v vj <= 16 /\ Seq.length v == nl /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index (vals v) k == Seq.index (vals vo) k + Seq.index (vals vms) k))
  decreases (16 - SZ.v (!j))
  {
    with v. assert (S.pts_to s v);
    let vj = !j;
    let x = S.(out.(vj));
    let y = S.(ms.(vj));
    S.((s.(vj) <- addw x y));
    vals_upd v (SZ.v vj) (addw x y);
    j := SZ.add vj 1sz;
  };
  with w. assert (S.pts_to s w);
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

#push-options "--z3rlimit 600"

fn msub_op (out a b s ms: S.slice S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to s vs ** S.pts_to a #pa va **
  S.pts_to b #pb vb ** S.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
        Seq.length vms == nl /\ vals vms == d.ms /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vs': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to s vs' ** S.pts_to a #pa va **
  S.pts_to b #pb vb ** S.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
        res d (vals vo') /\ vals vo' == msub d (vals va) (vals vb))
{
  S.pts_to_len out;
  S.pts_to_len s;
  S.pts_to_len ms;
  let co = negsub_op out a b;
  msub_pre d (vals va) (vals vb);
  with lo. assert (S.pts_to out lo);
  assert (pure (S64.v co <= 1));
  let m = S64.eq_mask co S64.zero;
  assert (pure ((S64.v m == 0) == (S64.v co =!= 0)));
  addm_op out s ms m;
  with vo'. assert (S.pts_to out vo');
  assert (pure (vals vo' == (if S64.v m = 0 then vals lo
                             else carry_low (addw (vals lo) (vals vms)))));
  msub_ok d (vals va) (vals vb);
  assert (pure (vals vo' == msub d (vals va) (vals vb)));
}

#pop-options

(** {2 Multiplication}

    The schoolbook product into thirty-one columns, copied into the
    thirty-three the reduction runs in with the top two cleared. *)

#push-options "--z3rlimit 300"

fn prod_op (t p a b: S.slice S64.t)
           (#vt: erased (Seq.seq S64.t)) (#vp: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires S.pts_to t vt ** S.pts_to p vp ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (Seq.length vt == ncol /\ Seq.length vp == nw /\
        Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
ensures exists* (vt': Seq.seq S64.t) (vp': Seq.seq S64.t).
  S.pts_to t vt' ** S.pts_to p vp' ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (Seq.length vt' == ncol /\ Seq.length vp' == nw /\
        vals vt' == prod (vals va) (vals vb))
{
  S.pts_to_len t;
  S.pts_to_len p;
  S.pts_to_len a;
  S.pts_to_len b;
  assert_norm (nl * ((base - 1) * (base - 1)) + (base - 1) * (base - 1) < pow2 64);
  mul_columns p a b (base - 1);
  with vp1. assert (S.pts_to p vp1);
  let z = S64.zero;
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 31sz)
  invariant exists* (vk: SZ.t) (v: Seq.seq S64.t).
    pts_to k vk ** S.pts_to t v ** S.pts_to p vp1 ** S.pts_to a #pa va **
    S.pts_to b #pb vb **
    pure (SZ.v vk <= 31 /\ Seq.length v == ncol /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index (vals v) j == Seq.index (vals vp1) j))
  decreases (31 - SZ.v (!k))
  {
    with v. assert (S.pts_to t v);
    let vk = !k;
    let x = S.(p.(vk));
    S.((t.(vk) <- x));
    vals_upd v (SZ.v vk) x;
    k := SZ.add vk 1sz;
  };
  with v. assert (S.pts_to t v);
  S.((t.(31sz) <- z));
  vals_upd v 31 z;
  with v2. assert (S.pts_to t v2);
  S.((t.(32sz) <- z));
  vals_upd v2 32 z;
  with v3. assert (S.pts_to t v3);
  assert (pure (vals v3 `Seq.equal` prod (vals va) (vals vb)));
}

#pop-options

(** [Spec.P256.Field.redc] only makes sense on a full-width accumulator,
    and a Pulse [ensures] is elaborated with no [requires] in scope, so the
    postcondition below goes through a total version of it. *)
let redcn (d: modulus) (t: Seq.seq nat) : (r: Seq.seq nat { Seq.length r == nl + 1 }) =
  if Seq.length t = ncol then redc d t else Seq.create (nl + 1) 0

(** The reduction proper: sixteen Montgomery steps, then the upper half
    normalised into sixteen proper limbs and a top carry. *)

#push-options "--z3rlimit 300"

fn redc_op (out t ms: S.slice S64.t) (mu: S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to t vt ** S.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vt == ncol /\
        Seq.length vms == nl /\ vals vms == d.ms /\ S64.v mu == d.mu /\
        ble (vals vt) cmax /\ eval (vals vt) < d.m * pow2 256)
returns top: S64.t
ensures exists* (vo': Seq.seq S64.t) (vt': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to t vt' ** S.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ Seq.length vt' == ncol /\
        vals vo' == Seq.slice (redcn d (vals vt)) 0 nl /\
        S64.v top == vat (redcn d (vals vt)) nl)
{
  S.pts_to_len out;
  S.pts_to_len t;
  S.pts_to_len ms;
  cmax_fits ();
  mreduce_op t ms mu cmax;
  with u. assert (S.pts_to t u);
  mrun_len d.ms d.mu nl (vals vt);
  assert (pure (Seq.slice (vals u) nl ncol == mreduce d.ms d.mu (vals vt)));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** S.pts_to out v ** S.pts_to t u ** S.pts_to ms #pm vms **
    pure (SZ.v vi <= 16 /\ Seq.length v == nl /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index (vals v) j == Seq.index (vals u) (16 + j)))
  decreases (16 - SZ.v (!i))
  {
    with v. assert (S.pts_to out v);
    let vi = !i;
    let x = S.(t.(SZ.add 16sz vi));
    S.((out.(vi) <- x));
    vals_upd v (SZ.v vi) x;
    i := SZ.add vi 1sz;
  };
  with w. assert (S.pts_to out w);
  assert (pure (vals w `Seq.equal`
                Seq.slice (mreduce d.ms d.mu (vals vt)) 0 nl));
  normalize_split (mreduce d.ms d.mu (vals vt));
  assert_norm (cmax + nl * pow2 33 + pow2 25 < base * (pow2 25 + 1));
  assert_norm (cmax + nl * pow2 33 + pow2 25 < pow2 64);
  carry_split_bnd (vals w) (cmax + nl * pow2 33) (pow2 25);
  let co = carry_out_op out (cmax + nl * pow2 33) (pow2 25);
  let hi = S.(t.(32sz));
  assert_norm (pow2 40 + pow2 25 < pow2 64);
  let top = addw hi co;
  top
}

#pop-options

#push-options "--z3rlimit 300"

fn mmul_op (out a b p t s ms nm: S.slice S64.t) (mu: S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vp: erased (Seq.seq S64.t))
           (#vt: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires S.pts_to out vo ** S.pts_to p vp ** S.pts_to t vt ** S.pts_to s vs **
  S.pts_to a #pa va ** S.pts_to b #pb vb **
  S.pts_to ms #pm vms ** S.pts_to nm #pn vnm **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vp == nw /\
        Seq.length vt == ncol /\ Seq.length vs == nl /\
        Seq.length vms == nl /\ Seq.length vnm == nl /\
        vals vms == d.ms /\ vals vnm == d.nm /\ S64.v mu == d.mu /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t) (vp': Seq.seq S64.t)
                (vt': Seq.seq S64.t) (vs': Seq.seq S64.t).
  S.pts_to out vo' ** S.pts_to p vp' ** S.pts_to t vt' ** S.pts_to s vs' **
  S.pts_to a #pa va ** S.pts_to b #pb vb **
  S.pts_to ms #pm vms ** S.pts_to nm #pn vnm **
  pure (Seq.length vo' == nl /\ Seq.length vp' == nw /\
        Seq.length vt' == ncol /\ Seq.length vs' == nl /\
        res d (vals vo') /\ vals vo' == mmul d (vals va) (vals vb))
{
  prod_op t p a b;
  prod_ok (vals va) (vals vb);
  Math.lemma_mult_le_right (eval (vals vb)) (eval (vals va)) (d.m - 1);
  Math.lemma_mult_le_left d.m (eval (vals vb)) (pow2 256);
  let top = redc_op out t ms mu d;
  redc_ok d (prod (vals va) (vals vb));
  csub_op out s nm top d;
  mmul_ok d (vals va) (vals vb);
  with vo'. assert (S.pts_to out vo');
  assert (pure (vals vo' == mmul d (vals va) (vals vb)));
}

#pop-options

#pop-options
