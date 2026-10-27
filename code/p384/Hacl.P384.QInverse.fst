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

(** Inversion in P-384's scalar field by an addition chain.

    [x^(n-2)] on {!Hacl.P384.QField}, in place of the generic Montgomery
    exponentiation.  The top 192 bits of [n - 2] are ones, so the chain
    first builds [x_192 = x^(2^192 - 1)] by doubling
    ([x_2, x_4, ..., x_128, x_192]), then runs a sliding window of width
    four over the low 192 bits with the odd powers [x, x^3, ..., x^15]:
    three hundred and eighty-four squarings and fifty-four
    multiplications.  The exponent is public and fixed, so the sequence of
    operations, and hence the time, is independent of the input.

    Generated, steps and all, by a short script; each step is
    [sqrn_mul], which says what it does to the exponent, so the proof is
    arithmetic on constants. *)
module Hacl.P384.QInverse

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Bignum.Base
open Hacl.P384.QField

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module MA = Spec.ModArith
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60 --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

[@@"opaque_to_smt"]
let ex (b: P.qelem) (e: nat) : P.qelem = MA.exp #P.order b e

(** [x_k]'s exponent. *)
let m1 (k: nat) : nat = pow2 k - 1


(** The exponents after each window step. *)
[@@"opaque_to_smt"] let e0 : nat = m1 192 * pow2 2 + 3
[@@"opaque_to_smt"] let e1 : nat = e0 * pow2 6 + 7
[@@"opaque_to_smt"] let e2 : nat = e1 * pow2 3 + 3
[@@"opaque_to_smt"] let e3 : nat = e2 * pow2 7 + 13
[@@"opaque_to_smt"] let e4 : nat = e3 * pow2 6 + 13
[@@"opaque_to_smt"] let e5 : nat = e4 * pow2 1 + 1
[@@"opaque_to_smt"] let e6 : nat = e5 * pow2 10 + 15
[@@"opaque_to_smt"] let e7 : nat = e6 * pow2 3 + 5
[@@"opaque_to_smt"] let e8 : nat = e7 * pow2 8 + 13
[@@"opaque_to_smt"] let e9 : nat = e8 * pow2 2 + 3
[@@"opaque_to_smt"] let e10 : nat = e9 * pow2 6 + 11
[@@"opaque_to_smt"] let e11 : nat = e10 * pow2 4 + 7
[@@"opaque_to_smt"] let e12 : nat = e11 * pow2 5 + 15
[@@"opaque_to_smt"] let e13 : nat = e12 * pow2 3 + 5
[@@"opaque_to_smt"] let e14 : nat = e13 * pow2 3 + 3
[@@"opaque_to_smt"] let e15 : nat = e14 * pow2 10 + 13
[@@"opaque_to_smt"] let e16 : nat = e15 * pow2 9 + 13
[@@"opaque_to_smt"] let e17 : nat = e16 * pow2 4 + 11
[@@"opaque_to_smt"] let e18 : nat = e17 * pow2 6 + 9
[@@"opaque_to_smt"] let e19 : nat = e18 * pow2 3 + 1
[@@"opaque_to_smt"] let e20 : nat = e19 * pow2 7 + 11
[@@"opaque_to_smt"] let e21 : nat = e20 * pow2 7 + 5
[@@"opaque_to_smt"] let e22 : nat = e21 * pow2 5 + 7
[@@"opaque_to_smt"] let e23 : nat = e22 * pow2 5 + 15
[@@"opaque_to_smt"] let e24 : nat = e23 * pow2 5 + 11
[@@"opaque_to_smt"] let e25 : nat = e24 * pow2 4 + 11
[@@"opaque_to_smt"] let e26 : nat = e25 * pow2 5 + 7
[@@"opaque_to_smt"] let e27 : nat = e26 * pow2 3 + 3
[@@"opaque_to_smt"] let e28 : nat = e27 * pow2 7 + 3
[@@"opaque_to_smt"] let e29 : nat = e28 * pow2 6 + 11
[@@"opaque_to_smt"] let e30 : nat = e29 * pow2 4 + 5
[@@"opaque_to_smt"] let e31 : nat = e30 * pow2 3 + 3
[@@"opaque_to_smt"] let e32 : nat = e31 * pow2 4 + 3
[@@"opaque_to_smt"] let e33 : nat = e32 * pow2 4 + 3
[@@"opaque_to_smt"] let e34 : nat = e33 * pow2 6 + 5
[@@"opaque_to_smt"] let e35 : nat = e34 * pow2 5 + 5
[@@"opaque_to_smt"] let e36 : nat = e35 * pow2 6 + 11
[@@"opaque_to_smt"] let e37 : nat = e36 * pow2 1 + 1
[@@"opaque_to_smt"] let e38 : nat = e37 * pow2 4 + 1

let sq_pow (b: P.qelem) (k: nat)
  : Lemma (P.qmul (ex b (pow2 k)) (ex b (pow2 k)) == ex b (pow2 (k + 1)))
  = reveal_opaque (`%ex) ex;
    MA.exp_two #P.order (ex b (pow2 k));
    MA.exp_mul #P.order b (pow2 k) 2;
    Math.pow2_double_mult k

let step_lem (b: P.qelem) (e1 e2 n: nat)
  : Lemma (P.qmul (ex (ex b e1) (pow2 n)) (ex b e2) == ex b (e1 * pow2 n + e2))
  = reveal_opaque (`%ex) ex;
    MA.exp_mul #P.order b e1 (pow2 n);
    MA.exp_add #P.order b (e1 * pow2 n) e2

let ex_one (b: P.qelem) : Lemma (ex b 1 == b) =
  reveal_opaque (`%ex) ex; MA.exp_one #P.order b

let ex_inv (b: P.qelem) : Lemma (ex b (P.order - 2) == P.qinv b) =
  reveal_opaque (`%ex) ex

let sq1 (b x y: P.qelem) (k: nat)
  : Lemma (requires x == ex b (pow2 k) /\ y == P.qmul x x)
          (ensures y == ex b (pow2 (k + 1)))
  = sq_pow b k

let sq2 (b x y z: P.qelem) (k: nat)
  : Lemma (requires x == ex b (pow2 (2 * k)) /\ y == P.qmul x x /\ z == P.qmul y y)
          (ensures z == ex b (pow2 (2 * (k + 1))))
  = sq_pow b (2 * k); sq_pow b (2 * k + 1)

let nb (h: SZ.t) (odd: bool) : nat = 2 * SZ.v h + (if odd then 1 else 0)

(** [a := a^(2^n)] with [n = 2h + odd], squaring back and forth between
    [a] and [t]. *)
fn sqrn (a t: A.array S64.t) (h: SZ.t) (odd: bool)
        (#va #vt: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to t vt **
  pure (qelem va /\ Seq.length vt == 6)
ensures exists* (va' vt': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to t vt' **
  pure (qelem va' /\ Seq.length vt' == 6 /\
        qev va' == ex (qev va) (pow2 (nb h odd)))
{
  ex_one (qev va);
  assert_norm (pow2 0 == 1);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi h)
  invariant exists* (vi: SZ.t) (v u: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to t u **
    pure (SZ.v vi <= SZ.v h /\ qelem v /\ Seq.length u == 6 /\
          qev v == ex (qev va) (pow2 (2 * SZ.v vi)))
  decreases (SZ.v h - SZ.v (!i))
  {
    let vi = !i;
    with v0. assert (A.pts_to a v0);
    qsqr t a;
    with u1. assert (A.pts_to t u1);
    qsqr a t;
    with v2. assert (A.pts_to a v2);
    sq2 (qev va) (qev v0) (qev u1) (qev v2) (SZ.v vi);
    SZ.fits_lte (SZ.v vi + 1) (SZ.v h);
    i := SZ.add vi 1sz;
  };
  if odd {
    with v0. assert (A.pts_to a v0);
    qsqr t a;
    with u1. assert (A.pts_to t u1);
    sq1 (qev va) (qev v0) (qev u1) (2 * SZ.v h);
    assert (pure (nb h odd == 2 * SZ.v h + 1));
    qcopy a t;
  } else {
    assert (pure (nb h odd == 2 * SZ.v h));
  }
}

(** [acc := acc^(2^n) * y]: on exponents of [b], [e1, e2 -> e1 2^n + e2]. *)
fn sqrn_mul (acc t y: A.array S64.t) (h: SZ.t) (odd: bool) (n: erased nat)
            (b: erased P.qelem) (e1 e2 e: erased nat)
            (#vacc #vt: erased (Seq.seq S64.t))
            (#py: perm) (#vy: erased (Seq.seq S64.t))
requires A.pts_to acc vacc ** A.pts_to t vt ** A.pts_to y #py vy **
  pure (qelem vacc /\ Seq.length vt == 6 /\ qelem vy /\ reveal n == nb h odd /\
        reveal e == e1 * pow2 n + e2 /\
        qev vacc == ex b e1 /\ qev vy == ex b e2)
ensures exists* (vacc' vt': Seq.seq S64.t).
  A.pts_to acc vacc' ** A.pts_to t vt' ** A.pts_to y #py vy **
  pure (qelem vacc' /\ Seq.length vt' == 6 /\
        qev vacc' == ex b e)
{
  sqrn acc t h odd;
  qmul t acc y;
  step_lem b e1 e2 (nb h odd);
  qcopy acc t;
}


let add_lem (b: P.qelem) (e1 e2: nat)
  : Lemma (P.qmul (ex b e1) (ex b e2) == ex b (e1 + e2))
  = reveal_opaque (`%ex) ex;
    MA.exp_add #P.order b e1 e2

(** [out := y * z]: on exponents of [b], [e1, e2 -> e1 + e2]. *)
fn mul_step (out y z: A.array S64.t) (b: erased P.qelem) (e1 e2 e: erased nat)
            (#vo: erased (Seq.seq S64.t))
            (#py: perm) (#vy: erased (Seq.seq S64.t))
            (#pz: perm) (#vz: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to y #py vy ** A.pts_to z #pz vz **
  pure (Seq.length vo == 6 /\ qelem vy /\ qelem vz /\ reveal e == e1 + e2 /\
        qev vy == ex b e1 /\ qev vz == ex b e2)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to y #py vy ** A.pts_to z #pz vz **
  pure (qelem vo' /\ qev vo' == ex b e)
{
  qmul out y z;
  with vo'. assert (A.pts_to out vo');
  add_lem b e1 e2;
  assert (pure (qev vo' == P.qmul (ex b e1) (ex b e2)));
  assert (pure (qev vo' == ex b (e1 + e2)));
}

(** [out := y * y]: on exponents of [b], [e1 -> 2 e1]. *)
fn sq_step (out y: A.array S64.t) (b: erased P.qelem) (e1 e: erased nat)
           (#vo: erased (Seq.seq S64.t))
           (#py: perm) (#vy: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to y #py vy **
  pure (Seq.length vo == 6 /\ qelem vy /\ reveal e == e1 + e1 /\ qev vy == ex b e1)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to y #py vy **
  pure (qelem vo' /\ qev vo' == ex b e)
{
  qsqr out y;
  with vo'. assert (A.pts_to out vo');
  add_lem b e1 e1;
  assert (pure (qev vo' == P.qmul (ex b e1) (ex b e1)));
  assert (pure (qev vo' == ex b (e1 + e1)));
}


(** The odd powers [b, b^3, ..., b^15]. *)
let tab_ok (b: P.qelem) (va v3 v5 v7 v9 v11 v13 v15: Seq.seq S64.t) : prop =
  qelem va /\ qelem v3 /\ qelem v5 /\ qelem v7 /\
  qelem v9 /\ qelem v11 /\ qelem v13 /\ qelem v15 /\
  qev va == ex b 1 /\ qev v3 == ex b 3 /\ qev v5 == ex b 5 /\ qev v7 == ex b 7 /\
  qev v9 == ex b 9 /\ qev v11 == ex b 11 /\ qev v13 == ex b 13 /\ qev v15 == ex b 15

(** Window steps 0 to 7. *)
fn win0 (out t a x3 x5 x7 x9 x11 x13 x15: A.array S64.t) (b: erased P.qelem)
         (#vo #vt: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t)) (#v3 #v5 #v7 #v9 #v11 #v13 #v15: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo /\ Seq.length vt == 6 /\ tab_ok b va v3 v5 v7 v9 v11 v13 v15 /\ qev vo == ex b (m1 192))
ensures exists* (vo' vt': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo' /\ Seq.length vt' == 6 /\ qev vo' == ex b (e7))
{
  assert_norm (m1 192 * pow2 2 + 3 == e0);
  assert (pure (nb 1sz false == 2));
  sqrn_mul out t x3 1sz false 2 b (m1 192) (3) (e0);
  assert_norm (e0 * pow2 6 + 7 == e1);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x7 3sz false 6 b (e0) (7) (e1);
  assert_norm (e1 * pow2 3 + 3 == e2);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x3 1sz true 3 b (e1) (3) (e2);
  assert_norm (e2 * pow2 7 + 13 == e3);
  assert (pure (nb 3sz true == 7));
  sqrn_mul out t x13 3sz true 7 b (e2) (13) (e3);
  assert_norm (e3 * pow2 6 + 13 == e4);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x13 3sz false 6 b (e3) (13) (e4);
  assert_norm (e4 * pow2 1 + 1 == e5);
  assert (pure (nb 0sz true == 1));
  sqrn_mul out t a 0sz true 1 b (e4) (1) (e5);
  assert_norm (e5 * pow2 10 + 15 == e6);
  assert (pure (nb 5sz false == 10));
  sqrn_mul out t x15 5sz false 10 b (e5) (15) (e6);
  assert_norm (e6 * pow2 3 + 5 == e7);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x5 1sz true 3 b (e6) (5) (e7);
}

(** Window steps 8 to 15. *)
fn win1 (out t a x3 x5 x7 x9 x11 x13 x15: A.array S64.t) (b: erased P.qelem)
         (#vo #vt: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t)) (#v3 #v5 #v7 #v9 #v11 #v13 #v15: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo /\ Seq.length vt == 6 /\ tab_ok b va v3 v5 v7 v9 v11 v13 v15 /\ qev vo == ex b (e7))
ensures exists* (vo' vt': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo' /\ Seq.length vt' == 6 /\ qev vo' == ex b (e15))
{
  assert_norm (e7 * pow2 8 + 13 == e8);
  assert (pure (nb 4sz false == 8));
  sqrn_mul out t x13 4sz false 8 b (e7) (13) (e8);
  assert_norm (e8 * pow2 2 + 3 == e9);
  assert (pure (nb 1sz false == 2));
  sqrn_mul out t x3 1sz false 2 b (e8) (3) (e9);
  assert_norm (e9 * pow2 6 + 11 == e10);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x11 3sz false 6 b (e9) (11) (e10);
  assert_norm (e10 * pow2 4 + 7 == e11);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t x7 2sz false 4 b (e10) (7) (e11);
  assert_norm (e11 * pow2 5 + 15 == e12);
  assert (pure (nb 2sz true == 5));
  sqrn_mul out t x15 2sz true 5 b (e11) (15) (e12);
  assert_norm (e12 * pow2 3 + 5 == e13);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x5 1sz true 3 b (e12) (5) (e13);
  assert_norm (e13 * pow2 3 + 3 == e14);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x3 1sz true 3 b (e13) (3) (e14);
  assert_norm (e14 * pow2 10 + 13 == e15);
  assert (pure (nb 5sz false == 10));
  sqrn_mul out t x13 5sz false 10 b (e14) (13) (e15);
}

(** Window steps 16 to 23. *)
fn win2 (out t a x3 x5 x7 x9 x11 x13 x15: A.array S64.t) (b: erased P.qelem)
         (#vo #vt: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t)) (#v3 #v5 #v7 #v9 #v11 #v13 #v15: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo /\ Seq.length vt == 6 /\ tab_ok b va v3 v5 v7 v9 v11 v13 v15 /\ qev vo == ex b (e15))
ensures exists* (vo' vt': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo' /\ Seq.length vt' == 6 /\ qev vo' == ex b (e23))
{
  assert_norm (e15 * pow2 9 + 13 == e16);
  assert (pure (nb 4sz true == 9));
  sqrn_mul out t x13 4sz true 9 b (e15) (13) (e16);
  assert_norm (e16 * pow2 4 + 11 == e17);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t x11 2sz false 4 b (e16) (11) (e17);
  assert_norm (e17 * pow2 6 + 9 == e18);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x9 3sz false 6 b (e17) (9) (e18);
  assert_norm (e18 * pow2 3 + 1 == e19);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t a 1sz true 3 b (e18) (1) (e19);
  assert_norm (e19 * pow2 7 + 11 == e20);
  assert (pure (nb 3sz true == 7));
  sqrn_mul out t x11 3sz true 7 b (e19) (11) (e20);
  assert_norm (e20 * pow2 7 + 5 == e21);
  assert (pure (nb 3sz true == 7));
  sqrn_mul out t x5 3sz true 7 b (e20) (5) (e21);
  assert_norm (e21 * pow2 5 + 7 == e22);
  assert (pure (nb 2sz true == 5));
  sqrn_mul out t x7 2sz true 5 b (e21) (7) (e22);
  assert_norm (e22 * pow2 5 + 15 == e23);
  assert (pure (nb 2sz true == 5));
  sqrn_mul out t x15 2sz true 5 b (e22) (15) (e23);
}

(** Window steps 24 to 31. *)
fn win3 (out t a x3 x5 x7 x9 x11 x13 x15: A.array S64.t) (b: erased P.qelem)
         (#vo #vt: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t)) (#v3 #v5 #v7 #v9 #v11 #v13 #v15: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo /\ Seq.length vt == 6 /\ tab_ok b va v3 v5 v7 v9 v11 v13 v15 /\ qev vo == ex b (e23))
ensures exists* (vo' vt': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo' /\ Seq.length vt' == 6 /\ qev vo' == ex b (e31))
{
  assert_norm (e23 * pow2 5 + 11 == e24);
  assert (pure (nb 2sz true == 5));
  sqrn_mul out t x11 2sz true 5 b (e23) (11) (e24);
  assert_norm (e24 * pow2 4 + 11 == e25);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t x11 2sz false 4 b (e24) (11) (e25);
  assert_norm (e25 * pow2 5 + 7 == e26);
  assert (pure (nb 2sz true == 5));
  sqrn_mul out t x7 2sz true 5 b (e25) (7) (e26);
  assert_norm (e26 * pow2 3 + 3 == e27);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x3 1sz true 3 b (e26) (3) (e27);
  assert_norm (e27 * pow2 7 + 3 == e28);
  assert (pure (nb 3sz true == 7));
  sqrn_mul out t x3 3sz true 7 b (e27) (3) (e28);
  assert_norm (e28 * pow2 6 + 11 == e29);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x11 3sz false 6 b (e28) (11) (e29);
  assert_norm (e29 * pow2 4 + 5 == e30);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t x5 2sz false 4 b (e29) (5) (e30);
  assert_norm (e30 * pow2 3 + 3 == e31);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x3 1sz true 3 b (e30) (3) (e31);
}

(** Window steps 32 to 38. *)
fn win4 (out t a x3 x5 x7 x9 x11 x13 x15: A.array S64.t) (b: erased P.qelem)
         (#vo #vt: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t)) (#v3 #v5 #v7 #v9 #v11 #v13 #v15: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo /\ Seq.length vt == 6 /\ tab_ok b va v3 v5 v7 v9 v11 v13 v15 /\ qev vo == ex b (e31))
ensures exists* (vo' vt': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to x3 v3 ** A.pts_to x5 v5 ** A.pts_to x7 v7 ** A.pts_to x9 v9 ** A.pts_to x11 v11 ** A.pts_to x13 v13 ** A.pts_to x15 v15 **
  pure (qelem vo' /\ Seq.length vt' == 6 /\ qev vo' == ex b (e38))
{
  assert_norm (e31 * pow2 4 + 3 == e32);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t x3 2sz false 4 b (e31) (3) (e32);
  assert_norm (e32 * pow2 4 + 3 == e33);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t x3 2sz false 4 b (e32) (3) (e33);
  assert_norm (e33 * pow2 6 + 5 == e34);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x5 3sz false 6 b (e33) (5) (e34);
  assert_norm (e34 * pow2 5 + 5 == e35);
  assert (pure (nb 2sz true == 5));
  sqrn_mul out t x5 2sz true 5 b (e34) (5) (e35);
  assert_norm (e35 * pow2 6 + 11 == e36);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x11 3sz false 6 b (e35) (11) (e36);
  assert_norm (e36 * pow2 1 + 1 == e37);
  assert (pure (nb 0sz true == 1));
  sqrn_mul out t a 0sz true 1 b (e36) (1) (e37);
  assert_norm (e37 * pow2 4 + 1 == e38);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t a 2sz false 4 b (e37) (1) (e38);
}

#push-options "--z3rlimit 200"

(** [out = a^(n-2)], the inverse of [a] (and zero for zero). *)
fn qinv (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == P.qinv (qev va))
{
  let b = Ghost.elift1 qev va;
  ex_one (qev va);
  assert (pure (reveal b == qev va));
  assert (pure (qev va == ex b 1));
  let z = S64.zero;
  let mut t = [| z; 6sz |];
  Mem.track t; A.pts_to_len t; let mut y = [| z; 6sz |];
  Mem.track y; A.pts_to_len y; let mut x2 = [| z; 6sz |];
  Mem.track x2; A.pts_to_len x2; let mut x3 = [| z; 6sz |];
  Mem.track x3; A.pts_to_len x3; let mut x5 = [| z; 6sz |];
  Mem.track x5; A.pts_to_len x5; let mut x7 = [| z; 6sz |];
  Mem.track x7; A.pts_to_len x7; let mut x9 = [| z; 6sz |];
  Mem.track x9; A.pts_to_len x9; let mut x11 = [| z; 6sz |];
  Mem.track x11; A.pts_to_len x11; let mut x13 = [| z; 6sz |];
  Mem.track x13; A.pts_to_len x13; let mut x15 = [| z; 6sz |];
  Mem.track x15; A.pts_to_len x15;
  A.pts_to_len out;
  sq_step x2 a b 1 2;
  mul_step x3 x2 a b 2 1 3;
  mul_step x5 x3 x2 b 3 2 5;
  mul_step x7 x5 x2 b 5 2 7;
  mul_step x9 x7 x2 b 7 2 9;
  mul_step x11 x9 x2 b 9 2 11;
  mul_step x13 x11 x2 b 11 2 13;
  mul_step x15 x13 x2 b 13 2 15;
  qcopy out x3;
  assert_norm (m1 2 == 3);
  qcopy y out;
  assert_norm (m1 2 * pow2 2 + m1 2 == m1 4);
  assert (pure (nb 1sz false == 2));
  sqrn_mul out t y 1sz false 2 b (m1 2) (m1 2) (m1 4);
  qcopy y out;
  assert_norm (m1 4 * pow2 4 + m1 4 == m1 8);
  assert (pure (nb 2sz false == 4));
  sqrn_mul out t y 2sz false 4 b (m1 4) (m1 4) (m1 8);
  qcopy y out;
  assert_norm (m1 8 * pow2 8 + m1 8 == m1 16);
  assert (pure (nb 4sz false == 8));
  sqrn_mul out t y 4sz false 8 b (m1 8) (m1 8) (m1 16);
  qcopy y out;
  assert_norm (m1 16 * pow2 16 + m1 16 == m1 32);
  assert (pure (nb 8sz false == 16));
  sqrn_mul out t y 8sz false 16 b (m1 16) (m1 16) (m1 32);
  qcopy y out;
  assert_norm (m1 32 * pow2 32 + m1 32 == m1 64);
  assert (pure (nb 16sz false == 32));
  sqrn_mul out t y 16sz false 32 b (m1 32) (m1 32) (m1 64);
  qcopy y out;
  assert_norm (m1 64 * pow2 64 + m1 64 == m1 128);
  assert (pure (nb 32sz false == 64));
  sqrn_mul out t y 32sz false 64 b (m1 64) (m1 64) (m1 128);
  assert_norm (m1 128 * pow2 64 + m1 64 == m1 192);
  assert (pure (nb 32sz false == 64));
  sqrn_mul out t y 32sz false 64 b (m1 128) (m1 64) (m1 192);
  win0 out t a x3 x5 x7 x9 x11 x13 x15 b;
  win1 out t a x3 x5 x7 x9 x11 x13 x15 b;
  win2 out t a x3 x5 x7 x9 x11 x13 x15 b;
  win3 out t a x3 x5 x7 x9 x11 x13 x15 b;
  win4 out t a x3 x5 x7 x9 x11 x13 x15 b;
  assert_norm (e38 == P.order - 2);
  ex_inv (qev va);
  Mem.wipe x15 6sz;
  Mem.wipe x13 6sz;
  Mem.wipe x11 6sz;
  Mem.wipe x9 6sz;
  Mem.wipe x7 6sz;
  Mem.wipe x5 6sz;
  Mem.wipe x3 6sz;
  Mem.wipe x2 6sz;
  Mem.wipe y 6sz;
  Mem.wipe t 6sz;
}

#pop-options

(** The inverse of a plain number below the order. *)
fn qinv_plain (out a: A.array S64.t)
              (#vo: erased (Seq.seq S64.t))
              (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ num va < P.order)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == 6 /\ num va < P.order /\ num vo' == P.qinv (num va))
{
  let z = S64.zero;
  let mut am = [| z; 6sz |];
  Mem.track am; A.pts_to_len am; let mut im = [| z; 6sz |];
  Mem.track im; A.pts_to_len im;
  qto am a;
  qinv im am;
  qfrom out im;
  Mem.wipe im 6sz;
  Mem.wipe am 6sz;
}

#pop-options
