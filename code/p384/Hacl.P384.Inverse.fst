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

(** Inversion in P-384's field by an addition chain.

    [x^(p-2)] with three hundred and eighty-five squarings and fourteen
    multiplications on {!Hacl.P384.Field}'s [fsqr] and [fmul], in place of
    the generic constant-time Montgomery exponentiation (which also pays a
    multiplication per bit and a table scan).  The chain is fixed, so the
    time is independent of the input.

    Writing [x_k] for [x^(2^k - 1)], the chain builds
    [x_2, x_3, x_6, x_12, x_15, x_30, x_60, x_120, x_240, x_255] and [x_32],
    and then
    [p - 2 = ((x_255 * 2^33 + x_32) * 2^94 + x_30) * 2^2 + 1]
    in exponent notation.  Each step is [sqrn_mul], which says what it does
    to the exponent, so the proof of the chain is arithmetic on constants. *)
module Hacl.P384.Inverse

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.P384.Field

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
let ex (b: P.felem) (e: nat) : P.felem = MA.exp #P.prime b e

(** [x_k]'s exponent, and the two exponents of the tail. *)
let m1 (k: nat) : nat = pow2 k - 1
let t1 : nat = m1 255 * pow2 33 + m1 32
let t2 : nat = t1 * pow2 94 + m1 30

let sq_pow (b: P.felem) (k: nat)
  : Lemma (P.fmul (ex b (pow2 k)) (ex b (pow2 k)) == ex b (pow2 (k + 1)))
  = reveal_opaque (`%ex) ex;
    MA.exp_two #P.prime (ex b (pow2 k));
    MA.exp_mul #P.prime b (pow2 k) 2;
    Math.pow2_double_mult k

let step_lem (b: P.felem) (e1 e2 n: nat)
  : Lemma (P.fmul (ex (ex b e1) (pow2 n)) (ex b e2) == ex b (e1 * pow2 n + e2))
  = reveal_opaque (`%ex) ex;
    MA.exp_mul #P.prime b e1 (pow2 n);
    MA.exp_add #P.prime b (e1 * pow2 n) e2

let ex_one (b: P.felem) : Lemma (ex b 1 == b) =
  reveal_opaque (`%ex) ex; MA.exp_one #P.prime b

let ex_inv (b: P.felem) : Lemma (ex b (P.prime - 2) == P.finv b) =
  reveal_opaque (`%ex) ex

let sq1 (b x y: P.felem) (k: nat)
  : Lemma (requires x == ex b (pow2 k) /\ y == P.fmul x x)
          (ensures y == ex b (pow2 (k + 1)))
  = sq_pow b k

let sq2 (b x y z: P.felem) (k: nat)
  : Lemma (requires x == ex b (pow2 (2 * k)) /\ y == P.fmul x x /\ z == P.fmul y y)
          (ensures z == ex b (pow2 (2 * (k + 1))))
  = sq_pow b (2 * k); sq_pow b (2 * k + 1)

let nb (h: SZ.t) (odd: bool) : nat = 2 * SZ.v h + (if odd then 1 else 0)

(** [a := a^(2^n)] with [n = 2h + odd], squaring back and forth between
    [a] and [t]. *)
fn sqrn (a t: A.array S64.t) (h: SZ.t) (odd: bool)
        (#va #vt: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to t vt **
  pure (felem va /\ Seq.length vt == 6)
ensures exists* (va' vt': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to t vt' **
  pure (felem va' /\ Seq.length vt' == 6 /\
        fev va' == ex (fev va) (pow2 (nb h odd)))
{
  ex_one (fev va);
  assert_norm (pow2 0 == 1);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi h)
  invariant exists* (vi: SZ.t) (v u: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to t u **
    pure (SZ.v vi <= SZ.v h /\ felem v /\ Seq.length u == 6 /\
          fev v == ex (fev va) (pow2 (2 * SZ.v vi)))
  decreases (SZ.v h - SZ.v (!i))
  {
    let vi = !i;
    with v0. assert (A.pts_to a v0);
    fsqr t a;
    with u1. assert (A.pts_to t u1);
    fsqr a t;
    with v2. assert (A.pts_to a v2);
    sq2 (fev va) (fev v0) (fev u1) (fev v2) (SZ.v vi);
    SZ.fits_lte (SZ.v vi + 1) (SZ.v h);
    i := SZ.add vi 1sz;
  };
  if odd {
    with v0. assert (A.pts_to a v0);
    fsqr t a;
    with u1. assert (A.pts_to t u1);
    sq1 (fev va) (fev v0) (fev u1) (2 * SZ.v h);
    assert (pure (nb h odd == 2 * SZ.v h + 1));
    fcopy a t;
  } else {
    assert (pure (nb h odd == 2 * SZ.v h));
  }
}

(** [acc := acc^(2^n) * y]: on exponents of [b], [e1, e2 -> e1 2^n + e2]. *)
fn sqrn_mul (acc t y: A.array S64.t) (h: SZ.t) (odd: bool) (n: erased nat)
            (b: erased P.felem) (e1 e2 e: erased nat)
            (#vacc #vt: erased (Seq.seq S64.t))
            (#py: perm) (#vy: erased (Seq.seq S64.t))
requires A.pts_to acc vacc ** A.pts_to t vt ** A.pts_to y #py vy **
  pure (felem vacc /\ Seq.length vt == 6 /\ felem vy /\ reveal n == nb h odd /\
        reveal e == e1 * pow2 n + e2 /\
        fev vacc == ex b e1 /\ fev vy == ex b e2)
ensures exists* (vacc' vt': Seq.seq S64.t).
  A.pts_to acc vacc' ** A.pts_to t vt' ** A.pts_to y #py vy **
  pure (felem vacc' /\ Seq.length vt' == 6 /\
        fev vacc' == ex b e)
{
  sqrn acc t h odd;
  fmul t acc y;
  step_lem b e1 e2 (nb h odd);
  fcopy acc t;
}

#push-options "--z3rlimit 200"

(** [out = a^(p-2)], the inverse of [a] (and zero for zero). *)
fn finv (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.finv (fev va))
{
  let b = Ghost.elift1 fev va;
  ex_one (fev va);
  let z = S64.zero;
  let mut t = [| z; 6sz |];
  Mem.track t; A.pts_to_len t; let mut x2 = [| z; 6sz |];
  Mem.track x2; A.pts_to_len x2; let mut x3 = [| z; 6sz |];
  Mem.track x3; A.pts_to_len x3; let mut x15 = [| z; 6sz |];
  Mem.track x15; A.pts_to_len x15; let mut x30 = [| z; 6sz |];
  Mem.track x30; A.pts_to_len x30;
  A.pts_to_len out;

  fcopy out a;
  with vo1. assert (A.pts_to out vo1);
  assert (pure (reveal b == fev va));
  assert (pure (fev vo1 == ex b 1));
  assert_norm (1 * pow2 1 + 1 == 3);
  assert (pure (nb 0sz true == 1));
  sqrn_mul out t a 0sz true 1 b 1 1 3;
  fcopy x2 out;
  assert_norm (3 * pow2 1 + 1 == 7);
  assert (pure (nb 0sz true == 1));
  sqrn_mul out t a 0sz true 1 b 3 1 7;
  fcopy x3 out;
  (* x15 holds x_6 for one step *)
  assert_norm (7 * pow2 3 + 7 == m1 6);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x3 1sz true 3 b 7 7 (m1 6);
  fcopy x15 out;
  assert_norm ((m1 6) * pow2 6 + (m1 6) == m1 12);
  assert (pure (nb 3sz false == 6));
  sqrn_mul out t x15 3sz false 6 b (m1 6) (m1 6) (m1 12);
  assert_norm ((m1 12) * pow2 3 + 7 == m1 15);
  assert (pure (nb 1sz true == 3));
  sqrn_mul out t x3 1sz true 3 b (m1 12) 7 (m1 15);
  fcopy x15 out;
  assert_norm ((m1 15) * pow2 15 + (m1 15) == m1 30);
  assert (pure (nb 7sz true == 15));
  sqrn_mul out t x15 7sz true 15 b (m1 15) (m1 15) (m1 30);
  fcopy x30 out;
  (* x3 is dead: it holds x_60, then x_120, then x_32 *)
  assert_norm ((m1 30) * pow2 30 + (m1 30) == m1 60);
  assert (pure (nb 15sz false == 30));
  sqrn_mul out t x30 15sz false 30 b (m1 30) (m1 30) (m1 60);
  fcopy x3 out;
  assert_norm ((m1 60) * pow2 60 + (m1 60) == m1 120);
  assert (pure (nb 30sz false == 60));
  sqrn_mul out t x3 30sz false 60 b (m1 60) (m1 60) (m1 120);
  fcopy x3 out;
  assert_norm ((m1 120) * pow2 120 + (m1 120) == m1 240);
  assert (pure (nb 60sz false == 120));
  sqrn_mul out t x3 60sz false 120 b (m1 120) (m1 120) (m1 240);
  assert_norm ((m1 240) * pow2 15 + (m1 15) == m1 255);
  assert (pure (nb 7sz true == 15));
  sqrn_mul out t x15 7sz true 15 b (m1 240) (m1 15) (m1 255);
  fcopy x3 x30;
  assert_norm ((m1 30) * pow2 2 + 3 == m1 32);
  assert (pure (nb 1sz false == 2));
  sqrn_mul x3 t x2 1sz false 2 b (m1 30) 3 (m1 32);
  (* the tail: x_255 * 2^33 + x_32, * 2^94 + x_30, * 2^2 + 1 *)
  assert (pure (nb 16sz true == 33));
  sqrn_mul out t x3 16sz true 33 b (m1 255) (m1 32) t1;
  assert (pure (nb 47sz false == 94));
  sqrn_mul out t x30 47sz false 94 b t1 (m1 30) t2;
  assert_norm (t2 * pow2 2 + 1 == P.prime - 2);
  assert (pure (nb 1sz false == 2));
  sqrn_mul out t a 1sz false 2 b t2 1 (P.prime - 2);
  ex_inv (fev va);
  Mem.wipe x30 6sz;
  Mem.wipe x15 6sz;
  Mem.wipe x3 6sz;
  Mem.wipe x2 6sz;
  Mem.wipe t 6sz;
}

#pop-options

#pop-options
