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

(** The scalar field [F_n] of P-384, in Montgomery form.

    The counterpart of {!Hacl.P384.Field} for the group order: six limbs
    holding [x R mod n] with [R = 2^384], read back by [qev].  Only what
    the scalar inversion of {!Hacl.P384.QInverse} needs: the product and
    the square of {!Hacl.P384.Scalar64}, a copy, and the two conversions. *)
module Hacl.P384.QField

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.Bignum.Montgomery
open Hacl.P384.Tables
open Hacl.P384.Lemmas

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Math = FStar.Math.Lemmas
module Mem = Hacl.Mem
module S = Hacl.P384.Scalar64
module W = Spec.Curve25519.Field64

(** [R^-1 mod n]. *)
let rinv : nat =
  8213155180316830564023772752902517460134849974600554980379995049303147060140144611822562736815346652390458105321745

let qelem (v: Seq.seq S64.t) : prop = Seq.length v == 6 /\ num v < P.order

let qev (v: Seq.seq S64.t) : GTot P.qelem = num v * rinv % P.order

let facts (_: unit)
  : Lemma (wt 6 == pow2 384 /\ pow2 384 * rinv % P.order == 1 /\
           SZ.fits 12 /\ P.order == S.qq /\ pow2 384 == W.w6)
  = assert_norm (wt 6 == pow2 384);
    assert_norm (pow2 384 * rinv % P.order == 1);
    SZ.fits_at_least_16 12;
    assert_norm (P.order == S.qq);
    assert_norm (pow2 384 == W.w6)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let num_fv (s: Seq.seq S64.t)
  : Lemma (requires Seq.length s == 6) (ensures num s == S.fv s)
  = let v = vals s in
    let v1 = Seq.slice v 1 6 in
    let v2 = Seq.slice v1 1 5 in
    let v3 = Seq.slice v2 1 4 in
    let v4 = Seq.slice v3 1 3 in
    let v5 = Seq.slice v4 1 2 in
    let v6 = Seq.slice v5 1 1 in
    W.consts ();
    eval_empty v6;
    assert (eval v5 == Seq.index v5 0 + base * eval v6);
    assert (eval v4 == Seq.index v4 0 + base * eval v5);
    assert (eval v3 == Seq.index v3 0 + base * eval v4);
    assert (eval v2 == Seq.index v2 0 + base * eval v3);
    assert (eval v1 == Seq.index v1 0 + base * eval v2);
    assert (eval v == Seq.index v 0 + base * eval v1)
#pop-options

let mul_fv (o a b: nat)
  : Lemma (requires o < S.qq /\ (W.w6 * o) % S.qq == (a * b) % S.qq)
          (ensures o < P.order /\ o * rinv % P.order == P.qmul (a * rinv % P.order) (b * rinv % P.order))
  = facts ();
    mul_lemma P.order (pow2 384) rinv o a b

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn qmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == P.qmul (qev va) (qev vb))
{
  A.pts_to_len a; A.pts_to_len b;
  num_fv va; num_fv vb; facts ();
  S.fmul out a b;
  with vo'. assert (A.pts_to out vo');
  num_fv vo';
  mul_fv (num vo') (num va) (num vb);
  assert (pure (qelem vo'));
  assert (pure (qev vo' == P.qmul (qev va) (qev vb)));
}

fn qsqr (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == P.qmul (qev va) (qev va))
{
  A.pts_to_len a;
  num_fv va; facts ();
  S.fsqr out a;
  with vo'. assert (A.pts_to out vo');
  num_fv vo';
  mul_fv (num vo') (num va) (num va);
  assert (pure (qelem vo'));
  assert (pure (qev vo' == P.qmul (qev va) (qev va)));
}

fn qcopy (dst src: A.array S64.t)
         (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == 6 /\ qelem vs)
ensures exists* (vd': Seq.seq S64.t).
  A.pts_to dst vd' ** A.pts_to src #ps vs **
  pure (qelem vd' /\ qev vd' == qev vs)
{
  copy dst src 6sz;
}

(** [qto] takes six plain limbs below the order. *)
fn qto (out a: A.array S64.t)
       (#vo: erased (Seq.seq S64.t))
       (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ num va < P.order)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == num va)
{
  facts ();
  let qm = qms ();
  let r2 = qr2 ();
  let z = S64.zero;
  let mut t = [| z; 12sz |];
  Mem.track t; A.pts_to_len t;
  mont_mul out a r2 t qm 6sz qmu;
  with vo'. assert (A.pts_to out vo');
  to_lemma P.order (pow2 384) rinv (num vo') (num va);
  Mem.wipe t 12sz;
  drop_table r2;
  drop_table qm;
}

(** [qfrom] gives them back. *)
fn qfrom (out a: A.array S64.t)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == 6 /\ num vo' == qev va)
{
  facts ();
  let qm = qms ();
  let z = S64.zero;
  let mut t = [| z; 12sz |];
  Mem.track t; A.pts_to_len t;
  from_mont out a t qm 6sz qmu;
  with vo'. assert (A.pts_to out vo');
  from_lemma P.order (pow2 384) rinv (num vo') (num va);
  Mem.wipe t 12sz;
  drop_table qm;
}

#pop-options
