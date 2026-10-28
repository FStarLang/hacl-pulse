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

(** A run of doublings in Jacobian coordinates, related to the homogeneous
    group law.

    The polynomial identities are in {!Spec.P256.JacChecks}; this module
    adds the two things they cannot say.  One is that the triple stays
    nonzero: a Jacobian point with [Z <> 0] has [Y <> 0] (the curve has no
    point of order two, {!Spec.P256.GroupNR.no_root_f}), so the doubled
    [Z = 2 Y Z] is again nonzero.  The other is infinity, which has no
    Jacobian representative with [Z <> 0]; it is carried as the fixed
    triple {!jinf}, a fixed point of {!jdouble}, and {!to_j} picks it when
    [Z = 0].

    {!jr} is the invariant a run of doublings keeps: "this Jacobian triple
    reads as a point equivalent to [e] copies of [p]". *)
module Spec.P256.Jac

open Spec.P256
open Spec.P256.JacSv
module S = Spec.P256.GroupSv
module NR = Spec.P256.GroupNR
module K = Spec.P256.GroupChecks
module JK = Spec.P256.JacChecks
module GR = Spec.P256.Group
module SM = Spec.P256.Smul
module Pj = Spec.Group.Proj
module F = Spec.Group.Field
module M = FStar.Math.Lemmas

let jinf : proj_point = (fone, fone, fzero)

(** Homogeneous to Jacobian. *)
let to_j (p: proj_point) : proj_point =
  let (_, _, z) = p in if z = fzero then jinf else tj p

[@@"opaque_to_smt"]
let jok (p: proj_point) : prop =
  jeq p /\ (let (_, _, z) = p in z <> fzero \/ p == jinf)

[@@"opaque_to_smt"]
let jr (j: proj_point) (e: nat) (p: proj_point) : prop =
  jok j /\ GR.peq (to_h j) (SM.smul e p)

let prime_lem () : Lemma (FStar.Math.Euclid.is_prime prime) =
  S.m0_lem (); S.prime_m0 ()

(** {2 Nonzero} *)

let dbl_nz (a: felem) : Lemma (requires a <> 0) (ensures fdbl a <> 0) =
  assert_norm (prime % 2 == 1);
  let s = a + a in
  if s < prime then M.small_mod s prime
  else begin M.lemma_mod_sub s prime 1; M.small_mod (s - prime) prime end

let y_nz (x y z: felem)
  : Lemma (requires jeq (x, y, z) /\ z <> 0) (ensures y <> 0)
  = prime_lem ();
    FStar.Pervasives.reveal_opaque (`%jeq) jeq;
    let e = fmul z z in
    F.mul_nonzero z z;
    let u = fmul x (finv e) in
    F.div_mul x e;
    K.k6 u e y;
    NR.no_root_f u;
    F.mul_nonzero e e;
    F.mul_nonzero (fmul e e) e;
    F.mul_nonzero (fmul (fmul e e) e) (S.ff u)

let cube_nz (z: felem) : Lemma (requires z <> 0) (ensures fmul z (fmul z z) <> 0) =
  prime_lem (); F.mul_nonzero z z; F.mul_nonzero z (fmul z z)

(** {2 Infinity} *)

let jinf_facts () : Lemma (jeq jinf /\ jdouble jinf == jinf /\
                           to_h jinf == point_at_infinity)
  = FStar.Pervasives.reveal_opaque (`%jeq) jeq;
    FStar.Pervasives.reveal_opaque (`%S.eqn_r) S.eqn_r;
    FStar.Pervasives.reveal_opaque (`%jdouble) jdouble;
    FStar.Pervasives.reveal_opaque (`%to_h) to_h;
    assert_norm (jeq jinf);
    assert_norm (jdouble jinf == jinf);
    assert_norm (to_h jinf == point_at_infinity)

(** {2 On the curve} *)

let oc_heq (p: proj_point)
  : Lemma (requires Pj.nz #prime p /\ S.heq p) (ensures GR.on_curve p)
  = FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
    FStar.Pervasives.reveal_opaque (`%S.eqn_l) S.eqn_l;
    FStar.Pervasives.reveal_opaque (`%S.eqn_r) S.eqn_r

let heq_oc (p: proj_point)
  : Lemma (requires GR.on_curve p) (ensures S.heq p)
  = FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
    FStar.Pervasives.reveal_opaque (`%S.eqn_l) S.eqn_l;
    FStar.Pervasives.reveal_opaque (`%S.eqn_r) S.eqn_r

let jok_on (j: proj_point)
  : Lemma (requires jok j) (ensures GR.on_curve (to_h j))
  = FStar.Pervasives.reveal_opaque (`%jok) jok;
    let (x, y, z) = j in
    if z = fzero then begin
      jinf_facts (); GR.point_at_infinity_on_curve ()
    end else begin
      JK.j3 x y z;
      cube_nz z;
      FStar.Pervasives.reveal_opaque (`%to_h) to_h;
      oc_heq (to_h j)
    end

(** {2 Doubling} *)

let jdouble_ok (j: proj_point)
  : Lemma (requires jok j)
          (ensures jok (jdouble j) /\
                   GR.peq (to_h (jdouble j)) (point_double (to_h j)))
  = FStar.Pervasives.reveal_opaque (`%jok) jok;
    let (x, y, z) = j in
    JK.j1 x y z;
    JK.j2 x y z;
    if z = fzero then jinf_facts ()
    else begin
      y_nz x y z;
      prime_lem ();
      F.mul_nonzero z y;
      dbl_nz (fmul z y);
      FStar.Pervasives.reveal_opaque (`%jdouble) jdouble
    end

(** {2 Converting in} *)

let to_j_ok (h: proj_point)
  : Lemma (requires GR.on_curve h)
          (ensures jok (to_j h) /\ GR.peq (to_h (to_j h)) h)
  = FStar.Pervasives.reveal_opaque (`%jok) jok;
    let (x, y, z) = h in
    if z = fzero then begin
      jinf_facts ();
      GR.peq_inf_z h
    end else begin
      heq_oc h;
      JK.j4 x y z;
      JK.j5 x y z;
      FStar.Pervasives.reveal_opaque (`%tj) tj;
      Pj.peq_scale_l #prime (fmul z z) h
    end

(** {2 The invariant} *)

let jr_in (h: proj_point) (e: nat) (p: proj_point)
  : Lemma (requires GR.on_curve p /\ GR.on_curve h /\ GR.peq h (SM.smul e p))
          (ensures jr (to_j h) e p)
  = FStar.Pervasives.reveal_opaque (`%jr) jr;
    to_j_ok h;
    jok_on (to_j h);
    SM.smul_ok e p;
    GR.peq_trans (to_h (to_j h)) h (SM.smul e p)

let jr_dbl (j: proj_point) (e: nat) (p: proj_point)
  : Lemma (requires GR.on_curve p /\ jr j e p)
          (ensures jr (jdouble j) (2 * e) p)
  = FStar.Pervasives.reveal_opaque (`%jr) jr;
    jdouble_ok j;
    jok_on j;
    jok_on (jdouble j);
    SM.smul_ok e p;
    SM.smul_dbl_congr e p (to_h j);
    SM.smul_ok (2 * e) p;
    GR.peq_trans (to_h (jdouble j)) (point_double (to_h j)) (SM.smul (2 * e) p)

let jr_out (j: proj_point) (e: nat) (p: proj_point)
  : Lemma (requires jr j e p)
          (ensures GR.on_curve (to_h j) /\ GR.peq (to_h j) (SM.smul e p))
  = FStar.Pervasives.reveal_opaque (`%jr) jr;
    jok_on j
