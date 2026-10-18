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

(** The base point of secp256k1 has prime order [n], and what follows from it.

    {!Spec.K256.Group} proves the group laws and {!Spec.K256.Smul} that
    [point_mul] computes the multiple [smul].  Neither says anything about
    the {e order} of [G], and both protocols need it: ECDSA reduces its
    scalars modulo [n] and inverts them there, and both protocols reject a
    result at infinity, so correctness needs a nonzero scalar not to land
    there.  This module establishes

    {ul
    {- {!order_is_prime}, by the Pocklington certificate in
       {!Spec.Group.OrderPrimes};}
    {- {!g_has_order}: [n G] is the point at infinity.  [smul n g] is [n]
       additions and cannot be evaluated, but [point_mul n g] is a 256-rung
       ladder on concrete field elements, which the normaliser evaluates in
       some seconds; {!Spec.K256.Smul.point_mul_is_smul} carries the
       answer over to [smul];}
    {- {!point_mul_g_nonzero}: [k G] is not at infinity for [k] not
       divisible by [n], from {!Spec.Group.ECDSA.smul_nonzero};}
    {- {!store_load}: a point that is not at infinity survives
       [store_point] followed by [load_point], up to [peq].  This needs the
       affine coordinates of an on-curve projective point to satisfy the
       affine equation, which is the canonical-representative argument of
       [Spec.K256.Group], repeated here because that module's helpers are
       behind its interface.}} *)
module Spec.K256.Order

open Hacl.Spec.Bytes
open Spec.K256
open Spec.K256.Group

module G = Spec.Group.Smul
module GE = Spec.Group.ECDSA
module SM = Spec.K256.Smul
module S = Spec.K256.GroupSv
module K = Spec.K256.GroupChecks
module Pj = Spec.Group.Proj
module F = Spec.Group.Field
module MA = Spec.ModArith
module E = FStar.Math.Euclid
module M = FStar.Math.Lemmas
module Seq = FStar.Seq
module Classical = FStar.Classical

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The two moduli are prime} *)

let prime_is_prime (_: unit) : Lemma (E.is_prime prime) =
  S.m0_lem (); S.prime_m0 ()

let order_is_prime (_: unit) : Lemma (E.is_prime order) =
  Spec.Group.OrderPrimes.prime_k256_order ();
  assert_norm (order == 115792089237316195423570985008687907852837564279074904382605163141518161494337)

let bounds (_: unit) : Lemma (prime < pow2 256 /\ order < pow2 256 /\ pow2 (8 * 32) == pow2 256) =
  assert_norm (prime < pow2 256);
  assert_norm (order < pow2 256)

(** {2 Points at infinity}

    At [z = 0] the homogeneous equation says [x^3 = 0], so [x = 0] and the
    point is [(0 : y : 0)], which is [peq] to [(0 : 1 : 0)]. *)

let at_infinity_peq (p: proj_point)
  : Lemma (requires on_curve p /\ is_point_at_infinity p)
          (ensures peq p point_at_infinity)
  = let (x, y, z) = p in
    prime_is_prime ();
    assert (fmul (fmul x x) x == 0);
    F.no_zero_div (fmul x x) x;
    F.no_zero_div x x

let g_not_zero (_: unit) : Lemma (~(peq g point_at_infinity)) =
  g_on_curve ();
  point_at_infinity_on_curve ();
  Classical.move_requires (peq_is_point_at_infinity g) point_at_infinity

(** A point equivalent to one that is not the identity is not at
    infinity. *)
let not_inf_of_peq (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ peq p q /\ ~(peq q point_at_infinity))
          (ensures ~(is_point_at_infinity p))
  = point_at_infinity_on_curve ();
    if is_point_at_infinity p then begin
      at_infinity_peq p;
      peq_sym p q;
      peq_trans q p point_at_infinity
    end

(** {2 The order of the base point} *)

(** The one expensive step: 256 doublings and the additions for the bits of
    [n], on concrete field elements. *)
let order_g_at_infinity (_: unit)
  : Lemma (is_point_at_infinity (point_mul order g))
  = assert_norm (is_point_at_infinity (point_mul order g))

let g_has_order (_: unit) : Lemma (GE.has_order SM.kg order g) =
  g_on_curve ();
  bounds ();
  SM.point_mul_is_smul order g;
  SM.smul_ok order g;
  order_g_at_infinity ();
  peq_is_point_at_infinity (point_mul order g) (SM.smul order g);
  at_infinity_peq (SM.smul order g)

(** [k G] is the identity only when [n] divides [k]. *)
let smul_g_nonzero (k: nat)
  : Lemma (requires k % order <> 0)
          (ensures on_curve (SM.smul k g) /\ ~(peq (SM.smul k g) point_at_infinity))
  = g_has_order ();
    order_is_prime ();
    g_not_zero ();
    SM.smul_ok k g;
    GE.smul_nonzero SM.kg order k g

let point_mul_g_nonzero (k: nat)
  : Lemma (requires k < pow2 256 /\ k % order <> 0)
          (ensures on_curve (point_mul_g k) /\ ~(is_point_at_infinity (point_mul_g k)) /\
                   peq (point_mul_g k) (SM.smul k g))
  = g_on_curve ();
    SM.point_mul_is_smul k g;
    smul_g_nonzero k;
    not_inf_of_peq (point_mul_g k) (SM.smul k g)

(** {2 Affine coordinates}

    Restated from [Spec.K256.Group], whose interface does not export them:
    the curve predicate through the opaque forms of [Spec.K256.GroupSv],
    and homogeneity of the equation, which is [Spec.K256.GroupChecks.k17]. *)

let oc_heq (p: proj_point) : Lemma (on_curve p <==> (Pj.nz #prime p /\ S.heq p)) =
  FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
  FStar.Pervasives.reveal_opaque (`%S.eqn_l) S.eqn_l;
  FStar.Pervasives.reveal_opaque (`%S.eqn_r) S.eqn_r

let ff_on (x y: felem) : Lemma (requires fmul y y == S.ff x) (ensures S.on x y) =
  S.cst_lem ();
  FStar.Pervasives.reveal_opaque (`%S.on) S.on;
  FStar.Pervasives.reveal_opaque (`%S.ff) S.ff

let heq_aff (x y: felem) : Lemma (S.heq (x, y, fone) <==> S.on x y) =
  FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
  K.k18 x y;
  Classical.move_requires (S.on_ff x) y;
  Classical.move_requires (ff_on x) y

let heq_unscale (s: felem) (p: proj_point)
  : Lemma (requires s <> 0 /\ S.heq (Pj.scale #prime s p)) (ensures S.heq p)
  = FStar.Pervasives.reveal_opaque (`%S.heq) S.heq;
    prime_is_prime ();
    let (x, y, z) = p in
    K.k17 s x y z;
    let s3 = fmul (fmul s s) s in
    F.mul_nonzero s s; F.mul_nonzero (fmul s s) s;
    MA.mul_comm s3 (S.eqn_l p); MA.mul_comm s3 (S.eqn_r p);
    F.cancel (S.eqn_l p) (S.eqn_r p) s3

(** A finite point's affine coordinates are on the curve, and the affine
    point is equivalent to it. *)
let aff_lift (p: proj_point)
  : Lemma (requires on_curve p /\ ~(is_point_at_infinity p))
          (ensures (let (x, y) = to_aff_point p in
                    is_on_curve x y /\ on_curve (x, y, fone) /\ peq (x, y, fone) p))
  = prime_is_prime ();
    oc_heq p;
    Pj.canon_scale #prime p;
    let cp = Pj.canon #prime p in
    heq_unscale (Pj.ck #prime p) cp;
    let (u, v, w) = cp in
    heq_aff u v;
    FStar.Pervasives.reveal_opaque (`%S.on) S.on;
    on_curve_affine u v;
    Pj.peq_scale_l #prime (Pj.ck #prime p) cp;
    peq_sym p cp

(** {2 Encoding round trip} *)

let store_load (p: proj_point)
  : Lemma (requires on_curve p /\ ~(is_point_at_infinity p))
          (ensures (let (x, y) = to_aff_point p in
                    load_point (store_point p) == Some (x, y, fone) /\
                    on_curve (x, y, fone) /\ peq (x, y, fone) p))
  = let (x, y) = to_aff_point p in
    aff_lift p;
    bounds ();
    Seq.Properties.append_slices (store_felem x) (store_felem y);
    Seq.lemma_eq_elim (Seq.slice (store_point p) 0 32) (store_felem x);
    Seq.lemma_eq_elim (Seq.slice (store_point p) 32 64) (store_felem y);
    be_nat_to_be 32 x;
    be_nat_to_be 32 y

#pop-options
