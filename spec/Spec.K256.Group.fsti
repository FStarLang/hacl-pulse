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

(** The group law of the secp256k1 curve.

    The companion of {!Spec.Ed25519.Group}, which carries the long
    explanation of why these statements are wanted, what they buy, and what
    HACL\* does instead.  In brief: a precomputed table of multiples of the
    base point is worth about 2.5x on key generation, on signing and on the
    initiator half of ECDH, and the table is only correct because scalar
    multiplication is a homomorphism, which is associativity.  The measured
    shape of the gap is unusually clean -- on variable-base ECDH, where
    HACL\* also has no table, this library is within 1.15x; on fixed-base
    ECDH it is 2.59x.  The whole of the difference is the table.

    secp256k1 differs from Ed25519 in two ways that matter here.

    The curve is short Weierstrass with [a = 0], [y^2 = x^3 + 7], and the
    addition law is Renes--Costello--Batina Algorithm 7 -- the [a = 0]
    specialisation of the same complete law P-256 uses in its Algorithm 4
    form.  That law is complete on *prime-order* curves, which secp256k1 is,
    so there is no cofactor subtlety and no exceptional case -- but
    completeness holds for a different reason than in the Edwards case, and
    the proof of {!point_add_denominators_nonzero} is correspondingly
    different.

    Everything in this file is the P-256 file with [a = 0] and [b = 7], in
    the same way that [code/k256] is [code/p256] with three files changed.
    If the two proofs turn out to share their structure it is worth
    factoring them through a common Weierstrass module; the statements are
    kept apart here because [Spec.P256] and [Spec.K256] are separate
    modules with separate [felem] types and a goal that mentions both is
    ruinously slow.

    The point at infinity is a real projective point here, [(0 : 1 : 0)],
    rather than an ordinary curve point as it is on an Edwards curve.  So
    the membership predicate must *admit* [Z = 0]: it is the homogeneous
    equation [Y^2 Z = X^3 - 3 X Z^2 + b Z^3] together with the triple being
    nonzero, and it is satisfied by [(0 : 1 : 0)].  Equality of points is
    therefore not [Spec.K256.to_aff_point] equality, which collapses
    infinity onto [(0, 0)]; it is projective equivalence, stated below as
    {!peq}. *)
module Spec.K256.Group

open Spec.K256

(** {2 Being on the curve}

    The homogeneous form of [y^2 = x^3 + 7], plus the requirement that
    the triple is not all zero.  [Spec.K256.is_on_curve] is the affine
    version and is used by the decoder; this is the one the addition law
    needs, and the two agree when [Z <> 0].  That agreement is worth stating
    separately because the decoder is what produces the points a caller
    supplies. *)
let on_curve (p: proj_point) : prop =
  let (x, y, z) = p in
  (x <> fzero \/ y <> fzero \/ z <> fzero) /\
  fmul (fmul y y) z ==
  fadd (fmul (fmul x x) x) (fmul b_coeff (fmul (fmul z z) z))

val on_curve_affine (x y: felem)
  : Lemma (requires is_on_curve x y)
          (ensures on_curve (x, y, fone))

val point_at_infinity_on_curve (_: unit)
  : Lemma (on_curve point_at_infinity)

val g_on_curve (_: unit) : Lemma (on_curve g)

(** {2 Projective equality}

    Two nonzero triples denote the same point exactly when they are scalar
    multiples of one another, which cross-multiplication expresses without
    naming the scalar.  All three pairs are needed: on a projective line any
    two of the three products can agree while the points differ. *)
let peq (p q: proj_point) : prop =
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in
  fmul x1 y2 == fmul x2 y1 /\
  fmul x1 z2 == fmul x2 z1 /\
  fmul y1 z2 == fmul y2 z1

val peq_refl (p: proj_point)
  : Lemma (requires on_curve p) (ensures peq p p)

val peq_sym (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ peq p q) (ensures peq q p)

val peq_trans (p q r: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ on_curve r /\
                    peq p q /\ peq q r)
          (ensures peq p r)

(** Equivalent points are at infinity together, and otherwise have the same
    affine coordinates.  These two are the bridge between a windowed
    implementation, whose answer is only equivalent to the specification's,
    and the encoder and the verification equation, which are what a caller
    sees.  Neither needs associativity, and both should be short: the second
    is [finv] applied to a cancellation. *)
val peq_is_point_at_infinity (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ peq p q)
          (ensures is_point_at_infinity p == is_point_at_infinity q)

val peq_to_aff_point (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ peq p q)
          (ensures to_aff_point p == to_aff_point q)

(** {2 The addition law is complete}

    RCB Algorithm 4 has no exceptional inputs on a prime-order curve.  As
    with Ed25519 this is stated as closure: the result is again a point, in
    particular a nonzero triple. *)
val point_add_denominators_nonzero (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q)
          (ensures (let (x, y, z) = point_add p q in
                    x <> fzero \/ y <> fzero \/ z <> fzero))

val point_add_on_curve (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q)
          (ensures on_curve (point_add p q))

val point_double_on_curve (p: proj_point)
  : Lemma (requires on_curve p) (ensures on_curve (point_double p))

val point_negate_on_curve (p: proj_point)
  : Lemma (requires on_curve p) (ensures on_curve (point_negate p))

val point_add_congr (p p' q q': proj_point)
  : Lemma (requires on_curve p /\ on_curve p' /\ on_curve q /\ on_curve q' /\
                    peq p p' /\ peq q q')
          (ensures peq (point_add p q) (point_add p' q'))

(** {2 The group axioms}

    [point_add] and [point_double] are [opaque_to_smt] in [Spec.K256] --
    they are forty lines of nested [fmul] when unfolded, and the scalar
    multiplication loop cannot afford to see them.  These proofs will have
    to [reveal_opaque] them, and are the only place in the library that
    does. *)

(** Associativity.  The reason this file exists. *)
val point_add_assoc_law (p q r: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ on_curve r)
          (ensures peq (point_add (point_add p q) r)
                       (point_add p (point_add q r)))

val point_add_comm_law (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q)
          (ensures peq (point_add p q) (point_add q p))

val point_add_identity (p: proj_point)
  : Lemma (requires on_curve p)
          (ensures peq (point_add point_at_infinity p) p)

val point_add_negate (p: proj_point)
  : Lemma (requires on_curve p)
          (ensures peq (point_add (point_negate p) p) point_at_infinity)

(** {2 Doubling agrees with addition} *)
val point_double_is_add (p: proj_point)
  : Lemma (requires on_curve p)
          (ensures peq (point_double p) (point_add p p))
