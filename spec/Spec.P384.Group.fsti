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

(** The group law of the P-384 curve.

    The same statements as {!Spec.P256.Group}, which explains them, proved
    the same way: P-384 is also a prime-order short Weierstrass curve with
    [a = -3], and [Spec.P384] uses the same Renes--Costello--Batina
    formulas, so only the constants of the machine-checked identities
    change ([spec/group-gen/p384/derive.py]).

    The curve is [y^2 = x^3 - 3x + b].  The point at infinity is the
    projective point [(0 : 1 : 0)], so the membership predicate admits
    [Z = 0], and equality of points is projective equivalence, {!peq},
    rather than [Spec.P384.to_aff_point] equality. *)
module Spec.P384.Group

open Spec.P384

(** {2 Being on the curve}

    The homogeneous form of [y^2 = x^3 - 3x + b], plus the requirement that
    the triple is not all zero.  [Spec.P384.is_on_curve] is the affine
    version and is used by the decoder; this is the one the addition law
    needs, and the two agree when [Z <> 0].  That agreement is worth stating
    separately because the decoder is what produces the points a caller
    supplies. *)
let on_curve (p: proj_point) : prop =
  let (x, y, z) = p in
  (x <> fzero \/ y <> fzero \/ z <> fzero) /\
  fmul (fmul y y) z ==
  fadd (fsub (fmul (fmul x x) x)
             (fmul (fmul (fadd fone (fadd fone fone)) x) (fmul z z)))
       (fmul b_coeff (fmul (fmul z z) z))

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

    [point_add] and [point_double] are [opaque_to_smt] in [Spec.P384] --
    they are forty lines of nested [fmul] when unfolded, and the scalar
    multiplication loop cannot afford to see them.  The proofs reveal them
    in exactly one place, [Spec.P384.GroupSv], which says once that the
    polynomial computations of the checks compute these functions. *)

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
