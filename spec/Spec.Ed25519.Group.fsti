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

(** The group law of the Ed25519 curve.

    {2 Why this file exists}

    [Spec.Ed25519.point_mul] is double-and-add over 256 bits, and the
    implementation follows it step for step.  Every fast Ed25519 signs with
    a *precomputed table of multiples of the base point* instead -- HACL\*'s
    is sixteen entries at each of sixty-four four-bit positions -- and that
    is worth about 2.5x on key generation and on signing, which is the whole
    of the gap between this library and HACL\* on those two operations.

    A window cannot be justified one point at a time.  It computes
    [sum_i d_i (16^i G)] and claims the answer is [k G]; the claim is
    exactly that scalar multiplication is a homomorphism from the integers,
    which holds because the points form a *commutative group*.  So the
    windowed algorithm needs associativity of [point_add], and nothing else
    of comparable depth.

    This module states what is needed, and nothing more.  It has no
    implementation: it is a specification of work, not an assumption.  The
    library assumes nothing mathematical anywhere -- [Hacl.Vec128] is the
    only [assume val] in the tree and every one of its declarations is
    realized by a C intrinsic -- and adding an admitted group law would
    change that, so the windowed implementations wait on these proofs rather
    than on a decision to skip them.

    It is worth knowing that HACL\* does not prove them.  In
    [specs/lemmas/Spec.Ed25519.Lemmas.fst] the corresponding statements read

    {[
      let aff_point_add_assoc_lemma p q s = admit()
      let aff_point_add_comm_lemma p q = admit()
      let to_aff_point_add_lemma p q = admit()
    ]}

    so HACL\*'s windowed Ed25519, its windowed P-256 and its GLV secp256k1
    all rest on the same four admitted facts.  Discharging them here would
    be new, not a catch-up.

    {2 What is cheap and what is not}

    Of the statements below, only {!point_add_assoc_law} is hard.  The
    curve-membership lemmas are polynomial identities that
    [FStar.Tactics.CanonCommSemiring] should close directly once the
    denominators are cleared; [point_equal] being an equivalence is field
    cancellation and needs only that [z] is never zero on the curve;
    commutativity is visible in the formula, which is symmetric in its two
    arguments except for the sign of [a] and [b], and reflexivity and the
    identity laws are computations.

    Associativity is the real content.  The standard route -- Bernstein and
    Lange's, and the one Fiat-Crypto follows -- is to clear denominators and
    reduce the resulting polynomial identity modulo the two curve equations.
    That last step is ideal membership: the cofactors are large and must
    come from a Groebner basis, which F\* cannot compute.  The practical
    shape of the proof is therefore

    - compute the cofactors offline, in a computer algebra system;
    - state the resulting identity as a polynomial equation over the field
      with those cofactors written out;
    - close it with [CanonCommSemiring], which proves ring identities and
      does not need to search.

    {2 What is built on top of it}

    These are consequences, not axioms, and they are not stated here: once
    the statements below are proved, [Spec.Ed25519.point_mul] can be shown
    equal to repeated addition, repeated addition shown to satisfy
    [smul (a + b) p == add (smul a p) (smul b p)], and the windowed
    algorithm proved against that, once, generically, for every curve in the
    library.  That layer is ordinary induction and is not the blocker. *)
module Spec.Ed25519.Group

open Spec.Curve25519
open Spec.Ed25519

(** {2 Being on the curve}

    [Spec.Ed25519.point_inv] says only that the fourth coordinate is
    consistent, [XY = ZT].  The addition law's completeness needs more: the
    point must satisfy the curve equation, and [Z] must be nonzero.  In
    extended coordinates [(X, Y, Z, T)] denoting [(X/Z, Y/Z)], the twisted
    Edwards equation [-x^2 + y^2 = 1 + d x^2 y^2] clears to

      [(Y^2 - X^2) Z^2 = Z^4 + d X^2 Y^2].

    Completeness is what makes the formulas branch-free, and it holds
    because [d] is not a square modulo [2^255 - 19]; that fact is not needed
    to state anything here, but it is needed to prove
    {!point_add_denominators_nonzero}, which is the hidden obligation inside
    every one of the lemmas below. *)
let on_curve (p: ext_point) : prop =
  let (x, y, z, t) = p in
  z <> 0 /\ fmul x y == fmul z t /\
  fmul (fsub (fmul y y) (fmul x x)) (fmul z z) ==
  fadd (fmul (fmul z z) (fmul z z)) (fmul d (fmul (fmul x x) (fmul y y)))

(** The two points the specification names are on the curve.  Both are
    concrete, so both should fall to normalisation; [g] is the more
    expensive of the two and may want its own [assert_norm]. *)
val point_at_infinity_on_curve (_: unit)
  : Lemma (on_curve point_at_infinity)

val g_on_curve (_: unit) : Lemma (on_curve g)

(** {2 The addition law is complete}

    This is the statement that the formulas never divide by zero, phrased
    as: the output is again a point on the curve, in particular with
    nonzero [Z].  It is the one that consumes non-squareness of [d], and
    everything else leans on it. *)
val point_add_denominators_nonzero (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q)
          (ensures (let (_, _, z, _) = point_add p q in z <> 0))

val point_add_on_curve (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q)
          (ensures on_curve (point_add p q))

val point_double_on_curve (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures on_curve (point_double p))

val point_negate_on_curve (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures on_curve (point_negate p))

(** {2 [point_equal] is an equivalence}

    Projective points are compared by cross-multiplication, so equality of
    the *points* is not syntactic equality of the quadruples.  Transitivity
    is the only one with content and it is field cancellation: from
    [x1 z2 = x2 z1] and [x2 z3 = x3 z2] one gets [x1 z3 z2 = x3 z1 z2], and
    [z2] cancels because it is nonzero, which is why these three carry
    [on_curve] hypotheses. *)
val point_equal_refl (p: ext_point)
  : Lemma (requires on_curve p) (ensures point_equal p p)

val point_equal_sym (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ point_equal p q)
          (ensures point_equal q p)

val point_equal_trans (p q r: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ on_curve r /\
                    point_equal p q /\ point_equal q r)
          (ensures point_equal p r)

(** Addition respects it.  Without this the window's table entries could
    not be replaced by equal points, which is the first thing the proof
    does. *)
val point_add_congr (p p' q q': ext_point)
  : Lemma (requires on_curve p /\ on_curve p' /\ on_curve q /\ on_curve q' /\
                    point_equal p p' /\ point_equal q q')
          (ensures point_equal (point_add p q) (point_add p' q'))

(** {2 The group axioms}

    Three lemmas, of which the first is the one that costs. *)

(** Associativity.  The reason this file exists. *)
val point_add_assoc_law (p q r: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ on_curve r)
          (ensures point_equal (point_add (point_add p q) r)
                               (point_add p (point_add q r)))

(** Commutativity.  The formula is symmetric in [p] and [q] except in [a]
    and [b], where the two factors swap; this should be short. *)
val point_add_comm_law (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q)
          (ensures point_equal (point_add p q) (point_add q p))

(** The point at infinity is the identity. *)
val point_add_identity (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures point_equal (point_add point_at_infinity p) p)

(** Negation gives inverses.  Not needed for an unsigned window, but a
    signed-digit one halves the table and does need it. *)
val point_add_negate (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures point_equal (point_add (point_negate p) p)
                               point_at_infinity)

(** {2 Doubling agrees with addition}

    [point_double] is a different formula, cheaper by four multiplications,
    and the windowed algorithm uses it between window steps while reasoning
    about addition.  This is the lemma that lets it. *)
val point_double_is_add (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures point_equal (point_double p) (point_add p p))

(** {2 The bridge to what the implementation already proves}

    Everything above is stated with [point_equal], but the existing
    Ed25519 proofs are stated with structural equality on [ext_point]: the
    implementation's [point_add] is proved to return the *same quadruple*
    as the specification's, not an equivalent one.  A windowed
    implementation cannot do that -- it computes a different quadruple --
    so its correctness statement has to be [point_equal], and the encoding
    step has to be shown to be blind to the difference.  It is, because
    [point_compress] normalises through [Z^-1], but that needs saying. *)
val point_compress_congr (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ point_equal p q)
          (ensures point_compress p == point_compress q)
