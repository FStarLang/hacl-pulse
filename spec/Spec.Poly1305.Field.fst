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

(** The five-limb representation of [Spec.Poly1305]'s field.

    An element is five natural numbers [a0..a4] standing for
    [a0 + a1 2^26 + a2 2^52 + a3 2^78 + a4 2^104].  Nothing here is a machine
    integer: this module is the arithmetic, and [Hacl.Poly1305.Field] will be
    the same arithmetic on [Hacl.Secret.UInt64.t], carrying the bounds that
    keep it from overflowing.

    The one real theorem is [mul_mod]: the schoolbook product of two five-limb
    numbers, with every term at or above [2^130] multiplied by five and
    brought down five limbs, is the product modulo [2^130 - 5].

    Three things were needed to make the ring tactic cooperate, and all three
    are worth remembering.

    - {b Decompose.}  The twenty-five-term identity handed to
      [FStar.Tactics.CanonCommSemiring] whole does not finish in any
      reasonable time.  Proved one limb of the left operand at a time — the
      five [shift] lemmas below — each goal closes in under a second.

    - {b Delta-reduce first.}  [eval5] is [unfold], but the goal the tactic
      receives still mentions it, and the tactic treats an unrecognised
      application as an opaque atom, silently gives up and dumps the whole
      thing on the SMT solver.  Hence [ring], which norms the definitions away
      before calling [canon_semiring].

    - {b Do not subtract.}  [canon_semiring int_cr] will not distribute a
      subtraction that sits inside a product: [(b^5 - 5) * c] stays stuck.  So
      the lemmas are stated additively, [lhs + 5 * c == rhs + b^5 * c], and
      the single subtraction is done once, at the end, by hand.

    Powers of the radix are an abstract [b] throughout, so the tactic sees a
    polynomial in eleven variables rather than a mess of numerals; [b] becomes
    [2^26] only in [mul_mod]. *)
module Spec.Poly1305.Field

open FStar.Tactics.V2
open FStar.Tactics.CanonCommSemiring

module Math = FStar.Math.Lemmas

let prime : pos = pow2 130 - 5

(** {2 The representation} *)

unfold let eval5 (b a0 a1 a2 a3 a4: int) : int =
  a0 + a1 * b + a2 * (b * b) + a3 * (b * b * b) + a4 * (b * b * b * b)

(** [b^5], written so that the tactic and the solver see the same term. *)
unfold let p5 (b: int) : int = b * (b * (b * (b * b)))

let as_nat5 (a0 a1 a2 a3 a4: nat) : nat =
  a0 + a1 * pow2 26 + a2 * pow2 52 + a3 * pow2 78 + a4 * pow2 104

let ring () : Tac unit =
  norm [delta_only [`%eval5; `%p5]];
  canon_semiring int_cr

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let as_nat5_eval (a0 a1 a2 a3 a4: nat)
  : Lemma (as_nat5 a0 a1 a2 a3 a4 == eval5 (pow2 26) a0 a1 a2 a3 a4)
  = Math.pow2_plus 26 26;
    Math.pow2_plus 52 26;
    Math.pow2_plus 78 26

let radix_p5 (_: unit) : Lemma (p5 (pow2 26) == pow2 130)
  = Math.pow2_plus 26 26;
    Math.pow2_plus 52 26;
    Math.pow2_plus 78 26;
    Math.pow2_plus 104 26

#pop-options

(** {2 The cofactors}

    [cof i] collects the products that [shift i] pushes past [b^5] and folds
    back down to the bottom of the number.  They are what the reduction owes,
    and [mul_identity] says the debt is exactly a multiple of [b^5 - 5]. *)

let cof1 (b h1 r4: int) : int = h1 * r4
let cof2 (b h2 r3 r4: int) : int = h2 * r3 + (h2 * r4) * b
let cof3 (b h3 r2 r3 r4: int) : int =
  h3 * r2 + (h3 * r3) * b + (h3 * r4) * (b * b)
let cof4 (b h4 r1 r2 r3 r4: int) : int =
  h4 * r1 + (h4 * r2) * b + (h4 * r3) * (b * b) + (h4 * r4) * (b * b * b)

let cofactor (b h1 h2 h3 h4 r1 r2 r3 r4: int) : int =
  cof1 b h1 r4 + cof2 b h2 r3 r4 + cof3 b h3 r2 r3 r4 + cof4 b h4 r1 r2 r3 r4

(** {2 One limb of the left operand at a time}

    [shift i] says what [h * b^i * (r0 + r1 b + ... + r4 b^4)] is: the top [i]
    limbs of [r] wrap round to the bottom multiplied by five, and the
    difference is [b^5 - 5] times the cofactor. *)

let shift0 (b h r0 r1 r2 r3 r4: int)
  : Lemma (h * eval5 b r0 r1 r2 r3 r4 ==
           eval5 b (h * r0) (h * r1) (h * r2) (h * r3) (h * r4))
  = assert (h * eval5 b r0 r1 r2 r3 r4 ==
            eval5 b (h * r0) (h * r1) (h * r2) (h * r3) (h * r4))
      by ring ()

let shift1 (b h r0 r1 r2 r3 r4: int)
  : Lemma (h * (b * eval5 b r0 r1 r2 r3 r4) + 5 * cof1 b h r4 ==
           eval5 b (5 * (h * r4)) (h * r0) (h * r1) (h * r2) (h * r3)
           + p5 b * cof1 b h r4)
  = assert (h * (b * eval5 b r0 r1 r2 r3 r4) + 5 * (h * r4) ==
            eval5 b (5 * (h * r4)) (h * r0) (h * r1) (h * r2) (h * r3)
            + p5 b * (h * r4))
      by ring ()

let shift2 (b h r0 r1 r2 r3 r4: int)
  : Lemma (h * ((b * b) * eval5 b r0 r1 r2 r3 r4) + 5 * cof2 b h r3 r4 ==
           eval5 b (5 * (h * r3)) (5 * (h * r4)) (h * r0) (h * r1) (h * r2)
           + p5 b * cof2 b h r3 r4)
  = assert (h * ((b * b) * eval5 b r0 r1 r2 r3 r4)
              + 5 * (h * r3 + (h * r4) * b) ==
            eval5 b (5 * (h * r3)) (5 * (h * r4)) (h * r0) (h * r1) (h * r2)
            + p5 b * (h * r3 + (h * r4) * b))
      by ring ()

let shift3 (b h r0 r1 r2 r3 r4: int)
  : Lemma (h * ((b * b * b) * eval5 b r0 r1 r2 r3 r4) + 5 * cof3 b h r2 r3 r4 ==
           eval5 b (5 * (h * r2)) (5 * (h * r3)) (5 * (h * r4)) (h * r0) (h * r1)
           + p5 b * cof3 b h r2 r3 r4)
  = assert (h * ((b * b * b) * eval5 b r0 r1 r2 r3 r4)
              + 5 * (h * r2 + (h * r3) * b + (h * r4) * (b * b)) ==
            eval5 b (5 * (h * r2)) (5 * (h * r3)) (5 * (h * r4)) (h * r0) (h * r1)
            + p5 b * (h * r2 + (h * r3) * b + (h * r4) * (b * b)))
      by ring ()

let shift4 (b h r0 r1 r2 r3 r4: int)
  : Lemma (h * ((b * b * b * b) * eval5 b r0 r1 r2 r3 r4)
             + 5 * cof4 b h r1 r2 r3 r4 ==
           eval5 b (5 * (h * r1)) (5 * (h * r2)) (5 * (h * r3)) (5 * (h * r4)) (h * r0)
           + p5 b * cof4 b h r1 r2 r3 r4)
  = assert (h * ((b * b * b * b) * eval5 b r0 r1 r2 r3 r4)
              + 5 * (h * r1 + (h * r2) * b + (h * r3) * (b * b) + (h * r4) * (b * b * b)) ==
            eval5 b (5 * (h * r1)) (5 * (h * r2)) (5 * (h * r3)) (5 * (h * r4)) (h * r0)
            + p5 b * (h * r1 + (h * r2) * b + (h * r3) * (b * b) + (h * r4) * (b * b * b)))
      by ring ()

(** Adding five five-limb numbers limbwise.  This too has to go through the
    tactic: to the solver, [(x + y) * (b * b)] and [x * (b * b) + y * (b * b)]
    are unrelated nonlinear terms, and asking it to do this for five limbs at
    once is what made the first version of [mul_identity] time out. *)
let eval5_sum5 (b: int)
    (a0 a1 a2 a3 a4 c0 c1 c2 c3 c4 e0 e1 e2 e3 e4 f0 f1 f2 f3 f4 g0 g1 g2 g3 g4: int)
  : Lemma (eval5 b a0 a1 a2 a3 a4 + eval5 b c0 c1 c2 c3 c4 + eval5 b e0 e1 e2 e3 e4
           + eval5 b f0 f1 f2 f3 f4 + eval5 b g0 g1 g2 g3 g4 ==
           eval5 b (a0+c0+e0+f0+g0) (a1+c1+e1+f1+g1) (a2+c2+e2+f2+g2)
                   (a3+c3+e3+f3+g3) (a4+c4+e4+f4+g4))
  = assert (eval5 b a0 a1 a2 a3 a4 + eval5 b c0 c1 c2 c3 c4 + eval5 b e0 e1 e2 e3 e4
            + eval5 b f0 f1 f2 f3 f4 + eval5 b g0 g1 g2 g3 g4 ==
            eval5 b (a0+c0+e0+f0+g0) (a1+c1+e1+f1+g1) (a2+c2+e2+f2+g2)
                    (a3+c3+e3+f3+g3) (a4+c4+e4+f4+g4))
      by ring ()

(** Splitting the left operand: distributivity, but it is the one place where
    a product of two sums appears, so the tactic earns its keep here too. *)
let split_left (b h0 h1 h2 h3 h4 rr: int)
  : Lemma (eval5 b h0 h1 h2 h3 h4 * rr ==
           h0 * rr + h1 * (b * rr) + h2 * ((b * b) * rr)
           + h3 * ((b * b * b) * rr) + h4 * ((b * b * b * b) * rr))
  = assert (eval5 b h0 h1 h2 h3 h4 * rr ==
            h0 * rr + h1 * (b * rr) + h2 * ((b * b) * rr)
            + h3 * ((b * b * b) * rr) + h4 * ((b * b * b * b) * rr))
      by ring ()

(** {2 The product} *)

let d0 (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat) : nat =
  h0 * r0 + 5 * (h1 * r4) + 5 * (h2 * r3) + 5 * (h3 * r2) + 5 * (h4 * r1)
let d1 (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat) : nat =
  h0 * r1 + h1 * r0 + 5 * (h2 * r4) + 5 * (h3 * r3) + 5 * (h4 * r2)
let d2 (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat) : nat =
  h0 * r2 + h1 * r1 + h2 * r0 + 5 * (h3 * r4) + 5 * (h4 * r3)
let d3 (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat) : nat =
  h0 * r3 + h1 * r2 + h2 * r1 + h3 * r0 + 5 * (h4 * r4)
let d4 (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat) : nat =
  h0 * r4 + h1 * r3 + h2 * r2 + h3 * r1 + h4 * r0

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The identity, still additive: the five [shift]s summed. *)
let mul_identity (b: int) (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat)
  : Lemma
      (eval5 b h0 h1 h2 h3 h4 * eval5 b r0 r1 r2 r3 r4
         + 5 * cofactor b h1 h2 h3 h4 r1 r2 r3 r4 ==
       eval5 b (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
       + p5 b * cofactor b h1 h2 h3 h4 r1 r2 r3 r4)
  = let rr = eval5 b r0 r1 r2 r3 r4 in
    split_left b h0 h1 h2 h3 h4 rr;
    shift0 b h0 r0 r1 r2 r3 r4;
    shift1 b h1 r0 r1 r2 r3 r4;
    shift2 b h2 r0 r1 r2 r3 r4;
    shift3 b h3 r0 r1 r2 r3 r4;
    shift4 b h4 r0 r1 r2 r3 r4;
    eval5_sum5 b
      (h0 * r0) (h0 * r1) (h0 * r2) (h0 * r3) (h0 * r4)
      (5 * (h1 * r4)) (h1 * r0) (h1 * r1) (h1 * r2) (h1 * r3)
      (5 * (h2 * r3)) (5 * (h2 * r4)) (h2 * r0) (h2 * r1) (h2 * r2)
      (5 * (h3 * r2)) (5 * (h3 * r3)) (5 * (h3 * r4)) (h3 * r0) (h3 * r1)
      (5 * (h4 * r1)) (5 * (h4 * r2)) (5 * (h4 * r3)) (5 * (h4 * r4)) (h4 * r0);
    let k1 = cof1 b h1 r4 in
    let k2 = cof2 b h2 r3 r4 in
    let k3 = cof3 b h3 r2 r3 r4 in
    let k4 = cof4 b h4 r1 r2 r3 r4 in
    Math.distributivity_add_right 5 k1 k2;
    Math.distributivity_add_right 5 (k1 + k2) k3;
    Math.distributivity_add_right 5 (k1 + k2 + k3) k4;
    Math.distributivity_add_right (p5 b) k1 k2;
    Math.distributivity_add_right (p5 b) (k1 + k2) k3;
    Math.distributivity_add_right (p5 b) (k1 + k2 + k3) k4

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The theorem the implementation needs. *)
let mul_mod (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat)
  : Lemma
      ((as_nat5 h0 h1 h2 h3 h4 * as_nat5 r0 r1 r2 r3 r4) % prime ==
       (as_nat5 (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)) % prime)
  = let b = pow2 26 in
    as_nat5_eval h0 h1 h2 h3 h4;
    as_nat5_eval r0 r1 r2 r3 r4;
    as_nat5_eval (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                 (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                 (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                 (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                 (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4);
    mul_identity b h0 h1 h2 h3 h4 r0 r1 r2 r3 r4;
    radix_p5 ();
    let c = cofactor b h1 h2 h3 h4 r1 r2 r3 r4 in
    let dd = as_nat5 (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                     (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                     (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                     (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                     (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4) in
    (* [p5 b] is [prime + 5], so the [5 * c] on the two sides cancel. *)
    Math.distributivity_add_left prime 5 c;
    assert (as_nat5 h0 h1 h2 h3 h4 * as_nat5 r0 r1 r2 r3 r4 == dd + c * prime);
    Math.lemma_mod_plus dd c prime

#pop-options

(** {2 Carrying}

    After [mul_mod] the limbs are wide — up to about [2^59] — and have to be
    brought back under [2^26] before anything else can be done with them.
    The implementation walks up the number moving the high bits of each limb
    into the next one, and then wraps the overflow of the top limb round to
    the bottom, multiplied by five.

    Only the last of these six steps changes the number: the first five are
    equalities, and [carry_top] is a congruence modulo [prime].  Keeping the
    two kinds apart is what lets the implementation's loop invariant say
    "equal to the accumulator" for as long as possible and only weaken to
    "congruent" once. *)

let radix : pos = pow2 26

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let carry0 (d0 d1 d2 d3 d4: nat)
  : Lemma (as_nat5 (d0 % radix) (d1 + d0 / radix) d2 d3 d4 ==
           as_nat5 d0 d1 d2 d3 d4)
  = Math.euclidean_division_definition d0 radix;
    Math.distributivity_add_left d1 (d0 / radix) radix

let carry1 (d0 d1 d2 d3 d4: nat)
  : Lemma (as_nat5 d0 (d1 % radix) (d2 + d1 / radix) d3 d4 ==
           as_nat5 d0 d1 d2 d3 d4)
  = Math.euclidean_division_definition d1 radix;
    Math.distributivity_add_left d2 (d1 / radix) (pow2 52);
    Math.pow2_plus 26 26;
    Math.paren_mul_right (d1 / radix) radix radix;
    Math.distributivity_add_left (d1 % radix) ((d1 / radix) * radix) radix

let carry2 (d0 d1 d2 d3 d4: nat)
  : Lemma (as_nat5 d0 d1 (d2 % radix) (d3 + d2 / radix) d4 ==
           as_nat5 d0 d1 d2 d3 d4)
  = Math.euclidean_division_definition d2 radix;
    Math.distributivity_add_left d3 (d2 / radix) (pow2 78);
    Math.pow2_plus 52 26;
    Math.paren_mul_right (d2 / radix) radix (pow2 52);
    Math.distributivity_add_left (d2 % radix) ((d2 / radix) * radix) (pow2 52)

let carry3 (d0 d1 d2 d3 d4: nat)
  : Lemma (as_nat5 d0 d1 d2 (d3 % radix) (d4 + d3 / radix) ==
           as_nat5 d0 d1 d2 d3 d4)
  = Math.euclidean_division_definition d3 radix;
    Math.distributivity_add_left d4 (d3 / radix) (pow2 104);
    Math.pow2_plus 78 26;
    Math.paren_mul_right (d3 / radix) radix (pow2 78);
    Math.distributivity_add_left (d3 % radix) ((d3 / radix) * radix) (pow2 78)

(** The one step that is only a congruence: [2^130] is [prime + 5], so the
    bits that fall off the top come back at the bottom multiplied by five. *)
let carry_top (d0 d1 d2 d3 d4: nat)
  : Lemma ((as_nat5 (d0 + 5 * (d4 / radix)) d1 d2 d3 (d4 % radix)) % prime ==
           (as_nat5 d0 d1 d2 d3 d4) % prime)
  = let c = d4 / radix in
    Math.euclidean_division_definition d4 radix;
    Math.distributivity_add_left (d4 % radix) (c * radix) (pow2 104);
    Math.paren_mul_right c radix (pow2 104);
    Math.pow2_plus 104 26;
    Math.distributivity_sub_left (pow2 130) 5 c;
    assert (as_nat5 d0 d1 d2 d3 d4 ==
            as_nat5 (d0 + 5 * c) d1 d2 d3 (d4 % radix) + c * prime);
    Math.lemma_mod_plus (as_nat5 (d0 + 5 * c) d1 d2 d3 (d4 % radix)) c prime

#pop-options

(** {2 Addition and bounds} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let add5_eval (a0 a1 a2 a3 a4 c0 c1 c2 c3 c4: nat)
  : Lemma (as_nat5 (a0 + c0) (a1 + c1) (a2 + c2) (a3 + c3) (a4 + c4) ==
           as_nat5 a0 a1 a2 a3 a4 + as_nat5 c0 c1 c2 c3 c4)
  = Math.distributivity_add_left a1 c1 (pow2 26);
    Math.distributivity_add_left a2 c2 (pow2 52);
    Math.distributivity_add_left a3 c3 (pow2 78);
    Math.distributivity_add_left a4 c4 (pow2 104)

(** Five limbs under the radix make a number under [2^130]: the bound the
    final reduction needs, and the invariant the carry chain restores. *)
let as_nat5_bound (a0 a1 a2 a3 a4: nat)
  : Lemma (requires a0 < radix /\ a1 < radix /\ a2 < radix /\ a3 < radix /\ a4 < radix)
          (ensures as_nat5 a0 a1 a2 a3 a4 < pow2 130)
  = Math.lemma_mult_le_right (pow2 26) a1 (radix - 1);
    Math.lemma_mult_le_right (pow2 52) a2 (radix - 1);
    Math.lemma_mult_le_right (pow2 78) a3 (radix - 1);
    Math.lemma_mult_le_right (pow2 104) a4 (radix - 1);
    Math.pow2_plus 26 26;
    Math.pow2_plus 52 26;
    Math.pow2_plus 78 26;
    Math.pow2_plus 104 26

#pop-options

(** {2 The last reduction}

    A fully carried accumulator is below [2^130], which is only a little more
    than [prime], so at most one subtraction is needed.  Rather than compare
    against [prime] — which would need a borrow chain to be constant time —
    add five and look at whether bit 130 came out: that is the same test, and
    the sum is the answer when it does. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let reduce_final (h: nat)
  : Lemma (requires h < pow2 130)
          (ensures h % prime == (if h + 5 >= pow2 130 then h + 5 - pow2 130 else h))
  = Math.pow2_le_compat 130 4;
    assert_norm (pow2 4 == 16);
    if h + 5 >= pow2 130 then begin
      assert (h >= prime /\ h - prime < prime);
      Math.lemma_mod_sub h prime 1;
      Math.small_mod (h - prime) prime
    end else
      Math.small_mod h prime

#pop-options

(** {2 Splitting a number into limbs}

    The implementation gets a block as bytes and has to turn it into five
    limbs.  It is tempting to specify that with shifts and masks, but then
    every proof about it is a bit-level proof.  Instead the limbs are
    specified as [(n / 2^(26 i)) mod 2^26] and the implementation shows its
    shifts and masks compute {i that}, which the secret-integer layer already
    knows how to do.  [decompose] is the only thing anyone needs to know
    about the split: it puts the number back together. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let decompose (n: nat)
  : Lemma (requires n < pow2 130)
          (ensures as_nat5 (n % radix)
                           ((n / pow2 26) % radix)
                           ((n / pow2 52) % radix)
                           ((n / pow2 78) % radix)
                           (n / pow2 104) == n)
  = let a1 = n / pow2 26 in
    let a2 = n / pow2 52 in
    let a3 = n / pow2 78 in
    let a4 = n / pow2 104 in
    Math.pow2_plus 26 26;
    Math.pow2_plus 52 26;
    Math.pow2_plus 78 26;
    Math.pow2_plus 104 26;
    Math.division_multiplication_lemma n (pow2 26) (pow2 26);
    Math.division_multiplication_lemma n (pow2 52) (pow2 26);
    Math.division_multiplication_lemma n (pow2 78) (pow2 26);
    Math.lemma_div_lt n 130 104;
    Math.small_mod a4 radix;
    Math.euclidean_division_definition n radix;
    Math.euclidean_division_definition a1 radix;
    Math.euclidean_division_definition a2 radix;
    Math.euclidean_division_definition a3 radix;
    (* [n = n % b + a1 b], and each [ai] splits the same way; the products
       have to be reassociated one power at a time. *)
    Math.distributivity_add_left (a1 % radix) (a2 * radix) (pow2 26);
    Math.paren_mul_right a2 radix (pow2 26);
    Math.distributivity_add_left (a2 % radix) (a3 * radix) (pow2 52);
    Math.paren_mul_right a3 radix (pow2 52);
    Math.distributivity_add_left (a3 % radix) (a4 * radix) (pow2 78);
    Math.paren_mul_right a4 radix (pow2 78)

#pop-options

(** {2 Overflow}

    The reason five twenty-six-bit limbs is the right choice for a
    sixty-four-bit machine: the widest thing the multiplication ever forms is
    a [d] limb, and it stays well under [2^64], so no part of Poly1305 needs a
    hundred-and-twenty-eight-bit type.

    The accumulator limbs are allowed one bit of slack over the radix --
    [carry_top] leaves [h0] a little wide, and adding a block adds another bit
    -- so they are bounded by [2^27] rather than [2^26]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let prod_bound (a b: nat)
  : Lemma (requires a < pow2 27 /\ b < pow2 26) (ensures a * b < pow2 53)
  = Math.pow2_plus 27 26;
    Math.lemma_mult_le_right b a (pow2 27 - 1);
    Math.lemma_mult_le_left (pow2 27 - 1) b (pow2 26 - 1)

unfold let bounded5 (a0 a1 a2 a3 a4: nat) (n: nat) : prop =
  a0 < pow2 n /\ a1 < pow2 n /\ a2 < pow2 n /\ a3 < pow2 n /\ a4 < pow2 n

let mul_no_overflow (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4: nat)
  : Lemma (requires bounded5 h0 h1 h2 h3 h4 27 /\ bounded5 r0 r1 r2 r3 r4 26)
          (ensures bounded5 (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
                            (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4) 58)
  = let bound (h r: nat) : Lemma (requires h < pow2 27 /\ r < pow2 26)
                                 (ensures h * r < pow2 53) = prod_bound h r in
    bound h0 r0; bound h0 r1; bound h0 r2; bound h0 r3; bound h0 r4;
    bound h1 r0; bound h1 r1; bound h1 r2; bound h1 r3; bound h1 r4;
    bound h2 r0; bound h2 r1; bound h2 r2; bound h2 r3; bound h2 r4;
    bound h3 r0; bound h3 r1; bound h3 r2; bound h3 r3; bound h3 r4;
    bound h4 r0; bound h4 r1; bound h4 r2; bound h4 r3; bound h4 r4;
    (* twenty-one times [2^53] is under [2^58]. *)
    Math.pow2_plus 5 53;
    assert_norm (pow2 5 == 32)

#pop-options

(** {2 Multiply, carry, and the bounds that hold afterwards}

    [mul_reduce_ok] is the whole of [Hacl.Poly1305.Field.fmul] as one
    statement about natural numbers.  Rather than have the Pulse code apply
    [mul_mod] and the six carry lemmas itself -- each application dragging the
    entire separation-logic context along with it -- the implementation only
    has to exhibit its five results as the expressions below, and this lemma
    supplies both the congruence and the bounds.

    It comes in three parts, and the split is not cosmetic: stated as one
    lemma, with the ten hypotheses defining the carry chain in scope for every
    sub-query, it does not finish.  [carry_chain_cong] knows nothing about
    where its inputs came from, [carry_chain_bounds] knows nothing about the
    prime, and only [mul_reduce_ok] mentions both. *)

(** The carry chain, named once so the three lemmas agree on it. *)
unfold let chain (e0 e1 e2 e3 e4 t0 t1 t2 t3 t4: nat) : prop =
  let f1 = e1 + e0 / radix in
  let f2 = e2 + f1 / radix in
  let f3 = e3 + f2 / radix in
  let f4 = e4 + f3 / radix in
  let g0 = e0 % radix + 5 * (f4 / radix) in
  t0 == g0 % radix /\
  t1 == f1 % radix + g0 / radix /\
  t2 == f2 % radix /\
  t3 == f3 % radix /\
  t4 == f4 % radix

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let carry_chain_cong (e0 e1 e2 e3 e4 t0 t1 t2 t3 t4: nat)
  : Lemma (requires chain e0 e1 e2 e3 e4 t0 t1 t2 t3 t4)
          (ensures as_nat5 t0 t1 t2 t3 t4 % prime == as_nat5 e0 e1 e2 e3 e4 % prime)
  = let f1 = e1 + e0 / radix in
    let f2 = e2 + f1 / radix in
    let f3 = e3 + f2 / radix in
    let f4 = e4 + f3 / radix in
    let g0 = e0 % radix + 5 * (f4 / radix) in
    carry0 e0 e1 e2 e3 e4;
    carry1 (e0 % radix) f1 e2 e3 e4;
    carry2 (e0 % radix) (f1 % radix) f2 e3 e4;
    carry3 (e0 % radix) (f1 % radix) (f2 % radix) f3 e4;
    carry_top (e0 % radix) (f1 % radix) (f2 % radix) (f3 % radix) f4;
    carry0 g0 (f1 % radix) (f2 % radix) (f3 % radix) (f4 % radix)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let div_bound (x: nat) (n m: nat)
  : Lemma (requires x < pow2 n /\ m <= n) (ensures x / pow2 m < pow2 (n - m))
  = Math.lemma_div_lt x n m

let add_bound (a b: nat) (n m: nat)
  : Lemma (requires a < pow2 n /\ b < pow2 m /\ m <= n)
          (ensures a + b < pow2 (n + 1))
  = Math.pow2_le_compat n m;
    Math.pow2_double_sum n

let carry_chain_bounds (e0 e1 e2 e3 e4 t0 t1 t2 t3 t4: nat)
  : Lemma (requires bounded5 e0 e1 e2 e3 e4 58 /\ chain e0 e1 e2 e3 e4 t0 t1 t2 t3 t4)
          (ensures bounded5 t0 t1 t2 t3 t4 27)
  = let f1 = e1 + e0 / radix in
    let f2 = e2 + f1 / radix in
    let f3 = e3 + f2 / radix in
    let f4 = e4 + f3 / radix in
    let g0 = e0 % radix + 5 * (f4 / radix) in
    div_bound e0 58 26;
    add_bound e1 (e0 / radix) 58 32;
    div_bound f1 59 26;
    add_bound e2 (f1 / radix) 58 33;
    div_bound f2 59 26;
    add_bound e3 (f2 / radix) 58 33;
    div_bound f3 59 26;
    add_bound e4 (f3 / radix) 58 33;
    div_bound f4 59 26;
    assert_norm (5 * pow2 33 < pow2 36);
    add_bound (5 * (f4 / radix)) (e0 % radix) 36 26;
    div_bound g0 37 26;
    Math.pow2_lt_compat 27 26;
    Math.pow2_lt_compat 26 11;
    Math.pow2_double_sum 26

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let mul_reduce_ok (h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 t0 t1 t2 t3 t4: nat)
  : Lemma
      (requires
         bounded5 h0 h1 h2 h3 h4 27 /\ bounded5 r0 r1 r2 r3 r4 26 /\
         chain (d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               (d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4)
               t0 t1 t2 t3 t4)
      (ensures
         bounded5 t0 t1 t2 t3 t4 27 /\
         as_nat5 t0 t1 t2 t3 t4 % prime ==
         (as_nat5 h0 h1 h2 h3 h4 * as_nat5 r0 r1 r2 r3 r4) % prime)
  = let e0 = d0 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e1 = d1 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e2 = d2 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e3 = d3 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    let e4 = d4 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4 in
    mul_no_overflow h0 h1 h2 h3 h4 r0 r1 r2 r3 r4;
    carry_chain_bounds e0 e1 e2 e3 e4 t0 t1 t2 t3 t4;
    carry_chain_cong e0 e1 e2 e3 e4 t0 t1 t2 t3 t4;
    mul_mod h0 h1 h2 h3 h4 r0 r1 r2 r3 r4

#pop-options
