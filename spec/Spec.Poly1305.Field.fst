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
