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

(** Montgomery form as an interface.

    [Spec.P256.Field] says what the four operations do to {i sequences}:
    [madd d a b] is the residue whose value is [(eval a + eval b) mod m].
    Everything above the field -- the curve formulas, ECDSA -- wants to
    speak of numbers instead, and it wants the [R] that the representation
    carries to be invisible.  This module is the translation, once: if [a]
    holds [x] and [b] holds [y], then [madd d a b] holds [add x y], and the
    same for the other three.

    {b Cancelling [R].}  [mmul_ok] is stated as [R z = a b (mod m)], because
    that is what the reduction proves and it needs no inverse.  Turning it
    into [z = ...] needs one, and F* has no modular-inverse theory, so the
    bundle carries a witness [ri] with [R ri = 1 (mod m)], checked by
    [assert_norm] at each instance.  [rcancel] is the one place it is used;
    everything else here is ordinary modular algebra. *)
module Spec.P256.Mont

open Spec.Bignum256
open Spec.P256.Field

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module MA = Spec.ModArith

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 Cancelling the radix} *)

let rcancel1 (d: modulus) (u: nat)
  : Lemma (requires modulus_ok d)
          (ensures pow2 256 * u * d.ri % d.m == u % d.m)
  = Math.paren_mul_right (pow2 256) u d.ri;
    Math.swap_mul u d.ri;
    Math.paren_mul_right (pow2 256) d.ri u;
    Math.swap_mul (pow2 256 * d.ri) u;
    Math.lemma_mod_mul_distr_r u (pow2 256 * d.ri) d.m

(** Multiplication by [R] is injective on residues, which is what lets a
    statement about [R z] become a statement about [z]. *)
let rcancel (d: modulus) (u v: nat)
  : Lemma (requires modulus_ok d /\ pow2 256 * u % d.m == pow2 256 * v % d.m)
          (ensures u % d.m == v % d.m)
  = Math.lemma_mod_mul_distr_l (pow2 256 * u) d.ri d.m;
    Math.lemma_mod_mul_distr_l (pow2 256 * v) d.ri d.m;
    rcancel1 d u;
    rcancel1 d v

(** {2 The constants} *)

let mone : Seq.seq nat = limbs 1

let mone_ok (_: unit)
  : Lemma (Seq.length mone == nl /\ bnd mone base /\ eval mone == 1)
  = assert_norm (1 < pow2 256);
    limbs_ok 1

let mform_zero (d: modulus)
  : Lemma (requires modulus_ok d) (ensures mform d (MA.zero #d.m) mzero)
  = mzero_ok ()

let mform_one (d: modulus)
  : Lemma (requires modulus_ok d) (ensures mform d (MA.one #d.m) d.r1)
  = Math.lemma_mod_lt (pow2 256) d.m

(** {2 Entering and leaving}

    [x] becomes [x R] by multiplying by [R^2], and [x R] becomes [x] by
    multiplying by one: both are the same [mmul]. *)

let to_mont (d: modulus) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a)
          (ensures mform d (eval a) (mmul d a d.r2))
  = mmul_ok d a d.r2;
    let z = eval (mmul d a d.r2) in
    let r = pow2 256 in
    let x = eval a in
    (* [R z = x (R^2 mod m) = R (x R mod m)] modulo [m]. *)
    Math.lemma_mod_mul_distr_r x (r * r) d.m;
    Math.paren_mul_right x r r;
    Math.swap_mul (x * r) r;
    Math.lemma_mod_mul_distr_r r (x * r) d.m;
    rcancel d z (x * r % d.m);
    Math.lemma_mod_lt (x * r) d.m;
    Math.small_mod (x * r % d.m) d.m;
    Math.small_mod z d.m

let of_mont (d: modulus) (x: nat) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ mform d x a /\ x < d.m)
          (ensures res d (mmul d a mone) /\ eval (mmul d a mone) == x)
  = mone_ok ();
    assert (res d mone);
    mmul_ok d a mone;
    let z = eval (mmul d a mone) in
    let r = pow2 256 in
    Math.lemma_mod_mul_distr_l (x * r) 1 d.m;
    rcancel d z x;
    Math.small_mod z d.m;
    Math.small_mod x d.m

(** {2 The four operations} *)

let mform_mul (d: modulus) (x y: MA.elem d.m) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ mform d x a /\ mform d y b)
          (ensures mform d (MA.mul x y) (mmul d a b))
  = mmul_form d x y a b

let mform_add (d: modulus) (x y: MA.elem d.m) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ mform d x a /\ mform d y b)
          (ensures mform d (MA.add x y) (madd d a b))
  = madd_ok d a b;
    let r = pow2 256 in
    Math.lemma_mod_plus_distr_l (x * r) (y * r % d.m) d.m;
    Math.lemma_mod_plus_distr_r (x * r) (y * r) d.m;
    Math.distributivity_add_left x y r;
    Math.lemma_mod_mul_distr_l (x + y) r d.m

let mform_sub (d: modulus) (x y: MA.elem d.m) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ mform d x a /\ mform d y b)
          (ensures mform d (MA.sub x y) (msub d a b))
  = msub_ok d a b;
    let r = pow2 256 in
    let aa = eval a in
    let bb = eval b in
    (* The value [msub] computes is [x R - y R] modulo [m]. *)
    Math.lemma_mod_plus (aa - bb) 1 d.m;
    Math.lemma_mod_plus_distr_l (x * r) (- bb) d.m;
    Math.lemma_mod_sub_distr (x * r) (y * r) d.m;
    assert ((aa + d.m - bb) % d.m == (x * r - y * r) % d.m);
    (* So is the Montgomery form of [x - y]. *)
    Math.lemma_mod_mul_distr_l (x + d.m - y) r d.m;
    Math.distributivity_sub_left (x + d.m) y r;
    Math.distributivity_add_left x d.m r;
    Math.swap_mul d.m r;
    Math.lemma_mod_plus (x * r - y * r) r d.m;
    assert (MA.sub x y * r % d.m == (x * r - y * r) % d.m)

let mform_neg (d: modulus) (x: MA.elem d.m) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ mform d x a)
          (ensures mform d (MA.neg x) (mneg d a))
  = mform_zero d;
    mform_sub d (MA.zero #d.m) x mzero a

#pop-options
