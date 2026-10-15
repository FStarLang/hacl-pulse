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

(** Montgomery form as an interface, over the four-limb core.

    The twin of {!Spec.Mont256}: the same translation from sequences to
    numbers, said against {!Spec.Field4}.  Nothing here mentions a limb
    width -- it is all [pow2 256] and the modulus record -- so the only
    difference is which core the residues come from.

    [Spec.Field4] says what the four operations do to {i sequences}:
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
module Spec.Mont4

open Spec.Bignum4
open Spec.Field4

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
  = mzero_ok ();
    assert (MA.zero #d.m == 0);
    assert (0 * pow2 256 == 0);
    Math.small_mod 0 d.m;
    assert (res d mzero);
    assert (eval mzero == MA.zero #d.m * pow2 256 % d.m)

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

(** {2 The value a residue holds}

    [mform] is a relation, and a relation makes a poor postcondition: the
    implementation would have to carry the number as a ghost argument
    through every operation.  It is in fact a function -- multiplication by
    [R] is injective -- and [mev] is that function, written with the same
    [ri] that [rcancel] uses.  The two lemmas below say the relation and
    the function agree, and after them the interface is
    [mev d (mmul d a b) == mul (mev d a) (mev d b)] and its three
    companions: no ghost arguments anywhere. *)

let mev (d: modulus) (s: Seq.seq nat) : GTot (MA.elem d.m) =
  eval s * d.ri % d.m

let mev_form (d: modulus) (s: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d s) (ensures mform d (mev d s) s)
  = let u = eval s in
    rcancel1 d u;
    Math.swap_mul (pow2 256) u;
    Math.paren_mul_right u (pow2 256) d.ri;
    Math.swap_mul (pow2 256) d.ri;
    Math.paren_mul_right u d.ri (pow2 256);
    Math.lemma_mod_mul_distr_l (u * d.ri) (pow2 256) d.m;
    Math.small_mod u d.m

let mev_uniq (d: modulus) (x: MA.elem d.m) (s: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ mform d x s) (ensures mev d s == x)
  = rcancel1 d x;
    Math.lemma_mod_mul_distr_l (pow2 256 * x) d.ri d.m;
    Math.small_mod x d.m

(** {2 The interface} *)

let mev_mul (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures res d (mmul d a b) /\
                   mev d (mmul d a b) == MA.mul (mev d a) (mev d b))
  = mev_form d a; mev_form d b;
    mform_mul d (mev d a) (mev d b) a b;
    mev_uniq d (MA.mul (mev d a) (mev d b)) (mmul d a b)

let mev_add (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures res d (madd d a b) /\
                   mev d (madd d a b) == MA.add (mev d a) (mev d b))
  = mev_form d a; mev_form d b;
    mform_add d (mev d a) (mev d b) a b;
    mev_uniq d (MA.add (mev d a) (mev d b)) (madd d a b)

let mev_sub (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures res d (msub d a b) /\
                   mev d (msub d a b) == MA.sub (mev d a) (mev d b))
  = mev_form d a; mev_form d b;
    mform_sub d (mev d a) (mev d b) a b;
    mev_uniq d (MA.sub (mev d a) (mev d b)) (msub d a b)

let mev_neg (d: modulus) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a)
          (ensures res d (mneg d a) /\ mev d (mneg d a) == MA.neg (mev d a))
  = mev_form d a;
    mform_neg d (mev d a) a;
    mev_uniq d (MA.neg (mev d a)) (mneg d a)

(** Entering: the plain number [eval a] comes out as the value held. *)
let mev_to (d: modulus) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a)
          (ensures res d (mmul d a d.r2) /\ mev d (mmul d a d.r2) == eval a)
  = to_mont d a;
    mmul_ok d a d.r2;
    mev_uniq d (eval a) (mmul d a d.r2)

(** Leaving: the value held comes out as a plain number. *)
let mev_of (d: modulus) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a)
          (ensures res d (mmul d a mone) /\ eval (mmul d a mone) == mev d a)
  = mev_form d a;
    of_mont d (mev d a) a

let mev_zero (d: modulus)
  : Lemma (requires modulus_ok d)
          (ensures res d mzero /\ mev d mzero == MA.zero #d.m)
  = mform_zero d; mev_uniq d (MA.zero #d.m) mzero

let mev_one (d: modulus)
  : Lemma (requires modulus_ok d)
          (ensures res d d.r1 /\ mev d d.r1 == MA.one #d.m)
  = mform_one d; mev_uniq d (MA.one #d.m) d.r1

(** Zero and equality are visible on the representation without leaving it:
    multiplication by [R] fixes zero and is injective. *)

let mev_iszero (d: modulus) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a)
          (ensures (mev d a == MA.zero #d.m <==> eval a == 0))
  = mev_form d a

let mev_eq (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures (mev d a == mev d b <==> eval a == eval b))
  = mev_form d a; mev_form d b

(** {2 Reading a bit}

    The exponentiation loop walks the exponent one bit at a time and the
    exponent arrives as limbs, so the two views have to be related once:
    bit [i] of the value is bit [i mod 32] of limb [i / 32]. *)

let ebit (s: Seq.seq nat) (i: nat { i < 256 })
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures eval s / pow2 i % 2 ==
                   Seq.index s (i / rad) / pow2 (i % rad) % 2)
  = let k = i / rad in
    let j = i % rad in
    Math.euclidean_division_definition i rad;
    Math.pow2_plus (rad * k) j;
    Math.division_multiplication_lemma (eval s) (pow2 (rad * k)) (pow2 j);
    eval_digit s k;
    let n = eval s / pow2 (rad * k) in
    Math.pow2_modulo_division_lemma_1 n j rad;
    Math.pow2_modulo_modulo_lemma_1 (n / pow2 j) 1 (rad - j)

(** And the same four bits at a time, which is what a windowed scalar
    multiplication reads.  The radix is a multiple of four, so a nibble at
    an index divisible by four never straddles two limbs; that is the only
    reason this is as short as {!ebit}. *)

let enib (s: Seq.seq nat) (i: nat { i < 256 })
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ i % 4 == 0)
          (ensures eval s / pow2 i % 16 ==
                   Seq.index s (i / rad) / pow2 (i % rad) % 16)
  = assert_norm (rad == 64);
    assert_norm (pow2 4 == 16);
    let k = i / rad in
    let j = i % rad in
    Math.euclidean_division_definition i rad;
    Math.pow2_plus (rad * k) j;
    Math.division_multiplication_lemma (eval s) (pow2 (rad * k)) (pow2 j);
    eval_digit s k;
    let n = eval s / pow2 (rad * k) in
    Math.pow2_modulo_division_lemma_1 n j rad;
    Math.pow2_modulo_modulo_lemma_1 (n / pow2 j) 4 (rad - j)

(** The two steps of a left-to-right exponentiation: one more bit of the
    exponent is one squaring and, when the bit is set, one multiplication. *)

let edigit (e: nat) (i: pos)
  : Lemma (e / pow2 (i - 1) == 2 * (e / pow2 i) + e / pow2 (i - 1) % 2)
  = Math.pow2_plus (i - 1) 1;
    Math.division_multiplication_lemma e (pow2 (i - 1)) 2;
    Math.euclidean_division_definition (e / pow2 (i - 1)) 2

let exp_step (#m: pos { 1 < m }) (x: MA.elem m) (k: nat) (b: nat { b < 2 })
  : Lemma (MA.exp x (2 * k + b) ==
             (let q = MA.mul (MA.exp x k) (MA.exp x k) in
              if b = 1 then MA.mul q x else q))
  = MA.exp_mul x k 2;
    MA.exp_two (MA.exp x k);
    MA.exp_add x (2 * k) b;
    MA.exp_one x;
    MA.mul_one (MA.exp x (2 * k))

(** A total wrapper for [MA.exp].  A Pulse [ensures] is elaborated with no
    [requires] in scope, so a postcondition may not mention a function whose
    argument is refined by one; [mpow] is [MA.exp] with the refinement moved
    inside, and under [modulus_ok] the two are the same by unfolding. *)
let mpow (d: modulus) (x: MA.elem d.m) (n: nat) : MA.elem d.m =
  if 1 < d.m then MA.exp x n else x

(** {2 Canonical limbs}

    Everything here is fully reduced, so equality of residues is equality of
    sequences, and a comparison need not normalise first.  [eval_digit] is
    the whole argument: a proper limb is a digit of the value. *)

let res_uniq (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl /\
                    bnd a base /\ bnd b base /\ eval a == eval b)
          (ensures a == b)
  = let aux (k: nat { k < nl }) : Lemma (Seq.index a k == Seq.index b k)
      = eval_digit a k; eval_digit b k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro a b

(** Reducing a value that is already below the modulus does nothing, and
    reducing one that is not changes it: so the conditional subtraction is
    itself the range check a decoder needs. *)
let csub_eq (d: modulus) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ Seq.length a == nl /\ bnd a base /\
                    eval a < 2 * d.m)
          (ensures res d (csub d a 0) /\
                   (eval (csub d a 0) == eval a <==> eval a < d.m))
  = csub_ok d a 0

#pop-options
