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

(** Arithmetic in [Z/m] for an arbitrary modulus, with the exponentiation
    lemmas an addition chain needs.

    [Spec.Curve25519] has its own copy of this specialised to [2^255 - 19],
    written before this module existed, and nothing is gained by disturbing
    it.  P-256 is the case that forces the generalisation: it has *two*
    moduli of equal standing -- the field prime and the group order -- and
    both need inversion by an addition chain, so both need [exp_add] and
    [exp_mul].  Writing the lemmas once over an abstract [m] is the whole
    point.

    The modulus is an implicit argument throughout, which makes
    [Spec.P256]'s formulas read as if there were only one field.  Where a
    proof needs the two apart, [elem p] and [elem order] are different
    types and F* keeps them apart for free. *)
module Spec.ModArith

module Math = FStar.Math.Lemmas

(** {2 The carrier} *)

let elem (m: pos) = x: nat { x < m }

let zero (#m: pos) : elem m = 0

let one (#m: pos { 1 < m }) : elem m = 1

(** {2 The ring operations}

    All three are total on [elem m] for any positive [m]; primality is only
    needed for [inv]. *)

let add (#m: pos) (x y: elem m) : elem m = (x + y) % m

let sub (#m: pos) (x y: elem m) : elem m = (x + m - y) % m

let mul (#m: pos) (x y: elem m) : elem m = (x * y) % m

let neg (#m: pos) (x: elem m) : elem m = (m - x) % m

(** Two multiplications by the same [x] reassociate, which is all that
    [mul_assoc] and [mul_comm] below are ever used for. *)
let mul_comm (#m: pos) (x y: elem m) : Lemma (mul x y == mul y x) =
  FStar.Math.Lemmas.swap_mul x y

let mul_assoc (#m: pos) (x y z: elem m)
  : Lemma (mul (mul x y) z == mul x (mul y z))
  = Math.lemma_mod_mul_distr_l (x * y) z m;
    Math.lemma_mod_mul_distr_r x (y * z) m;
    Math.paren_mul_right x y z

let add_comm (#m: pos) (x y: elem m) : Lemma (add x y == add y x) = ()

let mul_one (#m: pos { 1 < m }) (x: elem m) : Lemma (mul x one == x) =
  Math.small_mod x m

let mul_zero (#m: pos) (x: elem m) : Lemma (mul x zero == zero) = ()

(** {2 Exponentiation}

    Naive, recursing on the exponent.  An implementation never evaluates
    this; it builds an addition chain and discharges each step with
    [exp_add] or [exp_mul].  Those two lemmas are the entire interface. *)

let rec exp (#m: pos { 1 < m }) (x: elem m) (n: nat) : Tot (elem m) (decreases n) =
  if n = 0 then one else mul x (exp x (n - 1))

let exp_zero (#m: pos { 1 < m }) (x: elem m) : Lemma (exp x 0 == one) = ()

let exp_one (#m: pos { 1 < m }) (x: elem m) : Lemma (exp x 1 == x) = mul_one x

let exp_two (#m: pos { 1 < m }) (x: elem m) : Lemma (exp x 2 == mul x x) = mul_one x

(** [x^(a+b) = x^a * x^b]: one multiplication joins two chain elements. *)
let rec exp_add (#m: pos { 1 < m }) (x: elem m) (a b: nat)
  : Lemma (ensures exp x (a + b) == mul (exp x a) (exp x b)) (decreases a)
  = if a = 0 then (mul_comm (exp x b) (one #m); mul_one (exp x b))
    else begin
      exp_add x (a - 1) b;
      mul_assoc x (exp x (a - 1)) (exp x b)
    end

(** [x^(a*b) = (x^a)^b]: a run of [b] squarings, or of [b] applications of
    any chain step already built. *)
let rec exp_mul (#m: pos { 1 < m }) (x: elem m) (a b: nat)
  : Lemma (ensures exp x (a * b) == exp (exp x a) b) (decreases b)
  = if b = 0 then ()
    else begin
      exp_mul x a (b - 1);
      exp_add x a (a * (b - 1));
      Math.distributivity_add_right a 1 (b - 1)
    end

(** {2 Inversion}

    By Fermat, [x^(m-2)] inverts [x] when [m] is prime and [x] is nonzero,
    and gives zero when [x] is zero.  Nothing here proves that -- the
    library never needs [x * inv x == one] as a theorem, only that the
    implementation computes the same function the specification names. *)

let inv (#m: pos { 1 < m }) (x: elem m) : elem m = exp x (m - 2)

(** {2 Square roots for [m = 3 mod 4]}

    When [m % 4 == 3], [x^((m+1)/4)] squares to [x] exactly when [x] is a
    square, so a single exponentiation plus one check decides it.  This is
    the P-256 case; Curve25519's [m % 8 == 5] needs the messier two-candidate
    version, which is why that one lives in [Spec.Ed25519]. *)

let sqrt_cand (#m: pos { 1 < m /\ m % 4 == 3 }) (x: elem m) : elem m =
  exp x ((m + 1) / 4)

let sqrt (#m: pos { 1 < m /\ m % 4 == 3 }) (x: elem m) : option (elem m) =
  let r = sqrt_cand x in
  if mul r r = x then Some r else None
