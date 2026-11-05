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

(** The RSA permutation is a permutation: for a key [(n, e, d)] with
    [n = p * q], and every [m < n],

    {[ rsa_pow (rsa_pow m d n) e n == m ]}

    which is [rsa_inverse].  [rsa_pow] is the function the postconditions of
    {!Hacl.RSAPSS} are written with, repeated here verbatim so that this
    module depends on no implementation.

    {b The key.}  [rsa_key n e d p q] asks for [p] and [q] distinct primes
    with product [n], and [e * d = 1] modulo both [p - 1] and [q - 1] --
    that is, modulo [lcm(p - 1, q - 1)], which is the weakest hypothesis
    under which the theorem holds for every [m].  The usual
    [e * d = 1 mod (p - 1)(q - 1)] implies it ([rsa_key_phi]).  The
    congruences are stated with remainder [1] rather than [1 % (p - 1)],
    which rules out [p = 2]; that loses nothing, because the implementation
    rejects an even modulus anyway, and it is what makes [n] odd
    ([rsa_key_odd]).

    {b The proof} is the textbook one.  [(m^d)^e = m^(e*d)] modulo [n]
    ([pw_mod], [pw_pw]).  Modulo each prime, [m^(k(p-1)+1) = m]: either [p]
    divides [m] and both sides are zero, or Fermat's little theorem
    ({!FStar.Math.Fermat.fermat_alt}) makes [m^(p-1)] one ([fermat_exp]).
    Two numbers that agree modulo two distinct primes agree modulo their
    product, by Euclid's lemma ([crt]). *)
module Spec.RSAPSS.Fermat

open FStar.Math.Euclid
open Spec.Bignum

module Math = FStar.Math.Lemmas
module F = FStar.Math.Fermat

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(** {2 Powers} *)

#push-options "--fuel 1"

let rec pw_pow (a: nat) (k: nat)
  : Lemma (ensures pw a k == F.pow a k) (decreases k)
  = if k = 0 then () else pw_pow a (k - 1)

let rec pw_one (k: nat) : Lemma (ensures pw 1 k == 1) (decreases k)
  = if k = 0 then () else pw_one (k - 1)

#push-options "--fuel 2"
let pw_1 (a: nat) : Lemma (pw a 1 == a) = ()
#pop-options

let rec pw_mod (a: nat) (k: nat) (p: pos)
  : Lemma (ensures pw (a % p) k % p == pw a k % p) (decreases k)
  = if k = 0 then ()
    else begin
      pw_mod a (k - 1) p;
      Math.lemma_mod_mul_distr_r (a % p) (pw (a % p) (k - 1)) p;
      Math.lemma_mod_mul_distr_r (a % p) (pw a (k - 1)) p;
      Math.lemma_mod_mul_distr_l a (pw a (k - 1)) p
    end

let rec pw_pw (a: nat) (b c: nat)
  : Lemma (ensures pw (pw a b) c == pw a (b * c)) (decreases c)
  = if c = 0 then ()
    else begin
      pw_pw a b (c - 1);
      pw_add a b (b * (c - 1));
      Math.distributivity_sub_right b c 1
    end

#pop-options

(** {2 Fermat and the Chinese remainder theorem} *)

(** [m^x = m] modulo a prime [p], for every [x = 1] modulo [p - 1]. *)
let fermat_exp (p: int { is_prime p }) (m: nat) (x: nat)
  : Lemma (requires x % (p - 1) == 1) (ensures pw m x % p == m % p)
  = let k = x / (p - 1) in
    Math.euclidean_division_definition x (p - 1);
    pw_add m (k * (p - 1)) 1;
    pw_1 m;
    let a = pw m (k * (p - 1)) in
    assert (pw m x == a * m);
    if m % p = 0 then begin
      Math.lemma_mod_mul_distr_r a m p;
      assert (pw m x % p == 0)
    end else begin
      F.fermat_alt p m;
      pw_pow m (p - 1);
      pw_pw m (p - 1) k;
      Math.swap_mul (p - 1) k;
      pw_mod (pw m (p - 1)) k p;
      pw_one k;
      Math.small_mod 1 p;
      assert (a % p == 1);
      Math.lemma_mod_mul_distr_l a m p
    end

(** Agreement modulo two distinct primes is agreement modulo their
    product. *)
let crt (p q: int) (x y: nat)
  : Lemma (requires is_prime p /\ is_prime q /\ p <> q /\
                    x % p == y % p /\ x % q == y % q)
          (ensures x % (p * q) == y % (p * q))
  = Math.euclidean_division_definition x p;
    Math.euclidean_division_definition y p;
    Math.euclidean_division_definition x q;
    Math.euclidean_division_definition y q;
    let k = x / p - y / p in
    assert (x - y == p * k);
    assert (x - y == q * (x / q - y / q));
    Math.cancel_mul_mod (x / q - y / q) q;
    assert ((p * k) % q == 0);
    euclid_prime q p k;
    if p % q = 0 then begin
      mod_divides p q;
      assert (q `divides` p)
    end else begin
      Math.euclidean_division_definition k q;
      let j = k / q in
      assert (k == q * j);
      Math.paren_mul_right p q j;
      assert (x == y + (p * q) * j);
      Math.lemma_mod_plus y j (p * q)
    end

(** {2 RSA} *)

(** [s^e mod n], total in [n]: {!Hacl.RSAPSS.rsa_pow}, verbatim. *)
let rsa_pow (s e n: nat) : nat = if n = 0 then 0 else pw s e % n

(** A valid RSA key.  [p] and [q] are the secret factorization. *)
let rsa_key (n e d: nat) (p q: int) : prop =
  is_prime p /\ is_prime q /\ p <> q /\ n == p * q /\
  (e * d) % (p - 1) == 1 /\ (e * d) % (q - 1) == 1

let prime_odd (p: int)
  : Lemma (requires is_prime p /\ p <> 2) (ensures p % 2 == 1)
  = if p % 2 = 0 then mod_divides p 2

(** What the implementation checks of a modulus holds for a valid key. *)
let rsa_key_odd (n e d: nat) (p q: int)
  : Lemma (requires rsa_key n e d p q) (ensures 1 < n /\ n % 2 == 1)
  = prime_odd p;
    prime_odd q;
    Math.lemma_mod_mul_distr_l p q 2;
    Math.lemma_mod_mul_distr_r 1 q 2;
    Math.lemma_mult_le_right q 2 p

(** Signing then verifying is the identity on every number below [n]. *)
let rsa_inverse (n e d: nat) (p q: int) (m: nat)
  : Lemma (requires rsa_key n e d p q /\ m < n)
          (ensures rsa_pow (rsa_pow m d n) e n == m)
  = pw_mod (pw m d) e n;
    pw_pw m d e;
    Math.swap_mul d e;
    fermat_exp p m (d * e);
    fermat_exp q m (d * e);
    crt p q (pw m (d * e)) m;
    Math.small_mod m n

(** The textbook hypothesis [e * d = 1 mod phi(n)] implies [rsa_key], for
    odd primes. *)
let rsa_key_phi (n e d: nat) (p q: int)
  : Lemma (requires is_prime p /\ is_prime q /\ p <> q /\ 2 < p /\ 2 < q /\ n == p * q /\
                    (e * d) % ((p - 1) * (q - 1)) == 1)
          (ensures rsa_key n e d p q)
  = Math.modulo_modulo_lemma (e * d) (p - 1) (q - 1);
    Math.swap_mul (p - 1) (q - 1);
    Math.modulo_modulo_lemma (e * d) (q - 1) (p - 1);
    Math.small_mod 1 (p - 1);
    Math.small_mod 1 (q - 1)

#pop-options
