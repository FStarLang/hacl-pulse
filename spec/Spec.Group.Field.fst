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

(** The field facts the group-law proofs need, for [Spec.ModArith] at a
    prime modulus: Fermat's inverse really inverts, there are no zero
    divisors, nonzero factors cancel, and Euler's criterion rules out square
    roots.  [Spec.ModArith] deliberately proves none of these -- nothing
    outside the group law needs them -- and all of them rest on primality,
    which [Spec.Group.Prime] supplies. *)
module Spec.Group.Field

open Spec.ModArith
module M = FStar.Math.Lemmas
module E = FStar.Math.Euclid
module F = FStar.Math.Fermat

let prime_mod = m: pos { E.is_prime m }

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(** [exp] is [Fermat.pow] reduced. *)
let rec exp_pow (#m: pos { 1 < m }) (x: elem m) (n: nat)
  : Lemma (ensures exp x n == F.pow x n % m) (decreases n)
  = if n = 0 then M.small_mod 1 m
    else begin
      exp_pow x (n - 1);
      M.lemma_mod_mul_distr_r x (F.pow x (n - 1)) m
    end

let mul_inv (#m: prime_mod) (x: elem m)
  : Lemma (requires x <> 0) (ensures mul x (inv x) == one)
  = exp_pow x (m - 2);
    M.small_mod x m;
    F.fermat_alt m x;
    M.lemma_mod_mul_distr_r x (F.pow x (m - 2)) m;
    assert (F.pow x (m - 1) == x * F.pow x (m - 2))

let inv_mul (#m: prime_mod) (x: elem m)
  : Lemma (requires x <> 0) (ensures mul (inv x) x == one)
  = mul_inv x; mul_comm x (inv x)

let inv_nonzero (#m: prime_mod) (x: elem m)
  : Lemma (requires x <> 0) (ensures inv x <> 0)
  = mul_inv x

let no_zero_div (#m: prime_mod) (x y: elem m)
  : Lemma (requires mul x y == zero) (ensures x == zero \/ y == zero)
  = E.euclid_prime m x y;
    M.small_mod x m; M.small_mod y m

let mul_nonzero (#m: prime_mod) (x y: elem m)
  : Lemma (requires x <> 0 /\ y <> 0) (ensures mul x y <> 0)
  = if mul x y = 0 then no_zero_div x y

(** Cancel a nonzero factor on the right. *)
let cancel (#m: prime_mod) (a b c: elem m)
  : Lemma (requires c <> 0 /\ mul a c == mul b c) (ensures a == b)
  = calc (==) {
      a;
      == { mul_one a }
      mul a one;
      == { mul_inv c }
      mul a (mul c (inv c));
      == { mul_assoc a c (inv c) }
      mul (mul a c) (inv c);
      == { }
      mul (mul b c) (inv c);
      == { mul_assoc b c (inv c) }
      mul b (mul c (inv c));
      == { mul_inv c }
      mul b one;
      == { mul_one b }
      b;
    }

(** [x = (x * inv z) * z] for [z] nonzero: the canonical-representative
    decomposition in one line. *)
let div_mul (#m: prime_mod) (x z: elem m)
  : Lemma (requires z <> 0) (ensures mul (mul x (inv z)) z == x)
  = mul_assoc x (inv z) z; inv_mul z; mul_one x

let mul4 (#m: pos) (a b c d: elem m)
  : Lemma (mul (mul a b) (mul c d) == mul (mul a c) (mul b d))
  = mul_assoc a b (mul c d);
    mul_assoc b c d;
    mul_comm b c;
    mul_assoc c b d;
    mul_assoc a c (mul b d)

let rec exp_mul_distr (#m: pos { 1 < m }) (x y: elem m) (n: nat)
  : Lemma (ensures exp (mul x y) n == mul (exp x n) (exp y n)) (decreases n)
  = if n = 0 then mul_one (one #m)
    else begin
      exp_mul_distr x y (n - 1);
      mul4 x y (exp x (n - 1)) (exp y (n - 1))
    end

(** Fermat for [exp]: a nonzero [x] has [x^(m-1) = 1]. *)
let exp_fermat (#m: prime_mod) (x: elem m)
  : Lemma (requires x <> 0) (ensures exp x (m - 1) == one)
  = exp_pow x (m - 1); M.small_mod x m; F.fermat_alt m x

(** Euler's criterion, the half that is needed: if [d^((m-1)/2)] is
    [m - 1], then [d] is not a square. *)
let not_square (#m: prime_mod) (d: elem m)
  : Lemma (requires m % 2 == 1 /\ 2 < m /\ exp d ((m - 1) / 2) == m - 1)
          (ensures forall (s: elem m). mul s s =!= d)
  = let aux (s: elem m) : Lemma (mul s s =!= d) =
      if mul s s = d then begin
        if s = 0 then begin
          let rec z (n: pos) : Lemma (ensures exp #m 0 n == 0) (decreases n) =
            if n = 1 then () else z (n - 1) in
          z ((m - 1) / 2)
        end else begin
          let k = (m - 1) / 2 in
          assert (2 * k == m - 1);
          exp_mul s 2 k;
          exp_two s;
          exp_fermat s;
          assert (exp d k == exp s (m - 1));
          assert (one #m == 1)
        end
      end in
    FStar.Classical.forall_intro aux

#pop-options
