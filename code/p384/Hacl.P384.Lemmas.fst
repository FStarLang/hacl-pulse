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

(** Montgomery arithmetic, as statements about numbers.

    The generic bignum code states every Montgomery operation as a
    congruence -- [(v R) mod m = (a b) mod m] and the like -- and leaves the
    meaning of a residue to the caller.  The P-384 field keeps [x R mod p]
    and reads it back as [v R^-1 mod p], with [R^-1] a concrete number; the
    lemmas below turn each congruence into the [Spec.ModArith] operation it
    implements.  None of them knows which modulus it is about. *)
module Hacl.P384.Lemmas

open Spec.Bignum

module Math = FStar.Math.Lemmas
module MA = Spec.ModArith

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** [R R^-1 = 1], so multiplying by both changes nothing. *)
let cancel (m: pos) (r rinv: nat) (x: int)
  : Lemma (requires r * rinv % m == 1) (ensures x * r * rinv % m == x % m)
  = Math.paren_mul_right x r rinv;
    Math.lemma_mod_mul_distr_r x (r * rinv) m

let rearrange (a b c d: int) : Lemma (a * c * (b * d) == (a * b) * (c * d)) = ()

let rearrange2 (v r c: int) : Lemma (v * r * c * c == (v * r) * (c * c)) = ()

(** The Montgomery product. *)
let mul_lemma (m: pos) (r rinv: nat) (v a b: nat)
  : Lemma (requires r * rinv % m == 1 /\ (v * r) % m == (a * b) % m)
          (ensures v * rinv % m == ((a * rinv % m) * (b * rinv % m)) % m)
  = Math.lemma_mod_mul_distr_l (a * rinv) (b * rinv % m) m;
    Math.lemma_mod_mul_distr_r (a * rinv) (b * rinv) m;
    rearrange a b rinv rinv;
    cancel m r rinv v;
    Math.lemma_mod_mul_distr_l v rinv m;
    Math.lemma_mod_mul_distr_l (v * r * rinv) rinv m;
    rearrange2 v r rinv;
    Math.lemma_mod_mul_distr_l (v * r) (rinv * rinv) m;
    Math.lemma_mod_mul_distr_l (a * b) (rinv * rinv) m

(** Modular sum and difference commute with the representation. *)
let add_lemma (m: pos) (rinv: nat) (a b: nat)
  : Lemma (((a + b) % m) * rinv % m == ((a * rinv % m) + (b * rinv % m)) % m)
  = Math.lemma_mod_mul_distr_l (a + b) rinv m;
    Math.distributivity_add_left a b rinv;
    Math.lemma_mod_plus_distr_l (a * rinv) (b * rinv) m;
    Math.lemma_mod_plus_distr_r (a * rinv % m) (b * rinv) m

let sub_lemma (m: pos) (rinv: nat) (a b: nat)
  : Lemma (((a - b) % m) * rinv % m == ((a * rinv % m) + m - (b * rinv % m)) % m)
  = Math.lemma_mod_mul_distr_l (a - b) rinv m;
    Math.distributivity_sub_left a b rinv;
    Math.lemma_mod_plus_distr_l (a * rinv) (- (b * rinv)) m;
    Math.lemma_mod_sub_distr (a * rinv % m) (b * rinv) m;
    Math.lemma_mod_plus ((a * rinv % m) - (b * rinv % m)) 1 m

(** A constant stored as [x R mod m] reads back as [x]. *)
let const_lemma (m: pos) (r rinv: nat) (x: nat)
  : Lemma (requires r * rinv % m == 1) (ensures (x * r % m) * rinv % m == x % m)
  = Math.lemma_mod_mul_distr_l (x * r) rinv m;
    cancel m r rinv x

(** Entering Montgomery form is a product with [R^2 mod m]. *)
let to_lemma (m: pos) (r rinv: nat) (v a: nat)
  : Lemma (requires r * rinv % m == 1 /\ a < m /\ (v * r) % m == (a * (r * r % m)) % m)
          (ensures v * rinv % m == a)
  = mul_lemma m r rinv v a (r * r % m);
    Math.lemma_mod_mul_distr_l (r * r) rinv m;
    cancel m r rinv r;
    Math.lemma_mod_mul_distr_l (a * rinv) (r % m) m;
    Math.lemma_mod_mul_distr_r (a * rinv) r m;
    Math.small_mod a m;
    cancel m r rinv a;
    Math.paren_mul_right a rinv r;
    Math.paren_mul_right a r rinv;
    Math.swap_mul rinv r

(** Leaving it is a reduction of the residue alone. *)
let from_lemma (m: pos) (r rinv: nat) (v a: nat)
  : Lemma (requires r * rinv % m == 1 /\ v < m /\ (v * r) % m == a % m)
          (ensures v == a * rinv % m)
  = cancel m r rinv v;
    Math.small_mod v m;
    Math.lemma_mod_mul_distr_l (v * r) rinv m;
    Math.lemma_mod_mul_distr_l a rinv m

(** The representation is a bijection on residues. *)
let inj_lemma (m: pos) (r rinv: nat) (a b: nat)
  : Lemma (requires r * rinv % m == 1 /\ a < m /\ b < m /\ a * rinv % m == b * rinv % m)
          (ensures a == b)
  = Math.swap_mul r rinv;
    cancel m rinv r a;
    cancel m rinv r b;
    Math.lemma_mod_mul_distr_l (a * rinv) r m;
    Math.lemma_mod_mul_distr_l (b * rinv) r m;
    Math.small_mod a m;
    Math.small_mod b m

#pop-options

(** [Spec.Bignum.pw] reduced is [Spec.ModArith.exp]: the generic modular
    inverse states its result one way and [Spec.ModArith.inv] is defined the
    other. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let rec pw_exp (m: pos { 1 < m }) (x: nat { x < m }) (k: nat)
  : Lemma (ensures pw x k % m == MA.exp #m x k) (decreases k)
  = if k = 0 then Math.small_mod 1 m
    else begin
      pw_exp m x (k - 1);
      Math.lemma_mod_mul_distr_r x (pw x (k - 1)) m
    end
#pop-options
