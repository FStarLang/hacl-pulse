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

(** Ed25519's group order as an instance of {!Spec.Field4}.

    Ed25519 has a second modulus besides the field's: the order [q] of the
    prime-order subgroup, which is where the [S] half of a signature lives.
    Two things happen modulo [q] -- a 512-bit hash has to be reduced, and
    one product [k s] has to be formed -- and the sensible way to do either
    is the Montgomery arithmetic that P-256 and secp256k1 already use, so
    this module contributes the modulus, its Montgomery constant and a
    witness for [R]'s inverse, exactly as {!Spec.K256.Field} does.

    What is not shared is the direction the bytes run.  Ed25519 is
    little-endian everywhere and the other two curves are big-endian, so
    the byte layer of {!Spec.Field4} is mirrored here rather than widened
    there: {!eval_le} reads four limbs off a thirty-two byte string, and
    {!store_le_ok} writes them back.  They are the same two lemmas with the
    limb order reversed.

    The other two lemmas are about reducing something wider than a residue.
    Montgomery multiplication cancels one factor of [R], so multiplying a
    residue by a constant that already carries an [R] is a plain
    multiplication modulo [q] ({!mmul_const}), and multiplying by [R^2] and
    then cancelling twice is an ordinary product ({!mmul_plain}).  With the
    first of those, reducing a 512-bit number is four residues below
    [2^128] combined with three constants -- no wide division and no
    Barrett. *)
module Spec.Ed25519.Scalar

include Spec.Field4

open Spec.Bignum4
open Spec.Montgomery4
open Spec.Mont4
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The modulus} *)

let q : pos = Spec.Ed25519.q

let q_bound (_: unit) : Lemma (0 < q /\ 2 * q + 1 < pow2 256 /\ q < pow2 255) =
  assert_norm (2 * (pow2 252 + 27742317777372353535851937790883648493) + 1 < pow2 256);
  assert_norm (pow2 252 + 27742317777372353535851937790883648493 < pow2 255)

let qmod : modulus =
  assert_norm (q < pow2 256);
  mk q 15183074304973897243
     0x9db6c6f26fe9183614e75438ffa36beb7f5c66a973f754cc766cca43d5f0d24

let qmod_m (_: unit) : Lemma (qmod.m == q) = ()

let qmod_ok (_: unit) : Lemma (modulus_ok qmod) =
  assert_norm (q < pow2 256);
  assert_norm (1 < q);
  assert_norm (15183074304973897243 < pow2 rad);
  assert_norm (((q % pow2 rad) * 15183074304973897243 + 1) % pow2 rad == 0);
  assert_norm (pow2 256 *
    0x9db6c6f26fe9183614e75438ffa36beb7f5c66a973f754cc766cca43d5f0d24
    % q == 1);
  mk_ok q 15183074304973897243
    0x9db6c6f26fe9183614e75438ffa36beb7f5c66a973f754cc766cca43d5f0d24

(** {2 Multiplying by a constant that carries a radix}

    [mmul] computes [a b R^-1 mod q].  If [b] is a compile-time constant
    equal to [R k mod q] then the [R]s cancel and the result is [a k mod q]
    -- a plain modular multiplication by [k], for any [k] at all, including
    the powers of two that a wide reduction needs.

    The proof is one application of [rcancel]: [mmul_ok] states its
    conclusion multiplied by [R], and so does the goal once [eval b] is
    unfolded, so the two agree before the cancellation and the results
    agree after it. *)

let mmul_const (a p: Seq.seq nat) (k: nat)
  : Lemma (requires res qmod a /\ res qmod p /\ eval p == pow2 256 * k % q)
          (ensures res qmod (mmul qmod a p) /\
                   eval (mmul qmod a p) == eval a * k % q)
  = qmod_ok ();
    let d = qmod in
    let w = mmul d a p in
    mmul_ok d a p;
    (* [R w = a (R k mod q) = a (R k) = R (a k)] modulo [q]. *)
    Math.lemma_mod_mul_distr_r (eval a) (pow2 256 * k) d.m;
    Math.paren_mul_right (eval a) (pow2 256) k;
    Math.swap_mul (eval a) (pow2 256);
    Math.paren_mul_right (pow2 256) (eval a) k;
    rcancel d (eval w) (eval a * k);
    Math.small_mod (eval w) d.m

(** An ordinary product of two residues: cancel one [R] with [mmul] and put
    it back with [R^2], which is the constant the modulus already carries
    for entering Montgomery form. *)

let mmul_plain (a b: Seq.seq nat)
  : Lemma (requires res qmod a /\ res qmod b)
          (ensures res qmod (mmul qmod (mmul qmod a b) qmod.r2) /\
                   eval (mmul qmod (mmul qmod a b) qmod.r2) ==
                     eval a * eval b % q)
  = qmod_ok ();
    let d = qmod in
    let u = mmul d a b in
    mmul_ok d a b;
    Math.lemma_mod_lt (pow2 256 * pow2 256) d.m;
    assert (res d d.r2);
    mmul_const u d.r2 (pow2 256);
    Math.swap_mul (eval u) (pow2 256)

(** {2 Little-endian bytes}

    The mirror of [Spec.Field4]'s big-endian pair.  Reading is the easier
    direction: limb [k] is [le_nat] of bytes [8k] to [8k + 8], and cutting
    the string after eight bytes gives exactly the recursive step of [eval],
    so nothing has to be unfolded a byte at a time. *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let rec eval_le (b: Seq.seq S8.t) (s: Seq.seq nat)
  : Lemma (requires Seq.length b == 8 * Seq.length s /\
                    (forall (k: nat). {:pattern (Seq.index s k)}
                       k < Seq.length s ==>
                         Seq.index s k == le_nat (Seq.slice b (8 * k) (8 * k + 8))))
          (ensures eval s == le_nat b)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let b' = Seq.slice b 8 (8 * n) in
      let s' = Seq.slice s 1 n in
      le_nat_split b 8;
      assert_norm (pow2 (8 * 8) == base);
      Seq.lemma_eq_intro (Seq.slice b 0 8) (Seq.slice b (8 * 0) (8 * 0 + 8));
      let aux (k: nat { k < n - 1 })
        : Lemma (Seq.index s' k == le_nat (Seq.slice b' (8 * k) (8 * k + 8)))
        = Seq.lemma_eq_intro (Seq.slice b' (8 * k) (8 * k + 8))
                             (Seq.slice b (8 * (k + 1)) (8 * (k + 1) + 8)) in
      Classical.forall_intro aux;
      eval_le b' s'
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 400"

(** Byte [m] of limb [k], counted from the bottom of the limb, is byte
    [64 k + 8 m] of the number: [Spec.Field4.store_be_digit] with the
    within-limb index no longer reflected. *)
let store_le_digit (s: Seq.seq nat) (k: nat { k < Seq.length s }) (m: nat { m < 8 })
  : Lemma (requires bnd s base)
          (ensures (Seq.index s k / pow2 (8 * m)) % 256 ==
                   (eval s / pow2 (64 * k + 8 * m)) % 256)
  = let v = eval s in
    radf_lin k;
    assert_norm (base == 18446744073709551616);
    assert_norm (pow2 64 == 18446744073709551616);
    eval_digit s k;
    let a = v / pow2 (64 * k) in
    Math.pow2_plus (64 * k) (8 * m);
    Math.division_multiplication_lemma v (pow2 (64 * k)) (pow2 (8 * m));
    Math.pow2_modulo_division_lemma_1 a (8 * m) 64;
    Math.pow2_modulo_modulo_lemma_1 (a / pow2 (8 * m)) 8 (64 - 8 * m)

(** Byte [i] of a thirty-two byte little-endian string is byte [i mod 8] of
    limb [i / 8]. *)
let le_index_arith (i: nat { i < 32 })
  : Lemma (i / 8 < nl /\ i % 8 < 8 /\ 8 * i == 64 * (i / 8) + 8 * (i % 8))
  = assert_norm (nl == 4);
    Math.lemma_mod_lt i 8;
    Math.euclidean_division_definition i 8

(** Writing each limb out as eight bytes, least significant first and least
    significant limb first, produces the little-endian encoding.  As in the
    big-endian twin the hypothesis is quantified over the byte position and
    stated with [pow2]: eight simultaneous division facts about one limb
    are much worse for the solver than one instantiation per byte. *)
let store_le_ok (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\ bnd s base /\
                    (forall (k: nat) (m: nat). k < nl /\ m < 8 ==>
                       bat b (8 * k + m) ==
                         (Seq.index s k / pow2 (8 * m)) % 256))
          (ensures b == nat_to_le 32 (eval s))
  = let v = eval s in
    ebnd s;
    assert_norm (nl == 4);
    let aux (i: nat { i < 32 }) : Lemma (Seq.index b i == Seq.index (nat_to_le 32 v) i) =
      let k = i / 8 in
      let m = i % 8 in
      le_index_arith i;
      assert (8 * k + m == i);
      store_le_digit s k m;
      nat_to_le_index 32 v i;
      S8.v_extensional (Seq.index b i) (Seq.index (nat_to_le 32 v) i) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro b (nat_to_le 32 v)

#pop-options

#pop-options
