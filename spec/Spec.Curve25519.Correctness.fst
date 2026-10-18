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

(** X25519 key agreement: two honest parties compute the same secret.

    {!scalarmult_agree} says [scalarmult a (secret_to_public b)] and
    [scalarmult b (secret_to_public a)] are equal for every pair of
    32-byte secrets, and {!ecdh_agree} says the same of {!ecdh}, result and
    flag together.  There are no hypotheses: clamping is part of the
    specification, so every secret is a valid scalar.

    {2 Proof outline}

    {!Spec.Curve25519.Montgomery.ladder_smul} does the work: for a point
    [P] on Edwards25519 and an even scalar [k], the ladder run on
    [ucoord P] outputs [ucoord (k P)].  What is left here is bookkeeping.

    - A clamped scalar is even: its first byte is masked with [0xf8]
      ({!clamp_even}).
    - Decoding an encoded field element gives it back, so a public key
      [ucoord Q] is read as [ucoord Q] ({!decode_enc}).
    - The base point [9] is [ucoord] of the Edwards base point [g]
      ({!ucoord_g}): [g_y = 4/5], and [(1 + 4/5) / (1 - 4/5) = 9].

    So [secret_to_public b] encodes [ucoord (K_b g)], and [scalarmult a]
    of it encodes [ucoord (K_a (K_b g))], where [K] is the clamped scalar.
    Scalar multiplication composes ({!smul_mul}), so both parties hold
    [ucoord] of a point equivalent to [(K_a K_b) g], and equivalent points
    have the same [ucoord]. *)
module Spec.Curve25519.Correctness

open Spec.Ed25519
open Spec.Curve25519
open Spec.Ed25519.Group
open Spec.Curve25519.Montgomery

module M = FStar.Math.Lemmas
module Sm = Spec.Ed25519.Smul
module B = Hacl.Spec.Bytes
module S8 = Hacl.Secret.UInt8
module Seq = FStar.Seq

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40 --smtencoding.nl_arith_repr wrapped"

(** {2 Scalars and encodings} *)

let mask_even (x: nat { x < 256 }) : Lemma (UInt.logand #8 x 0xf8 % 2 == 0) =
  UInt.logand_mask #8 (UInt.logand #8 x 0xf8) 1;
  UInt.logand_associative #8 x 0xf8 1;
  assert_norm (UInt.logand #8 0xf8 1 == 0);
  UInt.logand_lemma_1 #8 x

#push-options "--smtencoding.nl_arith_repr boxwrap"
let low_byte (n: nat) : Lemma ((n / pow2 (8 * 0)) % 256 % 2 == n % 2) =
  assert_norm (pow2 (8 * 0) == 1);
  M.modulo_modulo_lemma n 2 128

let mul_comm (m n: nat) : Lemma (m * n == n * m) = ()

let mul_zero (n: nat) : Lemma (n * 0 == 0) = ()

let mul_succ (n: nat) (m: pos) : Lemma (n * (m - 1) + n == n * m) = ()
#pop-options

(** A clamped scalar is even. *)
let clamp_even (k: Seq.lseq S8.t 32) : Lemma (B.le_nat (clamp k) % 2 == 0) =
  B.le_nat_byte (clamp k) 0;
  mask_even (S8.v (Seq.index k 0));
  low_byte (B.le_nat (clamp k))

(** An encoded field element decodes to itself. *)
let decode_enc (x: elem) : Lemma (decode_point (B.nat_to_le 32 x) == x) =
  assert_norm (prime < pow2 255 /\ pow2 255 < pow2 (8 * 32));
  B.le_nat_to_le 32 x;
  M.small_mod x (pow2 255);
  M.small_mod x prime

let nine : elem = assert_norm (9 < prime); 9

(** The base point [9] is the image of the Edwards base point. *)
let ucoord_g () : Lemma (ucoord g == 9) =
  ucoord_def g;
  finv_one (); mul_one g_y;
  assert_norm (fsub one g_y <> 0);
  assert_norm (fmul nine (fsub one g_y) == fadd one g_y);
  div_mul (fadd one g_y) (fsub one g_y);
  cancel (uenc g_y) nine (fsub one g_y)

(** {2 Points} *)

let ucoord_congr (p q: ext_point)
  : Lemma (requires on_curve p /\ on_curve q /\ point_equal p q) (ensures ucoord p == ucoord q)
  = yv_eq p q; ucoord_def p; ucoord_def q

[@@"opaque_to_smt"]
let is_mul (m n: nat) (p: ext_point) : prop =
  point_equal (Sm.smul m (Sm.smul n p)) (Sm.smul (n * m) p)

let is_mul_def (m n: nat) (p: ext_point)
  : Lemma (is_mul m n p <==> point_equal (Sm.smul m (Sm.smul n p)) (Sm.smul (n * m) p)) =
  FStar.Pervasives.reveal_opaque (`%is_mul) is_mul

let is_mul_zero (n: nat) (p: ext_point) : Lemma (is_mul 0 n p) =
  is_mul_def 0 n p;
  mul_zero n;
  Sm.smul_zero (Sm.smul n p); Sm.smul_zero p;
  point_at_infinity_on_curve ();
  point_equal_refl point_at_infinity

(** [m (n P) = (m - 1) (n P) + n P = (n (m - 1)) P + n P = (n m) P]. *)
let is_mul_succ (m: pos) (n: nat) (p: ext_point)
  : Lemma (requires on_curve p /\ is_mul (m - 1) n p) (ensures is_mul m n p)
  = is_mul_def (m - 1) n p; is_mul_def m n p;
    let q = Sm.smul n p in
    let r = Sm.smul (m - 1) q in
    Sm.smul_ok n p; Sm.smul_ok (m - 1) q; Sm.smul_ok m q;
    Sm.smul_ok (n * (m - 1)) p; Sm.smul_ok (n * m) p;
    Sm.smul_one q; Sm.smul_ok 1 q;
    point_equal_sym (Sm.smul 1 q) q;
    point_equal_refl r; point_equal_refl q;
    Sm.smul_add_congr (m - 1) 1 q r q;
    Sm.smul_add_congr (n * (m - 1)) n p r q;
    mul_succ n m;
    point_equal_sym (point_add r q) (Sm.smul m q);
    point_equal_trans (Sm.smul m q) (point_add r q) (Sm.smul (n * m) p)

let nz (m: int) : Lemma (requires m <= 0 /\ m >= 0) (ensures m == 0) = ()

let pn (m: int) : Lemma (requires ~(m <= 0)) (ensures m - 1 >= 0) = ()

let rec is_mul_all (m n: nat) (p: ext_point)
  : Lemma (requires m >= 0 /\ on_curve p) (ensures is_mul m n p) (decreases m)
  = if m <= 0 then (nz m; is_mul_zero n p)
    else (pn m; is_mul_all (m - 1) n p; is_mul_succ m n p)

(** Scalar multiplication composes. *)
let smul_mul (m n: nat) (p: ext_point)
  : Lemma (requires on_curve p)
          (ensures point_equal (Sm.smul m (Sm.smul n p)) (Sm.smul (n * m) p))
  = is_mul_all m n p; is_mul_def m n p

(** {2 Agreement} *)

(** [scalarmult] on an honest public key multiplies the point. *)
let scalarmult_point (k: Seq.lseq S8.t 32) (q: ext_point)
  : Lemma (requires on_curve q)
          (ensures scalarmult k (B.nat_to_le 32 (ucoord q)) ==
                   B.nat_to_le 32 (ucoord (Sm.smul (B.le_nat (clamp k)) q)))
  = decode_enc (ucoord q);
    clamp_even k;
    ladder_smul (clamp k) q

let public_key (k: Seq.lseq S8.t 32)
  : Lemma (secret_to_public k == B.nat_to_le 32 (ucoord (Sm.smul (B.le_nat (clamp k)) g)))
  = ucoord_g ();
    g_on_curve ();
    scalarmult_point k g

let shared (a b: Seq.lseq S8.t 32)
  : Lemma (scalarmult a (secret_to_public b) ==
           B.nat_to_le 32 (ucoord (Sm.smul (B.le_nat (clamp b) * B.le_nat (clamp a)) g)))
  = let ka = B.le_nat (clamp a) in
    let kb = B.le_nat (clamp b) in
    g_on_curve ();
    public_key b;
    Sm.smul_ok kb g;
    scalarmult_point a (Sm.smul kb g);
    smul_mul ka kb g;
    Sm.smul_ok ka (Sm.smul kb g);
    Sm.smul_ok (kb * ka) g;
    ucoord_congr (Sm.smul ka (Sm.smul kb g)) (Sm.smul (kb * ka) g)

(** Two honest parties agree on the shared secret. *)
let scalarmult_agree (a b: Seq.lseq S8.t 32)
  : Lemma (Spec.Curve25519.scalarmult a (Spec.Curve25519.secret_to_public b) ==
           Spec.Curve25519.scalarmult b (Spec.Curve25519.secret_to_public a))
  = shared a b;
    shared b a;
    mul_comm (B.le_nat (clamp a)) (B.le_nat (clamp b))

(** ... and so on the [ecdh] result and its flag. *)
let ecdh_agree (a b: Seq.lseq S8.t 32)
  : Lemma (Spec.Curve25519.ecdh a (Spec.Curve25519.secret_to_public b) ==
           Spec.Curve25519.ecdh b (Spec.Curve25519.secret_to_public a))
  = scalarmult_agree a b

#pop-options
