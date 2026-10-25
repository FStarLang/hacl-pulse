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

(** RSASSA-PKCS1-v1_5 is correct: with a valid key, signing succeeds and
    the signature verifies.

    {!Hacl.RSAPKCS1} specifies its two directions by postconditions.  With
    [k = ceil(modBits/8)], [n = be_nat nb], [di] the DigestInfo prefix of
    the hash, and [rsa_pow] the function of {!Spec.RSAPSS.Fermat} (which is
    {!Hacl.RSAPSS.rsa_pow} verbatim), [sign] returns [ok] with

    {[ ok <==> pkcs1_signable p di k msg n
       ok ==> pkcs1_signed p di k msg n d (be_nat sg) ]}

    and [verify] accepts [sg] under the public exponent [e] exactly when

    {[ 1 < n /\ n % 2 == 1 /\ be_nat sg < n /\
       pkcs1_valid p di k msg (rsa_pow (be_nat sg) e n) ]}

    The headline, [sign_then_verify], is that with [rsa_key n e d p q] (see
    {!Spec.RSAPSS.Fermat}), [modBits] the bit length of [n] -- precisely,
    [pow2 (modBits - 1) <= n] -- and a modulus long enough for the
    encoding, both report success.  Unlike {!Spec.RSAPSS.Correctness}, the
    success of signing is a conclusion rather than a hypothesis: [sign]
    says exactly when it fails, and a valid key is never such a case.

    {b The proof} has two parts.

    - {b The encoding is below the modulus}
      ({!Spec.RSAPKCS1.pkcs1_encode_lt}).  It starts with a zero byte, so it
      is below [2^(8(k-1))], which is at most [2^(modBits-1) <= n].  So
      signing applies.

    - {b The RSA function inverts} ({!Spec.RSAPSS.Fermat.rsa_inverse}): for
      [m < n], [(m^d mod n)^e mod n = m].  So the verifier recovers the very
      encoding it recomputes. *)
module Spec.RSAPKCS1.Correctness

open Hacl.Secret.Word
open Spec.SHA2
open Hacl.Spec.Bytes
open Spec.RSAPKCS1
open Spec.RSAPSS.Fermat

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** A valid key, long enough for the encoding, can sign. *)
let sign_succeeds (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                  (modBits: pos) (msg: Seq.seq S8.t)
                  (n e d: nat) (pr qr: int)
  : Lemma (requires rsa_key n e d pr qr /\ pow2 (modBits - 1) <= n /\
                    Seq.length msg < max_input #t /\
                    pkcs1_ok p (Seq.length di) ((modBits + 7) / 8))
          (ensures pkcs1_signable p di ((modBits + 7) / 8) msg n)
  = let k = (modBits + 7) / 8 in
    rsa_key_odd n e d pr qr;
    pkcs1_encode_lt p di k msg;
    Math.pow2_le_compat (modBits - 1) (8 * (k - 1))

(** A signature made with a valid key passes verification under the
    matching public key.  [sg] is anything whose number is the signature;
    the conclusion is the right-hand side of [verify]'s [ok <==> ...]. *)
let sign_verify (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                (modBits: pos) (msg: Seq.seq S8.t)
                (n e d: nat) (pr qr: int) (sg: Seq.seq S8.t)
  : Lemma (requires rsa_key n e d pr qr /\ pow2 (modBits - 1) <= n /\
                    pkcs1_signed p di ((modBits + 7) / 8) msg n d (be_nat sg))
          (ensures 1 < n /\ n % 2 == 1 /\ be_nat sg < n /\
                   pkcs1_valid p di ((modBits + 7) / 8) msg (rsa_pow (be_nat sg) e n))
  = let k = (modBits + 7) / 8 in
    sign_succeeds p di modBits msg n e d pr qr;
    rsa_inverse n e d pr qr (be_nat (pkcs1_encode p di k msg))

(** The same, with [sign]'s and [verify]'s postconditions as they are
    written in {!Hacl.RSAPKCS1}: both report success. *)
let sign_then_verify (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                     (modBits: pos) (msg: Seq.seq S8.t)
                     (nb eb db sg: Seq.seq S8.t) (pr qr: int) (okS okV: bool)
  : Lemma (requires
      rsa_key (be_nat nb) (be_nat eb) (be_nat db) pr qr /\
      pow2 (modBits - 1) <= be_nat nb /\
      Seq.length msg < max_input #t /\
      pkcs1_ok p (Seq.length di) ((modBits + 7) / 8) /\
      (okS <==> pkcs1_signable p di ((modBits + 7) / 8) msg (be_nat nb)) /\
      (okS ==> pkcs1_signed p di ((modBits + 7) / 8) msg (be_nat nb) (be_nat db) (be_nat sg)) /\
      (okV <==> (1 < be_nat nb /\ be_nat nb % 2 == 1 /\ be_nat sg < be_nat nb /\
                 pkcs1_valid p di ((modBits + 7) / 8) msg
                             (rsa_pow (be_nat sg) (be_nat eb) (be_nat nb)))))
    (ensures okS /\ okV)
  = sign_succeeds p di modBits msg (be_nat nb) (be_nat eb) (be_nat db) pr qr;
    sign_verify p di modBits msg (be_nat nb) (be_nat eb) (be_nat db) pr qr sg

#pop-options
