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

(** Correctness of {!Spec.HPKE}: a receiver opens what a sender seals.

    The statements follow the layers of RFC 9180.

    - {!dh_agree}: the KEM's Diffie-Hellman gives both parties the same
      output (or fails for both), for X25519 by
      {!Spec.Curve25519.Correctness.ecdh_agree} and for P-256 by
      {!Spec.P256.ECDH.Correctness.dh_agree} through the SEC1 uncompressed
      encoding.
    - {!encap_decap} and {!auth_encap_decap}: decapsulation recovers the
      shared secret encapsulation produced.
    - {!setup_agree}: in every mode the receiver's context is the sender's.
    - {!aead_open_seal} and {!context_open_seal}: opening inverts sealing,
      for all three AEADs, by {!Spec.Chacha20Poly1305.Correctness} and
      {!Spec.GCM.Correctness}.
    - {!open_base_seal_base}: the single-shot API, end to end.

    The hypotheses are only that the receiver's public key is the one
    belonging to its private key, the same for the sender's static key in the
    authenticated modes, and that the sender succeeded.  Whether the sender
    can fail on honest keys is a separate question: for X25519 it would need
    the shared secret to be zero, and for P-256 the private key to be out of
    range, which the receiver's [secret_to_public] already excludes. *)
module Spec.HPKE.Correctness

open Spec.Byte
open Spec.HPKE

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module C = Spec.Curve25519
module P = Spec.P256
module CP = Spec.Chacha20Poly1305
module CC = Spec.Chacha20
module GCM = Spec.GCM
module AES = Spec.AES
module CPX = Spec.Chacha20Poly1305.Correctness
module GX = Spec.GCM.Correctness
module CX = Spec.Curve25519.Correctness
module PX = Spec.P256.ECDH.Correctness

#push-options "--fuel 0 --ifuel 1"

(** {2 The AEAD} *)

let aead_open_seal (a: aead_alg { ~(ExportOnly? a) })
                   (key: Seq.lseq S8.t (size_aead_key a))
                   (nonce: Seq.lseq S8.t (size_aead_nonce a))
                   (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
                   (pt: Seq.seq S8.t { aead_ok (Seq.length pt) })
  : Lemma (let ct = fst (aead_seal a key nonce aad pt) in
           let tag = snd (aead_seal a key nonce aad pt) in
           aead_open_ok a key nonce aad ct tag /\ aead_opened a key nonce ct == pt)
  = assert_norm (pow2 32 < pow2 36 - 32);
    assert_norm (pow2 32 < pow2 61 - 1);
    match a with
    | Seal_Chacha20Poly1305 ->
      assert_norm (pow2 32 <= CC.max_len 1ul);
      CPX.decrypt_encrypt key nonce aad pt
    | Seal_AES128_GCM | Seal_AES256_GCM ->
      let v = if Seal_AES128_GCM? a then AES.AES128 else AES.AES256 in
      GX.decrypt_encrypt v (vals key) (vals nonce) (vals aad) (vals pt)

(** {2 Diffie-Hellman agreement} *)

let p256_uncompressed (raw: Seq.lseq S8.t 64)
  : Lemma (P.uncompressed_to_raw (P.raw_to_uncompressed raw) == Some raw)
  = assert_norm (S8.v (S8.classify 4uy) == 4);
    Seq.lemma_eq_intro (Seq.slice (P.raw_to_uncompressed raw) 1 65) raw

let dh_agree (k: kem_alg) (skA skB: Seq.lseq S8.t (size_dh_key k))
  : Lemma (match secret_to_public k skA, secret_to_public k skB with
           | Some pA, Some pB -> dh k skA pB == dh k skB pA
           | _ -> True)
  = match k with
    | DH_X25519 -> CX.ecdh_agree skA skB
    | DH_P256 ->
      (match P.dh_initiator skA, P.dh_initiator skB with
       | Some rA, Some rB ->
         p256_uncompressed rA; p256_uncompressed rB;
         PX.dh_agree skA skB
       | _ -> ())

(** {2 The KEM} *)

let encap_decap (k: kem_alg) (skE skR: Seq.lseq S8.t (size_dh_key k))
                (pkR: Seq.lseq S8.t (size_dh_public k))
  : Lemma (requires secret_to_public k skR == Some pkR)
          (ensures (match encap k skE pkR with
                    | Some (ss, enc) -> decap k enc skR == Some ss
                    | None -> True))
  = dh_agree k skE skR

let auth_encap_decap (k: kem_alg) (skE skS skR: Seq.lseq S8.t (size_dh_key k))
                     (pkS pkR: Seq.lseq S8.t (size_dh_public k))
  : Lemma (requires secret_to_public k skR == Some pkR /\
                    secret_to_public k skS == Some pkS)
          (ensures (match auth_encap k skE skS pkR with
                    | Some (ss, enc) -> auth_decap k enc skR pkS == Some ss
                    | None -> True))
  = dh_agree k skE skR;
    dh_agree k skS skR

(** {2 Setup}

    [pkS] is the receiver's view of the sender's static key: absent in the
    unauthenticated modes, and the public half of [skS] in the others. *)

let sender_key (k: kem_alg)
               (skS: option (Seq.lseq S8.t (size_dh_key k)))
               (pkS: option (Seq.lseq S8.t (size_dh_public k))) : GTot prop =
  match skS, pkS with
  | None, None -> True
  | Some s, Some p -> secret_to_public k s == Some p
  | _ -> False

let setup_agree (#t: Type0) {| Hacl.Secret.Word.word t |} (cs: ciphersuite t) (m: mode)
                (skE skR: Seq.lseq S8.t (size_dh_key cs.kem))
                (skS: option (Seq.lseq S8.t (size_dh_key cs.kem)) { uses_auth m == Some? skS })
                (pkR: Seq.lseq S8.t (size_dh_public cs.kem))
                (pkS: option (Seq.lseq S8.t (size_dh_public cs.kem)) { uses_auth m == Some? pkS })
                (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
                (psk: Seq.seq S8.t { fits cs.kdf (Seq.length psk) })
                (psk_id: Seq.seq S8.t { fits cs.kdf (Seq.length psk_id) })
  : Lemma (requires secret_to_public cs.kem skR == Some pkR /\ sender_key cs.kem skS pkS)
          (ensures (match setup_s cs m skE skS pkR info psk psk_id with
                    | Some (enc, c) -> setup_r cs m enc skR pkS info psk psk_id == Some c
                    | None -> True))
  = match skS, pkS with
    | None, None -> encap_decap cs.kem skE skR pkR
    | Some s, Some p -> auth_encap_decap cs.kem skE s skR p pkR

(** {2 Sealing and opening with a context}

    One message at the context's current sequence number.  Both sides
    advance [cseq] in lockstep (the receiver's context after a successful
    open is the sender's after sealing), so the theorem applies to every
    message of a session. *)

let context_open_seal (#t: Type0) {| Hacl.Secret.Word.word t |} (#cs: ciphersuite t)
                      (c: context cs { ~(ExportOnly? cs.aead) })
                      (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
                      (pt: Seq.seq S8.t { aead_ok (Seq.length pt) })
  : Lemma (match context_seal c aad pt with
           | Some (ct, tag, c') ->
             context_open_ok c aad ct tag /\ context_opened c ct == pt /\
             c' == { c with cseq = c.cseq + 1 }
           | None -> True)
  = if c.cseq = max_seq then ()
    else aead_open_seal cs.aead c.ckey (compute_nonce c) aad pt

(** {2 Single-shot encryption} *)

let open_base_seal_base (#t: Type0) {| Hacl.Secret.Word.word t |}
                        (cs: ciphersuite t { ~(ExportOnly? cs.aead) })
                        (skE skR: Seq.lseq S8.t (size_dh_key cs.kem))
                        (pkR: Seq.lseq S8.t (size_dh_public cs.kem))
                        (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
                        (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
                        (pt: Seq.seq S8.t { aead_ok (Seq.length pt) })
  : Lemma (requires secret_to_public cs.kem skR == Some pkR)
          (ensures (match seal_base cs skE pkR info aad pt with
                    | Some (enc, ct, tag) ->
                      open_base_ok cs enc skR info aad ct tag /\
                      open_base cs enc skR info ct == Some pt
                    | None -> True))
  = setup_agree cs Base skE skR None pkR None info Seq.empty Seq.empty;
    match setup_s cs Base skE None pkR info Seq.empty Seq.empty with
    | None -> ()
    | Some (enc, c) -> context_open_seal c aad pt

#pop-options
