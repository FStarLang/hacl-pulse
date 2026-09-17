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

(** Hybrid Public Key Encryption, RFC 9180.

    HPKE seals a message to a public key.  A Diffie-Hellman key encapsulation
    turns the recipient's public key into a shared secret and an encapsulated
    ephemeral public key; a key schedule turns the shared secret, the mode,
    an application-supplied [info] string and an optional pre-shared key into
    an AEAD key, a base nonce and an exporter secret; and the AEAD then
    carries the payload.

    Everything the two KDF stages hash is {i labelled}: prefixed with the
    string [HPKE-v1], a suite identifier naming the three algorithms, and a
    per-use label.  That is what stops a value derived for one purpose in one
    ciphersuite from being mistaken for another, and it is why this module
    spends as much of its length on byte-string constants as on arithmetic.

    The ciphersuite is a record, not a type index: the KEM and the AEAD are
    enumerations, and the KDF is a [Spec.SHA2.params] because HPKE's three
    KDFs are HKDF over SHA-256, SHA-384 and SHA-512.  The record has a type
    parameter only because a SHA-2 parameter set does: SHA-256 works on
    32-bit words and SHA-512 on 64-bit ones. *)
module Spec.HPKE

open Hacl.Secret.Word
open Spec.SHA2
open Spec.Byte

module Seq = FStar.Seq
module List = FStar.List.Tot
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module HK = Spec.HKDF
module C = Spec.Curve25519
module P = Spec.P256
module CP = Spec.Chacha20Poly1305
module CC = Spec.Chacha20
module GCM = Spec.GCM
module AES = Spec.AES
module B = Hacl.Spec.Bytes
module Math = FStar.Math.Lemmas

(** {2 The algorithms}

    Only the two KEMs whose Diffie-Hellman this library implements.  The
    other two RFC 9180 registers -- P-384 and P-521 -- would need curves this
    library does not have. *)

type kem_alg =
  | DH_X25519
  | DH_P256

(** [ExportOnly] is a ciphersuite with no AEAD at all: the context can still
    derive exported secrets, but it cannot seal.  RFC 9180 gives it the AEAD
    identifier [0xFFFF]. *)
type aead_alg =
  | Seal_AES128_GCM
  | Seal_AES256_GCM
  | Seal_Chacha20Poly1305
  | ExportOnly

(** The four modes differ only in whether a pre-shared key and a sender
    identity take part; the byte below is the only thing about them the key
    schedule sees. *)
type mode =
  | Base
  | PSK
  | Auth
  | AuthPSK

let mode_id (m: mode) : n: nat { n < 256 } =
  match m with
  | Base -> 0 | PSK -> 1 | Auth -> 2 | AuthPSK -> 3

let uses_psk (m: mode) : bool = match m with PSK | AuthPSK -> true | _ -> false
let uses_auth (m: mode) : bool = match m with Auth | AuthPSK -> true | _ -> false

let kem_id (k: kem_alg) : n: nat { n < 65536 } =
  match k with DH_P256 -> 0x0010 | DH_X25519 -> 0x0020

let aead_id (a: aead_alg) : n: nat { n < 65536 } =
  match a with
  | Seal_AES128_GCM -> 0x0001
  | Seal_AES256_GCM -> 0x0002
  | Seal_Chacha20Poly1305 -> 0x0003
  | ExportOnly -> 0xffff

(** {2 Sizes}

    Both KEMs have 32-byte private keys and 32-byte shared secrets, and both
    use HKDF-SHA-256 internally.  They differ in the public key: X25519 is a
    32-byte u coordinate, P-256 a 65-byte SEC1 uncompressed point.  The
    Diffie-Hellman output is 32 bytes either way -- for P-256 that is the x
    coordinate of the shared point, not the whole point. *)

let size_dh_key (k: kem_alg) : n: pos { n == 32 } = 32

let size_dh_public (k: kem_alg) : n: pos { n == 32 \/ n == 65 } =
  match k with DH_X25519 -> 32 | DH_P256 -> 65

let size_dh_out (k: kem_alg) : n: pos { n == 32 } = 32

let size_kem_secret (k: kem_alg) : n: pos { n == 32 } = 32

let size_aead_key (a: aead_alg) : n: nat { n <= 32 } =
  match a with
  | Seal_AES128_GCM -> 16
  | Seal_AES256_GCM -> 32
  | Seal_Chacha20Poly1305 -> 32
  | ExportOnly -> 0

let size_aead_nonce (a: aead_alg) : n: nat { n == 0 \/ n == 12 } =
  match a with ExportOnly -> 0 | _ -> 12

let size_aead_tag (a: aead_alg) : n: nat { n == 0 \/ n == 16 } =
  match a with ExportOnly -> 0 | _ -> 16

(** {2 The ciphersuite} *)

noeq
type ciphersuite (t: Type0) {| word t |} = {
  kem: kem_alg;

  (** HKDF-SHA-256, HKDF-SHA-384 or HKDF-SHA-512: the refinement is what
      makes [kdf_id] below total. *)
  kdf: p: params t { hash_bytes p == 32 \/ hash_bytes p == 48 \/ hash_bytes p == 64 };

  aead: aead_alg;
}

let kdf_id (#t: Type0) {| word t |} (cs: ciphersuite t) : n: nat { n < 65536 } =
  if hash_bytes cs.kdf = 32 then 0x0001
  else if hash_bytes cs.kdf = 48 then 0x0002
  else 0x0003

unfold let size_kdf (#t: Type0) {| word t |} (cs: ciphersuite t) : pos = hash_bytes cs.kdf
unfold let size_key (#t: Type0) {| word t |} (cs: ciphersuite t) : nat = size_aead_key cs.aead
unfold let size_nonce (#t: Type0) {| word t |} (cs: ciphersuite t) : nat = size_aead_nonce cs.aead
unfold let size_tag (#t: Type0) {| word t |} (cs: ciphersuite t) : nat = size_aead_tag cs.aead

(** The key schedule context: one mode byte and two digests. *)
unfold let size_ks_context (#t: Type0) {| word t |} (cs: ciphersuite t) : pos =
  1 + 2 * size_kdf cs

(** {2 The labels}

    Every one of these is an ASCII string from RFC 9180, written out as the
    bytes it is.  They are secret-typed like every other byte in this
    library, which costs nothing: they are compile-time constants. *)

(** ['HPKE-v1'] *)
let version_list : list S8.t = [ S8.classify 0x48uy; S8.classify 0x50uy; S8.classify 0x4buy; S8.classify 0x45uy; S8.classify 0x2duy; S8.classify 0x76uy; S8.classify 0x31uy ]
let version : Seq.lseq S8.t 7 =
  assert_norm (List.length version_list == 7);
  Seq.seq_of_list version_list

(** ['HPKE'] *)
let hpke_prefix_list : list S8.t = [ S8.classify 0x48uy; S8.classify 0x50uy; S8.classify 0x4buy; S8.classify 0x45uy ]
let hpke_prefix : Seq.lseq S8.t 4 =
  assert_norm (List.length hpke_prefix_list == 4);
  Seq.seq_of_list hpke_prefix_list

(** ['KEM'] *)
let kem_prefix_list : list S8.t = [ S8.classify 0x4buy; S8.classify 0x45uy; S8.classify 0x4duy ]
let kem_prefix : Seq.lseq S8.t 3 =
  assert_norm (List.length kem_prefix_list == 3);
  Seq.seq_of_list kem_prefix_list

(** ['eae_prk'] *)
let label_eae_prk_list : list S8.t = [ S8.classify 0x65uy; S8.classify 0x61uy; S8.classify 0x65uy; S8.classify 0x5fuy; S8.classify 0x70uy; S8.classify 0x72uy; S8.classify 0x6buy ]
let label_eae_prk : Seq.lseq S8.t 7 =
  assert_norm (List.length label_eae_prk_list == 7);
  Seq.seq_of_list label_eae_prk_list

(** ['shared_secret'] *)
let label_shared_secret_list : list S8.t = [ S8.classify 0x73uy; S8.classify 0x68uy; S8.classify 0x61uy; S8.classify 0x72uy; S8.classify 0x65uy; S8.classify 0x64uy; S8.classify 0x5fuy; S8.classify 0x73uy; S8.classify 0x65uy; S8.classify 0x63uy; S8.classify 0x72uy; S8.classify 0x65uy; S8.classify 0x74uy ]
let label_shared_secret : Seq.lseq S8.t 13 =
  assert_norm (List.length label_shared_secret_list == 13);
  Seq.seq_of_list label_shared_secret_list

(** ['psk_id_hash'] *)
let label_psk_id_hash_list : list S8.t = [ S8.classify 0x70uy; S8.classify 0x73uy; S8.classify 0x6buy; S8.classify 0x5fuy; S8.classify 0x69uy; S8.classify 0x64uy; S8.classify 0x5fuy; S8.classify 0x68uy; S8.classify 0x61uy; S8.classify 0x73uy; S8.classify 0x68uy ]
let label_psk_id_hash : Seq.lseq S8.t 11 =
  assert_norm (List.length label_psk_id_hash_list == 11);
  Seq.seq_of_list label_psk_id_hash_list

(** ['info_hash'] *)
let label_info_hash_list : list S8.t = [ S8.classify 0x69uy; S8.classify 0x6euy; S8.classify 0x66uy; S8.classify 0x6fuy; S8.classify 0x5fuy; S8.classify 0x68uy; S8.classify 0x61uy; S8.classify 0x73uy; S8.classify 0x68uy ]
let label_info_hash : Seq.lseq S8.t 9 =
  assert_norm (List.length label_info_hash_list == 9);
  Seq.seq_of_list label_info_hash_list

(** ['secret'] *)
let label_secret_list : list S8.t = [ S8.classify 0x73uy; S8.classify 0x65uy; S8.classify 0x63uy; S8.classify 0x72uy; S8.classify 0x65uy; S8.classify 0x74uy ]
let label_secret : Seq.lseq S8.t 6 =
  assert_norm (List.length label_secret_list == 6);
  Seq.seq_of_list label_secret_list

(** ['key'] *)
let label_key_list : list S8.t = [ S8.classify 0x6buy; S8.classify 0x65uy; S8.classify 0x79uy ]
let label_key : Seq.lseq S8.t 3 =
  assert_norm (List.length label_key_list == 3);
  Seq.seq_of_list label_key_list

(** ['base_nonce'] *)
let label_base_nonce_list : list S8.t = [ S8.classify 0x62uy; S8.classify 0x61uy; S8.classify 0x73uy; S8.classify 0x65uy; S8.classify 0x5fuy; S8.classify 0x6euy; S8.classify 0x6fuy; S8.classify 0x6euy; S8.classify 0x63uy; S8.classify 0x65uy ]
let label_base_nonce : Seq.lseq S8.t 10 =
  assert_norm (List.length label_base_nonce_list == 10);
  Seq.seq_of_list label_base_nonce_list

(** ['exp'] *)
let label_exp_list : list S8.t = [ S8.classify 0x65uy; S8.classify 0x78uy; S8.classify 0x70uy ]
let label_exp : Seq.lseq S8.t 3 =
  assert_norm (List.length label_exp_list == 3);
  Seq.seq_of_list label_exp_list

(** ['sec'] *)
let label_sec_list : list S8.t = [ S8.classify 0x73uy; S8.classify 0x65uy; S8.classify 0x63uy ]
let label_sec : Seq.lseq S8.t 3 =
  assert_norm (List.length label_sec_list == 3);
  Seq.seq_of_list label_sec_list

(** {2 The labelled KDF}

    [labeled_extract] and [labeled_expand] are HKDF with the version string,
    the suite identifier and a label spliced in front of the input.  Both are
    used twice over: once inside the KEM, with the KEM's own suite identifier
    and always HKDF-SHA-256, and once in the key schedule, with the full
    suite identifier and the ciphersuite's KDF. *)

(** Two bytes, big endian: RFC 9180 writes this [I2OSP(x, 2)]. *)
let two_bytes (n: nat { n < 65536 }) : Seq.lseq S8.t 2 = B.nat_to_be 2 n

(** The bound under which every string a caller supplies is short enough to
    hash after a label and a suite identifier are put in front of it.  The
    slack is 64 bytes, which covers the longest label, the longest suite
    identifier, the version string and the two length bytes with room to
    spare.  [max_input] is [2^61] for SHA-256, so this rules out nothing that
    could be allocated. *)
unfold let fits (#t: Type0) {| word t |} (p: params t) (n: nat) : prop =
  block_len #t + hash_bytes p + n + 64 < max_input #t

(** Every hash in this library reserves two words for the message length, and
    the narrowest word is 32 bits, so no input this module builds can come
    anywhere near overflowing it.  Stating that once keeps [fits] out of the
    preconditions of everything internal. *)
let max_input_big (#t: Type0) {| word t |} ()
  : Lemma (max_input #t >= pow2 61 /\ block_len #t <= 256)
  = Math.pow2_le_compat (8 * len_len #t - 3) 61

(** The two byte strings that are hashed, as functions of their pieces.  The
    implementation lays them out in one scratch buffer, so each comes with a
    lemma saying that a buffer holding the pieces at the right offsets {i is}
    the concatenation.  That is the only fact the Pulse code needs, and
    proving it here keeps [Seq.append]'s associativity out of a heap query. *)

let extract_input (sid label ikm: Seq.seq S8.t) : Seq.seq S8.t =
  Seq.append (Seq.append (Seq.append version sid) label) ikm

let expand_input (len: nat { len < 65536 }) (sid label info: Seq.seq S8.t) : Seq.seq S8.t =
  Seq.append (Seq.append (Seq.append (Seq.append (two_bytes len) version) sid) label) info

let extract_input_len (sid label ikm: Seq.seq S8.t)
  : Lemma (Seq.length (extract_input sid label ikm) ==
           7 + Seq.length sid + Seq.length label + Seq.length ikm)
          [SMTPat (Seq.length (extract_input sid label ikm))]
  = ()

let expand_input_len (len: nat { len < 65536 }) (sid label info: Seq.seq S8.t)
  : Lemma (Seq.length (expand_input len sid label info) ==
           9 + Seq.length sid + Seq.length label + Seq.length info)
          [SMTPat (Seq.length (expand_input len sid label info))]
  = ()

(** A four-way concatenation, pointwise.  [cat5] below is the same argument
    with one more layer; both are written out rather than composed, because
    composing them would need index lemmas about the intermediate
    concatenations anyway. *)
let cat4_pointwise (m a b c d: Seq.seq S8.t)
  : Lemma (requires
             Seq.length m == Seq.length a + Seq.length b + Seq.length c + Seq.length d /\
             (forall (k: nat). k < Seq.length a ==> Seq.index m k == Seq.index a k) /\
             (forall (k: nat). k < Seq.length b ==>
                Seq.index m (Seq.length a + k) == Seq.index b k) /\
             (forall (k: nat). k < Seq.length c ==>
                Seq.index m (Seq.length a + Seq.length b + k) == Seq.index c k) /\
             (forall (k: nat). k < Seq.length d ==>
                Seq.index m (Seq.length a + Seq.length b + Seq.length c + k) == Seq.index d k))
          (ensures m == Seq.append (Seq.append (Seq.append a b) c) d)
  = let l1 = Seq.append a b in
    let l2 = Seq.append l1 c in
    let r = Seq.append l2 d in
    let aux (k: nat { k < Seq.length m }) : Lemma (Seq.index m k == Seq.index r k)
      = if k < Seq.length l2
        then begin
          Seq.lemma_index_app1 l2 d k;
          if k < Seq.length l1
          then begin
            Seq.lemma_index_app1 l1 c k;
            if k < Seq.length a
            then Seq.lemma_index_app1 a b k
            else Seq.lemma_index_app2 a b k
          end
          else Seq.lemma_index_app2 l1 c k
        end
        else Seq.lemma_index_app2 l2 d k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro m r

let cat5_pointwise (m a b c d e: Seq.seq S8.t)
  : Lemma (requires
             Seq.length m == Seq.length a + Seq.length b + Seq.length c +
                             Seq.length d + Seq.length e /\
             (forall (k: nat). k < Seq.length a ==> Seq.index m k == Seq.index a k) /\
             (forall (k: nat). k < Seq.length b ==>
                Seq.index m (Seq.length a + k) == Seq.index b k) /\
             (forall (k: nat). k < Seq.length c ==>
                Seq.index m (Seq.length a + Seq.length b + k) == Seq.index c k) /\
             (forall (k: nat). k < Seq.length d ==>
                Seq.index m (Seq.length a + Seq.length b + Seq.length c + k) ==
                  Seq.index d k) /\
             (forall (k: nat). k < Seq.length e ==>
                Seq.index m (Seq.length a + Seq.length b + Seq.length c +
                             Seq.length d + k) == Seq.index e k))
          (ensures m == Seq.append (Seq.append (Seq.append (Seq.append a b) c) d) e)
  = let l1 = Seq.append a b in
    let l2 = Seq.append l1 c in
    let l3 = Seq.append l2 d in
    let r = Seq.append l3 e in
    let aux (k: nat { k < Seq.length m }) : Lemma (Seq.index m k == Seq.index r k)
      = if k < Seq.length l3
        then begin
          Seq.lemma_index_app1 l3 e k;
          if k < Seq.length l2
          then begin
            Seq.lemma_index_app1 l2 d k;
            if k < Seq.length l1
            then begin
              Seq.lemma_index_app1 l1 c k;
              if k < Seq.length a
              then Seq.lemma_index_app1 a b k
              else Seq.lemma_index_app2 a b k
            end
            else Seq.lemma_index_app2 l1 c k
          end
          else Seq.lemma_index_app2 l2 d k
        end
        else Seq.lemma_index_app2 l3 e k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro m r

let labeled_extract (#t: Type0) {| word t |} (p: params t)
                    (sid: Seq.seq S8.t { Seq.length sid <= 16 })
                    (salt: Seq.seq S8.t { Seq.length salt <= 64 })
                    (label: Seq.seq S8.t { Seq.length label <= 16 })
                    (ikm: Seq.seq S8.t { fits p (Seq.length ikm) })
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = HK.extract p salt (extract_input sid label ikm)

let labeled_expand (#t: Type0) {| word t |} (p: params t)
                   (sid: Seq.seq S8.t { Seq.length sid <= 16 })
                   (prk: Seq.seq S8.t { Seq.length prk <= 64 })
                   (label: Seq.seq S8.t { Seq.length label <= 16 })
                   (info: Seq.seq S8.t { fits p (Seq.length info) })
                   (len: nat { len < 65536 /\ len <= 255 * hash_bytes p })
  : GTot (Seq.lseq S8.t len)
  = HK.expand p prk (expand_input len sid label info) len

(** {2 The key encapsulation mechanism}

    DHKEM, RFC 9180 section 4.1.  Its KDF is HKDF-SHA-256 for both of the
    KEMs here, and its suite identifier names only the KEM. *)

let kem_kdf : p: params S32.t { hash_bytes p == 32 } = Spec.SHA2.Constants.sha2_256

(** The KEM's own KDF is concrete, and every string it hashes is bounded by a
    handful of public keys, so [fits] holds outright.  Unfolding a
    [Spec.SHA2.params] record is expensive enough -- it carries the round
    constant table -- that this is worth proving once rather than at each
    call. *)
let kem_fits (n: nat { n <= 256 }) : Lemma (fits kem_kdf n) =
  max_input_big #S32.t ();
  assert_norm (block_len #S32.t == 64);
  assert_norm (416 < pow2 61)

let kem_suite_id (k: kem_alg) : Seq.lseq S8.t 5 =
  Seq.append kem_prefix (two_bytes (kem_id k))

(** The KEM's Diffie-Hellman.  [None] is the RFC's "invalid input" outcome:
    for X25519 a shared secret of zero, which is what a small-order peer
    point produces, and for P-256 a point that is not on the curve, is the
    point at infinity, or does not carry the uncompressed tag byte. *)
let dh (k: kem_alg) (sk: Seq.lseq S8.t (size_dh_key k))
       (pk: Seq.lseq S8.t (size_dh_public k))
  : GTot (option (Seq.lseq S8.t (size_dh_out k)))
  = match k with
    | DH_X25519 ->
      let (o, ok) = C.ecdh sk pk in
      if ok then Some o else None
    | DH_P256 ->
      (match P.uncompressed_to_raw pk with
       | None -> None
       | Some raw ->
         (match P.dh_responder raw sk with
          | None -> None
          | Some shared -> Some (Seq.slice shared 0 32)))

(** The public key belonging to a private one. *)
let secret_to_public (k: kem_alg) (sk: Seq.lseq S8.t (size_dh_key k))
  : GTot (option (Seq.lseq S8.t (size_dh_public k)))
  = match k with
    | DH_X25519 -> Some (C.secret_to_public sk)
    | DH_P256 ->
      (match P.dh_initiator sk with
       | None -> None
       | Some raw -> Some (P.raw_to_uncompressed raw))

(** [ExtractAndExpand]: the KEM's own two-step KDF over the Diffie-Hellman
    output and the transcript of public keys. *)
let extract_and_expand (k: kem_alg)
                       (dh_out: Seq.seq S8.t { Seq.length dh_out <= 64 })
                       (kem_context: Seq.seq S8.t { Seq.length kem_context <= 256 })
  : GTot (Seq.lseq S8.t (size_kem_secret k))
  = kem_fits (Seq.length dh_out);
    kem_fits (Seq.length kem_context);
    let eae_prk = labeled_extract kem_kdf (kem_suite_id k) Seq.empty label_eae_prk dh_out in
    labeled_expand kem_kdf (kem_suite_id k) eae_prk label_shared_secret kem_context
      (size_kem_secret k)

(** Encapsulation: the sender's ephemeral private key against the
    recipient's public key.  The ephemeral key is the caller's, as
    everywhere else in this library. *)
let encap (k: kem_alg) (skE: Seq.lseq S8.t (size_dh_key k))
          (pkR: Seq.lseq S8.t (size_dh_public k))
  : GTot (option (Seq.lseq S8.t (size_kem_secret k) & Seq.lseq S8.t (size_dh_public k)))
  = match dh k skE pkR with
    | None -> None
    | Some dh_out ->
      (match secret_to_public k skE with
       | None -> None
       | Some enc -> Some (extract_and_expand k dh_out (Seq.append enc pkR), enc))

(** Decapsulation. *)
let decap (k: kem_alg) (enc: Seq.lseq S8.t (size_dh_public k))
          (skR: Seq.lseq S8.t (size_dh_key k))
  : GTot (option (Seq.lseq S8.t (size_kem_secret k)))
  = match dh k skR enc with
    | None -> None
    | Some dh_out ->
      (match secret_to_public k skR with
       | None -> None
       | Some pkRm -> Some (extract_and_expand k dh_out (Seq.append enc pkRm)))

(** The authenticated variants additionally mix in a static sender key: two
    Diffie-Hellman outputs concatenated, and the sender's public key at the
    end of the transcript. *)
let auth_encap (k: kem_alg) (skE: Seq.lseq S8.t (size_dh_key k))
               (skS: Seq.lseq S8.t (size_dh_key k))
               (pkR: Seq.lseq S8.t (size_dh_public k))
  : GTot (option (Seq.lseq S8.t (size_kem_secret k) & Seq.lseq S8.t (size_dh_public k)))
  = match dh k skE pkR, dh k skS pkR, secret_to_public k skE, secret_to_public k skS with
    | Some d1, Some d2, Some enc, Some pkSm ->
      Some (extract_and_expand k (Seq.append d1 d2)
              (Seq.append (Seq.append enc pkR) pkSm), enc)
    | _ -> None

let auth_decap (k: kem_alg) (enc: Seq.lseq S8.t (size_dh_public k))
               (skR: Seq.lseq S8.t (size_dh_key k))
               (pkS: Seq.lseq S8.t (size_dh_public k))
  : GTot (option (Seq.lseq S8.t (size_kem_secret k)))
  = match dh k skR enc, dh k skR pkS, secret_to_public k skR with
    | Some d1, Some d2, Some pkRm ->
      Some (extract_and_expand k (Seq.append d1 d2)
              (Seq.append (Seq.append enc pkRm) pkS))
    | _ -> None

(** {2 The key schedule}

    RFC 9180 section 5.1.  Everything downstream of the KEM is here: the
    shared secret, the mode, the [info] string and the optional pre-shared
    key become an AEAD key, a base nonce and an exporter secret. *)

let suite_id (#t: Type0) {| word t |} (cs: ciphersuite t) : Seq.lseq S8.t 10 =
  Seq.append hpke_prefix
    (Seq.append (two_bytes (kem_id cs.kem))
       (Seq.append (two_bytes (kdf_id cs)) (two_bytes (aead_id cs.aead))))

(** The context a mode needs beyond the shared secret: a pre-shared key and
    its identifier, both empty in the unauthenticated modes.  RFC 9180
    requires a PSK of at least 32 bytes when one is used at all, and requires
    that a PSK and its identifier are either both present or both absent. *)
let psk_ok (m: mode) (psk psk_id: Seq.seq S8.t) : prop =
  if uses_psk m
  then Seq.length psk >= 32 /\ Seq.length psk_id > 0
  else Seq.length psk == 0 /\ Seq.length psk_id == 0

(** {3 The encryption context}

    [seq] is the number of messages sealed so far.  RFC 9180 allows it to run
    to [2^(8*Nn) - 1]; this library stops at [2^64 - 1], because the counter
    is a machine word.  At one message per nanosecond that is five hundred
    years, so the restriction is not one a caller can reach. *)

let max_seq : pos = pow2 64 - 1

noeq
type context (#t: Type0) {| word t |} (cs: ciphersuite t) = {
  ckey: Seq.lseq S8.t (size_key cs);
  cbase_nonce: Seq.lseq S8.t (size_nonce cs);
  cseq: n: nat { n <= max_seq };
  cexporter: Seq.lseq S8.t (size_kdf cs);
}

let xor_bytes (#n: nat) (a b: Seq.lseq S8.t n) : Seq.lseq S8.t n =
  Seq.init n (fun i -> S8.logxor (Seq.index a i) (Seq.index b i))

(** [ComputeNonce]: the base nonce exclusive-ored with the sequence number in
    big-endian.  The nonce is twelve bytes and the counter eight, so the
    leading four bytes of the base nonce always come through unchanged. *)
let compute_nonce (#t: Type0) {| word t |} (#cs: ciphersuite t)
                  (c: context cs)
  : Seq.lseq S8.t (size_nonce cs)
  = xor_bytes c.cbase_nonce (B.nat_to_be (size_nonce cs) c.cseq)

(** The key schedule context is one mode byte and two digests, so at most
    129 bytes: short enough to hash under any of the three KDFs. *)
let ks_fits (#t: Type0) {| word t |} (cs: ciphersuite t)
  : Lemma (fits cs.kdf (size_ks_context cs))
  = max_input_big #t (); assert_norm (513 < pow2 61)

#push-options "--z3rlimit 100"
let key_schedule (#t: Type0) {| word t |} (cs: ciphersuite t) (m: mode)
                 (shared_secret: Seq.lseq S8.t (size_kem_secret cs.kem))
                 (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
                 (psk: Seq.seq S8.t { fits cs.kdf (Seq.length psk) })
                 (psk_id: Seq.seq S8.t { fits cs.kdf (Seq.length psk_id) })
  : GTot (context cs)
  = max_input_big #t ();
    ks_fits cs;
    let sid = suite_id cs in
    let psk_id_hash = labeled_extract cs.kdf sid Seq.empty label_psk_id_hash psk_id in
    let info_hash = labeled_extract cs.kdf sid Seq.empty label_info_hash info in
    let ks : Seq.lseq S8.t (size_ks_context cs) =
      Seq.append (Seq.create 1 (S8.classify (U8.uint_to_t (mode_id m))))
        (Seq.append psk_id_hash info_hash) in
    let secret = labeled_extract cs.kdf sid shared_secret label_secret psk in
    { ckey = labeled_expand cs.kdf sid secret label_key ks (size_key cs);
      cbase_nonce = labeled_expand cs.kdf sid secret label_base_nonce ks (size_nonce cs);
      cseq = 0;
      cexporter = labeled_expand cs.kdf sid secret label_exp ks (size_kdf cs) }
#pop-options

(** {2 Exporting}

    The one operation an [ExportOnly] suite still has: a context can derive
    any number of independent secrets of any length from a caller-supplied
    exporter context. *)
let context_export (#t: Type0) {| word t |} (#cs: ciphersuite t) (c: context cs)
                   (exp_ctx: Seq.seq S8.t { fits cs.kdf (Seq.length exp_ctx) })
                   (len: nat { 0 < len /\ len < 65536 /\ len <= 255 * size_kdf cs })
  : GTot (Seq.lseq S8.t len)
  = labeled_expand cs.kdf (suite_id cs) c.cexporter label_sec exp_ctx len

(** {2 The AEAD}

    The three sealing algorithms, behind one interface.  AES-GCM is specified
    over public bytes and ChaCha20-Poly1305 over secret ones; [Spec.Byte]'s
    [vals] and [secrets] move between the two, and neither is anything but a
    ghost renaming of the same numbers.

    Ciphertext and tag are kept apart here, as both underlying
    specifications keep them apart and as the implementations write them to
    separate buffers.  RFC 9180's [ct] is their concatenation. *)

(** One bound for all three, well inside every one of their real limits:
    ChaCha20-Poly1305 stops at [(2^32 - 1) * 64] bytes of message and AES-GCM
    at [2^36 - 32]. *)
unfold let aead_ok (n: nat) : prop = n < pow2 32

let aead_seal (a: aead_alg { ~(ExportOnly? a) })
              (key: Seq.lseq S8.t (size_aead_key a))
              (nonce: Seq.lseq S8.t (size_aead_nonce a))
              (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
              (pt: Seq.seq S8.t { aead_ok (Seq.length pt) })
  : GTot (Seq.lseq S8.t (Seq.length pt) & Seq.lseq S8.t (size_aead_tag a))
  = assert_norm (pow2 32 < pow2 36 - 32);
    assert_norm (pow2 32 < pow2 61 - 1);
    match a with
    | Seal_Chacha20Poly1305 ->
      assert_norm (pow2 32 <= CC.max_len 1ul);
      CP.encrypt key nonce aad pt
    | Seal_AES128_GCM | Seal_AES256_GCM ->
      let v = if Seal_AES128_GCM? a then AES.AES128 else AES.AES256 in
      let (c, tg) = GCM.gcm_encrypt v (vals key) (vals nonce) (vals aad) (vals pt) in
      (secrets c, secrets tg)

(** Opening is a proposition and a function, not an [option]: a secret byte
    sequence has no decidable equality, and the implementation answers with a
    [bool] in any case.  This is the same shape [Spec.Chacha20Poly1305] uses. *)
let aead_open_ok (a: aead_alg { ~(ExportOnly? a) })
                 (key: Seq.lseq S8.t (size_aead_key a))
                 (nonce: Seq.lseq S8.t (size_aead_nonce a))
                 (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
                 (ct: Seq.seq S8.t { aead_ok (Seq.length ct) })
                 (tag: Seq.lseq S8.t (size_aead_tag a))
  : GTot prop
  = assert_norm (pow2 32 < pow2 36 - 32);
    assert_norm (pow2 32 < pow2 61 - 1);
    match a with
    | Seal_Chacha20Poly1305 -> CP.decrypt_ok key nonce aad ct tag
    | Seal_AES128_GCM | Seal_AES256_GCM ->
      let v = if Seal_AES128_GCM? a then AES.AES128 else AES.AES256 in
      Some? (GCM.gcm_decrypt v (vals key) (vals nonce) (vals aad) (vals ct) (vals tag))

let aead_opened (a: aead_alg { ~(ExportOnly? a) })
                (key: Seq.lseq S8.t (size_aead_key a))
                (nonce: Seq.lseq S8.t (size_aead_nonce a))
                (ct: Seq.seq S8.t { aead_ok (Seq.length ct) })
  : GTot (Seq.lseq S8.t (Seq.length ct))
  = assert_norm (pow2 32 < pow2 36 - 32);
    match a with
    | Seal_Chacha20Poly1305 ->
      assert_norm (pow2 32 <= CC.max_len 1ul);
      CP.decrypted key nonce ct
    | Seal_AES128_GCM | Seal_AES256_GCM ->
      let v = if Seal_AES128_GCM? a then AES.AES128 else AES.AES256 in
      let w = AES.key_expansion v (vals key) in
      let jj = GCM.j0 v w (vals nonce) in
      secrets (AES.ctr_encrypt v w (AES.inc32 jj) (vals ct))

(** {2 Sealing and opening with a context}

    Sealing advances the sequence number, which is why it returns a new
    context.  Running out of sequence numbers is a failure, not a wrap: a
    repeated nonce would destroy the AEAD's security outright. *)

#push-options "--z3rlimit 100"
let context_seal (#t: Type0) {| word t |} (#cs: ciphersuite t)
                 (c: context cs { ~(ExportOnly? cs.aead) })
                 (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
                 (pt: Seq.seq S8.t { aead_ok (Seq.length pt) })
  : GTot (option (Seq.lseq S8.t (Seq.length pt) & Seq.lseq S8.t (size_tag cs)
                  & context cs))
  = if c.cseq = max_seq then None
    else
      let (ct, tag) = aead_seal cs.aead c.ckey (compute_nonce c) aad pt in
      Some (ct, tag, { c with cseq = c.cseq + 1 })
#pop-options

let context_open_ok (#t: Type0) {| word t |} (#cs: ciphersuite t)
                    (c: context cs { ~(ExportOnly? cs.aead) })
                    (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
                    (ct: Seq.seq S8.t { aead_ok (Seq.length ct) })
                    (tag: Seq.lseq S8.t (size_tag cs))
  : GTot prop
  = c.cseq < max_seq /\ aead_open_ok cs.aead c.ckey (compute_nonce c) aad ct tag

let context_opened (#t: Type0) {| word t |} (#cs: ciphersuite t)
                   (c: context cs { ~(ExportOnly? cs.aead) })
                   (ct: Seq.seq S8.t { aead_ok (Seq.length ct) })
  : GTot (Seq.lseq S8.t (Seq.length ct))
  = aead_opened cs.aead c.ckey (compute_nonce c) ct

(** {2 Setup}

    The four modes, as two functions.  [Base] passes an empty pre-shared key
    and [Auth] a static sender key; the key schedule and the KEM do not
    otherwise care which mode they are in. *)

let setup_s (#t: Type0) {| word t |} (cs: ciphersuite t) (m: mode)
            (skE: Seq.lseq S8.t (size_dh_key cs.kem))
            (skS: option (Seq.lseq S8.t (size_dh_key cs.kem)) { uses_auth m == Some? skS })
            (pkR: Seq.lseq S8.t (size_dh_public cs.kem))
            (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
            (psk: Seq.seq S8.t { fits cs.kdf (Seq.length psk) })
            (psk_id: Seq.seq S8.t { fits cs.kdf (Seq.length psk_id) })
  : GTot (option (Seq.lseq S8.t (size_dh_public cs.kem) & context cs))
  = let r = match skS with
            | None -> encap cs.kem skE pkR
            | Some s -> auth_encap cs.kem skE s pkR in
    match r with
    | None -> None
    | Some (shared, enc) -> Some (enc, key_schedule cs m shared info psk psk_id)

let setup_r (#t: Type0) {| word t |} (cs: ciphersuite t) (m: mode)
            (enc: Seq.lseq S8.t (size_dh_public cs.kem))
            (skR: Seq.lseq S8.t (size_dh_key cs.kem))
            (pkS: option (Seq.lseq S8.t (size_dh_public cs.kem)) { uses_auth m == Some? pkS })
            (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
            (psk: Seq.seq S8.t { fits cs.kdf (Seq.length psk) })
            (psk_id: Seq.seq S8.t { fits cs.kdf (Seq.length psk_id) })
  : GTot (option (context cs))
  = let r = match pkS with
            | None -> decap cs.kem enc skR
            | Some p -> auth_decap cs.kem enc skR p in
    match r with
    | None -> None
    | Some shared -> Some (key_schedule cs m shared info psk psk_id)

(** {2 Single-shot encryption}

    The whole of HPKE for a caller with one message: a fresh ephemeral key,
    an encapsulation and a single sealing at sequence number zero. *)

let seal_base (#t: Type0) {| word t |} (cs: ciphersuite t { ~(ExportOnly? cs.aead) })
              (skE: Seq.lseq S8.t (size_dh_key cs.kem))
              (pkR: Seq.lseq S8.t (size_dh_public cs.kem))
              (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
              (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
              (pt: Seq.seq S8.t { aead_ok (Seq.length pt) })
  : GTot (option (Seq.lseq S8.t (size_dh_public cs.kem)
                  & Seq.lseq S8.t (Seq.length pt)
                  & Seq.lseq S8.t (size_tag cs)))
  = match setup_s cs Base skE None pkR info Seq.empty Seq.empty with
    | None -> None
    | Some (enc, c) ->
      (match context_seal c aad pt with
       | None -> None
       | Some (ct, tag, _) -> Some (enc, ct, tag))

let open_base_ok (#t: Type0) {| word t |} (cs: ciphersuite t { ~(ExportOnly? cs.aead) })
                 (enc: Seq.lseq S8.t (size_dh_public cs.kem))
                 (skR: Seq.lseq S8.t (size_dh_key cs.kem))
                 (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
                 (aad: Seq.seq S8.t { aead_ok (Seq.length aad) })
                 (ct: Seq.seq S8.t { aead_ok (Seq.length ct) })
                 (tag: Seq.lseq S8.t (size_tag cs))
  : GTot prop
  = match setup_r cs Base enc skR None info Seq.empty Seq.empty with
    | None -> False
    | Some c -> context_open_ok c aad ct tag

let open_base (#t: Type0) {| word t |} (cs: ciphersuite t { ~(ExportOnly? cs.aead) })
              (enc: Seq.lseq S8.t (size_dh_public cs.kem))
              (skR: Seq.lseq S8.t (size_dh_key cs.kem))
              (info: Seq.seq S8.t { fits cs.kdf (Seq.length info) })
              (ct: Seq.seq S8.t { aead_ok (Seq.length ct) })
  : GTot (option (Seq.lseq S8.t (Seq.length ct)))
  = match setup_r cs Base enc skR None info Seq.empty Seq.empty with
    | None -> None
    | Some c -> Some (context_opened c ct)
