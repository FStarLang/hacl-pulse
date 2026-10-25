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

(** RSASSA-PKCS1-v1_5, PKCS #1 v2.2 (RFC 8017), sections 8.2 and 9.2.

    That signatures made by this specification verify under it is
    {!Spec.RSAPKCS1.Correctness}.

    The encoding is deterministic, so unlike PSS there is no separate
    verification predicate: RFC 8017 itself verifies by encoding the message
    and comparing (section 8.2.2, steps 3 and 4).  It is

      EM = 0x00 | 0x01 | PS | 0x00 | T

    where [T] is the DER encoding of a DigestInfo -- a fixed prefix naming the
    hash, followed by the digest -- and [PS] is as many [0xff] bytes as fill
    [EM] out to the length of the modulus, at least eight of them.

    Verifying by re-encoding is what makes this format safe.  The forgeries
    against it (Bleichenbacher's of 2006, and the parsing bugs found since)
    all attack verifiers that parse [EM] and then trust what they find; a
    verifier that only ever compares against the one valid encoding has no
    parser to attack. *)
module Spec.RSAPKCS1

open Hacl.Secret.Word
open Spec.SHA2
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0"

(** {2 DigestInfo prefixes, RFC 8017 section 9.2, note 1}

    The DER encoding of [DigestInfo ::= SEQUENCE { digestAlgorithm
    AlgorithmIdentifier, digest OCTET STRING }] up to the digest itself.  The
    algorithm parameters are an explicit NULL, which is the only encoding the
    RFC lists; the variant that omits them is rejected, as by OpenSSL and
    BoringSSL.  Each is a list as well as a sequence so that the
    implementation can lay out the very same literals as a static table. *)

let digest_info_sha256_list : list S8.t = [
  S8.classify 0x30uy; S8.classify 0x31uy; S8.classify 0x30uy; S8.classify 0x0duy;
  S8.classify 0x06uy; S8.classify 0x09uy; S8.classify 0x60uy; S8.classify 0x86uy;
  S8.classify 0x48uy; S8.classify 0x01uy; S8.classify 0x65uy; S8.classify 0x03uy;
  S8.classify 0x04uy; S8.classify 0x02uy; S8.classify 0x01uy; S8.classify 0x05uy;
  S8.classify 0x00uy; S8.classify 0x04uy; S8.classify 0x20uy
]

let digest_info_sha256 : Seq.lseq S8.t 19 =
  assert_norm (List.Tot.length digest_info_sha256_list == 19);
  Seq.seq_of_list digest_info_sha256_list

let digest_info_sha384_list : list S8.t = [
  S8.classify 0x30uy; S8.classify 0x41uy; S8.classify 0x30uy; S8.classify 0x0duy;
  S8.classify 0x06uy; S8.classify 0x09uy; S8.classify 0x60uy; S8.classify 0x86uy;
  S8.classify 0x48uy; S8.classify 0x01uy; S8.classify 0x65uy; S8.classify 0x03uy;
  S8.classify 0x04uy; S8.classify 0x02uy; S8.classify 0x02uy; S8.classify 0x05uy;
  S8.classify 0x00uy; S8.classify 0x04uy; S8.classify 0x30uy
]

let digest_info_sha384 : Seq.lseq S8.t 19 =
  assert_norm (List.Tot.length digest_info_sha384_list == 19);
  Seq.seq_of_list digest_info_sha384_list

let digest_info_sha512_list : list S8.t = [
  S8.classify 0x30uy; S8.classify 0x51uy; S8.classify 0x30uy; S8.classify 0x0duy;
  S8.classify 0x06uy; S8.classify 0x09uy; S8.classify 0x60uy; S8.classify 0x86uy;
  S8.classify 0x48uy; S8.classify 0x01uy; S8.classify 0x65uy; S8.classify 0x03uy;
  S8.classify 0x04uy; S8.classify 0x02uy; S8.classify 0x03uy; S8.classify 0x05uy;
  S8.classify 0x00uy; S8.classify 0x04uy; S8.classify 0x40uy
]

let digest_info_sha512 : Seq.lseq S8.t 19 =
  assert_norm (List.Tot.length digest_info_sha512_list == 19);
  Seq.seq_of_list digest_info_sha512_list


(** {2 EMSA-PKCS1-v1_5, RFC 8017 section 9.2} *)

(** Room for the encoding: [emLen >= tLen + 11].  When it fails, the RFC's
    encoder outputs "intended encoded message length too short" and the
    verifier "invalid signature". *)
unfold let pkcs1_ok (#t: Type0) {| word t |} (p: params t) (diLen: nat) (emLen: nat) =
  diLen + hash_bytes p + 11 <= emLen

(** [0x00 | 0x01 | PS | 0x00 | di | h], as a function of the digest [h]. *)
let emsa_pkcs1 (di: Seq.seq S8.t) (h: Seq.seq S8.t)
               (emLen: nat { Seq.length di + Seq.length h + 11 <= emLen })
  : Seq.lseq S8.t emLen
  = let psLen = emLen - Seq.length di - Seq.length h - 3 in
    let head = Seq.append (Seq.create 1 S8.zero) (Seq.create 1 (S8.classify 1uy)) in
    let ps = Seq.create psLen (S8.classify 0xffuy) in
    let sep = Seq.create 1 S8.zero in
    let tt = Seq.append di h in
    Seq.append (Seq.append (Seq.append head ps) sep) tt

(** EMSA-PKCS1-v1_5-ENCODE, with the DigestInfo prefix [di] naming [p]. *)
let pkcs1_encode (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                 (emLen: nat { pkcs1_ok p (Seq.length di) emLen })
                 (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : GTot (Seq.lseq S8.t emLen)
  = emsa_pkcs1 di (hash p msg) emLen

let pkcs1_encode_eq (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                    (emLen: nat { pkcs1_ok p (Seq.length di) emLen })
                    (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : Lemma (pkcs1_encode p di emLen msg == emsa_pkcs1 di (hash p msg) emLen)
  = ()

(** The verification predicate of RSASSA-PKCS1-v1_5-VERIFY (section
    8.2.2): [m], the number the RSA function produced, is the encoding of
    [msg].  Total, so that a postcondition may mention it without carrying
    the side conditions on its binders: a message too long to hash, or a
    modulus too short to hold the encoding, makes every signature invalid. *)
let pkcs1_valid (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                (emLen: nat) (msg: Seq.seq S8.t) (m: nat)
  : GTot prop
  = Seq.length msg < max_input #t /\
    pkcs1_ok p (Seq.length di) emLen /\
    m == be_nat (pkcs1_encode p di emLen msg)

(** RSASSA-PKCS1-v1_5-SIGN (section 8.2.1) can proceed: the encoding
    exists, and the RSA function under the private exponent applies to it,
    the modulus being odd, greater than one, and above the encoding.  Total,
    like [pkcs1_valid]. *)
let pkcs1_signable (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                   (emLen: nat) (msg: Seq.seq S8.t) (n: nat)
  : GTot prop
  = Seq.length msg < max_input #t /\
    pkcs1_ok p (Seq.length di) emLen /\
    1 < n /\ n % 2 == 1 /\
    be_nat (pkcs1_encode p di emLen msg) < n

(** [s] is the signature of [msg] under the private exponent [d]. *)
let pkcs1_signed (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                 (emLen: nat) (msg: Seq.seq S8.t) (n d s: nat)
  : GTot prop
  = Seq.length msg < max_input #t /\
    pkcs1_ok p (Seq.length di) emLen /\
    s == Spec.RSAPSS.Fermat.rsa_pow (be_nat (pkcs1_encode p di emLen msg)) d n


(** {2 Lemmas for the implementation}

    The implementation writes the encoding piece by piece into one buffer,
    and never materializes the appends. *)

#push-options "--z3rlimit 100"

(** The encoding, byte by byte. *)
let emsa_pkcs1_index (di: Seq.seq S8.t) (h: Seq.seq S8.t)
                     (emLen: nat { Seq.length di + Seq.length h + 11 <= emLen })
                     (k: nat { k < emLen })
  : Lemma (let psLen = emLen - Seq.length di - Seq.length h - 3 in
           Seq.index (emsa_pkcs1 di h emLen) k ==
             (if k = 0 then S8.zero
              else if k = 1 then S8.classify 1uy
              else if k < psLen + 2 then S8.classify 0xffuy
              else if k = psLen + 2 then S8.zero
              else if k < psLen + 3 + Seq.length di then Seq.index di (k - psLen - 3)
              else Seq.index h (k - psLen - 3 - Seq.length di)))
  = let psLen = emLen - Seq.length di - Seq.length h - 3 in
    let head = Seq.append (Seq.create 1 S8.zero) (Seq.create 1 (S8.classify 1uy)) in
    let ps = Seq.create psLen (S8.classify 0xffuy) in
    let sep = Seq.create 1 S8.zero in
    let tt = Seq.append di h in
    let a = Seq.append head ps in
    let b = Seq.append a sep in
    if k < psLen + 3
    then begin
      Seq.lemma_index_app1 b tt k;
      if k < psLen + 2
      then begin
        Seq.lemma_index_app1 a sep k;
        if k < 2
        then begin
          Seq.lemma_index_app1 head ps k;
          if k = 0 then Seq.lemma_index_app1 (Seq.create 1 S8.zero) (Seq.create 1 (S8.classify 1uy)) k
          else Seq.lemma_index_app2 (Seq.create 1 S8.zero) (Seq.create 1 (S8.classify 1uy)) k
        end
        else Seq.lemma_index_app2 head ps k
      end
      else Seq.lemma_index_app2 a sep k
    end
    else begin
      Seq.lemma_index_app2 b tt k;
      if k < psLen + 3 + Seq.length di
      then Seq.lemma_index_app1 di h (k - (psLen + 3))
      else Seq.lemma_index_app2 di h (k - (psLen + 3))
    end

(** ... and read backwards: a buffer holding the right byte everywhere is
    the encoding.  The hypotheses are in the shape the implementation's
    writes leave them in. *)
let emsa_pkcs1_intro (di: Seq.seq S8.t) (h: Seq.seq S8.t)
                     (emLen: nat { Seq.length di + Seq.length h + 11 <= emLen })
                     (w: Seq.seq S8.t)
  : Lemma (requires
      (let psLen = emLen - Seq.length di - Seq.length h - 3 in
       Seq.length w == emLen /\
       Seq.index w 0 == S8.zero /\
       Seq.index w 1 == S8.classify 1uy /\
       (forall (k: nat). k < psLen ==> Seq.index w (2 + k) == S8.classify 0xffuy) /\
       Seq.index w (psLen + 2) == S8.zero /\
       (forall (k: nat). k < Seq.length di ==> Seq.index w (psLen + 3 + k) == Seq.index di k) /\
       (forall (k: nat). k < Seq.length h ==>
          Seq.index w (emLen - Seq.length h + k) == Seq.index h k)))
    (ensures w == emsa_pkcs1 di h emLen)
  = let psLen = emLen - Seq.length di - Seq.length h - 3 in
    let e = emsa_pkcs1 di h emLen in
    let aux (k: nat { k < emLen }) : Lemma (Seq.index w k == Seq.index e k)
      = emsa_pkcs1_index di h emLen k;
        if 2 <= k && k < psLen + 2 then assert (Seq.index w (2 + (k - 2)) == S8.classify 0xffuy)
        else if psLen + 3 <= k && k < psLen + 3 + Seq.length di
        then assert (Seq.index w (psLen + 3 + (k - psLen - 3)) == Seq.index di (k - psLen - 3))
        else if psLen + 3 + Seq.length di <= k
        then assert (Seq.index w (emLen - Seq.length h + (k - psLen - 3 - Seq.length di)) ==
                     Seq.index h (k - psLen - 3 - Seq.length di))
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro w e

#pop-options


(** {2 The encoding is below the modulus}

    It starts with a zero byte, so as a number it is below [2^(8(emLen-1))],
    which for [emLen = ceil(modBits/8)] is at most [2^(modBits-1)]. *)

#push-options "--z3rlimit 40"

let pkcs1_encode_lt (#t: Type0) {| word t |} (p: params t) (di: Seq.seq S8.t)
                    (emLen: nat { pkcs1_ok p (Seq.length di) emLen })
                    (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : Lemma (be_nat (pkcs1_encode p di emLen msg) < pow2 (8 * (emLen - 1)))
  = let em = pkcs1_encode p di emLen msg in
    emsa_pkcs1_index di (hash p msg) emLen 0;
    Spec.RSAPSS.be_nat_prefix_zero em (emLen - 1)

#pop-options

#pop-options
