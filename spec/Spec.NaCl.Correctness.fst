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

(** Opening inverts sealing for {!Spec.NaCl}'s secretbox.

    The specification phrases opening the way the implementation reports it:
    [secretbox_open_ok] says the tag is accepted, and the plaintext an
    accepting open writes is [cipher] applied to the ciphertext -- encryption
    and decryption are the same operation.  {!secretbox_open_secretbox}
    states both for the detached form, and {!secretbox_open_easy} for the
    combined form, tag first, in exactly the slices [crypto_secretbox_open_easy]
    is verified against.  The only hypothesis is the message bound
    [secretbox] itself requires.

    Box is secretbox under the key [fst (beforenm pk sk)], and the
    specification has no separate box function, so for a fixed shared key the
    round trip is the secretbox theorem at that key; {!box_open_box} and
    {!box_open_easy} spell this out against the shapes [crypto_box_*] use.
    {!beforenm_agree} is X25519 agreement
    ({!Spec.Curve25519.Correctness.ecdh_agree}) carried through HSalsa20:
    the sender's key [beforenm pkR skS] and the receiver's key
    [beforenm pkS skR] are the same, flag included, so
    {!box_open_box_agree} and {!box_open_easy_agree} state the round trip
    between two parties holding only each other's public keys.

    The proof is the stream-cipher argument, byte by byte: [cipher] xors byte
    [i] with keystream byte [32 + i], and doing it twice cancels
    ({!Spec.Chacha20Poly1305.Correctness.logxor_twice}). *)
module Spec.NaCl.Correctness

open Spec.NaCl

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S = Spec.Salsa20
module X = Spec.Chacha20Poly1305.Correctness
module C = Spec.Curve25519
module CX = Spec.Curve25519.Correctness

#push-options "--fuel 0 --ifuel 0"

(** {2 The cipher is an involution} *)

let cipher_involutive (k: S.key) (n: S.xnonce) (m: msg_bound)
  : Lemma (cipher k n (cipher k n m) == m)
  = let c = cipher k n m in
    let aux (i: nat { i < Seq.length m })
      : Lemma (Seq.index (cipher k n c) i == Seq.index m i)
      = S.div_lt S.size_block (size_pad + i) (pow2 32);
        X.logxor_twice (Seq.index m i) (sb_byte k n (size_pad + i))
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (cipher k n c) m;
    Seq.lemma_eq_elim (cipher k n c) m

(** {2 Secretbox} *)

let secretbox_open_secretbox (k: S.key) (n: S.xnonce) (m: msg_bound)
  : Lemma (let ct = fst (secretbox k n m) in
           let tag = snd (secretbox k n m) in
           secretbox_open_ok k n ct tag /\ cipher k n ct == m)
  = cipher_involutive k n m

(** The combined form: the tag, then the ciphertext. *)
let secretbox_open_easy (k: S.key) (n: S.xnonce) (m: msg_bound)
  : Lemma (let c = Seq.append (snd (secretbox k n m)) (fst (secretbox k n m)) in
           Seq.length c >= 16 /\
           Seq.length (Seq.slice c 16 (Seq.length c)) <= max_len /\
           secretbox_open_ok k n (Seq.slice c 16 (Seq.length c)) (Seq.slice c 0 16) /\
           cipher k n (Seq.slice c 16 (Seq.length c)) == m)
  = let ct = fst (secretbox k n m) in
    let tag = snd (secretbox k n m) in
    let c = Seq.append tag ct in
    Seq.lemma_eq_intro (Seq.slice c 0 16) tag;
    Seq.lemma_eq_intro (Seq.slice c 16 (Seq.length c)) ct;
    secretbox_open_secretbox k n m

(** {2 Box, for a fixed shared key} *)

let box_open_box (pk sk: Seq.lseq S8.t 32) (n: S.xnonce) (m: msg_bound)
  : Lemma (let key = fst (beforenm pk sk) in
           let ct = fst (secretbox key n m) in
           let tag = snd (secretbox key n m) in
           secretbox_open_ok key n ct tag /\ cipher key n ct == m)
  = secretbox_open_secretbox (fst (beforenm pk sk)) n m

let box_open_easy (pk sk: Seq.lseq S8.t 32) (n: S.xnonce) (m: msg_bound)
  : Lemma (let key = fst (beforenm pk sk) in
           let c = Seq.append (snd (secretbox key n m)) (fst (secretbox key n m)) in
           Seq.length c >= 16 /\
           Seq.length (Seq.slice c 16 (Seq.length c)) <= max_len /\
           secretbox_open_ok key n (Seq.slice c 16 (Seq.length c)) (Seq.slice c 0 16) /\
           cipher key n (Seq.slice c 16 (Seq.length c)) == m)
  = secretbox_open_easy (fst (beforenm pk sk)) n m

(** {2 Box, between two parties}

    The sender holds [skS] and the receiver's public key, the receiver holds
    [skR] and the sender's; both derive the same [beforenm] key and flag. *)

let beforenm_agree (skS skR: Seq.lseq S8.t 32)
  : Lemma (beforenm (C.secret_to_public skR) skS ==
           beforenm (C.secret_to_public skS) skR)
  = CX.ecdh_agree skS skR

let box_open_box_agree (skS skR: Seq.lseq S8.t 32) (n: S.xnonce) (m: msg_bound)
  : Lemma (let kS = fst (beforenm (C.secret_to_public skR) skS) in
           let kR = fst (beforenm (C.secret_to_public skS) skR) in
           let ct = fst (secretbox kS n m) in
           let tag = snd (secretbox kS n m) in
           secretbox_open_ok kR n ct tag /\ cipher kR n ct == m)
  = beforenm_agree skS skR;
    box_open_box (C.secret_to_public skR) skS n m

let box_open_easy_agree (skS skR: Seq.lseq S8.t 32) (n: S.xnonce) (m: msg_bound)
  : Lemma (let kS = fst (beforenm (C.secret_to_public skR) skS) in
           let kR = fst (beforenm (C.secret_to_public skS) skR) in
           let c = Seq.append (snd (secretbox kS n m)) (fst (secretbox kS n m)) in
           Seq.length c >= 16 /\
           Seq.length (Seq.slice c 16 (Seq.length c)) <= max_len /\
           secretbox_open_ok kR n (Seq.slice c 16 (Seq.length c)) (Seq.slice c 0 16) /\
           cipher kR n (Seq.slice c 16 (Seq.length c)) == m)
  = beforenm_agree skS skR;
    box_open_easy (C.secret_to_public skR) skS n m

#pop-options
