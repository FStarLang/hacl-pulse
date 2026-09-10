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

(** ChaCha20-Poly1305 AEAD, RFC 8439 section 2.8.

    Three things happen.  The ChaCha20 block at counter zero is generated and
    its first thirty-two bytes become a one-time Poly1305 key -- the rest of
    that block is discarded, which is what keeps the authenticator's key
    independent of the keystream that encrypts.  The message is encrypted
    starting at counter one.  And the tag is Poly1305 over the additional
    data, the ciphertext and their two lengths, each of the first two padded
    out to a multiple of sixteen so that the boundary between them cannot be
    moved.

    The padding is the reason the implementation cannot simply call the
    Poly1305 MAC three times: the padded segments are concatenated *before*
    Poly1305 sees them, and a segment's last block is a full sixteen-byte
    block whose tail is zero, not a short block.  [Spec.Poly1305.seg_acc] is
    the shape an implementation can run, and [mac_input_acc] below is the
    proof that running it three times is the same as authenticating the
    concatenation. *)
module Spec.Chacha20Poly1305

open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U32 = FStar.UInt32
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module C = Spec.Chacha20
module P = Spec.Poly1305

let size_key = 32
let size_nonce = 12
let size_tag = 16

(** {2 The one-time key} *)

(** RFC 8439 section 2.6.  Only the first half of the block is used. *)
let otk (k: C.key) (n: C.nonce) : GTot (Seq.lseq S8.t 32) =
  Seq.slice (C.keystream (C.init k n 0ul) 0ul) 0 32

(** An implementation gets it by encrypting thirty-two zero bytes, which is
    the same thing and reuses the encryption loop unchanged. *)
let otk_is_encrypt (k: C.key) (n: C.nonce)
  : Lemma (C.chacha20 k n 0ul (P.zeros 32) == otk k n)
  = let aux (i: nat { i < 32 })
      : Lemma (Seq.index (C.chacha20 k n 0ul (P.zeros 32)) i ==
               Seq.index (otk k n) i)
      = C.div_lt C.size_block i (pow2 32);
        UInt.logxor_commutative #8 0 (S8.v (C.ks_byte (C.init k n 0ul) 0ul i));
        UInt.logxor_lemma_1 #8 (S8.v (C.ks_byte (C.init k n 0ul) 0ul i))
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (C.chacha20 k n 0ul (P.zeros 32)) (otk k n)

(** {2 The authenticated input} *)

let len_block (la lc: nat) : GTot (Seq.lseq S8.t 16) =
  Seq.append (nat_to_le 8 (la % pow2 64)) (nat_to_le 8 (lc % pow2 64))

let mac_input (aad ct: Seq.seq S8.t) : GTot (Seq.seq S8.t) =
  Seq.append (P.pad16 aad)
             (Seq.append (P.pad16 ct)
                         (len_block (Seq.length aad) (Seq.length ct)))

(** The three segments, as three passes over a running accumulator.  This is
    exactly the implementation's control flow. *)
let mac_acc (aad ct: Seq.seq S8.t) (r: nat) : GTot nat =
  P.seg_acc (len_block (Seq.length aad) (Seq.length ct)) r
            (P.seg_acc ct r (P.seg_acc aad r 0))

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"

let mac_input_acc (aad ct: Seq.seq S8.t) (r: nat)
  : Lemma (P.poly (mac_input aad ct) r == mac_acc aad ct r)
  = let l = len_block (Seq.length aad) (Seq.length ct) in
    let pa = P.pad16 aad in
    let pc = P.pad16 ct in
    P.pad16_aligned aad;
    P.pad16_aligned ct;
    Seq.lemma_eq_intro (P.pad16 l) l;
    Seq.lemma_eq_elim (P.pad16 l) l;
    P.poly_is_acc (mac_input aad ct) r;
    P.poly_acc_append pa (Seq.append pc l) r 0;
    P.poly_acc_append pc l r (P.poly_acc pa r 0);
    P.poly_acc_seg aad r 0;
    P.poly_acc_seg ct r (P.poly_acc pa r 0);
    P.poly_acc_seg l r (P.poly_acc pc r (P.poly_acc pa r 0))

#pop-options

(** {2 The two operations} *)

(** The ciphertext starts at counter one; counter zero was spent on the
    one-time key. *)
let encrypt (k: C.key) (n: C.nonce) (aad: Seq.seq S8.t)
            (msg: Seq.seq S8.t { Seq.length msg <= C.max_len 1ul })
  : GTot (Seq.lseq S8.t (Seq.length msg) & Seq.lseq S8.t 16)
  = let ct = C.chacha20 k n 1ul msg in
    (ct, P.poly1305 (mac_input aad ct) (otk k n))

let tag_of (k: C.key) (n: C.nonce) (aad ct: Seq.seq S8.t)
  : GTot (Seq.lseq S8.t 16)
  = P.poly1305 (mac_input aad ct) (otk k n)

(** Decryption verifies first and only then decrypts, which is the property
    the implementation has to preserve: no plaintext is written unless the tag
    is right.  It is stated as a proposition and a function rather than as one
    [option]-valued definition, because a byte sequence is not an [eqtype]
    here -- a secret byte has no decidable equality, which is the point of the
    representation -- and the implementation's own answer is a [bool] anyway. *)
let decrypt_ok (k: C.key) (n: C.nonce) (aad ct: Seq.seq S8.t)
               (tag: Seq.lseq S8.t 16) : GTot prop
  = tag_of k n aad ct == tag

let decrypted (k: C.key) (n: C.nonce)
              (ct: Seq.seq S8.t { Seq.length ct <= C.max_len 1ul })
  : GTot (Seq.lseq S8.t (Seq.length ct))
  = C.chacha20 k n 1ul ct
