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

(** HMAC, RFC 2104, over any member of the SHA-2 family.

    [hmac p key msg = H(K0 ^ opad || H(K0 ^ ipad || msg))], where [K0] is the
    key padded to one block with zeros, having first been hashed if it was
    longer than a block.

    Like [Spec.SHA2], this is generic in the word type and takes the algorithm
    as a [params] record, so a single implementation specializes to
    HMAC-SHA-224/256/384/512.  The inner message [K0 ^ ipad || msg] is never
    built by the implementation -- it hashes the first block and then reads
    the caller's buffer -- which is exactly why [Hacl.Hash.SHA2.Core] is
    stated for a message with a ghost block-aligned prefix. *)
module Spec.HMAC

open Hacl.Secret.Word
open Spec.SHA2

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8

(** {2 The padded key} *)

let zeros (n: nat) : Seq.lseq S8.t n = Seq.create n (S8.classify 0uy)

(** [K0]: the key, hashed if it does not fit in a block, then zero-extended to
    exactly one block. *)
let key_block (#t: Type0) {| word t |} (p: params t)
              (key: Seq.seq S8.t { Seq.length key < max_input #t })
  : GTot (Seq.lseq S8.t (block_len #t))
  = let bl = block_len #t in
    if Seq.length key <= bl
    then Seq.append key (zeros (bl - Seq.length key))
    else Seq.append (hash p key) (zeros (bl - hash_bytes p))

(** A block exclusive-ored with a repeated constant byte. *)
let xor_byte (#t: Type0) {| word t |} (b: Seq.lseq S8.t (block_len #t)) (c: U8.t)
  : Seq.lseq S8.t (block_len #t)
  = Seq.init (block_len #t) (fun i -> S8.logxor (Seq.index b i) (S8.classify c))

unfold let ipad : U8.t = 0x36uy
unfold let opad : U8.t = 0x5cuy

(** {2 HMAC} *)

(** Every member of the family has a digest of at most half a block, and the
    smallest block is 64 bytes against a length field of [2^61], so the outer
    message always fits. *)
let outer_fits (#t: Type0) {| word t |} (p: params t)
  : Lemma (block_len #t + hash_bytes p < max_input #t)
  = Math.pow2_le_compat (8 * len_len #t - 3) 61;
    assert_norm (24 * 16 < pow2 61)

(** The two hashed messages are one block longer than their arguments, hence
    the bound on [msg]; [hash_bytes p < block_len #t] holds for every member
    of the family, so the outer message is always in range. *)
let hmac (#t: Type0) {| word t |} (p: params t)
         (key: Seq.seq S8.t { Seq.length key < max_input #t })
         (msg: Seq.seq S8.t { block_len #t + Seq.length msg < max_input #t })
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = outer_fits #t p;
    Seq.lemma_len_append (xor_byte #t (key_block p key) ipad) msg;
    let k0 = key_block p key in
    let inner = hash p (Seq.append (xor_byte #t k0 ipad) msg) in
    Seq.lemma_len_append (xor_byte #t k0 opad) inner;
    hash p (Seq.append (xor_byte #t k0 opad) inner)

(** {2 Lemmas for the implementation} *)

(** The implementation zeroes a block and writes [src] over its beginning;
    this says that what it is left with is [K0]. *)
let key_block_pointwise (#t: Type0) {| word t |} (b: Seq.seq S8.t) (src: Seq.seq S8.t)
  : Lemma (requires
             Seq.length b == block_len #t /\ Seq.length src <= block_len #t /\
             (forall (k: nat). k < Seq.length src ==> Seq.index b k == Seq.index src k) /\
             (forall (k: nat). Seq.length src <= k /\ k < block_len #t ==>
                Seq.index b k == S8.classify 0uy))
          (ensures b == Seq.append src (zeros (block_len #t - Seq.length src)))
  = let r = Seq.append src (zeros (block_len #t - Seq.length src)) in
    let aux (k: nat { k < block_len #t }) : Lemma (Seq.index b k == Seq.index r k)
      = if k < Seq.length src
        then Seq.lemma_index_app1 src (zeros (block_len #t - Seq.length src)) k
        else Seq.lemma_index_app2 src (zeros (block_len #t - Seq.length src)) k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro b r

(** Likewise for the two exclusive-or blocks. *)
let xor_byte_pointwise (#t: Type0) {| word t |} (b: Seq.seq S8.t) (k0: Seq.seq S8.t) (c: U8.t)
  : Lemma (requires
             Seq.length b == block_len #t /\ Seq.length k0 == block_len #t /\
             (forall (k: nat). k < block_len #t ==>
                Seq.index b k == S8.logxor (Seq.index k0 k) (S8.classify c)))
          (ensures b == xor_byte #t k0 c)
  = Seq.lemma_eq_intro b (xor_byte #t k0 c)
