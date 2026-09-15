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

(** HMAC-SHA1, RFC 2104.

    [hmac key msg = H(K0 ^ opad || H(K0 ^ ipad || msg))].  This is the one
    place SHA-1 is still defensible: HMAC's security proof rests on the
    compression function being a PRF, not on collision resistance, so
    HMAC-SHA1 survives the collision attacks that killed the bare hash.  It is
    what TLS 1.0/1.1, PBKDF2, TOTP and a great deal of deployed X.509 use.

    Only [key_block] and [hmac] are restated.  A block is sixty-four bytes for
    SHA-1 exactly as it is for SHA-256, so [Spec.HMAC]'s [zeros], [xor_byte],
    [ipad], [opad] and the two pointwise lemmas are reused at [S32.t] rather
    than written again -- the same reuse [Spec.SHA1.Lemmas] buys for the
    padding. *)
module Spec.HMAC.SHA1

open Spec.SHA1
open Spec.HMAC

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32

(** The block length SHA-1 and SHA-256 share, so that [Spec.HMAC]'s
    block-shaped definitions apply to both. *)
let block_agree ()
  : Lemma (Spec.SHA2.block_len #S32.t == block_len)
  = ()

(** [K0]: the key, hashed if it does not fit in a block, then zero-extended to
    exactly one block. *)
let key_block (key: Seq.seq S8.t { Seq.length key < max_input })
  : GTot (Seq.lseq S8.t block_len)
  = if Seq.length key <= block_len
    then Seq.append key (zeros (block_len - Seq.length key))
    else Seq.append (hash key) (zeros (block_len - hash_bytes))

(** A twenty-byte digest and a sixty-four byte block against a [2^61] bound:
    the outer message is never anywhere near the limit. *)
let outer_fits () : Lemma (block_len + hash_bytes < max_input)
  = assert_norm (84 < pow2 61)

let hmac (key: Seq.seq S8.t { Seq.length key < max_input })
         (msg: Seq.seq S8.t { block_len + Seq.length msg < max_input })
  : GTot (Seq.lseq S8.t hash_bytes)
  = outer_fits ();
    let k0 = key_block key in
    Seq.lemma_len_append (xor_byte #S32.t k0 ipad) msg;
    let inner = hash (Seq.append (xor_byte #S32.t k0 ipad) msg) in
    Seq.lemma_len_append (xor_byte #S32.t k0 opad) inner;
    hash (Seq.append (xor_byte #S32.t k0 opad) inner)
