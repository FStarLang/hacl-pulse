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

(** NaCl's secretbox and box.

    Secretbox is XSalsa20-Poly1305, and its key schedule is the one place
    where it differs from ChaCha20-Poly1305 in more than the cipher.  NaCl
    does not generate a block for the authenticator and then restart the
    keystream: it prepends thirty-two zero bytes to the message and encrypts
    the whole padded thing in one pass.  The first thirty-two keystream bytes
    come back unchanged -- exclusive-or with zero -- and {i are} the one-time
    Poly1305 key; the ciphertext is what follows.  That is why the ciphertext
    of a one-byte message is the thirty-third byte of the keystream and not
    the first byte of block one.

    Written pointwise, the way {!Spec.Salsa20} writes encryption, that whole
    story is the single offset of thirty-two in {!cipher} below.

    The authenticated input is the ciphertext and nothing else: no additional
    data, no padding, no length block.  Secretbox predates AEAD.

    Box adds a key agreement in front.  [beforenm] is X25519 followed by
    HSalsa20 with an all-zero nonce, which is NaCl's way of turning a curve
    point into a uniform symmetric key; everything after that is secretbox.

    The return convention is NaCl's rather than the library's: [0] for
    success and [0xffffffff] for failure.  It is confined to the C entry
    points -- everything here and in the implementation says [bool]. *)
module Spec.NaCl

open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S = Spec.Salsa20
module P = Spec.Poly1305
module C = Spec.Curve25519

let size_key = 32
let size_nonce = 24
let size_mac = 16
let size_beforenm = 32

(** The thirty-two keystream bytes NaCl's zero padding consumes. *)
let size_pad = 32

(** {2 The key schedule}

    The XSalsa20 state secretbox runs on: the sixteen-byte half of the nonce
    has already been spent on the subkey, and the eight-byte half is the
    Salsa20 nonce. *)
let sb_state (k: S.key) (n: S.xnonce) : GTot S.state =
  S.init (S.xkey k n) (S.xnonce_tail n) 0ul

(** Keystream byte [i], counting from the start of block zero. *)
let sb_byte (k: S.key) (n: S.xnonce)
            (i: nat { i / S.size_block < pow2 32 }) : GTot S8.t =
  S.ks_byte (sb_state k n) 0ul i

(** The longest message secretbox can take: thirty-two of the keystream's
    bytes are gone before the message starts. *)
let max_len : nat = S.max_len 0ul - size_pad

let msg_bound = m: Seq.seq S8.t { Seq.length m <= max_len }

(** The one-time Poly1305 key: the first thirty-two keystream bytes, which
    the padding hands back unchanged. *)
let otk (k: S.key) (n: S.xnonce) : GTot (Seq.lseq S8.t 32) =
  Seq.init_ghost 32 (fun i -> S.div_lt S.size_block i (pow2 32); sb_byte k n i)

(** The ciphertext, from keystream byte thirty-two onwards. *)
let cipher (k: S.key) (n: S.xnonce) (msg: msg_bound)
  : GTot (Seq.lseq S8.t (Seq.length msg))
  = Seq.init_ghost (Seq.length msg) (fun i ->
      S.div_lt S.size_block (size_pad + i) (pow2 32);
      S8.logxor (Seq.index msg i) (sb_byte k n (size_pad + i)))

(** Encryption and decryption are the same operation, as ever. *)
let tag_of (k: S.key) (n: S.xnonce) (ct: Seq.seq S8.t) : GTot (Seq.lseq S8.t 16) =
  P.poly1305 ct (otk k n)

(** {2 What the implementation actually runs}

    Three lemmas, one for each of the three pieces the implementation splits
    the keystream into: block zero holds the Poly1305 key, the second half of
    block zero encrypts the first thirty-two message bytes, and everything
    beyond that is an ordinary Salsa20 encryption starting at counter one. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Within block zero, [sb_byte] is just an index into it. *)
let block0_byte (k: S.key) (n: S.xnonce) (i: nat { i < S.size_block })
  : Lemma (Seq.index (S.key_block0 (S.xkey k n) (S.xnonce_tail n)) i == sb_byte k n i)
  = Math.small_div i S.size_block;
    Math.small_mod i S.size_block

(** The one-time key is the first half of block zero. *)
let otk_is_block0 (k: S.key) (n: S.xnonce)
  : Lemma (otk k n == Seq.slice (S.key_block0 (S.xkey k n) (S.xnonce_tail n)) 0 32)
  = let b0 = S.key_block0 (S.xkey k n) (S.xnonce_tail n) in
    let aux (i: nat { i < 32 }) : Lemma (Seq.index (otk k n) i == Seq.index b0 i)
      = block0_byte k n i
    in FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (otk k n) (Seq.slice b0 0 32);
    Seq.lemma_eq_elim (otk k n) (Seq.slice b0 0 32)

(** The first thirty-two ciphertext bytes come out of block zero's tail. *)
let cipher_head (k: S.key) (n: S.xnonce) (msg: msg_bound)
                (i: nat { i < Seq.length msg /\ i < size_pad })
  : Lemma (Seq.index (cipher k n msg) i ==
           S8.logxor (Seq.index msg i)
                     (Seq.index (S.key_block0 (S.xkey k n) (S.xnonce_tail n))
                                (size_pad + i)))
  = block0_byte k n (size_pad + i)

(** Past block zero the keystream is Salsa20's own from counter one: shifting
    the message by thirty-two and the counter by one are the same shift. *)
let tail_byte (k: S.key) (n: S.xnonce)
              (p: nat { 1 + p / S.size_block < pow2 32 })
  : Lemma (sb_byte k n (S.size_block + p) == S.ks_byte (sb_state k n) 1ul p)
  = Math.lemma_div_plus p 1 S.size_block;
    Math.lemma_mod_plus p 1 S.size_block

let cipher_tail (k: S.key) (n: S.xnonce)
                (msg: msg_bound { Seq.length msg > size_pad })
  : Lemma (Seq.slice (cipher k n msg) size_pad (Seq.length msg) ==
           S.salsa20 (S.xkey k n) (S.xnonce_tail n) 1ul
                     (Seq.slice msg size_pad (Seq.length msg)))
  = let tl = Seq.slice msg size_pad (Seq.length msg) in
    let rhs = S.salsa20 (S.xkey k n) (S.xnonce_tail n) 1ul tl in
    let aux (p: nat { p < Seq.length tl })
      : Lemma (Seq.index (Seq.slice (cipher k n msg) size_pad (Seq.length msg)) p ==
               Seq.index rhs p)
      = S.div_lt S.size_block p (pow2 32 - 1);
        tail_byte k n p;
        S.keystream_init (S.xkey k n) (S.xnonce_tail n) 0ul 1ul (S.ctr_at 1ul p)
    in FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro (Seq.slice (cipher k n msg) size_pad (Seq.length msg)) rhs;
    Seq.lemma_eq_elim (Seq.slice (cipher k n msg) size_pad (Seq.length msg)) rhs

#pop-options

(** {2 Secretbox} *)

let secretbox (k: S.key) (n: S.xnonce) (msg: msg_bound)
  : GTot (Seq.lseq S8.t (Seq.length msg) & Seq.lseq S8.t 16)
  = let ct = cipher k n msg in
    (ct, tag_of k n ct)

let secretbox_open_ok (k: S.key) (n: S.xnonce) (ct: Seq.seq S8.t)
                      (tag: Seq.lseq S8.t 16) : GTot prop
  = tag_of k n ct == tag

(** {2 Box}

    X25519, then HSalsa20 with a zero nonce.  The agreement fails exactly
    when the shared secret is zero, which is what X25519's own contributory
    behaviour check reports. *)

let zero_nonce : S.hnonce = Seq.create 16 (S8.classify 0uy)

let beforenm (pk sk: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32 & bool) =
  let (s, ok) = C.ecdh sk pk in
  (S.hsalsa20 s zero_nonce, ok)
