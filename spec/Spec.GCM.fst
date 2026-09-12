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

(** AES-GCM, as specified in NIST SP 800-38D.

    GCM is counter mode over AES plus GHASH over the ciphertext, with three
    details that are easy to get wrong and are therefore spelled out here
    rather than folded into the implementation:

    - The hash subkey [h] is the encryption of the {i zero} block, not of
      anything derived from the nonce.  It depends on the key alone.

    - The counter starts at [inc32 j0], not at [j0]: the block [j0] itself is
      reserved for masking the tag.  Encrypting the message with it would leak
      the tag mask.

    - GHASH runs over the padded associated data, then the padded ciphertext,
      then a block holding the two lengths in bits.  The padding is hashed but
      the lengths of the {i unpadded} inputs are what the final block records,
      which is what stops an attacker moving bytes between the two fields.

    The nonce may be any non-empty length.  Twelve bytes is the case every
    protocol uses and the only one with a short path -- [j0] is then the nonce
    with a counter of one appended -- but SP 800-38D defines the general case
    as a GHASH of the nonce, and leaving it out would make this library unable
    to decrypt something another implementation produced.

    Decryption compares tags and returns nothing at all on a mismatch.  It
    does not return the plaintext "but unauthenticated", and it does not write
    a partial result: a caller that never sees invalid plaintext cannot
    accidentally use it.

    {2 Nonce reuse}

    Two messages encrypted under the same key and nonce reveal the xor of the
    plaintexts and, worse, enough to recover [h] and forge arbitrary messages.
    Nothing in this interface can prevent that; a caller that cannot guarantee
    unique nonces should use a nonce-misuse-resistant mode instead. *)
module Spec.GCM

open Spec.Byte
open Spec.AES

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module G = Spec.GF128

(** {2 Sizes and limits}

    SP 800-38D 5.2.1.1: at most 2^39 - 256 bits of plaintext and fewer than
    2^64 bits of associated data per invocation.  Both are stated in bytes
    here.  The plaintext bound is the one that bites: it is what keeps the
    32-bit counter from wrapping back onto [j0]. *)

let taglen = 16

let max_msg : pos = pow2 36 - 32
let max_aad : pos = pow2 61 - 1

let msg_ok (m: Seq.seq elem) : prop = Seq.length m <= max_msg
let aad_ok (a: Seq.seq elem) : prop = Seq.length a <= max_aad
let iv_ok (n: Seq.seq elem) : prop = 0 < Seq.length n /\ Seq.length n <= max_aad

(** {2 Padding and lengths} *)

let padlen (n: nat) : nat = (blocklen - n % blocklen) % blocklen

let pad_mod (n: nat)
  : Lemma ((n + padlen n) % blocklen == 0)
  = let r = n % blocklen in
    if r = 0 then ()
    else begin
      Math.small_mod (blocklen - r) blocklen;
      Math.lemma_mod_add_distr (padlen n) n blocklen
    end

(** Two multiples of the block length add up to one. *)
let ghash_input_mod (a b: nat)
  : Lemma (requires a % blocklen == 0 /\ b % blocklen == 0)
          (ensures (a + b) % blocklen == 0)
  = Math.modulo_distributivity a b blocklen

let pad (s: Seq.seq elem) : (r: Seq.seq elem { Seq.length r % blocklen == 0 }) =
  pad_mod (Seq.length s);
  Seq.append s (Seq.create (padlen (Seq.length s)) 0)

let u64be (n: nat { n < pow2 64 }) : Seq.lseq elem 8 =
  Seq.init 8 (fun i -> byte_at n (8 * (7 - i)))

(** The final GHASH block: the two lengths, in bits, as 64-bit numbers. *)
let len_block (a c: Seq.seq elem)
  : Pure (Seq.lseq elem blocklen)
         (requires aad_ok a /\ Seq.length c <= max_msg)
         (ensures fun _ -> True)
  = assert_norm (8 * (pow2 61 - 1) < pow2 64);
    assert_norm (8 * (pow2 36 - 32) < pow2 64);
    let r = Seq.append (u64be (8 * Seq.length a)) (u64be (8 * Seq.length c)) in
    Seq.lemma_len_append (u64be (8 * Seq.length a)) (u64be (8 * Seq.length c));
    r

(** {2 The pieces} *)

(** The hash subkey: the encryption of the zero block. *)
let hkey (v: variant) (w: Seq.lseq elem (xkeylen v)) : G.block =
  cipher v w (Seq.create blocklen 0)

(** The pre-counter block.  With a twelve-byte nonce it is the nonce and a
    counter of one; otherwise it is a GHASH of the padded nonce and its
    length, which is why [j0] needs the subkey. *)
let j0 (v: variant) (w: Seq.lseq elem (xkeylen v)) (iv: Seq.seq elem { iv_ok iv })
  : G.block =
  if Seq.length iv = 12 then
    Seq.append iv (Seq.init 4 (fun i -> (if i = 3 then 1 else 0) <: elem))
  else begin
    assert_norm (8 * (pow2 61 - 1) < pow2 64);
    let padded = Seq.append (pad iv) (Seq.append (u64be 0) (u64be (8 * Seq.length iv))) in
    Seq.lemma_len_append (pad iv) (Seq.append (u64be 0) (u64be (8 * Seq.length iv)));
    Seq.lemma_len_append (u64be 0) (u64be (8 * Seq.length iv));
    ghash_input_mod (Seq.length (pad iv)) 16;
    G.ghash (hkey v w) padded
  end

(** The authenticated data of the tag: padded AAD, padded ciphertext, then
    the length block. *)
let tag_input (a c: Seq.seq elem)
  : Pure (Seq.seq elem)
         (requires aad_ok a /\ Seq.length c <= max_msg)
         (ensures fun r -> Seq.length r % blocklen == 0)
  = let s = Seq.append (pad a) (Seq.append (pad c) (len_block a c)) in
    Seq.lemma_len_append (pad a) (Seq.append (pad c) (len_block a c));
    Seq.lemma_len_append (pad c) (len_block a c);
    ghash_input_mod (Seq.length (pad c)) blocklen;
    ghash_input_mod (Seq.length (pad a)) (Seq.length (pad c) + blocklen);
    s

let gtag (v: variant) (w: Seq.lseq elem (xkeylen v)) (jj: G.block)
         (a c: Seq.seq elem)
  : Pure (Seq.lseq elem taglen)
         (requires aad_ok a /\ Seq.length c <= max_msg)
         (ensures fun _ -> True)
  = G.gadd (cipher v w jj) (G.ghash (hkey v w) (tag_input a c))

(** {2 GHASH without the concatenation}

    [tag_input] is a sequence no implementation can build: it is three pieces
    long and one of them is padding.  What an implementation does instead is
    fold, with [Spec.GF128.ghash_upd], over the whole blocks of the associated
    data, then a zero-padded final block, then the same for the ciphertext,
    then the length block.  The lemmas below are what license that. *)

(** The whole blocks of [s], and the partial one padded out to a block. *)

let whole (s: Seq.seq elem) : (r: Seq.seq elem { Seq.length r % blocklen == 0 }) =
  Math.lemma_mult_le_right blocklen (G.nblocks s) (Seq.length s);
  Math.multiple_division_lemma (G.nblocks s) blocklen;
  Math.multiple_modulo_lemma (G.nblocks s) blocklen;
  Seq.slice s 0 (G.nblocks s * blocklen)

let tail_block (s: Seq.seq elem { Seq.length s % blocklen <> 0 })
  : Seq.lseq elem blocklen =
  Math.lemma_mult_le_right blocklen (G.nblocks s) (Seq.length s);
  Math.euclidean_division_definition (Seq.length s) blocklen;
  let r = Seq.append (Seq.slice s (G.nblocks s * blocklen) (Seq.length s))
                     (Seq.create (padlen (Seq.length s)) 0) in
  Seq.lemma_len_append (Seq.slice s (G.nblocks s * blocklen) (Seq.length s))
                       (Seq.create (padlen (Seq.length s)) 0);
  r

let nblocks_whole (s: Seq.seq elem)
  : Lemma (Seq.length (whole s) == G.nblocks s * blocklen /\
           G.nblocks (whole s) == G.nblocks s)
  = Math.lemma_mult_le_right blocklen (G.nblocks s) (Seq.length s);
    Math.multiple_division_lemma (G.nblocks s) blocklen

(** A whole block of [s] is a block of [whole s], so a loop over the input
    needs no view of the padding at all. *)
let blk_whole (s: Seq.seq elem) (k: nat { (k + 1) * blocklen <= Seq.length s })
  : Lemma (k + 1 <= G.nblocks (whole s) /\
           (k + 1) * blocklen <= Seq.length (whole s) /\
           G.blk (whole s) k == Seq.slice s (k * blocklen) (k * blocklen + blocklen))
  = nblocks_whole s;
    Math.lemma_mult_le_right blocklen (k + 1) (G.nblocks s);
    Math.lemma_div_le ((k + 1) * blocklen) (Seq.length s) blocklen;
    Math.multiple_division_lemma (k + 1) blocklen;
    Seq.lemma_eq_intro (G.blk (whole s) k)
                       (Seq.slice s (k * blocklen) (k * blocklen + blocklen))

let pad_split (s: Seq.seq elem)
  : Lemma (pad s == (if Seq.length s % blocklen = 0
                     then whole s
                     else Seq.append (whole s) (tail_block s)))
  = Math.lemma_mult_le_right blocklen (G.nblocks s) (Seq.length s);
    Math.euclidean_division_definition (Seq.length s) blocklen;
    if Seq.length s % blocklen = 0 then begin
      Math.multiple_division_lemma (G.nblocks s) blocklen;
      Seq.lemma_eq_intro (pad s) (whole s)
    end else
      Seq.lemma_eq_intro (pad s) (Seq.append (whole s) (tail_block s))

(** Folding the padding of [s] is folding its whole blocks and then, if there
    is one, its padded final block. *)
let ghash_pad (h acc: G.block) (s: Seq.seq elem)
  : Lemma (G.ghash_upd h acc (pad s) ==
             (let a1 = G.ghash_upd h acc (whole s) in
              if Seq.length s % blocklen = 0 then a1
              else G.ghash_upd h a1 (tail_block s)))
  = pad_split s;
    if Seq.length s % blocklen = 0 then ()
    else G.ghash_upd_append h acc (whole s) (tail_block s)

(** And the tag is three folds. *)
let gtag_fold (v: variant) (w: Seq.lseq elem (xkeylen v)) (jj: G.block)
              (a c: Seq.seq elem)
  : Lemma (requires aad_ok a /\ Seq.length c <= max_msg)
          (ensures (let h = hkey v w in
                    let acc = G.ghash_upd h (G.ghash_upd h
                                (G.ghash_upd h G.zero (pad a)) (pad c))
                                (len_block a c) in
                    gtag v w jj a c == G.gadd (cipher v w jj) acc))
  = let h = hkey v w in
    let t = Seq.append (pad c) (len_block a c) in
    Seq.lemma_len_append (pad c) (len_block a c);
    ghash_input_mod (Seq.length (pad c)) blocklen;
    G.ghash_is_upd h (tag_input a c);
    G.ghash_upd_append h G.zero (pad a) t;
    G.ghash_upd_append h (G.ghash_upd h G.zero (pad a)) (pad c) (len_block a c)

(** {2 The two directions} *)

let gcm_encrypt (v: variant) (key: Seq.lseq elem (keylen v))
                (iv: Seq.seq elem { iv_ok iv })
                (a: Seq.seq elem { aad_ok a })
                (m: Seq.seq elem { msg_ok m })
  : Seq.seq elem & Seq.lseq elem taglen =
  let w = key_expansion v key in
  let jj = j0 v w iv in
  let c = ctr_encrypt v w (inc32 jj) m in
  Seq.lemma_init_len (Seq.length m)
    (fun i -> Seq.index m i ^^ ctr_keystream v w (inc32 jj) (Seq.length m) i);
  c, gtag v w jj a c

(** [None] on a tag mismatch: nothing else is returned and nothing is
    written. *)
let gcm_decrypt (v: variant) (key: Seq.lseq elem (keylen v))
                (iv: Seq.seq elem { iv_ok iv })
                (a: Seq.seq elem { aad_ok a })
                (c: Seq.seq elem { msg_ok c })
                (tag: Seq.lseq elem taglen)
  : GTot (option (Seq.seq elem)) =
  let w = key_expansion v key in
  let jj = j0 v w iv in
  if Seq.equal (gtag v w jj a c) tag then Some (ctr_encrypt v w (inc32 jj) c)
  else None
