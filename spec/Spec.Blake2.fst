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

(** BLAKE2b and BLAKE2s, as specified in RFC 7693.

    The two differ only in the word width, the number of rounds and the four
    rotation distances, so -- exactly as for SHA-2 -- there is one description,
    parametric in [Hacl.Secret.Word.word], and a record of the differences.
    BLAKE2b is that description at [Hacl.Secret.UInt64.t]; BLAKE2s is it at
    [Hacl.Secret.UInt32.t].

    Two things distinguish it from the SHA-2 spec.  There is no message
    schedule: the sixteen words of the block are used directly, in an order
    given by the public permutation [Spec.Blake2.Constants.sigma], so the
    "expand then shuffle" split does not arise and a round is just eight
    applications of the mixing function [g].  And words are little-endian, both
    on the way in and on the way out, which is what
    [Hacl.Spec.Bytes.words_from_le] and [words_to_le] are for.

    Keying is not a separate construction the way HMAC is: a key is simply
    prepended to the message as one zero-padded block, and the block counter of
    the final compression is shifted by a block to account for it.  So a keyed
    BLAKE2 is a MAC without any of HMAC's two-pass machinery, and it costs one
    extra compression. *)
module Spec.Blake2

open Hacl.Secret.Word
open Hacl.Spec.Loops
open Hacl.Spec.Bytes
open Spec.Blake2.Constants
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

(** {2 What the two members of the family differ in} *)

let rotv (t: Type0) {| word t |} = s: U32.t { 0 < U32.v s /\ U32.v s < bits #t }

noeq
type params (t: Type0) {| word t |} = {
  (** Twelve rounds for BLAKE2b, ten for BLAKE2s.  A machine value for the
      same reason as in [Spec.SHA2.params]: every field either is one or is
      erased, so the record has a C representation. *)
  nrounds: n: SZ.t { 0 < SZ.v n };

  (** The initialization vector.  Read only by specifications -- the
      implementation fills a table of its own and proves it equal -- so it is
      erased and cannot reach the generated code. *)
  iv: G.erased (Seq.lseq t 8);

  (** Digest length in bytes: 1..64 for BLAKE2b, 1..32 for BLAKE2s.  It is a
      parameter of the algorithm, not just a truncation, because it is mixed
      into the initial state. *)
  nhash_bytes: n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 8 * bytes #t };

  (** The four rotation distances of the mixing function: 32, 24, 16, 63 for
      BLAKE2b and 16, 12, 8, 7 for BLAKE2s. *)
  rot1: rotv t; rot2: rotv t; rot3: rotv t; rot4: rotv t;
}

unfold let rounds (#t: Type0) {| word t |} (p: params t) : pos = SZ.v p.nrounds
unfold let hash_bytes (#t: Type0) {| word t |} (p: params t) : pos = SZ.v p.nhash_bytes

(** A block is sixteen words: 128 bytes for BLAKE2b, 64 for BLAKE2s. *)
unfold let block_words : pos = 16
unfold let block_len (#t: Type0) {| word t |} : pos = block_words * bytes #t

(** The largest key: eight words, so 64 bytes for BLAKE2b and 32 for BLAKE2s.
    It has to fit in one block, and it has to fit in the byte of the parameter
    word that records it. *)
unfold let max_key_len (#t: Type0) {| word t |} : pos = 8 * bytes #t

(** {2 The mixing function}

    [g] is RFC 7693 section 3.1, with the eight assignments in the order the
    reference implementation performs them.  The four indices are always
    distinct, so the four [Seq.upd]s at the end commute; they are written in
    index order.

    The working vector is sixteen words -- the eight-word state on top of the
    eight-word initialization vector -- so [g] takes and returns a
    [Seq.lseq t 16] rather than four separate words.  That is what lets a round
    be eight calls with nothing threaded between them but the vector. *)

let g (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
      (v0: Seq.lseq t 16) (a b c d: nat { a < 16 /\ b < 16 /\ c < 16 /\ d < 16 })
      (x y: t)
  : Seq.lseq t 16
  = let va = add_mod #t (add_mod #t (Seq.index v0 a) (Seq.index v0 b)) x in
    let vd = rotate_right #t (logxor #t (Seq.index v0 d) va) p.rot1 in
    let vc = add_mod #t (Seq.index v0 c) vd in
    let vb = rotate_right #t (logxor #t (Seq.index v0 b) vc) p.rot2 in
    let va = add_mod #t (add_mod #t va vb) y in
    let vd = rotate_right #t (logxor #t vd va) p.rot3 in
    let vc = add_mod #t vc vd in
    let vb = rotate_right #t (logxor #t vb vc) p.rot4 in
    Seq.upd (Seq.upd (Seq.upd (Seq.upd v0 a va) b vb) c vc) d vd

(** One round: the four columns, then the four diagonals, with the message
    words picked out by row [r] of [sigma].  [r] is the round number modulo
    ten, since BLAKE2b runs twelve rounds over a ten-row table.

    The two halves are named because the implementation is split at the same
    seam: eight mixes in one Pulse function produce a postcondition that no
    rlimit discharges, and four do. *)

let columns (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
            (m: Seq.lseq t 16) (v0: Seq.lseq t 16) (r: nat { r < 10 })
  : Seq.lseq t 16
  = let s (i: nat { i < 16 }) : t = Seq.index m (sigma r i) in
    let v1 = g p v0 0 4  8 12 (s 0) (s 1) in
    let v2 = g p v1 1 5  9 13 (s 2) (s 3) in
    let v3 = g p v2 2 6 10 14 (s 4) (s 5) in
    g p v3 3 7 11 15 (s 6) (s 7)

let diagonals (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
              (m: Seq.lseq t 16) (v0: Seq.lseq t 16) (r: nat { r < 10 })
  : Seq.lseq t 16
  = let s (i: nat { i < 16 }) : t = Seq.index m (sigma r i) in
    let v1 = g p v0 0 5 10 15 (s  8) (s  9) in
    let v2 = g p v1 1 6 11 12 (s 10) (s 11) in
    let v3 = g p v2 2 7  8 13 (s 12) (s 13) in
    g p v3 3 4  9 14 (s 14) (s 15)

let round (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
          (m: Seq.lseq t 16) (v0: Seq.lseq t 16) (r: nat { r < 10 })
  : Seq.lseq t 16
  = diagonals p m (columns p m v0 r) r

(** The state after the first [n] rounds.  Defined this way round -- the [n]th
    round applied to the result of the first [n-1] -- so that it is exactly a
    loop invariant: after [i] iterations the working vector is
    [rounds_upto p m v i]. *)
let rec rounds_upto (#t: Type0) {| word t |} (p: params t)
                    (m: Seq.lseq t 16) (v0: Seq.lseq t 16) (n: nat)
  : Tot (Seq.lseq t 16) (decreases n)
  = if n = 0 then v0
    else round p m (rounds_upto p m v0 (n - 1)) ((n - 1) % 10)

(** {2 The compression function}

    RFC 7693 section 3.2.  The block counter is a [nat] here and is reduced
    into two words on the spot, so no bound on it appears in the type; the two
    words are the low and the next-lowest [bits] of it, which for BLAKE2b is a
    128-bit counter and for BLAKE2s a 64-bit one. *)

let low_word (#t: Type0) {| word t |} (n: nat) : GTot t =
  Math.lemma_mod_lt n (pow2 (bits #t));
  of_v (n % pow2 (bits #t))

(** The working vector a compression starts from: the state on top of the
    initialization vector, with the block counter mixed into words twelve and
    thirteen and word fourteen inverted if this is the last block.

    Named, rather than inlined into [compress], because the implementation is
    split at the same seam. *)
let init_vector (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                (h: Seq.lseq t 8) (ctr: nat) (last: bool)
  : GTot (Seq.lseq t 16)
  = let v0 : Seq.lseq t 16 = Seq.append h (G.reveal p.iv) in
    let v1 = Seq.upd v0 12 (logxor #t (Seq.index v0 12) (low_word #t ctr)) in
    let v2 = Seq.upd v1 13 (logxor #t (Seq.index v1 13) (low_word #t (ctr / pow2 (bits #t)))) in
    if last then Seq.upd v2 14 (lognot #t (Seq.index v2 14)) else v2

(** The feedforward: each half of the working vector is xored back into the
    state. *)
let mix_state (#t: Type0) {| word t |} (h: Seq.lseq t 8) (v4: Seq.lseq t 16) : Seq.lseq t 8 =
  Seq.init 8 (fun i -> logxor #t (logxor #t (Seq.index h i) (Seq.index v4 i))
                                 (Seq.index v4 (i + 8)))

let compress (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (h: Seq.lseq t 8) (m: Seq.lseq t 16) (ctr: nat) (last: bool)
  : GTot (Seq.lseq t 8)
  = mix_state h (rounds_upto p m (init_vector p h ctr last) (rounds p))

(** {2 The data a hash is taken over}

    A keyed BLAKE2 is the unkeyed one over the key, zero-padded to a block,
    followed by the message.  The one wrinkle is the empty input: an unkeyed
    hash of the empty string still compresses one block, of zeros, whereas a
    keyed hash of the empty string compresses only the key block. *)

let zeros (n: nat) : Seq.lseq S8.t n = Seq.create n (S8.classify 0uy)

(** [s] followed by enough zeros to reach a whole number of blocks.  The empty
    sequence is already a whole number of blocks -- namely none. *)
let pad_to_block (#t: Type0) {| word t |} (s: Seq.seq S8.t) : Seq.seq S8.t =
  Seq.append s (zeros ((block_len #t - Seq.length s % block_len #t) % block_len #t))

let data (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) : Seq.seq S8.t =
  let kb = if Seq.length key = 0 then Seq.empty #S8.t else pad_to_block #t key in
  let mb = if Seq.length msg = 0 && Seq.length key = 0
           then (zeros (block_len #t) <: Seq.seq S8.t)
           else pad_to_block #t msg in
  Seq.append kb mb

(** {2 The hash} *)

(** The block at a byte offset; out of range, an arbitrary constant that
    nothing depends on.  Total, so it may appear in a separation logic
    assertion without a bounds proof in tow. *)
let block_at (#t: Type0) {| word t |} (s: Seq.seq S8.t) (off: nat) : Seq.lseq S8.t (block_len #t) =
  if off + block_len #t <= Seq.length s
  then Seq.slice s off (off + block_len #t)
  else zeros (block_len #t)

let block_at_shift (#t: Type0) {| word t |} (s: Seq.seq S8.t) (a: nat) (b: nat) (off: nat)
  : Lemma (requires a + b <= Seq.length s /\ off + block_len #t <= b)
          (ensures block_at #t (Seq.slice s a (a + b)) off == block_at #t s (a + off))
  = Seq.slice_slice s a (a + b) off (off + block_len #t)

(** The parameter word xored into the first state word: digest length in the
    low byte, key length in the next, then the fanout and depth of the
    unbranched tree, both one.  The three fields do not overlap, so the xor of
    RFC 7693 is a sum. *)
let param_word (nn kk: nat { nn < 256 /\ kk < 256 }) : n: nat { n < pow2 32 } =
  0x01010000 + kk * 256 + nn

let small_word (#t: Type0) {| word t |} (n: nat { n < pow2 32 }) : GTot t =
  Math.pow2_le_compat (bits #t) 32;
  of_v n

let init (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
         (kk: nat { kk <= max_key_len #t })
  : GTot (Seq.lseq t 8)
  = let iv = G.reveal p.iv in
    Seq.upd iv 0 (logxor #t (Seq.index iv 0) (small_word #t (param_word (hash_bytes p) kk)))

(** Compression number [i], of a block that is not the last one, at counter
    [(i + 1) * block_len]: the number of bytes absorbed so far, including this
    block, which is what the RFC's [F(h, d[i], (i+1)*bb, FALSE)] says. *)
let compress_at (#t: Type0) {| word t |} (p: params t) (d: Seq.seq S8.t)
                (i: nat) (h: Seq.lseq t 8)
  : GTot (Seq.lseq t 8)
  = if (i + 1) * block_len #t <= Seq.length d
    then compress p h (words_from_le block_words (block_at #t d (i * block_len #t)))
                    ((i + 1) * block_len #t) false
    else h

let final (#t: Type0) {| word t |} (p: params t) (h: Seq.lseq t 8)
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = Seq.slice (words_to_le 8 h) 0 (hash_bytes p)

(** The counter of the last compression: the message length, plus a block if a
    key was prepended.  Note it is the length of the *message*, not of the
    padded data -- the zeros of the last block are not counted, which is what
    makes the padding unambiguous without a length field. *)
let last_counter (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) : nat =
  if Seq.length key = 0 then Seq.length msg else Seq.length msg + block_len #t

let blake2 (#t: Type0) {| word t |} (p: params t)
           (key: Seq.seq S8.t { Seq.length key <= max_key_len #t })
           (msg: Seq.seq S8.t)
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = let d = data #t key msg in
    let nb = Seq.length d / block_len #t in
    (* [nb] is always at least one; taking the predecessor this way keeps the
       definition total without a lemma. *)
    let nlast : nat = if nb = 0 then 0 else nb - 1 in
    let h = repeati_g nlast (compress_at p d) (init p (Seq.length key)) in
    final p (compress p h (words_from_le block_words (block_at #t d (nlast * block_len #t)))
                        (last_counter #t key msg) true)

(** {2 The two algorithms}

    Unlike SHA-2, the digest length is not fixed by the choice of algorithm:
    BLAKE2b produces 1 to 64 bytes and BLAKE2s 1 to 32, and the length is
    mixed into the initial state, so it is a parameter of these records rather
    than a truncation applied afterwards. *)

let blake2b_with (nn: (n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 64 })) : params S64.t = {
  nrounds = 12sz; iv = G.hide iv64; nhash_bytes = nn;
  rot1 = 32ul; rot2 = 24ul; rot3 = 16ul; rot4 = 63ul;
}

let blake2s_with (nn: (n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 32 })) : params S32.t = {
  nrounds = 10sz; iv = G.hide iv32; nhash_bytes = nn;
  rot1 = 16ul; rot2 = 12ul; rot3 = 8ul; rot4 = 7ul;
}
