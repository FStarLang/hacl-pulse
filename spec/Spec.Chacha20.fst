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

(** The ChaCha20 stream cipher, as specified in RFC 8439.

    ChaCha20 is a 32-bit-only design: unlike SHA-2 and BLAKE2 there is no
    second width to abstract over, so this is written directly at
    [Hacl.Secret.UInt32.t] rather than through the [Hacl.Secret.Word] class.
    Being explicit about the width where the algorithm is explicit about it
    reads better, and it keeps the extracted C free of a monomorphization
    layer.

    The state is sixteen words: four constants, the eight key words, a 32-bit
    block counter, and three nonce words -- RFC 8439's "IETF" flavour, with a
    96-bit nonce, which is the only one HACL* exposes and the only one this
    library exposes.

    Two presentational choices are worth calling out.

    First, encryption is specified {i pointwise}: [encrypt_bytes] says what the
    [i]th output byte is, rather than folding a block function over a sequence
    of blocks.  The two are equivalent, but the pointwise form is what the
    implementation's loop invariant wants to say, so stating it this way makes
    the whole of [Hacl.Chacha20] a proof about one [Seq.init] instead of a
    proof about a fold with a partial last step.  It also makes the ChaCha20
    contract insensitive to whether the caller's buffer length is a multiple
    of the block length.

    Second, encryption and decryption are literally the same function -- as
    they are for any additive stream cipher -- so only one is defined here, and
    [Hacl.Chacha20.Ptr] exposes it under both names. *)
module Spec.Chacha20

open Hacl.Spec.Loops
open Hacl.Spec.Bytes
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32

(** {2 Sizes} *)

let size_key = 32
let size_nonce = 12
let size_block = 64
let size_state = 16

type state = Seq.lseq S32.t size_state
type key = Seq.lseq S8.t size_key
type nonce = Seq.lseq S8.t size_nonce
type block = Seq.lseq S8.t size_block

(** {2 The state}

    The four constants spell out the ASCII string ["expand 32-byte k"] in
    little-endian order, which is where the funny-looking literals come
    from. *)

let c0 : S32.t = S32.classify 0x61707865ul
let c1 : S32.t = S32.classify 0x3320646eul
let c2 : S32.t = S32.classify 0x79622d32ul
let c3 : S32.t = S32.classify 0x6b206574ul

let constant (i: nat { i < 4 }) : S32.t =
  if i = 0 then c0 else if i = 1 then c1 else if i = 2 then c2 else c3

(** [init k n ctr] is the initial state.  The counter is public -- it is
    chosen by the caller and, in ChaCha20-Poly1305, by the protocol -- so it
    is classified on the way in rather than being secret already. *)
let init (k: key) (n: nonce) (ctr: U32.t) : GTot state =
  let kw = words_from_le #S32.t 8 k in
  let nw = words_from_le #S32.t 3 n in
  Seq.init_ghost size_state (fun i ->
    if i < 4 then constant i
    else if i < 12 then Seq.index kw (i - 4)
    else if i = 12 then S32.classify ctr
    else Seq.index nw (i - 13))

(** {2 The round function} *)

let idx = i: nat { i < size_state }
let rotval = s: U32.t { 0 < U32.v s /\ U32.v s < 32 }

(** One of the two halves of a quarter round: [a += b; d ^= a; d <<<= s]. *)
let line (a b d: idx) (s: rotval) (m: state) : state =
  let m = Seq.upd m a (S32.add_mod (Seq.index m a) (Seq.index m b)) in
  let m = Seq.upd m d (S32.rotate_left (S32.logxor (Seq.index m d) (Seq.index m a)) s) in
  m

let quarter_round (a b c d: idx) (m: state) : state =
  let m = line a b d 16ul m in
  let m = line c d b 12ul m in
  let m = line a b d 8ul m in
  let m = line c d b 7ul m in
  m

(** A double round is four column rounds followed by four diagonal rounds. *)
let double_round (m: state) : state =
  let m = quarter_round 0 4  8 12 m in
  let m = quarter_round 1 5  9 13 m in
  let m = quarter_round 2 6 10 14 m in
  let m = quarter_round 3 7 11 15 m in
  let m = quarter_round 0 5 10 15 m in
  let m = quarter_round 1 6 11 12 m in
  let m = quarter_round 2 7  8 13 m in
  let m = quarter_round 3 4  9 14 m in
  m

let rounds (m: state) : state =
  repeati 10 (fun _ m -> double_round m) m

(** {2 The block function}

    [core st ctr] is the state with the counter word replaced by [ctr], put
    through twenty rounds, and added back to itself word by word.  That final
    addition is what makes ChaCha20 a permutation-plus-feedforward rather than
    a permutation, and hence not invertible. *)
let with_counter (st: state) (ctr: U32.t) : state =
  Seq.upd st 12 (S32.classify ctr)

let core (st: state) (ctr: U32.t) : state =
  let s0 = with_counter st ctr in
  let s1 = rounds s0 in
  Seq.init size_state (fun i -> S32.add_mod (Seq.index s1 i) (Seq.index s0 i))

(** The keystream block, little-endian as everything in ChaCha20 is. *)
let keystream (st: state) (ctr: U32.t) : GTot block =
  words_to_le #S32.t size_state (core st ctr)

(** {2 Encryption}

    [ks_byte st ctr0 i] is the [i]th byte of the keystream that starts at
    block counter [ctr0].  Everything below is phrased in terms of it. *)

let ctr_at (ctr0: U32.t) (i: nat { U32.v ctr0 + i / size_block < pow2 32 }) : U32.t =
  U32.uint_to_t (U32.v ctr0 + i / size_block)

let ks_byte (st: state) (ctr0: U32.t)
            (i: nat { U32.v ctr0 + i / size_block < pow2 32 })
  : GTot S8.t
  = Seq.index (keystream st (ctr_at ctr0 i)) (i % size_block)

(** [i < q * b] implies [i / b < q].  Used to see that the block index of
    every byte of a message of admissible length fits in the counter. *)
let div_lt (b: pos) (i q: nat)
  : Lemma (requires i < q * b) (ensures i / b < q)
  = Math.euclidean_division_definition i b;
    if i / b >= q then Math.lemma_mult_le_right b q (i / b)

(** The largest message length that may be encrypted starting at [ctr0]: the
    counter is 32 bits and does not wrap. *)
let max_len (ctr0: U32.t) : nat = (pow2 32 - U32.v ctr0) * size_block

let encrypt_bytes (st: state) (ctr0: U32.t)
                  (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
  : GTot (Seq.lseq S8.t (Seq.length msg))
  = Seq.init_ghost (Seq.length msg) (fun i ->
      div_lt size_block i (pow2 32 - U32.v ctr0);
      S8.logxor (Seq.index msg i) (ks_byte st ctr0 i))

(** {2 The top-level function}

    Encryption and decryption coincide. *)
let chacha20 (k: key) (n: nonce) (ctr0: U32.t)
             (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
  : GTot (Seq.lseq S8.t (Seq.length msg))
  = encrypt_bytes (init k n ctr0) ctr0 msg
