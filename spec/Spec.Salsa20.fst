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

(** The Salsa20 stream cipher, and the two constructions on top of it.

    Salsa20 is ChaCha20's predecessor, and everything {!Spec.Chacha20} says
    about presentation applies here unchanged: a 32-bit-only design written
    directly at [Hacl.Secret.UInt32.t]; encryption specified {i pointwise},
    so that the implementation's loop invariant is a statement about one
    [Seq.init]; and encryption and decryption the same function, exposed
    under both names.

    What differs is the state layout and the round.

    ChaCha20 puts its four constants first and its counter and nonce last.
    Salsa20 scatters the constants down the diagonal -- words 0, 5, 10 and
    15 -- with the key in two blocks either side and the counter and nonce
    in the middle.  The reshuffle is the main reason ChaCha20 exists: it
    lets the quarter round work on four words that are adjacent in a SIMD
    register.

    The quarter round is also written differently.  ChaCha20's is four
    copies of [a += b; d ^= a; d <<<= s]; Salsa20's is four copies of
    [a ^= (b + c) <<< s], with the addition feeding the rotation rather than
    the exclusive-or.  Both are given here as a [line] and four uses of it,
    so the two specifications can be read side by side.

    Above Salsa20 sit HSalsa20 -- the same twenty rounds with a longer nonce
    and {i no} feedforward, which is what makes it a PRF suitable for key
    derivation -- and XSalsa20, which is HSalsa20 followed by Salsa20 and is
    what NaCl actually uses. *)
module Spec.Salsa20

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
let size_nonce = 8
let size_hnonce = 16
let size_xnonce = 24
let size_block = 64
let size_state = 16

type state = Seq.lseq S32.t size_state
type key = Seq.lseq S8.t size_key
type nonce = Seq.lseq S8.t size_nonce
type hnonce = Seq.lseq S8.t size_hnonce
type xnonce = Seq.lseq S8.t size_xnonce
type block = Seq.lseq S8.t size_block

(** {2 The state}

    The same four constants as ChaCha20 -- ["expand 32-byte k"] in
    little-endian order -- but on the diagonal. *)

let c0 : S32.t = S32.classify 0x61707865ul
let c1 : S32.t = S32.classify 0x3320646eul
let c2 : S32.t = S32.classify 0x79622d32ul
let c3 : S32.t = S32.classify 0x6b206574ul

let idx = i: nat { i < size_state }

(** Everything but words 6 to 9: the four constants and the eight key
    words, which Salsa20 splits into [k0..k3] at 1--4 and [k4..k7] at
    11--14.  Salsa20 and HSalsa20 agree on all twelve and differ only in
    what goes in the hole. *)
let base (kw: Seq.lseq S32.t 8) (i: idx { i < 6 \/ 9 < i }) : S32.t =
  if i = 0 then c0
  else if i = 5 then c1
  else if i = 10 then c2
  else if i = 15 then c3
  else if i < 5 then Seq.index kw (i - 1)
  else Seq.index kw (i - 7)

(** [init k n ctr] is the initial state.  Salsa20's counter is 64 bits, but
    the interface HACL* exposes -- and therefore this one -- takes a 32-bit
    one, so word 9 is always zero.  As in ChaCha20 the counter is public and
    is classified on the way in. *)
let init (k: key) (n: nonce) (ctr: U32.t) : GTot state =
  let kw = words_from_le #S32.t 8 k in
  let nw = words_from_le #S32.t 2 n in
  Seq.init_ghost size_state (fun i ->
    if i = 6 || i = 7 then Seq.index nw (i - 6)
    else if i = 8 then S32.classify ctr
    else if i = 9 then S32.classify 0ul
    else base kw i)

(** HSalsa20's state: the same, with a sixteen-byte nonce filling all four
    of the middle words and no counter at all. *)
let hinit (k: key) (n: hnonce) : GTot state =
  let kw = words_from_le #S32.t 8 k in
  let nw = words_from_le #S32.t 4 n in
  Seq.init_ghost size_state (fun i ->
    if 6 <= i && i <= 9 then Seq.index nw (i - 6) else base kw i)

(** {2 The round function} *)

let rotval = s: U32.t { 0 < U32.v s /\ U32.v s < 32 }

(** [a ^= (b + c) <<< s].  ChaCha20's [line] adds into one word and rotates
    another; Salsa20's does both to the same word. *)
let line (a b c: idx) (s: rotval) (m: state) : state =
  Seq.upd m a (S32.logxor (Seq.index m a)
                 (S32.rotate_left (S32.add_mod (Seq.index m b) (Seq.index m c)) s))

let quarter_round (a b c d: idx) (m: state) : state =
  let m = line b a d 7ul m in
  let m = line c b a 9ul m in
  let m = line d c b 13ul m in
  let m = line a d c 18ul m in
  m

(** The columns, each starting on the diagonal.  As in ChaCha20 the two
    halves of a double round are named separately, because the
    implementation proves them separately. *)
let column_round (m: state) : state =
  let m = quarter_round 0 4 8 12 m in
  let m = quarter_round 5 9 13 1 m in
  let m = quarter_round 10 14 2 6 m in
  let m = quarter_round 15 3 7 11 m in
  m

let row_round (m: state) : state =
  let m = quarter_round 0 1 2 3 m in
  let m = quarter_round 5 6 7 4 m in
  let m = quarter_round 10 11 8 9 m in
  let m = quarter_round 15 12 13 14 m in
  m

let double_round (m: state) : state = row_round (column_round m)

let rounds (m: state) : state =
  repeati 10 (fun _ m -> double_round m) m

(** {2 The block function}

    As in ChaCha20: twenty rounds, then the input added back word by word.
    It is that feedforward that makes the whole thing non-invertible, and it
    is exactly what HSalsa20 leaves out. *)
let with_counter (st: state) (ctr: U32.t) : state =
  Seq.upd st 8 (S32.classify ctr)

let core_of (s0: state) : state =
  let s1 = rounds s0 in
  Seq.init size_state (fun i -> S32.add_mod (Seq.index s1 i) (Seq.index s0 i))

let core (st: state) (ctr: U32.t) : state = core_of (with_counter st ctr)

let keystream (st: state) (ctr: U32.t) : GTot block =
  words_to_le #S32.t size_state (core st ctr)

(** {2 Encryption}

    Identical in shape to ChaCha20's, down to the names. *)

let ctr_at (ctr0: U32.t) (i: nat { U32.v ctr0 + i / size_block < pow2 32 }) : U32.t =
  U32.uint_to_t (U32.v ctr0 + i / size_block)

let ks_byte (st: state) (ctr0: U32.t)
            (i: nat { U32.v ctr0 + i / size_block < pow2 32 })
  : GTot S8.t
  = Seq.index (keystream st (ctr_at ctr0 i)) (i % size_block)

let div_lt (b: pos) (i q: nat)
  : Lemma (requires i < q * b) (ensures i / b < q)
  = Math.euclidean_division_definition i b;
    if i / b >= q then Math.lemma_mult_le_right b q (i / b)

let max_len (ctr0: U32.t) : nat = (pow2 32 - U32.v ctr0) * size_block

let encrypt_bytes (st: state) (ctr0: U32.t)
                  (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
  : GTot (Seq.lseq S8.t (Seq.length msg))
  = Seq.init_ghost (Seq.length msg) (fun i ->
      div_lt size_block i (pow2 32 - U32.v ctr0);
      S8.logxor (Seq.index msg i) (ks_byte st ctr0 i))

(** {2 The top-level functions}

    Encryption and decryption coincide. *)
let salsa20 (k: key) (n: nonce) (ctr0: U32.t)
            (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
  : GTot (Seq.lseq S8.t (Seq.length msg))
  = encrypt_bytes (init k n ctr0) ctr0 msg

(** Keystream block zero, which HACL* exposes because NaCl's secretbox needs
    it: the first thirty-two bytes become the Poly1305 key and the rest is
    discarded. *)
let key_block0 (k: key) (n: nonce) : GTot block =
  keystream (init k n 0ul) 0ul

(** {2 HSalsa20}

    Twenty rounds and no feedforward, and the eight words taken out are the
    four constants' neighbours: the diagonal and the nonce.  Those are
    precisely the words that are {i not} the key, which is what makes this a
    key-derivation function rather than a keystream. *)

let hpick (i: nat { i < 8 }) : idx =
  if i = 0 then 0 else if i = 1 then 5 else if i = 2 then 10
  else if i = 3 then 15 else i + 2

let hsalsa20 (k: key) (n: hnonce) : GTot (Seq.lseq S8.t 32) =
  let s = rounds (hinit k n) in
  words_to_le #S32.t 8 (Seq.init_ghost 8 (fun i -> Seq.index s (hpick i)))

(** {2 XSalsa20}

    The long-nonce construction NaCl uses: sixteen bytes of the nonce go
    into HSalsa20 to make a subkey, and the remaining eight are the Salsa20
    nonce.  The counter starts at zero. *)

let xkey (k: key) (n: xnonce) : GTot key = hsalsa20 k (Seq.slice n 0 16)

let xnonce_tail (n: xnonce) : nonce = Seq.slice n 16 24

let xsalsa20 (k: key) (n: xnonce)
             (msg: Seq.seq S8.t { Seq.length msg <= max_len 0ul })
  : GTot (Seq.lseq S8.t (Seq.length msg))
  = salsa20 (xkey k n) (xnonce_tail n) 0ul msg
