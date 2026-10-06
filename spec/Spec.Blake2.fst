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

(** RFC 7693 defines exactly two round counts, and the implementation needs to
    know it: it runs the rounds as ten straight-line bodies and two more, so
    that the message schedule indices are literals rather than table reads.

    Opaque to the solver, and stated alongside the [0 < n] that is all the
    specifications themselves ever want.  Written as a bare disjunction in the
    field's refinement it would enter the context of every proof that so much
    as mentions a [params], and a disjunction is a case split: [mix_columns],
    which does not care how many rounds there are, went from seconds to a
    timeout at three times the resource limit.  Behind [nrounds_ok] it is an
    uninterpreted atom until [nrounds_cases] asks for it, which one function
    does. *)
[@@"opaque_to_smt"]
let nrounds_ok (n: SZ.t) : prop = SZ.v n == 10 \/ SZ.v n == 12

let nrounds_ok_intro (n: SZ.t)
  : Lemma (requires SZ.v n == 10 \/ SZ.v n == 12) (ensures nrounds_ok n)
  = reveal_opaque (`%nrounds_ok) nrounds_ok

let nrounds_cases (n: SZ.t { nrounds_ok n })
  : Lemma (SZ.v n == 10 \/ SZ.v n == 12)
  = reveal_opaque (`%nrounds_ok) nrounds_ok

noeq
type params (t: Type0) {| word t |} = {
  (** Twelve rounds for BLAKE2b, ten for BLAKE2s.  A machine value for the
      same reason as in [Spec.SHA2.params]: every field either is one or is
      erased, so the record has a C representation.

      RFC 7693 defines exactly these two, and [nrounds_ok] says so rather than
      leaving it at [0 < n]; see the note there for why it is opaque and why
      the positivity is spelled out separately. *)
  nrounds: n: SZ.t { 0 < SZ.v n /\ nrounds_ok n };

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

let g_length (#t: Type0) {| word t |} (p: params t)
      (v0: Seq.lseq t 16) (a b c d: nat { a < 16 /\ b < 16 /\ c < 16 /\ d < 16 })
      (x y: t)
  : Lemma (Seq.length (g p v0 a b c d x y) == 16)
          [SMTPat (g p v0 a b c d x y)]
  = ()

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

let blake2b_with (nn: (n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 64 })) : params S64.t =
  nrounds_ok_intro 12sz;
  {
  nrounds = 12sz; iv = G.hide iv64; nhash_bytes = nn;
  rot1 = 32ul; rot2 = 24ul; rot3 = 16ul; rot4 = 63ul;
}

let blake2s_with (nn: (n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 32 })) : params S32.t =
  nrounds_ok_intro 10sz;
  {
  nrounds = 10sz; iv = G.hide iv32; nhash_bytes = nn;
  rot1 = 16ul; rot2 = 12ul; rot3 = 8ul; rot4 = 7ul;
}

(** {2 The blocks of [data], without building [data]}

    The implementation must not materialize [data key msg]: it would mean
    copying the whole message.  Instead it reads block [i] straight out of the
    key or the message, zero-filling past the end.  [block_of] is that view,
    and [block_at_data] is the proof that it is the same view. *)

(** The [block_len] bytes of [s] at [off], zero beyond the end of [s].  Total
    at any offset, which is what makes it usable as a loop invariant. *)
let pad_block (#t: Type0) {| word t |} (s: Seq.seq S8.t) (off: nat)
  : Seq.lseq S8.t (block_len #t)
  = Seq.init (block_len #t)
      (fun j -> if off + j < Seq.length s then Seq.index s (off + j) else S8.classify 0uy)

(** One if a key was given, and so occupies the first block; zero otherwise. *)
let koff (#t: Type0) {| word t |} (key: Seq.seq S8.t) : nat =
  if Seq.length key = 0 then 0 else 1

let block_of (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) (i: nat)
  : Seq.lseq S8.t (block_len #t)
  = if i < koff #t key then pad_block #t key 0
    else pad_block #t msg ((i - koff #t key) * block_len #t)

let nblocks (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) : nat =
  Seq.length (data #t key msg) / block_len #t

(** [pad_to_block] rounds the length up to a multiple of the block length. *)
let pad_to_block_len (#t: Type0) {| word t |} (s: Seq.seq S8.t)
  : Lemma (Seq.length (pad_to_block #t s) % block_len #t == 0 /\
           Seq.length s <= Seq.length (pad_to_block #t s) /\
           Seq.length (pad_to_block #t s) < Seq.length s + block_len #t)
  = Math.lemma_mod_lt (Seq.length s) (block_len #t);
    Math.lemma_mod_plus_distr_l (Seq.length s) (block_len #t - Seq.length s % block_len #t)
                                (block_len #t);
    Math.lemma_mod_add_distr (Seq.length s % block_len #t)
                             (block_len #t - Seq.length s % block_len #t) (block_len #t)

let pad_to_block_block (#t: Type0) {| word t |} (s: Seq.seq S8.t) (j: nat)
  : Lemma (requires (j + 1) * block_len #t <= Seq.length (pad_to_block #t s))
          (ensures block_at #t (pad_to_block #t s) (j * block_len #t)
                   == pad_block #t s (j * block_len #t))
  = let bl = block_len #t in
    let p = pad_to_block #t s in
    Math.lemma_mult_le_right bl j (j + 1);
    assert (Seq.equal (Seq.slice p (j * bl) (j * bl + bl)) (pad_block #t s (j * bl)))

(** The key, if there is one, fills exactly one block. *)
let key_block (#t: Type0) {| word t |} (key: Seq.seq S8.t)
  : Lemma (requires 0 < Seq.length key /\ Seq.length key <= max_key_len #t)
          (ensures Seq.length (pad_to_block #t key) == block_len #t /\
                   pad_to_block #t key == pad_block #t key 0)
  = pad_to_block_len #t key;
    assert (Seq.equal (pad_to_block #t key) (pad_block #t key 0))

let data_len (#t: Type0) {| word t |} (key msg: Seq.seq S8.t)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures Seq.length (data #t key msg) % block_len #t == 0 /\
                   0 < Seq.length (data #t key msg))
  = let bl = block_len #t in
    if Seq.length key = 0 then begin
      if Seq.length msg = 0 then Math.cancel_mul_mod 1 bl
      else pad_to_block_len #t msg
    end else begin
      key_block #t key;
      pad_to_block_len #t msg;
      Math.lemma_mod_add_distr (Seq.length (pad_to_block #t msg)) bl bl;
      Math.cancel_mul_mod 1 bl
    end

let nblocks_bound (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) (i: nat)
  : Lemma (requires Seq.length key <= max_key_len #t /\ i < nblocks #t key msg)
          (ensures (i + 1) * block_len #t <= Seq.length (data #t key msg))
  = let bl = block_len #t in
    data_len #t key msg;
    Math.lemma_mult_le_right bl (i + 1) (nblocks #t key msg);
    Math.lemma_div_exact (Seq.length (data #t key msg)) bl

(** There is always at least one block, and if the key is the only data there
    is exactly one. *)
let nblocks_pos (#t: Type0) {| word t |} (key msg: Seq.seq S8.t)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures 0 < nblocks #t key msg)
  = data_len #t key msg;
    Math.lemma_div_exact (Seq.length (data #t key msg)) (block_len #t)

let block_at_data (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) (i: nat)
  : Lemma (requires Seq.length key <= max_key_len #t /\ i < nblocks #t key msg)
          (ensures block_at #t (data #t key msg) (i * block_len #t)
                   == block_of #t key msg i)
  = let bl = block_len #t in
    let d = data #t key msg in
    nblocks_bound #t key msg i;
    Math.distributivity_add_left i 1 bl;
    if Seq.length key = 0 then begin
      if Seq.length msg = 0 then begin
        Math.multiple_division_lemma 1 bl;
        assert (Seq.equal (Seq.slice d (i * bl) (i * bl + bl)) (pad_block #t msg (i * bl)))
      end else begin
        pad_to_block_len #t msg;
        Seq.lemma_eq_elim d (pad_to_block #t msg);
        pad_to_block_block #t msg i
      end
    end else begin
      key_block #t key;
      pad_to_block_len #t msg;
      let mb = pad_to_block #t msg in
      if i = 0 then
        assert (Seq.equal (Seq.slice d 0 bl) (pad_block #t key 0))
      else begin
        Math.distributivity_sub_left i 1 bl;
        assert (Seq.equal (Seq.slice d (i * bl) (i * bl + bl))
                          (Seq.slice mb ((i - 1) * bl) ((i - 1) * bl + bl)));
        pad_to_block_block #t msg (i - 1)
      end
    end

(** How many blocks there are, in the form the implementation computes it: a
    division and a remainder on the message length, plus one for the key
    block, with the empty unkeyed hash still compressing a block of zeros. *)
let pad_to_block_nblocks (#t: Type0) {| word t |} (s: Seq.seq S8.t)
  : Lemma (Seq.length (pad_to_block #t s) / block_len #t ==
           (if Seq.length s % block_len #t = 0
            then Seq.length s / block_len #t
            else Seq.length s / block_len #t + 1))
  = let bl = block_len #t in
    let n = Seq.length s in
    Math.euclidean_division_definition n bl;
    if n % bl = 0 then Math.multiple_division_lemma (n / bl) bl
    else begin
      Math.distributivity_add_left (n / bl) 1 bl;
      Math.multiple_division_lemma (n / bl + 1) bl
    end

let nblocks_eq (#t: Type0) {| word t |} (key msg: Seq.seq S8.t)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures nblocks #t key msg ==
                   (if Seq.length key = 0 && Seq.length msg = 0 then 1
                    else koff #t key +
                         (if Seq.length msg % block_len #t = 0
                          then Seq.length msg / block_len #t
                          else Seq.length msg / block_len #t + 1)))
  = let bl = block_len #t in
    pad_to_block_nblocks #t msg;
    if Seq.length key = 0 then begin
      if Seq.length msg = 0 then Math.multiple_division_lemma 1 bl
      else Seq.lemma_eq_elim (data #t key msg) (pad_to_block #t msg)
    end else begin
      key_block #t key;
      pad_to_block_len #t msg;
      Seq.lemma_len_append (pad_to_block #t key) (pad_to_block #t msg);
      Math.lemma_div_plus (Seq.length (pad_to_block #t msg)) 1 bl
    end

(** The message offset of block [koff + j] never runs past the message. *)
let msg_blocks_bound (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) (j: nat)
  : Lemma (requires Seq.length key <= max_key_len #t /\
                    koff #t key + j < nblocks #t key msg)
          (ensures j * block_len #t <= Seq.length msg)
  = let bl = block_len #t in
    let n = Seq.length msg in
    nblocks_eq #t key msg;
    Math.euclidean_division_definition n bl;
    if n % bl = 0 then Math.lemma_mult_le_right bl j (n / bl)
    else Math.lemma_mult_le_right bl j (n / bl)

(** [data] is the message plus at most two blocks: one for the key and one for
    the padding. *)
let data_len_bound (#t: Type0) {| word t |} (key msg: Seq.seq S8.t)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures Seq.length (data #t key msg) <= Seq.length msg + 2 * block_len #t)
  = if Seq.length key = 0 then begin
      if Seq.length msg = 0 then () else pad_to_block_len #t msg
    end else begin
      key_block #t key;
      pad_to_block_len #t msg;
      Seq.lemma_len_append (pad_to_block #t key) (pad_to_block #t msg)
    end

(** [nblocks] blocks is exactly the length of [data]. *)
let nblocks_exact (#t: Type0) {| word t |} (key msg: Seq.seq S8.t)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures nblocks #t key msg * block_len #t == Seq.length (data #t key msg))
  = data_len #t key msg;
    Math.lemma_div_exact (Seq.length (data #t key msg)) (block_len #t)
