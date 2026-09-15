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

(** SHA-1, FIPS 180-4 section 6.1.

    {2 This is a legacy algorithm}

    SHA-1 is broken: collisions have been public since 2017 and cost a few
    tens of thousands of core-hours, and chosen-prefix collisions since 2020.
    Nothing new should use it, and this module exists for the same reason
    HACL* has one -- TLS 1.0/1.1 transcripts, HMAC-SHA1 in PBKDF2 and in
    older key schedules, HOTP/TOTP, Git object names, legacy X.509 -- where an
    implementation is needed to {i read} what already exists.  HMAC-SHA1
    retains its security proof under much weaker assumptions than collision
    resistance, which is why the deprecation has never been total.

    {2 Shape}

    The module is written to look as much like [Spec.SHA2] as the algorithm
    allows: [ws_at] slotwise rather than as a fold, [set5] as five [Seq.upd]s
    in the order the implementation writes them, and the same padding, block
    and driver layer.  That is deliberate -- the streaming layer, the HMAC
    layer and the implementation's proof obligations all have the same shape
    as SHA-2's, so none of them needs a new idea.

    It is not, however, an instance of [Spec.SHA2.params].  SHA-1 has a
    five-word state, eighty rounds with a round function that changes every
    twenty, one rotation where SHA-2 has three, and its constants are indexed
    by quarter rather than by round.  A record big enough to cover both would
    describe neither. *)
module Spec.SHA1

open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Loops
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32

(** {2 Sizes} *)

unfold let rounds : pos = 80
unfold let block_words : pos = 16
unfold let block_len : pos = 64
unfold let len_len : pos = 8
unfold let hash_bytes : pos = 20
unfold let state_words : pos = 5

(** The length field is 64 bits and counts bits, so a message is at most
    [2^61 - 1] bytes. *)
unfold let max_input : pos = pow2 61

(** {2 The round function and the constants}

    FIPS 180-4 gives four twenty-round quarters, each with its own [f] and its
    own [K].  [Ch] and [Maj] are written exactly as in [Spec.SHA2] so that the
    implementation can share them. *)

let _Ch (x y z: S32.t) : S32.t =
  S32.logxor (S32.logand x y) (S32.logand (S32.lognot x) z)

let _Par (x y z: S32.t) : S32.t =
  S32.logxor (S32.logxor x y) z

let _Maj (x y z: S32.t) : S32.t =
  S32.logxor (S32.logxor (S32.logand x y) (S32.logand x z)) (S32.logand y z)

let _f (i: nat { i < rounds }) (x y z: S32.t) : S32.t =
  if i < 20 then _Ch x y z
  else if i < 40 then _Par x y z
  else if i < 60 then _Maj x y z
  else _Par x y z

let k (i: nat { i < rounds }) : S32.t =
  if i < 20 then S32.classify 0x5a827999ul
  else if i < 40 then S32.classify 0x6ed9eba1ul
  else if i < 60 then S32.classify 0x8f1bbcdcul
  else S32.classify 0xca62c1d6ul

(** {2 The initial state} *)

let iv : Seq.lseq S32.t state_words =
  Seq.init state_words (fun i ->
    ((if i = 0 then S32.classify 0x67452301ul
      else if i = 1 then S32.classify 0xefcdab89ul
      else if i = 2 then S32.classify 0x98badcfeul
      else if i = 3 then S32.classify 0x10325476ul
      else S32.classify 0xc3d2e1f0ul) <: S32.t))

(** {2 Message schedule}

    [W(t) = ROTL^1 (W(t-3) xor W(t-8) xor W(t-14) xor W(t-16))].  Slotwise,
    for the same reason as in [Spec.SHA2]: the implementation's loop invariant
    -- "slots below [i] are final" -- then holds by unfolding. *)

let rec ws_at (b: Seq.lseq S32.t block_words) (i: nat) : Tot S32.t (decreases i) =
  if i < 16 then Seq.index b i
  else
    S32.rotate_left
      (S32.logxor
        (S32.logxor (S32.logxor (ws_at b (i - 3)) (ws_at b (i - 8)))
                    (ws_at b (i - 14)))
        (ws_at b (i - 16)))
      1ul

let ws (b: Seq.lseq S32.t block_words) : Seq.lseq S32.t rounds =
  Seq.init rounds (ws_at b)

(** {2 Shuffle} *)

let set5 (h: Seq.lseq S32.t state_words) (x0 x1 x2 x3 x4: S32.t)
  : Seq.lseq S32.t state_words =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd h 0 x0) 1 x1) 2 x2) 3 x3) 4 x4

let set5_irrelevant (h1 h2: Seq.lseq S32.t state_words) (x0 x1 x2 x3 x4: S32.t)
  : Lemma (set5 h1 x0 x1 x2 x3 x4 == set5 h2 x0 x1 x2 x3 x4)
  = Seq.lemma_eq_intro (set5 h1 x0 x1 x2 x3 x4) (set5 h2 x0 x1 x2 x3 x4)

let shuffle_core (w: Seq.lseq S32.t rounds) (i: nat) (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = if i >= rounds then h else begin
      let a = Seq.index h 0 in let b = Seq.index h 1 in
      let c = Seq.index h 2 in let d = Seq.index h 3 in
      let e = Seq.index h 4 in
      let t =
        S32.add_mod
          (S32.add_mod
            (S32.add_mod (S32.add_mod (S32.rotate_left a 5ul) (_f i b c d)) e)
            (k i))
          (Seq.index w i)
      in
      set5 h t a (S32.rotate_left b 30ul) c d
    end

let shuffle (w: Seq.lseq S32.t rounds) (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = repeati_g rounds (shuffle_core w) h

(** {2 One block} *)

let add_state (h h': Seq.lseq S32.t state_words) : Seq.lseq S32.t state_words =
  set5 h
    (S32.add_mod (Seq.index h 0) (Seq.index h' 0))
    (S32.add_mod (Seq.index h 1) (Seq.index h' 1))
    (S32.add_mod (Seq.index h 2) (Seq.index h' 2))
    (S32.add_mod (Seq.index h 3) (Seq.index h' 3))
    (S32.add_mod (Seq.index h 4) (Seq.index h' 4))

let update_block (block: Seq.lseq S8.t block_len) (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = let b = words_from_be #S32.t block_words block in
    add_state h (shuffle (ws b) h)

(** {2 Padding}

    Byte for byte the same as SHA-2 at 32 bits: an [0x80], zeros, and the bit
    length big-endian in eight bytes. *)

let pad_zeros (len: nat) : n: nat { (len + 1 + n + len_len) % block_len == 0 } =
  (block_len - (len + 1 + len_len) % block_len) % block_len

let padding (len: nat { len < max_input }) : Seq.seq S8.t =
  Seq.append
    (Seq.append (Seq.create 1 (S8.classify 0x80uy))
                (Seq.create (pad_zeros len) (S8.classify 0uy)))
    (nat_to_be len_len (8 * len))

let padded (msg: Seq.seq S8.t { Seq.length msg < max_input }) : Seq.seq S8.t =
  Seq.append msg (padding (Seq.length msg))

let padded_len (msg: Seq.seq S8.t { Seq.length msg < max_input })
  : Lemma (Seq.length (padded msg) ==
             Seq.length msg + 1 + pad_zeros (Seq.length msg) + len_len /\
           Seq.length (padded msg) % block_len == 0)
  = ()

(** {2 The hash} *)

let block_at (s: Seq.seq S8.t) (off: nat) : Seq.lseq S8.t block_len =
  if off + block_len <= Seq.length s
  then Seq.slice s off (off + block_len)
  else Seq.create block_len (S8.classify 0uy)

let block_at_shift (s: Seq.seq S8.t) (a: nat) (b: nat) (off: nat)
  : Lemma (requires a + b <= Seq.length s /\ off + block_len <= b)
          (ensures block_at (Seq.slice s a (a + b)) off == block_at s (a + off))
  = Seq.slice_slice s a (a + b) off (off + block_len)

let update_step (s: Seq.seq S8.t) (i: nat) (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = if (i + 1) * block_len <= Seq.length s
    then update_block (block_at s (i * block_len)) h
    else h

let update_all (s: Seq.seq S8.t) (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = repeati_g (Seq.length s / block_len) (update_step s) h

let finish (h: Seq.lseq S32.t state_words) : GTot (Seq.lseq S8.t hash_bytes) =
  words_to_be #S32.t state_words h

let hash (msg: Seq.seq S8.t { Seq.length msg < max_input })
  : GTot (Seq.lseq S8.t hash_bytes)
  = finish (update_all (padded msg) iv)
