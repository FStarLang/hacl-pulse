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

(** MD5, RFC 1321.

    {2 This is a legacy algorithm}

    MD5 is thoroughly broken: collisions are a matter of seconds, and
    chosen-prefix collisions have been used to forge a real certificate
    authority.  It is here for the same reason SHA-1 is -- there are file
    formats, protocol transcripts and stored digests that have to be read --
    and for nothing else.  Unlike HMAC-SHA1, HMAC-MD5 is not something to
    reach for.

    {2 Shape}

    Written like [Spec.SHA1] so the implementation and any streaming layer
    can be: [set4] as four [Seq.upd]s in the order the implementation writes
    them, and the same padding and driver layer.

    Three things differ from everything else in the library.  MD5 is
    {i little}-endian -- the block is read with [words_from_le] and the digest
    and the bit length are written with [words_to_le] and [nat_to_le] -- so
    this is the one place [Hacl.Spec.Bytes]'s little-endian half is used.
    There is no message schedule: each of the sixty-four rounds reads one of
    the sixteen block words, chosen by a permutation [g] that depends on the
    quarter.  And the rotation amount is a per-round constant rather than a
    per-algorithm one. *)
module Spec.MD5

open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Loops
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module List = FStar.List.Tot

(** {2 Sizes} *)

unfold let rounds : pos = 64
unfold let block_words : pos = 16
unfold let block_len : pos = 64
unfold let len_len : pos = 8
unfold let hash_bytes : pos = 16
unfold let state_words : pos = 4

(** The length field is 64 bits and counts bits, so a message is at most
    [2^61 - 1] bytes. *)
unfold let max_input : pos = pow2 61

(** {2 The round function}

    RFC 1321 section 3.4.  [F] is [_Ch]; [G] is [_Ch] with its arguments
    rotated, which is the sort of thing that is much easier to see when the
    auxiliary functions have names. *)

let _Ch (x y z: S32.t) : S32.t =
  S32.logor (S32.logand x y) (S32.logand (S32.lognot x) z)

let _Par (x y z: S32.t) : S32.t = S32.logxor (S32.logxor x y) z

(** [I(x, y, z) = y xor (x or not z)]. *)
let _I (x y z: S32.t) : S32.t =
  S32.logxor y (S32.logor x (S32.lognot z))

let _f (i: nat { i < rounds }) (b c d: S32.t) : S32.t =
  if i < 16 then _Ch b c d
  else if i < 32 then _Ch d b c
  else if i < 48 then _Par b c d
  else _I b c d

(** Which block word round [i] reads. *)
let g (i: nat { i < rounds }) : n: nat { n < block_words } =
  if i < 16 then i
  else if i < 32 then (5 * i + 1) % 16
  else if i < 48 then (3 * i + 5) % 16
  else (7 * i) % 16

(** {2 The constants}

    [k.(i)] is the integer part of [2^32 * abs (sin (i + 1))] with [i + 1] in
    radians, as RFC 1321 tabulates it; [s.(i)] is the rotation. *)

let k_list : list S32.t = [
  S32.classify 0xd76aa478ul; S32.classify 0xe8c7b756ul; S32.classify 0x242070dbul; S32.classify 0xc1bdceeeul;
  S32.classify 0xf57c0faful; S32.classify 0x4787c62aul; S32.classify 0xa8304613ul; S32.classify 0xfd469501ul;
  S32.classify 0x698098d8ul; S32.classify 0x8b44f7aful; S32.classify 0xffff5bb1ul; S32.classify 0x895cd7beul;
  S32.classify 0x6b901122ul; S32.classify 0xfd987193ul; S32.classify 0xa679438eul; S32.classify 0x49b40821ul;
  S32.classify 0xf61e2562ul; S32.classify 0xc040b340ul; S32.classify 0x265e5a51ul; S32.classify 0xe9b6c7aaul;
  S32.classify 0xd62f105dul; S32.classify 0x02441453ul; S32.classify 0xd8a1e681ul; S32.classify 0xe7d3fbc8ul;
  S32.classify 0x21e1cde6ul; S32.classify 0xc33707d6ul; S32.classify 0xf4d50d87ul; S32.classify 0x455a14edul;
  S32.classify 0xa9e3e905ul; S32.classify 0xfcefa3f8ul; S32.classify 0x676f02d9ul; S32.classify 0x8d2a4c8aul;
  S32.classify 0xfffa3942ul; S32.classify 0x8771f681ul; S32.classify 0x6d9d6122ul; S32.classify 0xfde5380cul;
  S32.classify 0xa4beea44ul; S32.classify 0x4bdecfa9ul; S32.classify 0xf6bb4b60ul; S32.classify 0xbebfbc70ul;
  S32.classify 0x289b7ec6ul; S32.classify 0xeaa127faul; S32.classify 0xd4ef3085ul; S32.classify 0x04881d05ul;
  S32.classify 0xd9d4d039ul; S32.classify 0xe6db99e5ul; S32.classify 0x1fa27cf8ul; S32.classify 0xc4ac5665ul;
  S32.classify 0xf4292244ul; S32.classify 0x432aff97ul; S32.classify 0xab9423a7ul; S32.classify 0xfc93a039ul;
  S32.classify 0x655b59c3ul; S32.classify 0x8f0ccc92ul; S32.classify 0xffeff47dul; S32.classify 0x85845dd1ul;
  S32.classify 0x6fa87e4ful; S32.classify 0xfe2ce6e0ul; S32.classify 0xa3014314ul; S32.classify 0x4e0811a1ul;
  S32.classify 0xf7537e82ul; S32.classify 0xbd3af235ul; S32.classify 0x2ad7d2bbul; S32.classify 0xeb86d391ul;
]

let k_table : Seq.lseq S32.t rounds =
  assert_norm (List.length k_list == rounds);
  Seq.seq_of_list k_list

let k (i: nat { i < rounds }) : S32.t = Seq.index k_table i

unfold let rot = r: U32.t { 0 < U32.v r /\ U32.v r < 32 }

let s_list : list rot = [
  7ul; 12ul; 17ul; 22ul; 7ul; 12ul; 17ul; 22ul;
  7ul; 12ul; 17ul; 22ul; 7ul; 12ul; 17ul; 22ul;
  5ul; 9ul; 14ul; 20ul; 5ul; 9ul; 14ul; 20ul;
  5ul; 9ul; 14ul; 20ul; 5ul; 9ul; 14ul; 20ul;
  4ul; 11ul; 16ul; 23ul; 4ul; 11ul; 16ul; 23ul;
  4ul; 11ul; 16ul; 23ul; 4ul; 11ul; 16ul; 23ul;
  6ul; 10ul; 15ul; 21ul; 6ul; 10ul; 15ul; 21ul;
  6ul; 10ul; 15ul; 21ul; 6ul; 10ul; 15ul; 21ul;
]

let s_table : Seq.lseq rot rounds =
  assert_norm (List.length s_list == rounds);
  Seq.seq_of_list s_list

(** Every MD5 rotation is between 4 and 23, which is what [rotate_left]
    wants. *)
let s (i: nat { i < rounds }) : rot = Seq.index s_table i

(** The initial state, RFC 1321 section 3.3.  The constants are the same four
    words SHA-1 starts from, minus the fifth; they are written here as the
    little-endian byte order they are quoted in. *)
let iv : Seq.lseq S32.t state_words =
  Seq.seq_of_list [
    S32.classify 0x67452301ul; S32.classify 0xefcdab89ul;
    S32.classify 0x98badcfeul; S32.classify 0x10325476ul
  ]

(** {2 The sixty-four rounds} *)

let set4 (h: Seq.lseq S32.t state_words) (a b c d: S32.t)
  : Seq.lseq S32.t state_words
  = Seq.upd (Seq.upd (Seq.upd (Seq.upd h 0 a) 1 b) 2 c) 3 d

(** [set4] overwrites everything, so the sequence it started from does not
    matter.  Stated on binder refinements so that the [ensures] typechecks
    without the [requires] in scope. *)
let set4_irrelevant (h1: Seq.lseq S32.t state_words) (h2: Seq.lseq S32.t state_words)
                    (a b c d: S32.t)
  : Lemma (set4 h1 a b c d == set4 h2 a b c d)
  = Seq.lemma_eq_intro (set4 h1 a b c d) (set4 h2 a b c d)

(** One round.  [w] is the block, read once; there is no expansion. *)
let shuffle_core (w: Seq.lseq S32.t block_words) (i: nat)
                 (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = if i >= rounds then h else begin
      let a = Seq.index h 0 in
      let b = Seq.index h 1 in
      let c = Seq.index h 2 in
      let d = Seq.index h 3 in
      let t = S32.add_mod
                (S32.add_mod (S32.add_mod a (_f i b c d)) (k i))
                (Seq.index w (g i)) in
      set4 h d (S32.add_mod b (S32.rotate_left t (s i))) b c
    end

let shuffle (w: Seq.lseq S32.t block_words) (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = repeati_g rounds (shuffle_core w) h

(** {2 One block} *)

let add_state (h h': Seq.lseq S32.t state_words) : Seq.lseq S32.t state_words =
  set4 h
    (S32.add_mod (Seq.index h 0) (Seq.index h' 0))
    (S32.add_mod (Seq.index h 1) (Seq.index h' 1))
    (S32.add_mod (Seq.index h 2) (Seq.index h' 2))
    (S32.add_mod (Seq.index h 3) (Seq.index h' 3))

let update_block (block: Seq.lseq S8.t block_len) (h: Seq.lseq S32.t state_words)
  : GTot (Seq.lseq S32.t state_words)
  = let b = words_from_le #S32.t block_words block in
    add_state h (shuffle b h)

(** {2 Padding}

    The same [0x80] and zeros as SHA-1 and SHA-2, but the bit length is
    written {i little}-endian. *)

let pad_zeros (len: nat) : n: nat { (len + 1 + n + len_len) % block_len == 0 } =
  (block_len - (len + 1 + len_len) % block_len) % block_len

let padding (len: nat { len < max_input }) : Seq.seq S8.t =
  Seq.append
    (Seq.append (Seq.create 1 (S8.classify 0x80uy))
                (Seq.create (pad_zeros len) (S8.classify 0uy)))
    (nat_to_le len_len (8 * len))

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
  words_to_le #S32.t state_words h

let hash (msg: Seq.seq S8.t { Seq.length msg < max_input })
  : GTot (Seq.lseq S8.t hash_bytes)
  = finish (update_all (padded msg) iv)
