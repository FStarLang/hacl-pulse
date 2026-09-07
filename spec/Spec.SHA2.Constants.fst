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

(** The constants of FIPS 180-4 section 4.2.2/5.3, and the four members of the
    SHA-2 family as [Spec.SHA2.params] values.

    The round constants are the first thirty-two (sixty-four) bits of the
    fractional parts of the cube roots of the first sixty-four (eighty) primes; the
    initial states are the same for square roots.  They are written out rather
    than computed because F* has no reals in the executable fragment, but they
    were generated from those definitions and checked against the published
    values, not transcribed.

    Each table is a chain of [Seq.upd]s over a zeroed sequence rather than the
    obvious [Seq.createL], because that is exactly the shape a slice acquires
    when [Hacl.Hash.SHA2] fills it one store at a time: the implementation's
    table is then equal to this one by unfolding, and the solver never sees a
    sixty-four-way case analysis on an index. *)
module Spec.SHA2.Constants

open Spec.SHA2
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module SZ = FStar.SizeT
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

(** [Seq.upd] with the length kept in the type, so that a chain of eighty of
    them does not make the solver re-derive the length eighty times. *)
unfold let up (#a: Type) (#n: nat) (s: Seq.lseq a n) (i: nat { i < n }) (x: a) : Seq.lseq a n =
  Seq.upd s i x

(** {2 SHA-224 / SHA-256} *)

[@@FStar.Custard.no_specialize]
let k256 : Seq.lseq S32.t 64 =
  let s = Seq.create 64 (S32.classify 0ul) in
  let s = up s  0 (S32.classify 0x428a2f98ul) in
  let s = up s  1 (S32.classify 0x71374491ul) in
  let s = up s  2 (S32.classify 0xb5c0fbcful) in
  let s = up s  3 (S32.classify 0xe9b5dba5ul) in
  let s = up s  4 (S32.classify 0x3956c25bul) in
  let s = up s  5 (S32.classify 0x59f111f1ul) in
  let s = up s  6 (S32.classify 0x923f82a4ul) in
  let s = up s  7 (S32.classify 0xab1c5ed5ul) in
  let s = up s  8 (S32.classify 0xd807aa98ul) in
  let s = up s  9 (S32.classify 0x12835b01ul) in
  let s = up s 10 (S32.classify 0x243185beul) in
  let s = up s 11 (S32.classify 0x550c7dc3ul) in
  let s = up s 12 (S32.classify 0x72be5d74ul) in
  let s = up s 13 (S32.classify 0x80deb1feul) in
  let s = up s 14 (S32.classify 0x9bdc06a7ul) in
  let s = up s 15 (S32.classify 0xc19bf174ul) in
  let s = up s 16 (S32.classify 0xe49b69c1ul) in
  let s = up s 17 (S32.classify 0xefbe4786ul) in
  let s = up s 18 (S32.classify 0x0fc19dc6ul) in
  let s = up s 19 (S32.classify 0x240ca1ccul) in
  let s = up s 20 (S32.classify 0x2de92c6ful) in
  let s = up s 21 (S32.classify 0x4a7484aaul) in
  let s = up s 22 (S32.classify 0x5cb0a9dcul) in
  let s = up s 23 (S32.classify 0x76f988daul) in
  let s = up s 24 (S32.classify 0x983e5152ul) in
  let s = up s 25 (S32.classify 0xa831c66dul) in
  let s = up s 26 (S32.classify 0xb00327c8ul) in
  let s = up s 27 (S32.classify 0xbf597fc7ul) in
  let s = up s 28 (S32.classify 0xc6e00bf3ul) in
  let s = up s 29 (S32.classify 0xd5a79147ul) in
  let s = up s 30 (S32.classify 0x06ca6351ul) in
  let s = up s 31 (S32.classify 0x14292967ul) in
  let s = up s 32 (S32.classify 0x27b70a85ul) in
  let s = up s 33 (S32.classify 0x2e1b2138ul) in
  let s = up s 34 (S32.classify 0x4d2c6dfcul) in
  let s = up s 35 (S32.classify 0x53380d13ul) in
  let s = up s 36 (S32.classify 0x650a7354ul) in
  let s = up s 37 (S32.classify 0x766a0abbul) in
  let s = up s 38 (S32.classify 0x81c2c92eul) in
  let s = up s 39 (S32.classify 0x92722c85ul) in
  let s = up s 40 (S32.classify 0xa2bfe8a1ul) in
  let s = up s 41 (S32.classify 0xa81a664bul) in
  let s = up s 42 (S32.classify 0xc24b8b70ul) in
  let s = up s 43 (S32.classify 0xc76c51a3ul) in
  let s = up s 44 (S32.classify 0xd192e819ul) in
  let s = up s 45 (S32.classify 0xd6990624ul) in
  let s = up s 46 (S32.classify 0xf40e3585ul) in
  let s = up s 47 (S32.classify 0x106aa070ul) in
  let s = up s 48 (S32.classify 0x19a4c116ul) in
  let s = up s 49 (S32.classify 0x1e376c08ul) in
  let s = up s 50 (S32.classify 0x2748774cul) in
  let s = up s 51 (S32.classify 0x34b0bcb5ul) in
  let s = up s 52 (S32.classify 0x391c0cb3ul) in
  let s = up s 53 (S32.classify 0x4ed8aa4aul) in
  let s = up s 54 (S32.classify 0x5b9cca4ful) in
  let s = up s 55 (S32.classify 0x682e6ff3ul) in
  let s = up s 56 (S32.classify 0x748f82eeul) in
  let s = up s 57 (S32.classify 0x78a5636ful) in
  let s = up s 58 (S32.classify 0x84c87814ul) in
  let s = up s 59 (S32.classify 0x8cc70208ul) in
  let s = up s 60 (S32.classify 0x90befffaul) in
  let s = up s 61 (S32.classify 0xa4506cebul) in
  let s = up s 62 (S32.classify 0xbef9a3f7ul) in
  let s = up s 63 (S32.classify 0xc67178f2ul) in
  s

[@@FStar.Custard.no_specialize]
let iv256 : Seq.lseq S32.t 8 =
  let s = Seq.create 8 (S32.classify 0ul) in
  let s = up s 0 (S32.classify 0x6a09e667ul) in
  let s = up s 1 (S32.classify 0xbb67ae85ul) in
  let s = up s 2 (S32.classify 0x3c6ef372ul) in
  let s = up s 3 (S32.classify 0xa54ff53aul) in
  let s = up s 4 (S32.classify 0x510e527ful) in
  let s = up s 5 (S32.classify 0x9b05688cul) in
  let s = up s 6 (S32.classify 0x1f83d9abul) in
  let s = up s 7 (S32.classify 0x5be0cd19ul) in
  s

[@@FStar.Custard.no_specialize]
let iv224 : Seq.lseq S32.t 8 =
  let s = Seq.create 8 (S32.classify 0ul) in
  let s = up s 0 (S32.classify 0xc1059ed8ul) in
  let s = up s 1 (S32.classify 0x367cd507ul) in
  let s = up s 2 (S32.classify 0x3070dd17ul) in
  let s = up s 3 (S32.classify 0xf70e5939ul) in
  let s = up s 4 (S32.classify 0xffc00b31ul) in
  let s = up s 5 (S32.classify 0x68581511ul) in
  let s = up s 6 (S32.classify 0x64f98fa7ul) in
  let s = up s 7 (S32.classify 0xbefa4fa4ul) in
  s

(** {2 SHA-384 / SHA-512} *)

[@@FStar.Custard.no_specialize]
let k512 : Seq.lseq S64.t 80 =
  let s = Seq.create 80 (S64.classify 0uL) in
  let s = up s  0 (S64.classify 0x428a2f98d728ae22uL) in
  let s = up s  1 (S64.classify 0x7137449123ef65cduL) in
  let s = up s  2 (S64.classify 0xb5c0fbcfec4d3b2fuL) in
  let s = up s  3 (S64.classify 0xe9b5dba58189dbbcuL) in
  let s = up s  4 (S64.classify 0x3956c25bf348b538uL) in
  let s = up s  5 (S64.classify 0x59f111f1b605d019uL) in
  let s = up s  6 (S64.classify 0x923f82a4af194f9buL) in
  let s = up s  7 (S64.classify 0xab1c5ed5da6d8118uL) in
  let s = up s  8 (S64.classify 0xd807aa98a3030242uL) in
  let s = up s  9 (S64.classify 0x12835b0145706fbeuL) in
  let s = up s 10 (S64.classify 0x243185be4ee4b28cuL) in
  let s = up s 11 (S64.classify 0x550c7dc3d5ffb4e2uL) in
  let s = up s 12 (S64.classify 0x72be5d74f27b896fuL) in
  let s = up s 13 (S64.classify 0x80deb1fe3b1696b1uL) in
  let s = up s 14 (S64.classify 0x9bdc06a725c71235uL) in
  let s = up s 15 (S64.classify 0xc19bf174cf692694uL) in
  let s = up s 16 (S64.classify 0xe49b69c19ef14ad2uL) in
  let s = up s 17 (S64.classify 0xefbe4786384f25e3uL) in
  let s = up s 18 (S64.classify 0x0fc19dc68b8cd5b5uL) in
  let s = up s 19 (S64.classify 0x240ca1cc77ac9c65uL) in
  let s = up s 20 (S64.classify 0x2de92c6f592b0275uL) in
  let s = up s 21 (S64.classify 0x4a7484aa6ea6e483uL) in
  let s = up s 22 (S64.classify 0x5cb0a9dcbd41fbd4uL) in
  let s = up s 23 (S64.classify 0x76f988da831153b5uL) in
  let s = up s 24 (S64.classify 0x983e5152ee66dfabuL) in
  let s = up s 25 (S64.classify 0xa831c66d2db43210uL) in
  let s = up s 26 (S64.classify 0xb00327c898fb213fuL) in
  let s = up s 27 (S64.classify 0xbf597fc7beef0ee4uL) in
  let s = up s 28 (S64.classify 0xc6e00bf33da88fc2uL) in
  let s = up s 29 (S64.classify 0xd5a79147930aa725uL) in
  let s = up s 30 (S64.classify 0x06ca6351e003826fuL) in
  let s = up s 31 (S64.classify 0x142929670a0e6e70uL) in
  let s = up s 32 (S64.classify 0x27b70a8546d22ffcuL) in
  let s = up s 33 (S64.classify 0x2e1b21385c26c926uL) in
  let s = up s 34 (S64.classify 0x4d2c6dfc5ac42aeduL) in
  let s = up s 35 (S64.classify 0x53380d139d95b3dfuL) in
  let s = up s 36 (S64.classify 0x650a73548baf63deuL) in
  let s = up s 37 (S64.classify 0x766a0abb3c77b2a8uL) in
  let s = up s 38 (S64.classify 0x81c2c92e47edaee6uL) in
  let s = up s 39 (S64.classify 0x92722c851482353buL) in
  let s = up s 40 (S64.classify 0xa2bfe8a14cf10364uL) in
  let s = up s 41 (S64.classify 0xa81a664bbc423001uL) in
  let s = up s 42 (S64.classify 0xc24b8b70d0f89791uL) in
  let s = up s 43 (S64.classify 0xc76c51a30654be30uL) in
  let s = up s 44 (S64.classify 0xd192e819d6ef5218uL) in
  let s = up s 45 (S64.classify 0xd69906245565a910uL) in
  let s = up s 46 (S64.classify 0xf40e35855771202auL) in
  let s = up s 47 (S64.classify 0x106aa07032bbd1b8uL) in
  let s = up s 48 (S64.classify 0x19a4c116b8d2d0c8uL) in
  let s = up s 49 (S64.classify 0x1e376c085141ab53uL) in
  let s = up s 50 (S64.classify 0x2748774cdf8eeb99uL) in
  let s = up s 51 (S64.classify 0x34b0bcb5e19b48a8uL) in
  let s = up s 52 (S64.classify 0x391c0cb3c5c95a63uL) in
  let s = up s 53 (S64.classify 0x4ed8aa4ae3418acbuL) in
  let s = up s 54 (S64.classify 0x5b9cca4f7763e373uL) in
  let s = up s 55 (S64.classify 0x682e6ff3d6b2b8a3uL) in
  let s = up s 56 (S64.classify 0x748f82ee5defb2fcuL) in
  let s = up s 57 (S64.classify 0x78a5636f43172f60uL) in
  let s = up s 58 (S64.classify 0x84c87814a1f0ab72uL) in
  let s = up s 59 (S64.classify 0x8cc702081a6439ecuL) in
  let s = up s 60 (S64.classify 0x90befffa23631e28uL) in
  let s = up s 61 (S64.classify 0xa4506cebde82bde9uL) in
  let s = up s 62 (S64.classify 0xbef9a3f7b2c67915uL) in
  let s = up s 63 (S64.classify 0xc67178f2e372532buL) in
  let s = up s 64 (S64.classify 0xca273eceea26619cuL) in
  let s = up s 65 (S64.classify 0xd186b8c721c0c207uL) in
  let s = up s 66 (S64.classify 0xeada7dd6cde0eb1euL) in
  let s = up s 67 (S64.classify 0xf57d4f7fee6ed178uL) in
  let s = up s 68 (S64.classify 0x06f067aa72176fbauL) in
  let s = up s 69 (S64.classify 0x0a637dc5a2c898a6uL) in
  let s = up s 70 (S64.classify 0x113f9804bef90daeuL) in
  let s = up s 71 (S64.classify 0x1b710b35131c471buL) in
  let s = up s 72 (S64.classify 0x28db77f523047d84uL) in
  let s = up s 73 (S64.classify 0x32caab7b40c72493uL) in
  let s = up s 74 (S64.classify 0x3c9ebe0a15c9bebcuL) in
  let s = up s 75 (S64.classify 0x431d67c49c100d4cuL) in
  let s = up s 76 (S64.classify 0x4cc5d4becb3e42b6uL) in
  let s = up s 77 (S64.classify 0x597f299cfc657e2auL) in
  let s = up s 78 (S64.classify 0x5fcb6fab3ad6faecuL) in
  let s = up s 79 (S64.classify 0x6c44198c4a475817uL) in
  s

[@@FStar.Custard.no_specialize]
let iv512 : Seq.lseq S64.t 8 =
  let s = Seq.create 8 (S64.classify 0uL) in
  let s = up s 0 (S64.classify 0x6a09e667f3bcc908uL) in
  let s = up s 1 (S64.classify 0xbb67ae8584caa73buL) in
  let s = up s 2 (S64.classify 0x3c6ef372fe94f82buL) in
  let s = up s 3 (S64.classify 0xa54ff53a5f1d36f1uL) in
  let s = up s 4 (S64.classify 0x510e527fade682d1uL) in
  let s = up s 5 (S64.classify 0x9b05688c2b3e6c1fuL) in
  let s = up s 6 (S64.classify 0x1f83d9abfb41bd6buL) in
  let s = up s 7 (S64.classify 0x5be0cd19137e2179uL) in
  s

[@@FStar.Custard.no_specialize]
let iv384 : Seq.lseq S64.t 8 =
  let s = Seq.create 8 (S64.classify 0uL) in
  let s = up s 0 (S64.classify 0xcbbb9d5dc1059ed8uL) in
  let s = up s 1 (S64.classify 0x629a292a367cd507uL) in
  let s = up s 2 (S64.classify 0x9159015a3070dd17uL) in
  let s = up s 3 (S64.classify 0x152fecd8f70e5939uL) in
  let s = up s 4 (S64.classify 0x67332667ffc00b31uL) in
  let s = up s 5 (S64.classify 0x8eb44a8768581511uL) in
  let s = up s 6 (S64.classify 0xdb0c2e0d64f98fa7uL) in
  let s = up s 7 (S64.classify 0x47b5481dbefa4fa4uL) in
  s

(** {2 The four algorithms} *)

inline_for_extraction noextract
let params256_with (iv: Seq.lseq S32.t 8) (nhash_bytes: (n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 32 })) : params S32.t = {
  nrounds = 64sz; k = k256; iv = iv; nhash_bytes = nhash_bytes;
  cs0_a = 2ul;  cs0_b = 13ul; cs0_c = 22ul;
  cs1_a = 6ul;  cs1_b = 11ul; cs1_c = 25ul;
  s0_a  = 7ul;  s0_b  = 18ul; s0_c  = 3ul;
  s1_a  = 17ul; s1_b  = 19ul; s1_c  = 10ul;
}

inline_for_extraction noextract
let params512_with (iv: Seq.lseq S64.t 8) (nhash_bytes: (n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 64 })) : params S64.t = {
  nrounds = 80sz; k = k512; iv = iv; nhash_bytes = nhash_bytes;
  cs0_a = 28ul; cs0_b = 34ul; cs0_c = 39ul;
  cs1_a = 14ul; cs1_b = 18ul; cs1_c = 41ul;
  s0_a  = 1ul;  s0_b  = 8ul;  s0_c  = 7ul;
  s1_a  = 19ul; s1_b  = 61ul; s1_c  = 6ul;
}

inline_for_extraction noextract let sha2_224 : params S32.t = params256_with iv224 28sz
inline_for_extraction noextract let sha2_256 : params S32.t = params256_with iv256 32sz
inline_for_extraction noextract let sha2_384 : params S64.t = params512_with iv384 48sz
inline_for_extraction noextract let sha2_512 : params S64.t = params512_with iv512 64sz
