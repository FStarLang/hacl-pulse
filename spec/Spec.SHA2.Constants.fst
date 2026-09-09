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

    Each table is given twice over: once as a [list], and once as the
    [Seq.lseq] that the specification uses.  The list is the interesting one,
    because it is also what [Hacl.Hash.SHA2] hands to
    [Pulse.Lib.GlobalArray.mk_static_array]: the literals reach the C array
    initializer from here, so the table in the program image and the table in
    the specification cannot drift.  The sequence is [Seq.seq_of_list] of the
    list, which is definitionally what the global array's contents are, so the
    implementation's postcondition matches the specification by unfolding. *)
module Spec.SHA2.Constants

open Spec.SHA2
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module SZ = FStar.SizeT
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

(** {2 SHA-224 / SHA-256} *)

(** The k256 table, as a list, so that the same literal spine can be both the
    specification below and the compile-time array in [Hacl.Hash.SHA2]. *)
let k256_list : list S32.t = [
  S32.classify 0x428a2f98ul; S32.classify 0x71374491ul; S32.classify 0xb5c0fbcful; S32.classify 0xe9b5dba5ul;
  S32.classify 0x3956c25bul; S32.classify 0x59f111f1ul; S32.classify 0x923f82a4ul; S32.classify 0xab1c5ed5ul;
  S32.classify 0xd807aa98ul; S32.classify 0x12835b01ul; S32.classify 0x243185beul; S32.classify 0x550c7dc3ul;
  S32.classify 0x72be5d74ul; S32.classify 0x80deb1feul; S32.classify 0x9bdc06a7ul; S32.classify 0xc19bf174ul;
  S32.classify 0xe49b69c1ul; S32.classify 0xefbe4786ul; S32.classify 0x0fc19dc6ul; S32.classify 0x240ca1ccul;
  S32.classify 0x2de92c6ful; S32.classify 0x4a7484aaul; S32.classify 0x5cb0a9dcul; S32.classify 0x76f988daul;
  S32.classify 0x983e5152ul; S32.classify 0xa831c66dul; S32.classify 0xb00327c8ul; S32.classify 0xbf597fc7ul;
  S32.classify 0xc6e00bf3ul; S32.classify 0xd5a79147ul; S32.classify 0x06ca6351ul; S32.classify 0x14292967ul;
  S32.classify 0x27b70a85ul; S32.classify 0x2e1b2138ul; S32.classify 0x4d2c6dfcul; S32.classify 0x53380d13ul;
  S32.classify 0x650a7354ul; S32.classify 0x766a0abbul; S32.classify 0x81c2c92eul; S32.classify 0x92722c85ul;
  S32.classify 0xa2bfe8a1ul; S32.classify 0xa81a664bul; S32.classify 0xc24b8b70ul; S32.classify 0xc76c51a3ul;
  S32.classify 0xd192e819ul; S32.classify 0xd6990624ul; S32.classify 0xf40e3585ul; S32.classify 0x106aa070ul;
  S32.classify 0x19a4c116ul; S32.classify 0x1e376c08ul; S32.classify 0x2748774cul; S32.classify 0x34b0bcb5ul;
  S32.classify 0x391c0cb3ul; S32.classify 0x4ed8aa4aul; S32.classify 0x5b9cca4ful; S32.classify 0x682e6ff3ul;
  S32.classify 0x748f82eeul; S32.classify 0x78a5636ful; S32.classify 0x84c87814ul; S32.classify 0x8cc70208ul;
  S32.classify 0x90befffaul; S32.classify 0xa4506cebul; S32.classify 0xbef9a3f7ul; S32.classify 0xc67178f2ul
]

[@@FStar.Custard.no_specialize]
let k256 : Seq.lseq S32.t 64 =
  assert_norm (List.Tot.length k256_list == 64);
  Seq.seq_of_list k256_list

(** The iv256 table, as a list, so that the same literal spine can be both the
    specification below and the compile-time array in [Hacl.Hash.SHA2]. *)
let iv256_list : list S32.t = [
  S32.classify 0x6a09e667ul; S32.classify 0xbb67ae85ul; S32.classify 0x3c6ef372ul; S32.classify 0xa54ff53aul;
  S32.classify 0x510e527ful; S32.classify 0x9b05688cul; S32.classify 0x1f83d9abul; S32.classify 0x5be0cd19ul
]

[@@FStar.Custard.no_specialize]
let iv256 : Seq.lseq S32.t 8 =
  assert_norm (List.Tot.length iv256_list == 8);
  Seq.seq_of_list iv256_list

(** The iv224 table, as a list, so that the same literal spine can be both the
    specification below and the compile-time array in [Hacl.Hash.SHA2]. *)
let iv224_list : list S32.t = [
  S32.classify 0xc1059ed8ul; S32.classify 0x367cd507ul; S32.classify 0x3070dd17ul; S32.classify 0xf70e5939ul;
  S32.classify 0xffc00b31ul; S32.classify 0x68581511ul; S32.classify 0x64f98fa7ul; S32.classify 0xbefa4fa4ul
]

[@@FStar.Custard.no_specialize]
let iv224 : Seq.lseq S32.t 8 =
  assert_norm (List.Tot.length iv224_list == 8);
  Seq.seq_of_list iv224_list

(** {2 SHA-384 / SHA-512} *)

(** The k512 table, as a list, so that the same literal spine can be both the
    specification below and the compile-time array in [Hacl.Hash.SHA2]. *)
let k512_list : list S64.t = [
  S64.classify 0x428a2f98d728ae22uL; S64.classify 0x7137449123ef65cduL; S64.classify 0xb5c0fbcfec4d3b2fuL; S64.classify 0xe9b5dba58189dbbcuL;
  S64.classify 0x3956c25bf348b538uL; S64.classify 0x59f111f1b605d019uL; S64.classify 0x923f82a4af194f9buL; S64.classify 0xab1c5ed5da6d8118uL;
  S64.classify 0xd807aa98a3030242uL; S64.classify 0x12835b0145706fbeuL; S64.classify 0x243185be4ee4b28cuL; S64.classify 0x550c7dc3d5ffb4e2uL;
  S64.classify 0x72be5d74f27b896fuL; S64.classify 0x80deb1fe3b1696b1uL; S64.classify 0x9bdc06a725c71235uL; S64.classify 0xc19bf174cf692694uL;
  S64.classify 0xe49b69c19ef14ad2uL; S64.classify 0xefbe4786384f25e3uL; S64.classify 0x0fc19dc68b8cd5b5uL; S64.classify 0x240ca1cc77ac9c65uL;
  S64.classify 0x2de92c6f592b0275uL; S64.classify 0x4a7484aa6ea6e483uL; S64.classify 0x5cb0a9dcbd41fbd4uL; S64.classify 0x76f988da831153b5uL;
  S64.classify 0x983e5152ee66dfabuL; S64.classify 0xa831c66d2db43210uL; S64.classify 0xb00327c898fb213fuL; S64.classify 0xbf597fc7beef0ee4uL;
  S64.classify 0xc6e00bf33da88fc2uL; S64.classify 0xd5a79147930aa725uL; S64.classify 0x06ca6351e003826fuL; S64.classify 0x142929670a0e6e70uL;
  S64.classify 0x27b70a8546d22ffcuL; S64.classify 0x2e1b21385c26c926uL; S64.classify 0x4d2c6dfc5ac42aeduL; S64.classify 0x53380d139d95b3dfuL;
  S64.classify 0x650a73548baf63deuL; S64.classify 0x766a0abb3c77b2a8uL; S64.classify 0x81c2c92e47edaee6uL; S64.classify 0x92722c851482353buL;
  S64.classify 0xa2bfe8a14cf10364uL; S64.classify 0xa81a664bbc423001uL; S64.classify 0xc24b8b70d0f89791uL; S64.classify 0xc76c51a30654be30uL;
  S64.classify 0xd192e819d6ef5218uL; S64.classify 0xd69906245565a910uL; S64.classify 0xf40e35855771202auL; S64.classify 0x106aa07032bbd1b8uL;
  S64.classify 0x19a4c116b8d2d0c8uL; S64.classify 0x1e376c085141ab53uL; S64.classify 0x2748774cdf8eeb99uL; S64.classify 0x34b0bcb5e19b48a8uL;
  S64.classify 0x391c0cb3c5c95a63uL; S64.classify 0x4ed8aa4ae3418acbuL; S64.classify 0x5b9cca4f7763e373uL; S64.classify 0x682e6ff3d6b2b8a3uL;
  S64.classify 0x748f82ee5defb2fcuL; S64.classify 0x78a5636f43172f60uL; S64.classify 0x84c87814a1f0ab72uL; S64.classify 0x8cc702081a6439ecuL;
  S64.classify 0x90befffa23631e28uL; S64.classify 0xa4506cebde82bde9uL; S64.classify 0xbef9a3f7b2c67915uL; S64.classify 0xc67178f2e372532buL;
  S64.classify 0xca273eceea26619cuL; S64.classify 0xd186b8c721c0c207uL; S64.classify 0xeada7dd6cde0eb1euL; S64.classify 0xf57d4f7fee6ed178uL;
  S64.classify 0x06f067aa72176fbauL; S64.classify 0x0a637dc5a2c898a6uL; S64.classify 0x113f9804bef90daeuL; S64.classify 0x1b710b35131c471buL;
  S64.classify 0x28db77f523047d84uL; S64.classify 0x32caab7b40c72493uL; S64.classify 0x3c9ebe0a15c9bebcuL; S64.classify 0x431d67c49c100d4cuL;
  S64.classify 0x4cc5d4becb3e42b6uL; S64.classify 0x597f299cfc657e2auL; S64.classify 0x5fcb6fab3ad6faecuL; S64.classify 0x6c44198c4a475817uL
]

[@@FStar.Custard.no_specialize]
let k512 : Seq.lseq S64.t 80 =
  assert_norm (List.Tot.length k512_list == 80);
  Seq.seq_of_list k512_list

(** The iv512 table, as a list, so that the same literal spine can be both the
    specification below and the compile-time array in [Hacl.Hash.SHA2]. *)
let iv512_list : list S64.t = [
  S64.classify 0x6a09e667f3bcc908uL; S64.classify 0xbb67ae8584caa73buL; S64.classify 0x3c6ef372fe94f82buL; S64.classify 0xa54ff53a5f1d36f1uL;
  S64.classify 0x510e527fade682d1uL; S64.classify 0x9b05688c2b3e6c1fuL; S64.classify 0x1f83d9abfb41bd6buL; S64.classify 0x5be0cd19137e2179uL
]

[@@FStar.Custard.no_specialize]
let iv512 : Seq.lseq S64.t 8 =
  assert_norm (List.Tot.length iv512_list == 8);
  Seq.seq_of_list iv512_list

(** The iv384 table, as a list, so that the same literal spine can be both the
    specification below and the compile-time array in [Hacl.Hash.SHA2]. *)
let iv384_list : list S64.t = [
  S64.classify 0xcbbb9d5dc1059ed8uL; S64.classify 0x629a292a367cd507uL; S64.classify 0x9159015a3070dd17uL; S64.classify 0x152fecd8f70e5939uL;
  S64.classify 0x67332667ffc00b31uL; S64.classify 0x8eb44a8768581511uL; S64.classify 0xdb0c2e0d64f98fa7uL; S64.classify 0x47b5481dbefa4fa4uL
]

[@@FStar.Custard.no_specialize]
let iv384 : Seq.lseq S64.t 8 =
  assert_norm (List.Tot.length iv384_list == 8);
  Seq.seq_of_list iv384_list

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
