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

(** The constants of RFC 7693: the two initialization vectors and the message
    schedule.

    The initialization vectors are the same numbers SHA-512 and SHA-256 use --
    the fractional parts of the square roots of the first eight primes -- so
    they could be shared with [Spec.SHA2.Constants].  They are written out
    again here because the two algorithms have no other relationship and a
    shared table would only couple them.

    [sigma] is the message-word permutation, ten rows of sixteen.  It is a
    *public* table of indices, not secret data, so it is an ordinary function
    from a round and a position to a message index, with its bound in the
    result type.  That is what lets the implementation use it as an array
    subscript. *)
module Spec.Blake2.Constants

module Seq = FStar.Seq
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

unfold let up (#a: Type) (#n: nat) (s: Seq.lseq a n) (i: nat { i < n }) (x: a) : Seq.lseq a n =
  Seq.upd s i x

(** {2 The initialization vectors} *)

[@@FStar.Custard.no_specialize]
let iv64 : Seq.lseq S64.t 8 =
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
let iv32 : Seq.lseq S32.t 8 =
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

(** {2 The message schedule}

    [sigma_at] is the ten rows of sixteen laid out end to end, as a function of
    a single index rather than as a [Seq].  A function because it is only ever
    looked up, never manipulated as a whole, and flat because that is the shape
    the implementation's table has: filling it is a loop over [sigma_at], and
    each of the hundred and sixty proof obligations that produces is the
    if-chain evaluated at a literal, which is cheap.  A nested lookup would put
    a division and a remainder in every one of them.

    The result carries its own bound, so it can be used directly as a subscript
    into the sixteen-word message block.  These are public indices -- which
    message word a round mixes in is not a secret -- so this is ordinary
    arithmetic, not a constant-time selection. *)
[@@"opaque_to_smt"]
let sigma_at (k: nat { k < 160 }) : n: nat { n < 16 } =
  if k = 0 then 0 else
  if k = 1 then 1 else
  if k = 2 then 2 else
  if k = 3 then 3 else
  if k = 4 then 4 else
  if k = 5 then 5 else
  if k = 6 then 6 else
  if k = 7 then 7 else
  if k = 8 then 8 else
  if k = 9 then 9 else
  if k = 10 then 10 else
  if k = 11 then 11 else
  if k = 12 then 12 else
  if k = 13 then 13 else
  if k = 14 then 14 else
  if k = 15 then 15 else
  if k = 16 then 14 else
  if k = 17 then 10 else
  if k = 18 then 4 else
  if k = 19 then 8 else
  if k = 20 then 9 else
  if k = 21 then 15 else
  if k = 22 then 13 else
  if k = 23 then 6 else
  if k = 24 then 1 else
  if k = 25 then 12 else
  if k = 26 then 0 else
  if k = 27 then 2 else
  if k = 28 then 11 else
  if k = 29 then 7 else
  if k = 30 then 5 else
  if k = 31 then 3 else
  if k = 32 then 11 else
  if k = 33 then 8 else
  if k = 34 then 12 else
  if k = 35 then 0 else
  if k = 36 then 5 else
  if k = 37 then 2 else
  if k = 38 then 15 else
  if k = 39 then 13 else
  if k = 40 then 10 else
  if k = 41 then 14 else
  if k = 42 then 3 else
  if k = 43 then 6 else
  if k = 44 then 7 else
  if k = 45 then 1 else
  if k = 46 then 9 else
  if k = 47 then 4 else
  if k = 48 then 7 else
  if k = 49 then 9 else
  if k = 50 then 3 else
  if k = 51 then 1 else
  if k = 52 then 13 else
  if k = 53 then 12 else
  if k = 54 then 11 else
  if k = 55 then 14 else
  if k = 56 then 2 else
  if k = 57 then 6 else
  if k = 58 then 5 else
  if k = 59 then 10 else
  if k = 60 then 4 else
  if k = 61 then 0 else
  if k = 62 then 15 else
  if k = 63 then 8 else
  if k = 64 then 9 else
  if k = 65 then 0 else
  if k = 66 then 5 else
  if k = 67 then 7 else
  if k = 68 then 2 else
  if k = 69 then 4 else
  if k = 70 then 10 else
  if k = 71 then 15 else
  if k = 72 then 14 else
  if k = 73 then 1 else
  if k = 74 then 11 else
  if k = 75 then 12 else
  if k = 76 then 6 else
  if k = 77 then 8 else
  if k = 78 then 3 else
  if k = 79 then 13 else
  if k = 80 then 2 else
  if k = 81 then 12 else
  if k = 82 then 6 else
  if k = 83 then 10 else
  if k = 84 then 0 else
  if k = 85 then 11 else
  if k = 86 then 8 else
  if k = 87 then 3 else
  if k = 88 then 4 else
  if k = 89 then 13 else
  if k = 90 then 7 else
  if k = 91 then 5 else
  if k = 92 then 15 else
  if k = 93 then 14 else
  if k = 94 then 1 else
  if k = 95 then 9 else
  if k = 96 then 12 else
  if k = 97 then 5 else
  if k = 98 then 1 else
  if k = 99 then 15 else
  if k = 100 then 14 else
  if k = 101 then 13 else
  if k = 102 then 4 else
  if k = 103 then 10 else
  if k = 104 then 0 else
  if k = 105 then 7 else
  if k = 106 then 6 else
  if k = 107 then 3 else
  if k = 108 then 9 else
  if k = 109 then 2 else
  if k = 110 then 8 else
  if k = 111 then 11 else
  if k = 112 then 13 else
  if k = 113 then 11 else
  if k = 114 then 7 else
  if k = 115 then 14 else
  if k = 116 then 12 else
  if k = 117 then 1 else
  if k = 118 then 3 else
  if k = 119 then 9 else
  if k = 120 then 5 else
  if k = 121 then 0 else
  if k = 122 then 15 else
  if k = 123 then 4 else
  if k = 124 then 8 else
  if k = 125 then 6 else
  if k = 126 then 2 else
  if k = 127 then 10 else
  if k = 128 then 6 else
  if k = 129 then 15 else
  if k = 130 then 14 else
  if k = 131 then 9 else
  if k = 132 then 11 else
  if k = 133 then 3 else
  if k = 134 then 0 else
  if k = 135 then 8 else
  if k = 136 then 12 else
  if k = 137 then 2 else
  if k = 138 then 13 else
  if k = 139 then 7 else
  if k = 140 then 1 else
  if k = 141 then 4 else
  if k = 142 then 10 else
  if k = 143 then 5 else
  if k = 144 then 10 else
  if k = 145 then 2 else
  if k = 146 then 8 else
  if k = 147 then 4 else
  if k = 148 then 7 else
  if k = 149 then 6 else
  if k = 150 then 1 else
  if k = 151 then 5 else
  if k = 152 then 15 else
  if k = 153 then 11 else
  if k = 154 then 9 else
  if k = 155 then 14 else
  if k = 156 then 3 else
  if k = 157 then 12 else
  if k = 158 then 13 else
  0

(** Position [i] of round [r]. *)
unfold let sigma (r: nat { r < 10 }) (i: nat { i < 16 }) : n: nat { n < 16 } =
  sigma_at (16 * r + i)
