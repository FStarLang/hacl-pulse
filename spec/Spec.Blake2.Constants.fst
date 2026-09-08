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

    Written as a function rather than as a sequence because it is looked up
    with two indices and never manipulated as a whole; a nested [Seq] would
    only add a projection to every query.  The result carries its own bound,
    so [sigma r i] can be used directly as a subscript into the sixteen-word
    message block. *)
let sigma (r: nat { r < 10 }) (i: nat { i < 16 }) : n: nat { n < 16 } =
  if r = 0 then (
    if i = 0 then 0 else
    if i = 1 then 1 else
    if i = 2 then 2 else
    if i = 3 then 3 else
    if i = 4 then 4 else
    if i = 5 then 5 else
    if i = 6 then 6 else
    if i = 7 then 7 else
    if i = 8 then 8 else
    if i = 9 then 9 else
    if i = 10 then 10 else
    if i = 11 then 11 else
    if i = 12 then 12 else
    if i = 13 then 13 else
    if i = 14 then 14 else
    15)
  else
  if r = 1 then (
    if i = 0 then 14 else
    if i = 1 then 10 else
    if i = 2 then 4 else
    if i = 3 then 8 else
    if i = 4 then 9 else
    if i = 5 then 15 else
    if i = 6 then 13 else
    if i = 7 then 6 else
    if i = 8 then 1 else
    if i = 9 then 12 else
    if i = 10 then 0 else
    if i = 11 then 2 else
    if i = 12 then 11 else
    if i = 13 then 7 else
    if i = 14 then 5 else
    3)
  else
  if r = 2 then (
    if i = 0 then 11 else
    if i = 1 then 8 else
    if i = 2 then 12 else
    if i = 3 then 0 else
    if i = 4 then 5 else
    if i = 5 then 2 else
    if i = 6 then 15 else
    if i = 7 then 13 else
    if i = 8 then 10 else
    if i = 9 then 14 else
    if i = 10 then 3 else
    if i = 11 then 6 else
    if i = 12 then 7 else
    if i = 13 then 1 else
    if i = 14 then 9 else
    4)
  else
  if r = 3 then (
    if i = 0 then 7 else
    if i = 1 then 9 else
    if i = 2 then 3 else
    if i = 3 then 1 else
    if i = 4 then 13 else
    if i = 5 then 12 else
    if i = 6 then 11 else
    if i = 7 then 14 else
    if i = 8 then 2 else
    if i = 9 then 6 else
    if i = 10 then 5 else
    if i = 11 then 10 else
    if i = 12 then 4 else
    if i = 13 then 0 else
    if i = 14 then 15 else
    8)
  else
  if r = 4 then (
    if i = 0 then 9 else
    if i = 1 then 0 else
    if i = 2 then 5 else
    if i = 3 then 7 else
    if i = 4 then 2 else
    if i = 5 then 4 else
    if i = 6 then 10 else
    if i = 7 then 15 else
    if i = 8 then 14 else
    if i = 9 then 1 else
    if i = 10 then 11 else
    if i = 11 then 12 else
    if i = 12 then 6 else
    if i = 13 then 8 else
    if i = 14 then 3 else
    13)
  else
  if r = 5 then (
    if i = 0 then 2 else
    if i = 1 then 12 else
    if i = 2 then 6 else
    if i = 3 then 10 else
    if i = 4 then 0 else
    if i = 5 then 11 else
    if i = 6 then 8 else
    if i = 7 then 3 else
    if i = 8 then 4 else
    if i = 9 then 13 else
    if i = 10 then 7 else
    if i = 11 then 5 else
    if i = 12 then 15 else
    if i = 13 then 14 else
    if i = 14 then 1 else
    9)
  else
  if r = 6 then (
    if i = 0 then 12 else
    if i = 1 then 5 else
    if i = 2 then 1 else
    if i = 3 then 15 else
    if i = 4 then 14 else
    if i = 5 then 13 else
    if i = 6 then 4 else
    if i = 7 then 10 else
    if i = 8 then 0 else
    if i = 9 then 7 else
    if i = 10 then 6 else
    if i = 11 then 3 else
    if i = 12 then 9 else
    if i = 13 then 2 else
    if i = 14 then 8 else
    11)
  else
  if r = 7 then (
    if i = 0 then 13 else
    if i = 1 then 11 else
    if i = 2 then 7 else
    if i = 3 then 14 else
    if i = 4 then 12 else
    if i = 5 then 1 else
    if i = 6 then 3 else
    if i = 7 then 9 else
    if i = 8 then 5 else
    if i = 9 then 0 else
    if i = 10 then 15 else
    if i = 11 then 4 else
    if i = 12 then 8 else
    if i = 13 then 6 else
    if i = 14 then 2 else
    10)
  else
  if r = 8 then (
    if i = 0 then 6 else
    if i = 1 then 15 else
    if i = 2 then 14 else
    if i = 3 then 9 else
    if i = 4 then 11 else
    if i = 5 then 3 else
    if i = 6 then 0 else
    if i = 7 then 8 else
    if i = 8 then 12 else
    if i = 9 then 2 else
    if i = 10 then 13 else
    if i = 11 then 7 else
    if i = 12 then 1 else
    if i = 13 then 4 else
    if i = 14 then 10 else
    5)
  else (
    if i = 0 then 10 else
    if i = 1 then 2 else
    if i = 2 then 8 else
    if i = 3 then 4 else
    if i = 4 then 7 else
    if i = 5 then 6 else
    if i = 6 then 1 else
    if i = 7 then 5 else
    if i = 8 then 15 else
    if i = 9 then 11 else
    if i = 10 then 9 else
    if i = 11 then 14 else
    if i = 12 then 3 else
    if i = 13 then 12 else
    if i = 14 then 13 else
    0)
