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

(** The Keccak round constants and rotation offsets (FIPS 202, tables in
    sections 3.2.2 and 3.2.5).

    The rotation offsets are public -- they are shift amounts, and the number
    of bits a lane is rotated by does not depend on any secret -- so [rotc] is
    an ordinary function returning a [nat] and carries its own bound.  The
    round constants become secret values because they are exclusive-ored into
    the state. *)
module Spec.SHA3.Constants

module S64 = Hacl.Secret.UInt64
module U64 = FStar.UInt64
module Seq = FStar.Seq

unfold let up (#a: Type) (#n: nat) (s: Seq.lseq a n) (i: nat { i < n }) (x: a) : Seq.lseq a n =
  Seq.upd s i x

(** The twenty-four iota constants, RC[0] through RC[23]. *)
[@@FStar.Custard.no_specialize]
let rc : Seq.lseq S64.t 24 =
  let s = Seq.create 24 (S64.classify 0uL) in
  let s = up s  0 (S64.classify 0x0000000000000001uL) in
  let s = up s  1 (S64.classify 0x0000000000008082uL) in
  let s = up s  2 (S64.classify 0x800000000000808auL) in
  let s = up s  3 (S64.classify 0x8000000080008000uL) in
  let s = up s  4 (S64.classify 0x000000000000808buL) in
  let s = up s  5 (S64.classify 0x0000000080000001uL) in
  let s = up s  6 (S64.classify 0x8000000080008081uL) in
  let s = up s  7 (S64.classify 0x8000000000008009uL) in
  let s = up s  8 (S64.classify 0x000000000000008auL) in
  let s = up s  9 (S64.classify 0x0000000000000088uL) in
  let s = up s 10 (S64.classify 0x0000000080008009uL) in
  let s = up s 11 (S64.classify 0x000000008000000auL) in
  let s = up s 12 (S64.classify 0x000000008000808buL) in
  let s = up s 13 (S64.classify 0x800000000000008buL) in
  let s = up s 14 (S64.classify 0x8000000000008089uL) in
  let s = up s 15 (S64.classify 0x8000000000008003uL) in
  let s = up s 16 (S64.classify 0x8000000000008002uL) in
  let s = up s 17 (S64.classify 0x8000000000000080uL) in
  let s = up s 18 (S64.classify 0x000000000000800auL) in
  let s = up s 19 (S64.classify 0x800000008000000auL) in
  let s = up s 20 (S64.classify 0x8000000080008081uL) in
  let s = up s 21 (S64.classify 0x8000000000008080uL) in
  let s = up s 22 (S64.classify 0x0000000080000001uL) in
  let s = up s 23 (S64.classify 0x8000000080008008uL) in
  s

(** The rho offsets, in the [x + 5 * y] order the state is flattened in.  Note
    [rotc 0] is zero, which is why the specification rotates through
    [Spec.SHA3.rotl] rather than through [Hacl.Secret.UInt64.rotate_left]. *)
let rotc (i: nat { i < 25 }) : n: nat { n < 64 } =
  match i with
  |  0 ->  0
  |  1 ->  1
  |  2 -> 62
  |  3 -> 28
  |  4 -> 27
  |  5 -> 36
  |  6 -> 44
  |  7 ->  6
  |  8 -> 55
  |  9 -> 20
  | 10 ->  3
  | 11 -> 10
  | 12 -> 43
  | 13 -> 25
  | 14 -> 39
  | 15 -> 41
  | 16 -> 45
  | 17 -> 15
  | 18 -> 21
  | 19 ->  8
  | 20 -> 18
  | 21 ->  2
  | 22 -> 61
  | 23 -> 56
  | _  -> 14
