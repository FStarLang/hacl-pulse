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

module Hacl.Secret.Cast

(* [friend] is how a module says "I need to see through that abstraction".
   It is recorded in the dependency graph and shows up in a build log, which
   is the property that makes the secret-integer abstraction auditable: the
   set of modules that can see a secret's representation is the set of
   modules that say [friend Hacl.Secret.*], and it is this one,
   [Hacl.Secret.Declassify], and [Hacl.Secret.UInt128] -- which needs to see
   a secret [uint64] in order to multiply two of them. *)
friend Hacl.Secret.UInt8
friend Hacl.Secret.UInt16
friend Hacl.Secret.UInt32
friend Hacl.Secret.UInt64
friend Hacl.Secret.UInt128

module Cast = FStar.Int.Cast
module Cast128 = FStar.Int.Cast.Full

let u8_to_u32 x = Cast.uint8_to_uint32 x
let u16_to_u32 x = Cast.uint16_to_uint32 x
let u16_to_u64 x = Cast.uint16_to_uint64 x
let u8_to_u64 x = Cast.uint8_to_uint64 x
let u32_to_u64 x = Cast.uint32_to_uint64 x
let u64_to_u128 x = Cast128.uint64_to_uint128 x

let u32_to_u8 x = Cast.uint32_to_uint8 x
let u64_to_u8 x = Cast.uint64_to_uint8 x
let u64_to_u32 x = Cast.uint64_to_uint32 x
let u64_to_u16 x = Cast.uint64_to_uint16 x
let u16_to_u8 x = Cast.uint16_to_uint8 x
let u32_to_u16 x = Cast.uint32_to_uint16 x
let u128_to_u64 x = Cast128.uint128_to_uint64 x
