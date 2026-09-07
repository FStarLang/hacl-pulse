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

(** Width conversions between secret integers.

    Widening and truncation preserve secrecy, so unlike [Hacl.Secret.Declassify]
    this module is not an escape hatch and needs no audit; it exists only
    because each width is its own abstract type. *)
module Hacl.Secret.Cast

module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

val u8_to_u32 (x: S8.t) : r: S32.t { S32.v r == S8.v x }
val u8_to_u64 (x: S8.t) : r: S64.t { S64.v r == S8.v x }
val u32_to_u64 (x: S32.t) : r: S64.t { S64.v r == S32.v x }

val u32_to_u8 (x: S32.t) : r: S8.t { S8.v r == S32.v x % pow2 8 }
val u64_to_u8 (x: S64.t) : r: S8.t { S8.v r == S64.v x % pow2 8 }
val u64_to_u32 (x: S64.t) : r: S32.t { S32.v r == S64.v x % pow2 32 }
