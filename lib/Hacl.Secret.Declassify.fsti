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

(** Turning a secret back into a value the program may look at.

    Every use of this module is a place where the constant-time argument stops
    being a typing property and becomes a claim someone has to check.  There
    should be very few of them, they should be easy to find -- grepping for
    this module name finds all of them -- and each should be accompanied by an
    argument for why the value is not secret after all.

    Legitimate uses look like: a public length that was computed with secret
    arithmetic; the result of a constant-time tag comparison, which is a single
    bit the caller is entitled to; a value that a standard says is transmitted
    in the clear. *)
module Hacl.Secret.Declassify

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

val u8 (x: S8.t) : r: U8.t { U8.v r == S8.v x }
val u32 (x: S32.t) : r: U32.t { U32.v r == S32.v x }
val u64 (x: S64.t) : r: U64.t { U64.v r == S64.v x }

(** The common case: a mask produced by [eq_mask] or [gte_mask] is one bit of
    information the caller asked for, and this is how that bit is delivered.
    Stated at 8 bits because that is the width every tag comparison is
    accumulated at. *)
val bool_of_mask (mask: S8.t)
  : Pure bool
      (requires S8.v mask == 0 \/ S8.v mask == pow2 8 - 1)
      (ensures fun b -> b <==> S8.v mask == pow2 8 - 1)
