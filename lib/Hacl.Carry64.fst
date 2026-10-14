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

(** Add-with-carry and subtract-with-borrow.

    Both are [assume val]s realized in [c/Hacl_Carry64.h] by
    [_addcarry_u64] and [_subborrow_u64], and both postconditions are axioms;
    [tests/test_carry64.c] checks them against [__int128] arithmetic.  They
    exist because a carry chain written with [__int128] is not turned back
    into [adc] by gcc, and the radix-2^64 X25519 field is nothing but carry
    chains.

    The sum is returned through a reference rather than packed with the
    carry into one double word: that is the shape the intrinsic has, and
    the one the compilers keep in registers.  The postconditions name
    neither value with a function; they state the one equation that pins
    both down, which is what the field's proofs consume.

    [supported] says the machine has BMI2.  Nothing here needs it -- [adc]
    and [sbb] are baseline x86-64 -- but the code that uses these is
    compiled for [mulx], and this is the check that guards it. *)
module Hacl.Carry64

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives

module S64 = Hacl.Secret.UInt64

[@@custard_extern "Hacl_Carry64_supported"; custard_c_header "Hacl_Carry64.h"]
assume val supported (_: unit) : bool

(** [s + 2^64 c' == a + b + c]. *)
[@@custard_extern "Hacl_Carry64_addc"; custard_c_header "Hacl_Carry64.h"]
assume val addc (c a b: S64.t) (r: ref S64.t) (#v: erased S64.t)
  : stt S64.t (requires pts_to r v ** pure (S64.v c <= 1))
              (ensures fun c' -> exists* (s: S64.t). pts_to r s **
                 pure (S64.v c' <= 1 /\
                       S64.v s + pow2 64 * S64.v c' == S64.v a + S64.v b + S64.v c))

(** [s - 2^64 c' == a - b - c]. *)
[@@custard_extern "Hacl_Carry64_subb"; custard_c_header "Hacl_Carry64.h"]
assume val subb (c a b: S64.t) (r: ref S64.t) (#v: erased S64.t)
  : stt S64.t (requires pts_to r v ** pure (S64.v c <= 1))
              (ensures fun c' -> exists* (s: S64.t). pts_to r s **
                 pure (S64.v c' <= 1 /\
                       S64.v s - pow2 64 * S64.v c' == S64.v a - S64.v b - S64.v c))
