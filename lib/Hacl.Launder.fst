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

(** A value barrier.

    Every constant-time selection in this library has the same shape: build a
    mask that is all ones when some secret equals some candidate and all
    zeroes otherwise, and fold the candidate through the mask so that the
    answer depends on the secret but the control flow and the addresses do
    not.  The verified statement is about the value computed.  It says
    nothing about how the value is computed, because F* has no way to talk
    about that, and so the whole constant-time claim rests on the C compiler
    emitting the mask arithmetic as mask arithmetic.

    It is entitled not to.  {!Hacl.Bignum.Base.table_select} compares a
    secret four-bit digit against the sixteen constants zero through fifteen;
    a compiler that unrolls the loop sees sixteen comparisons of a runtime
    value against literals, and may decide the cheapest code is a cascade
    that tests the digit and jumps to the entry it names.  That is a correct
    compilation of the C and a complete defeat of the algorithm, and clang
    at [-O3] performed it: the lookup's running time rose monotonically with
    the digit, from 3.7ns at zero to 8.9ns at fifteen.

    [launder] is the smallest thing that stops this.  It is the identity, and
    that is all it is required to be; the C behind it is an empty [asm]
    statement with a read-write register constraint, which emits no
    instruction but leaves the optimizer holding a value it has no
    information about.  A mask that has been laundered cannot be recognised
    as the result of a comparison, so there is no comparison left to turn
    into a branch and the fold must be emitted as written.

    The barrier belongs on the mask rather than on the secret.  Laundering
    the secret would not help: the comparisons against the sixteen literals
    would still be there, and specialising a runtime value against literals
    is exactly what the compiler was doing. *)

module Hacl.Launder

module S64 = Hacl.Secret.UInt64

(** [launder x] is [x], and the extracted C says so too.  The only reason it
    is not [let launder x = x] is that the generated code must contain a call
    the optimizer cannot see through. *)
[@@custard_extern "Hacl_Launder_u64"; custard_c_header "Hacl_Launder.h"]
assume val launder (x: S64.t) : r: S64.t { r == x }
