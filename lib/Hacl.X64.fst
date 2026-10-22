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

(** Whether the C compiler targets x86-64.

    Every function that carries a [target(...)] attribute -- the AES-NI,
    SHA-NI, AVX2, AVX-512 and BMI2 paths -- also carries

    {[
      custard_c_closure_guard "defined(__x86_64__)"
    ]}

    so that it, and every copy [custard_c_closure_prologue] makes of what it
    reaches, is compiled only inside [#if defined(__x86_64__)].  On any other
    target those functions do not exist, and a call to one would not compile.
    So every call to one, and every runtime CPU check that guards such a
    call, sits in the [then] branch of

    {[
      if x86_64 then (if supported () then fast else portable) else portable
    ]}

    which Custard prints as [#if defined(__x86_64__)] / [#else] / [#endif].
    F* knows nothing about [x86_64], so both branches are verified.

    The condition is a string and Custard does not compare it with the
    guard's, so the two must be kept equal by hand.  A mismatch shows up as an
    undeclared function when the C is compiled for another architecture; the
    [cross] target in the Makefile does that for aarch64. *)
module Hacl.X64

open FStar.Attributes

[@@custard_c_ifdef "defined(__x86_64__)"]
assume val x86_64 : bool
