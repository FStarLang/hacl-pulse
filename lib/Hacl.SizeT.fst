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

(** Size literals that do not fit in sixteen bits.

    C only promises that [size_t] holds 65535, so [FStar.SizeT] refuses a
    larger literal unless the caller has assumed [fits_u32].  Every platform
    this library targets has a [size_t] of at least thirty-two bits; the
    assumption is made here, once, so that it is visible.

    This is the only assumption in the library that is not a property of the
    C compiler's own type system. *)
module Hacl.SizeT

module SZ = FStar.SizeT

(** Part of the trusted computing base: [size_t] is at least 32 bits. *)
let fits32 () : Lemma (SZ.fits_u32) = assume (SZ.fits_u32)

(** A literal up to [2^32 - 1], with its value in its type. *)
inline_for_extraction
let big (n: nat { n < pow2 32 }) : (r: SZ.t { SZ.v r == n }) =
  fits32 ();
  SZ.fits_u32_implies_fits n;
  SZ.uint_to_t n
