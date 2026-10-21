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

(** Secret 128-bit unsigned integers.

    The same discipline as the narrower widths -- [t] is abstract, is not an
    [eqtype], and every operation here is independent of its arguments in
    time and in memory-access pattern -- but for a type that exists only as
    a place to put a product.

    {b Why this module exists.}  A schoolbook multiply wants a double word:
    the product of two limbs, plus the carries, has to land somewhere exact
    before it is split.  Without a 128-bit type the radix has to come down
    far enough that the product still fits in a [uint64], which costs a
    factor of four in the number of limb multiplications -- and the library
    paid it, twice: {!Spec.Bignum} at radix [2^32] and {!Spec.Bignum256} at
    radix [2^16].  With [mul_wide] the bignum runs at radix [2^64] and the
    curves can run at radix [2^51], which is what HACL* does.

    {b What it is not.}  There is no [mul] and no [div].  A general
    128 x 128 multiply is not a machine instruction and 128-bit division is
    a library call; neither is wanted, and [FStar.UInt128] does not offer
    them either.  The only way to {i make} a wide value is to widen a
    [uint64] or to multiply two of them, which is exactly the vocabulary a
    schoolbook step needs and nothing more.

    {b Constant time.}  On the targets that matter a 128-bit add, subtract,
    shift and the 64x64 multiply are a fixed short sequence of machine
    instructions -- [add]/[adc], [shrd], [mul] on x86-64, [adds]/[adcs],
    [umulh] on AArch64 -- with no data-dependent branch and no table.  That
    is the assumption this module rests on, and it is the same assumption
    the narrower widths rest on.

    {b Extraction.}  Custard compiles [FStar.UInt128] to C's
    [unsigned __int128] under [--codegen C], which is on by default
    (the [--custard_int128] option turns it off for a target whose compiler
    lacks the extension).  Everything below is then the machine instruction
    it names, and the abstraction is free, as at 8, 32 and 64 bits.

    Width conversions live in {!Hacl.Secret.Cast}, with the others. *)
module Hacl.Secret.UInt128

module U32 = FStar.UInt32
module UInt = FStar.UInt
module S64 = Hacl.Secret.UInt64

val t : Type0

(** The mathematical value of a secret.  [GTot]: available to proofs, and to
    nothing that runs. *)
val v (x: t) : GTot (n: nat { n < pow2 128 })

val v_extensional (x y: t)
  : Lemma (requires v x == v y) (ensures x == y) [SMTPat (v x); SMTPat (v y)]

(** {2 Introduction}

    There is no [classify] here.  A 128-bit public constant has no C literal
    to be written as, and no caller has wanted one: a wide value is always
    built from narrower ones. *)

val zero : r: t { v r == 0 }

(** [2^64], the weight of the high half.  A subtraction step borrows this in
    advance so that its result stays a natural number; see
    {!Hacl.Impl.Limb64.diff}. *)
val pow2_64 : r: t { v r == pow2 64 }

(** {2 Arithmetic}

    As at the narrower widths, only the wrapping operations: an overflow
    check would be a branch on a secret. *)

val add_mod (x y: t) : r: t { v r == (v x + v y) % pow2 128 }
val sub_mod (x y: t) : r: t { v r == (v x - v y) % pow2 128 }

(** The widening multiply, and the reason for the module.  The product of
    two 64-bit values always fits, so this one is exact rather than
    wrapping -- the only operation here that is. *)
val mul_wide (x y: S64.t) : r: t { v r == S64.v x * S64.v y }

(** {2 Bitwise} *)

val logand (x y: t) : r: t { v r == UInt.logand #128 (v x) (v y) }
val logor  (x y: t) : r: t { v r == UInt.logor  #128 (v x) (v y) }
val logxor (x y: t) : r: t { v r == UInt.logxor #128 (v x) (v y) }
val lognot (x: t)   : r: t { v r == UInt.lognot #128 (v x) }

(** The shift distance is public, and must be, for the same reason as at the
    narrower widths. *)
val shift_left  (x: t) (s: U32.t { U32.v s < 128 }) : r: t { v r == (v x * pow2 (U32.v s)) % pow2 128 }
val shift_right (x: t) (s: U32.t { U32.v s < 128 }) : r: t { v r == v x / pow2 (U32.v s) }
