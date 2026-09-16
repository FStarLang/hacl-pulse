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

(** Secret 64-bit unsigned integers.

    A value of type [t] is a 64-bit unsigned integer that the program is not
    allowed to look at.  Concretely, [t] is abstract, it is not an [eqtype],
    and the only operations this interface exports are ones whose running time
    and memory-access pattern are independent of their arguments.  There is no
    comparison returning a [bool], no division, no conversion back to
    [FStar.UInt64.t] and no way to use a [t] as an array index or as the
    condition of an [if].  Consequently a program that type-checks against this
    interface cannot branch on, or index with, a secret -- constant-timeness is
    a typing property rather than the conclusion of an audit.

    [Hacl.Secret.Declassify] is the single, auditable escape hatch.

    At extraction the abstraction is free: Custard sees through it and [t]
    becomes [uint64_t], with every operation below compiled to the machine
    instruction it names.

    The 8-, 32- and 64-bit modules are deliberately three separate interfaces
    rather than one indexed family.  Client code that is genuinely parametric
    in the width should use the [Hacl.Secret.Word] type class, which Custard
    monomorphizes; client code that is not -- which is most of it -- reads
    better naming the width it means. *)
module Hacl.Secret.UInt64

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt

val t : Type0

(** The mathematical value of a secret.  It is [GTot]: available to proofs,
    and to nothing that runs. *)
val v (x: t) : GTot (n: nat { n < pow2 64 })

val v_extensional (x y: t)
  : Lemma (requires v x == v y) (ensures x == y) [SMTPat (v x); SMTPat (v y)]

(** {2 Introduction}

    Making a secret out of a public value is always sound, and is the only
    direction that needs no justification. *)

val classify (x: U64.t) : r: t { v r == U64.v x }

val zero : r: t { v r == 0 }
val ones : r: t { v r == pow2 64 - 1 }

(** {2 Arithmetic}

    Only the wrapping operations are exported: an overflow check would be a
    branch on a secret.  Division and remainder are absent because no
    mainstream processor divides in constant time. *)

val add_mod (x y: t) : r: t { v r == (v x + v y) % pow2 64 }
val sub_mod (x y: t) : r: t { v r == (v x - v y) % pow2 64 }
val mul_mod (x y: t) : r: t { v r == (v x * v y) % pow2 64 }

(** {2 Bitwise} *)

val logand (x y: t) : r: t { v r == UInt.logand #64 (v x) (v y) }
val logor  (x y: t) : r: t { v r == UInt.logor  #64 (v x) (v y) }
val logxor (x y: t) : r: t { v r == UInt.logxor #64 (v x) (v y) }
val lognot (x: t)   : r: t { v r == UInt.lognot #64 (v x) }

(** The shift distance is public, and must be: a variable-distance shift is
    not constant time on every microarchitecture. *)
val shift_left  (x: t) (s: U32.t { U32.v s < 64 }) : r: t { v r == (v x * pow2 (U32.v s)) % pow2 64 }
val shift_right (x: t) (s: U32.t { U32.v s < 64 }) : r: t { v r == v x / pow2 (U32.v s) }

val rotate_right (x: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 })
  : r: t { v r == v x / pow2 (U32.v s) + (v x % pow2 (U32.v s)) * pow2 (64 - U32.v s) }

val rotate_left (x: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 })
  : r: t { v r == (v x % pow2 (64 - U32.v s)) * pow2 (U32.v s) + v x / pow2 (64 - U32.v s) }

(** {2 Constant-time comparison}

    Asking a question about a secret yields a secret answer: an all-ones or
    all-zeroes mask, to be consumed by [select] or by further bitwise
    arithmetic.  There is deliberately no way to turn one into a [bool]. *)

val eq_mask (x y: t)
  : r: t { (v x == v y ==> v r == pow2 64 - 1) /\ (v x =!= v y ==> v r == 0) }

val gte_mask (x y: t)
  : r: t { (v x >= v y ==> v r == pow2 64 - 1) /\ (v x < v y ==> v r == 0) }

val lt_mask (x y: t)
  : r: t { (v x < v y ==> v r == pow2 64 - 1) /\ (v x >= v y ==> v r == 0) }

(** [select mask x y] is [x] if [mask] is all ones and [y] if it is all
    zeroes: a branch-free conditional. *)
val select (mask x y: t)
  : Pure t
      (requires v mask == 0 \/ v mask == pow2 64 - 1)
      (ensures fun r -> r == (if v mask = 0 then y else x))

(** {2 Truncation}

    [mask_low n] is the constant with exactly its [n] least significant bits
    set, so that [logand x (mask_low n)] keeps the bottom [n] bits of [x].
    Both ends of the range are covered: at zero the mask is empty and at
    sixty-four it is all ones. *)

val mask_low (n: U32.t { U32.v n <= 64 }) : r: t { v r == pow2 (U32.v n) - 1 }

val logand_mask_low (x: t) (n: U32.t { U32.v n <= 64 })
  : Lemma (v (logand x (mask_low n)) == v x % pow2 (U32.v n))
