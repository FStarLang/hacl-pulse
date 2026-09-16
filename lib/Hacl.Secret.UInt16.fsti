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

(** Secret 16-bit unsigned integers.

    The fourth width, and the one with a single client: FrodoKEM, whose
    matrices are arrays of secrets modulo [2^16].  The interface is
    [Hacl.Secret.UInt32]'s, read that module's header for what abstraction
    buys and what it costs.

    Two things are exported here that the other widths do not have, because
    Frodo is the only algorithm that wants them:

    - [mul_mod] is used in a hot inner loop rather than for a single
      multiply-accumulate, and a 16-bit multiply is genuinely constant time
      on every processor this library targets.
    - [to_bytes_le] and [of_bytes_le] appear as [S8.t] pairs rather than as
      array operations, because a Frodo matrix is serialized element by
      element and there is no gain in going through a buffer. *)
module Hacl.Secret.UInt16

module U16 = FStar.UInt16
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module UInt = FStar.UInt

val t : Type0

val v (x: t) : GTot (n: nat { n < pow2 16 })

val v_extensional (x y: t)
  : Lemma (requires v x == v y) (ensures x == y) [SMTPat (v x); SMTPat (v y)]

(** {2 Introduction} *)

val classify (x: U16.t) : r: t { v r == U16.v x }

val zero : r: t { v r == 0 }
val one  : r: t { v r == 1 }
val ones : r: t { v r == pow2 16 - 1 }

(** {2 Arithmetic} *)

val add_mod (x y: t) : r: t { v r == (v x + v y) % pow2 16 }
val sub_mod (x y: t) : r: t { v r == (v x - v y) % pow2 16 }
val mul_mod (x y: t) : r: t { v r == (v x * v y) % pow2 16 }

(** {2 Bitwise} *)

val logand (x y: t) : r: t { v r == UInt.logand #16 (v x) (v y) }
val logor  (x y: t) : r: t { v r == UInt.logor  #16 (v x) (v y) }
val logxor (x y: t) : r: t { v r == UInt.logxor #16 (v x) (v y) }
val lognot (x: t)   : r: t { v r == UInt.lognot #16 (v x) }

val shift_left  (x: t) (s: U32.t { U32.v s < 16 }) : r: t { v r == (v x * pow2 (U32.v s)) % pow2 16 }
val shift_right (x: t) (s: U32.t { U32.v s < 16 }) : r: t { v r == v x / pow2 (U32.v s) }

(** [mask_low n] is [2^n - 1], the mask that keeps the low [n] bits.  Frodo
    reduces modulo [2^logq] constantly, and writing that as a mask rather
    than as a shift pair keeps the specification's [% pow2 logq] visible. *)
val mask_low (n: U32.t { U32.v n <= 16 }) : r: t { v r == pow2 (U32.v n) - 1 }

val logand_mask_low (x: t) (n: U32.t { U32.v n <= 16 })
  : Lemma (v (logand x (mask_low n)) == v x % pow2 (U32.v n))

(** {2 Constant-time comparison} *)

val eq_mask (x y: t)
  : r: t { (v x == v y ==> v r == pow2 16 - 1) /\ (v x =!= v y ==> v r == 0) }

val gte_mask (x y: t)
  : r: t { (v x >= v y ==> v r == pow2 16 - 1) /\ (v x < v y ==> v r == 0) }

val lt_mask (x y: t)
  : r: t { (v x < v y ==> v r == pow2 16 - 1) /\ (v x >= v y ==> v r == 0) }

val select (mask x y: t)
  : Pure t
      (requires v mask == 0 \/ v mask == pow2 16 - 1)
      (ensures fun r -> r == (if v mask = 0 then y else x))

(** {2 Bytes}

    Little-endian, which is the order every 16-bit quantity in Frodo is
    written in: the matrix serialization, the SHAKE output that becomes a
    matrix entry, and the row index fed to SHAKE. *)

val lo (x: t) : r: S8.t { S8.v r == v x % pow2 8 }
val hi (x: t) : r: S8.t { S8.v r == v x / pow2 8 }

val of_bytes_le (l h: S8.t) : r: t { v r == S8.v l + S8.v h * pow2 8 }

val of_bytes_le_lo_hi (x: t)
  : Lemma (of_bytes_le (lo x) (hi x) == x) [SMTPat (of_bytes_le (lo x) (hi x))]
