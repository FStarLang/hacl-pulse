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

(** Secret 8-bit unsigned integers.

    See [Hacl.Secret.UInt32] for the rationale and the rules that every
    [Hacl.Secret.*] module obeys; this module is its 8-bit twin, minus the
    operations that make no sense at this width. *)
module Hacl.Secret.UInt8

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module UInt = FStar.UInt

val t : Type0

val v (x: t) : GTot (n: nat { n < pow2 8 })

val v_extensional (x y: t)
  : Lemma (requires v x == v y) (ensures x == y) [SMTPat (v x); SMTPat (v y)]

(** {2 Introduction} *)

val classify (x: U8.t) : r: t { v r == U8.v x }

val zero : r: t { v r == 0 }
val ones : r: t { v r == pow2 8 - 1 }

(** {2 Arithmetic} *)

val add_mod (x y: t) : r: t { v r == (v x + v y) % pow2 8 }
val sub_mod (x y: t) : r: t { v r == (v x - v y) % pow2 8 }
val mul_mod (x y: t) : r: t { v r == (v x * v y) % pow2 8 }

(** {2 Bitwise} *)

val logand (x y: t) : r: t { v r == UInt.logand #8 (v x) (v y) }
val logor  (x y: t) : r: t { v r == UInt.logor  #8 (v x) (v y) }
val logxor (x y: t) : r: t { v r == UInt.logxor #8 (v x) (v y) }
val lognot (x: t)   : r: t { v r == UInt.lognot #8 (v x) }

(** The shift amount is public, and must be, since a variable-distance shift
    is not constant time on every microarchitecture. *)
val shift_left  (x: t) (s: U32.t { U32.v s < 8 }) : r: t { v r == (v x * pow2 (U32.v s)) % pow2 8 }
val shift_right (x: t) (s: U32.t { U32.v s < 8 }) : r: t { v r == v x / pow2 (U32.v s) }

val rotate_right (x: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 8 })
  : r: t { v r == v x / pow2 (U32.v s) + (v x % pow2 (U32.v s)) * pow2 (8 - U32.v s) }

val rotate_left (x: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 8 })
  : r: t { v r == (v x % pow2 (8 - U32.v s)) * pow2 (U32.v s) + v x / pow2 (8 - U32.v s) }

(** {2 Constant-time comparison}

    These are the only way to ask a question about a secret: the answer is
    itself a secret, delivered as an all-ones or all-zeroes mask. *)

val eq_mask (x y: t)
  : r: t { (v x == v y ==> v r == pow2 8 - 1) /\ (v x =!= v y ==> v r == 0) }

val gte_mask (x y: t)
  : r: t { (v x >= v y ==> v r == pow2 8 - 1) /\ (v x < v y ==> v r == 0) }

val lt_mask (x y: t)
  : r: t { (v x < v y ==> v r == pow2 8 - 1) /\ (v x >= v y ==> v r == 0) }

(** [select mask a b] is [a] if [mask] is all ones and [b] if it is all
    zeroes -- a branch-free conditional. *)
val select (mask x y: t)
  : Pure t
      (requires v mask == 0 \/ v mask == pow2 8 - 1)
      (ensures fun r -> r == (if v mask = 0 then y else x))
