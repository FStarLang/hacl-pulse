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

(** The element types whose all-zero bit pattern is a value.

    [Hacl.Mem.wipe] zeroes memory and promises only that the array still
    holds {i some} sequence of [t]s.  That is true only if all-zero bytes
    are a [t]: not for an empty type, nor for a refinement that excludes
    zero (such as [x: U8.t { U8.v x == 1 }]), and a proof could then assume
    a value the memory does not hold.  So [wipe] asks for an instance of
    [zeroable].

    The class is abstract, so the only instances are the ones below and
    those built from them with [zeroable_refine], which proves that the
    refinement holds of zero.  The vector types, whose representation is
    trusted anyway, assume theirs next to their [zero]; [mk/memlint.pl]
    allows that nowhere else, nor [friend Hacl.Zeroable].  It is erasable:
    it costs nothing at run time.

    Code generic over [{| word t |}] that wipes arrays of [t] asks for
    [{| zeroable t |}] as well, rather than [word] providing it: [word]'s
    laws do not say all-zero bytes are a value, so a user's [word] instance
    could not soundly carry one. *)
module Hacl.Zeroable

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128

[@@erasable; FStar.Tactics.Typeclasses.tcclass]
val zeroable (t: Type0) : Type0

(** The value that all-zero bytes represent. *)
val zero_value (#t: Type0) (d: zeroable t) : GTot t

instance val zeroable_u8   : d: zeroable U8.t   { zero_value d == 0uy }
instance val zeroable_u16  : d: zeroable U16.t  { zero_value d == 0us }
instance val zeroable_u32  : d: zeroable U32.t  { zero_value d == 0ul }
instance val zeroable_u64  : d: zeroable U64.t  { zero_value d == 0uL }
instance val zeroable_u128 : d: zeroable U128.t { U128.v (zero_value d) == 0 }
instance val zeroable_sz   : d: zeroable SZ.t   { zero_value d == 0sz }

instance val zeroable_s8   : d: zeroable S8.t   { zero_value d == S8.zero }
instance val zeroable_s16  : d: zeroable S16.t  { zero_value d == S16.zero }
instance val zeroable_s32  : d: zeroable S32.t  { zero_value d == S32.zero }
instance val zeroable_s64  : d: zeroable S64.t  { zero_value d == S64.zero }
instance val zeroable_s128 : d: zeroable S128.t { zero_value d == S128.zero }

(** A refinement of a zeroable type is zeroable if zero satisfies it.  Not
    an instance, since resolution cannot discharge the proof: declare one
    per refined type, naming the base instance so that its [zero_value] is
    known, e.g.
    [instance z : zeroable zqt = zeroable_refine #_ #zeroable_s16 (fun x -> S16.v x < q) ()]. *)
val zeroable_refine (#b: Type0) {| d: zeroable b |} (p: b -> prop)
  (_: squash (p (zero_value d))) : zeroable (x: b { p x })
