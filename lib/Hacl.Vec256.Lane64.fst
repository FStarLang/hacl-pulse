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

(** The 256-bit vector as four sixty-four-bit secret words.

    Keccak, run four states at once, wants each sixty-four-bit lane as the
    secret word the scalar permutation computes with, so that the four-way
    permutation can be specified lane by lane against [Spec.SHA3] without a
    second model of the bitwise operations.  [lane_s] is that word; it is a
    definition in terms of [Hacl.Vec256.lane64], so the existing axioms
    ([bcast64], [set64], [store64]) already speak about it through
    [Hacl.Secret.UInt64.v_extensional].  The three operations below are
    stated on it directly.

    These live apart from [Hacl.Vec256] so that the modules that use only
    the thirty-two-bit view do not carry them in their proof context. *)
module Hacl.Vec256.Lane64

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Vec256

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U32 = FStar.UInt32
module S64 = Hacl.Secret.UInt64
let lane_s (x: t) (i: nat { i < 4 }) : GTot S64.t =
  S64.classify (FStar.UInt64.uint_to_t (lane64 x i))

let lane_s_v (x: t) (i: nat { i < 4 })
  : Lemma (S64.v (lane_s x i) == lane64 x i) [SMTPat (lane_s x i)]
  = ()

(** The same instruction as [vxor], stated on the sixty-four-bit words. *)
[@@custard_extern "Hacl_Vec256_xor64"; custard_c_header "Hacl_Vec256.h"]
assume val xor64 (a b: t)
  : r: t { forall (i: nat). i < 4 ==> lane_s r i == S64.logxor (lane_s a i) (lane_s b i) }

(** [VPANDN]: the complement of the {i first} operand, and the second. *)
[@@custard_extern "Hacl_Vec256_andnot64"; custard_c_header "Hacl_Vec256.h"]
assume val andnot64 (a b: t)
  : r: t { forall (i: nat). i < 4 ==>
             lane_s r i == S64.logand (S64.lognot (lane_s a i)) (lane_s b i) }

(** A rotation of every sixty-four-bit lane by the same nonzero distance.
    As with [rotl], every call site passes a literal; [c/Hacl_Vec256.h]
    turns eight and fifty-six into a byte shuffle. *)
[@@custard_extern "Hacl_Vec256_rotl64"; custard_c_header "Hacl_Vec256.h"]
assume val rotl64 (a: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 })
  : r: t { forall (i: nat). i < 4 ==> lane_s r i == S64.rotate_left (lane_s a i) s }

(** {2 For the SHA-512 message schedule} *)

(** [add64] and [shr64], which [Hacl.Vec256] states on natural numbers,
    restated on the words. *)
let add64_s (a b: t) (i: nat { i < 4 })
  : Lemma (lane_s (add64 a b) i == S64.add_mod (lane_s a i) (lane_s b i))
  = S64.v_extensional (lane_s (add64 a b) i) (S64.add_mod (lane_s a i) (lane_s b i))

let shr64_s (a: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 }) (i: nat { i < 4 })
  : Lemma (lane_s (shr64 a s) i == S64.shift_right (lane_s a i) s)
  = S64.v_extensional (lane_s (shr64 a s) i) (S64.shift_right (lane_s a i) s)

[@@custard_extern "Hacl_Vec256_rotr64"; custard_c_header "Hacl_Vec256.h"]
assume val rotr64 (a: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 })
  : r: t { forall (i: nat). i < 4 ==> lane_s r i == S64.rotate_right (lane_s a i) s }

(** Words [i .. i + 3] of an array. *)
[@@custard_extern "Hacl_Vec256_load64"; custard_c_header "Hacl_Vec256.h"]
assume val load64_at (p: A.array S64.t) (i: SZ.t)
                     (#pm: perm) (#v: erased (Seq.seq S64.t))
  : stt t (requires A.pts_to p #pm v ** pure (SZ.v i + 4 <= Seq.length v))
          (ensures fun r -> A.pts_to p #pm v **
             pure (SZ.v i + 4 <= Seq.length v /\
                   (forall (j: nat). j < 4 ==> lane_s r j == Seq.index v (SZ.v i + j))))

(** The four lanes to words [i .. i + 3]; the rest are unchanged. *)
[@@custard_extern "Hacl_Vec256_store64_at"; custard_c_header "Hacl_Vec256.h"]
assume val store64_at (p: A.array S64.t) (i: SZ.t) (x: t) (#v: erased (Seq.seq S64.t))
  : stt unit (requires A.pts_to p v ** pure (SZ.v i + 4 <= Seq.length v))
             (ensures fun _ -> exists* (v': Seq.seq S64.t). A.pts_to p v' **
                pure (Seq.length v' == Seq.length v /\
                      (forall (k: nat). k < Seq.length v ==>
                         Seq.index v' k == (if SZ.v i <= k && k < SZ.v i + 4
                                            then lane_s x (k - SZ.v i)
                                            else Seq.index v k))))

(** Lanes 1, 2, 3 of [lo] and lane 0 of [hi]. *)
[@@custard_extern "Hacl_Vec256_window64"; custard_c_header "Hacl_Vec256.h"]
assume val window64 (lo hi: t)
  : r: t { lane_s r 0 == lane_s lo 1 /\ lane_s r 1 == lane_s lo 2 /\
           lane_s r 2 == lane_s lo 3 /\ lane_s r 3 == lane_s hi 0 }

(** Lanes 2, 3 moved to 0, 1.  The other two are zero, which nothing needs. *)
[@@custard_extern "Hacl_Vec256_hi_to_lo64"; custard_c_header "Hacl_Vec256.h"]
assume val hi_to_lo64 (a: t)
  : r: t { lane_s r 0 == lane_s a 2 /\ lane_s r 1 == lane_s a 3 }

(** Lanes 0, 1 moved to 2, 3.  The other two are zero, which nothing needs. *)
[@@custard_extern "Hacl_Vec256_lo_to_hi64"; custard_c_header "Hacl_Vec256.h"]
assume val lo_to_hi64 (a: t)
  : r: t { lane_s r 2 == lane_s a 0 /\ lane_s r 3 == lane_s a 1 }

(** Lanes 0, 1 of [lo] and 2, 3 of [hi]. *)
[@@custard_extern "Hacl_Vec256_blend_lohi64"; custard_c_header "Hacl_Vec256.h"]
assume val blend_lohi64 (lo hi: t)
  : r: t { lane_s r 0 == lane_s lo 0 /\ lane_s r 1 == lane_s lo 1 /\
           lane_s r 2 == lane_s hi 2 /\ lane_s r 3 == lane_s hi 3 }
