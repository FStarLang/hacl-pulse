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
open Hacl.Vec256

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
