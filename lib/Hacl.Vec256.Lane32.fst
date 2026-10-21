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

(** Thirty-two-bit lane arithmetic, and polynomials as arrays of words.

    ML-DSA's coefficients are words below [q = 8380417], held in arrays of
    a refinement of {!Hacl.Secret.UInt32.t}; its transforms and its
    pointwise product want eight of them at a time.  This module adds what
    that needs to {!Hacl.Vec256}: the load and store of eight consecutive
    words of such an array, the remaining lane-wise arithmetic (subtraction,
    the low and high halves of a product, the unsigned minimum), and one
    general permutation of lanes.

    Arrays are indexed by an offset rather than sliced, so that a caller
    walking a polynomial does not have to split and rejoin its permission
    eight words at a time; and they are parametric in the refinement [w] of
    the words they hold, so that the same store writes any array of
    refined words.  An array of plain words is not one of those (an
    unrefined type is not a refinement), so it has its own load.

    As with {!Hacl.Vec256.Lane64}, these live apart from [Hacl.Vec256] so
    that the modules that do not use them do not carry them in their proof
    context.  [tests/test_vec256.c] checks each against a scalar
    transcription. *)
module Hacl.Vec256.Lane32

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Vec256

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S32 = Hacl.Secret.UInt32

(** {2 Memory} *)

(** Words [i .. i + 7] of an array of words satisfying [w]. *)
[@@custard_extern "Hacl_Vec256_load32"; custard_c_header "Hacl_Vec256.h"]
assume val load_at (#w: S32.t -> prop) (p: A.array (x: S32.t { w x })) (i: SZ.t)
                   (#pm: perm) (#v: erased (Seq.seq (x: S32.t { w x })))
  : stt t (requires A.pts_to p #pm v ** pure (SZ.v i + 8 <= Seq.length v))
          (ensures fun r -> A.pts_to p #pm v **
             pure (SZ.v i + 8 <= Seq.length v /\
                   (forall (j: nat). j < 8 ==> lane r j == Seq.index v (SZ.v i + j))))

(** The same, from an array of arbitrary words. *)
[@@custard_extern "Hacl_Vec256_load32"; custard_c_header "Hacl_Vec256.h"]
assume val load_word_at (p: A.array S32.t) (i: SZ.t)
                        (#pm: perm) (#v: erased (Seq.seq S32.t))
  : stt t (requires A.pts_to p #pm v ** pure (SZ.v i + 8 <= Seq.length v))
          (ensures fun r -> A.pts_to p #pm v **
             pure (SZ.v i + 8 <= Seq.length v /\
                   (forall (j: nat). j < 8 ==> lane r j == Seq.index v (SZ.v i + j))))

(** Words [i .. i + 7] of an array of words satisfying [w] become the
    lanes of [x], each of which must satisfy [w]; the rest are unchanged. *)
[@@custard_extern "Hacl_Vec256_store32"; custard_c_header "Hacl_Vec256.h"]
assume val store_at (#w: S32.t -> prop) (p: A.array (x: S32.t { w x })) (i: SZ.t)
                    (x: t { forall (j: nat). j < 8 ==> w (lane x j) })
                    (#v: erased (Seq.seq (x: S32.t { w x })))
  : stt unit (requires A.pts_to p v ** pure (SZ.v i + 8 <= Seq.length v))
             (ensures fun _ -> exists* (v': Seq.seq (x: S32.t { w x })). A.pts_to p v' **
                pure (Seq.length v' == Seq.length v /\
                      (forall (k: nat). k < Seq.length v ==>
                         Seq.index v' k == (if SZ.v i <= k && k < SZ.v i + 8
                                            then lane x (k - SZ.v i)
                                            else Seq.index v k))))

(** {2 Lane arithmetic} *)

[@@custard_extern "Hacl_Vec256_sub32"; custard_c_header "Hacl_Vec256.h"]
assume val sub32 (a b: t)
  : r: t { forall (i: nat). i < 8 ==> lane r i == S32.sub_mod (lane a i) (lane b i) }

(** [VPMULLD]: the low half of the product. *)
[@@custard_extern "Hacl_Vec256_mullo32"; custard_c_header "Hacl_Vec256.h"]
assume val mullo32 (a b: t)
  : r: t { forall (i: nat). i < 8 ==> lane r i == S32.mul_mod (lane a i) (lane b i) }

(** The high half of the product.  There is no one instruction for this;
    [c/Hacl_Vec256.h] does the even lanes and the odd lanes with a
    [VPMULUDQ] each and blends them. *)
[@@custard_extern "Hacl_Vec256_mulhi32"; custard_c_header "Hacl_Vec256.h"]
assume val mulhi32 (a b: t)
  : r: t { forall (i: nat). i < 8 ==>
             S32.v (lane r i) == (S32.v (lane a i) * S32.v (lane b i)) / pow2 32 }

(** [VPMINUD]. *)
[@@custard_extern "Hacl_Vec256_minu32"; custard_c_header "Hacl_Vec256.h"]
assume val minu32 (a b: t)
  : r: t { forall (i: nat). i < 8 ==>
             lane r i == (if S32.v (lane a i) <= S32.v (lane b i) then lane a i else lane b i) }

(** {2 Permutation} *)

(** [VPERMD] with a constant index vector: lane [j] of the result is lane
    [ij] of [a].  Every call site passes literals. *)
[@@custard_extern "Hacl_Vec256_perm32"; custard_c_header "Hacl_Vec256.h"]
assume val perm32 (a: t) (i0 i1 i2 i3 i4 i5 i6 i7: (i: U32.t { U32.v i < 8 }))
  : r: t { lane r 0 == lane a (U32.v i0) /\ lane r 1 == lane a (U32.v i1) /\
           lane r 2 == lane a (U32.v i2) /\ lane r 3 == lane a (U32.v i3) /\
           lane r 4 == lane a (U32.v i4) /\ lane r 5 == lane a (U32.v i5) /\
           lane r 6 == lane a (U32.v i6) /\ lane r 7 == lane a (U32.v i7) }
