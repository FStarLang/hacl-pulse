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

(** The inner product of two vectors in the NTT domain.  The
    implementation needs the [gamma] table; this interface keeps
    {!Hacl.MLKEM.Tables} out of its callers' solver context, as
    {!Hacl.Impl.MLKEM.Poly} does for the transform. *)
module Hacl.Impl.MLKEM.Dot

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq

(** [dst <- sum of u_i * v_i], both [k]-vectors in the NTT domain. *)
val dot (dst u v: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
        (#pu #pv: perm) (#vd #vu #vv: erased (Seq.seq zqt))
  : stt unit
      (A.pts_to dst vd ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
       pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vd == n /\
             Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n))
      (fun _ -> exists* (w: Seq.seq zqt). A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
        pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == n /\
              Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
              as_poly w == dot #(SZ.v k) (as_zqs vu) (as_zqs vv)))
