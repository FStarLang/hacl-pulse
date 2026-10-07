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

(** The point at infinity, which the windowed multiplication starts its
    accumulator and its table from. *)
module Hacl.P256.PointStep

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.P256.Field
open Hacl.P256.Point

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 The point at infinity} *)

fn set_infinity (ox oy oz: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_at_infinity)
{
  fzero ox;
  fone oy;
  fzero oz;
}

#pop-options
