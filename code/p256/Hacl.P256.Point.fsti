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

(** P-256 point arithmetic in Jacobian coordinates.

    Addition and doubling, both complete for the curve's prime order group
    and both branch free.  The dozen-odd field temporaries each needs are
    allocated and discharged inside. *)
module Hacl.P256.Point

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.P256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

(** A triple of limb sequences read as a projective point, and what it takes
    for that reading to be meaningful.  Clients state both in their own
    specifications, so both stay transparent. *)
let pt (x y z: Seq.seq S64.t) : GTot P.proj_point = (fev x, fev y, fev z)

let pt_ok (x y z: Seq.seq S64.t) : prop = felem x /\ felem y /\ felem z

val point_add (ox oy oz: A.array S64.t)
             (x1 y1 z1: A.array S64.t) (x2 y2 z2: A.array S64.t)
             (#vox #voy #voz: erased (Seq.seq S64.t))
             (#p1: perm) (#vx1 #vy1 #vz1: erased (Seq.seq S64.t))
             (#p2: perm) (#vx2 #vy2 #vz2: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
      A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
      A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 ** A.pts_to z2 #p2 vz2 **
      pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
            pt_ok vx1 vy1 vz1 /\ pt_ok vx2 vy2 vz2))
    (ensures fun _ -> exists* (wx wy wz: Seq.seq S64.t).
      A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
      A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
      A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 ** A.pts_to z2 #p2 vz2 **
      pure (pt_ok wx wy wz /\
            pt wx wy wz == P.point_add (pt vx1 vy1 vz1) (pt vx2 vy2 vz2)))

val point_double (ox oy oz: A.array S64.t) (x y z: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
                (#p1: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
      A.pts_to x #p1 vx ** A.pts_to y #p1 vy ** A.pts_to z #p1 vz **
      pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
            pt_ok vx vy vz))
    (ensures fun _ -> exists* (wx wy wz: Seq.seq S64.t).
      A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
      A.pts_to x #p1 vx ** A.pts_to y #p1 vy ** A.pts_to z #p1 vz **
      pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_double (pt vx vy vz)))

