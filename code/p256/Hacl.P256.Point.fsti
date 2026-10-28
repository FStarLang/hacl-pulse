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
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.P256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module JS = Spec.P256.JacSv
module J = Spec.P256.Jac

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

(** Mixed addition, the second point affine: {!point_add} at [Z2 = 1],
    one multiplication cheaper. *)
val point_madd (ox oy oz: A.array S64.t)
               (x1 y1 z1: A.array S64.t) (x2 y2: A.array S64.t)
               (#vox #voy #voz: erased (Seq.seq S64.t))
               (#p1: perm) (#vx1 #vy1 #vz1: erased (Seq.seq S64.t))
               (#p2: perm) (#vx2 #vy2: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
      A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
      A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
      pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
            pt_ok vx1 vy1 vz1 /\ felem vx2 /\ felem vy2))
    (ensures fun _ -> exists* (wx wy wz: Seq.seq S64.t).
      A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
      A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
      A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
      pure (pt_ok wx wy wz /\
            pt wx wy wz == P.point_add (pt vx1 vy1 vz1) (fev vx2, fev vy2, P.fone)))

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

(** {2 Jacobian coordinates} *)

val jdouble (x y z t0 t1 t2: A.array S64.t)
           (#vx #vy #vz: erased (Seq.seq S64.t))
           (#v0 #v1 #v2: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz **
      A.pts_to t0 v0 ** A.pts_to t1 v1 ** A.pts_to t2 v2 **
      pure (Seq.length v0 == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl /\
            pt_ok vx vy vz))
    (ensures fun _ -> exists* (wx wy wz w0 w1 w2: Seq.seq S64.t).
      A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz **
      A.pts_to t0 w0 ** A.pts_to t1 w1 ** A.pts_to t2 w2 **
      pure (Seq.length w0 == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
            pt_ok wx wy wz /\ pt wx wy wz == JS.jdouble (pt vx vy vz)))

val to_j (x y z t0 t1: A.array S64.t)
        (#vx #vy #vz: erased (Seq.seq S64.t))
        (#v0 #v1: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz **
      A.pts_to t0 v0 ** A.pts_to t1 v1 **
      pure (Seq.length v0 == nl /\ Seq.length v1 == nl /\ pt_ok vx vy vz))
    (ensures fun _ -> exists* (wx wy w0 w1: Seq.seq S64.t).
      A.pts_to x wx ** A.pts_to y wy ** A.pts_to z vz **
      A.pts_to t0 w0 ** A.pts_to t1 w1 **
      pure (Seq.length w0 == nl /\ Seq.length w1 == nl /\
            pt_ok wx wy vz /\ pt wx wy vz == J.to_j (pt vx vy vz)))

val to_h (x y z t0: A.array S64.t)
        (#vx #vy #vz: erased (Seq.seq S64.t))
        (#v0: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz ** A.pts_to t0 v0 **
      pure (Seq.length v0 == nl /\ pt_ok vx vy vz))
    (ensures fun _ -> exists* (wx wz w0: Seq.seq S64.t).
      A.pts_to x wx ** A.pts_to y vy ** A.pts_to z wz ** A.pts_to t0 w0 **
      pure (Seq.length w0 == nl /\ pt_ok wx vy wz /\
            pt wx vy wz == JS.to_h (pt vx vy vz)))
