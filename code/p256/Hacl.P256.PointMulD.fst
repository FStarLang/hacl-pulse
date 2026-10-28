(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required cy applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** [u1 G + u2 Q], the combination signature verification needs.

    Both products share one doubling chain: {!Hacl.P256.Straus} reads the
    two scalars as signed five-bit digits and adds one entry of each per
    rung.  This module keeps the name the verifier calls. *)
module Hacl.P256.PointMulD

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.P256.Point

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module GR = Spec.P256.Group
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn point_mul_double_g (ox oy oz: A.array S64.t)
                      (u1 u2: A.array S64.t)
                      (qx qy qz: A.array S64.t)
                      (#vox #voy #voz: erased (Seq.seq S64.t))
                      (#p1: perm) (#v1: erased (Seq.seq S64.t))
                      (#p2: perm) (#v2: erased (Seq.seq S64.t))
                      (#pp: perm)
                      (#vqx #vqy #vqz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to u1 #p1 v1 ** A.pts_to u2 #p2 v2 **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length v1 == nl /\ bnd (vals v1) base /\
        Seq.length v2 == nl /\ bnd (vals v2) base /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to u1 #p1 v1 ** A.pts_to u2 #p2 v2 **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_double_g (eval (vals v1))
                       (eval (vals v2)) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz)
               (P.point_mul_double_g (eval (vals v1))
                  (eval (vals v2)) (pt vqx vqy vqz)))
{
  Hacl.P256.Straus.point_mul2 ox oy oz qx qy qz u1 u2;
  ()
}

#pop-options
