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

    Computing it as two independent multiplications wastes the doubling
    chain the two could share -- Shamir's trick would halve the work.  But
    verification handles no secrets and is not on anybody's critical path,
    and a table-driven combined ladder is a great deal of code to get
    right; this stays simple on purpose. *)
module Hacl.P256.PointMulD

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.P256.Point
open Hacl.P256.PointMul

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

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
        Seq.length v2 == nl /\ bnd (vals v2) base /\ pt_ok vqx vqy vqz)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to u1 #p1 v1 ** A.pts_to u2 #p2 v2 **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  pure (pt_ok wx wy wz /\
        pt wx wy wz ==
          P.point_mul_double_g (eval (vals v1)) (eval (vals v2))
                               (pt vqx vqy vqz))
{
  let z = S64.zero;
  let mut a0 = [| z; 4sz |]; A.pts_to_len a0; let mut a1 = [| z; 4sz |]; A.pts_to_len a1; let mut a2 = [| z; 4sz |]; A.pts_to_len a2; let mut a3 = [| z; 4sz |]; A.pts_to_len a3; let mut a4 = [| z; 4sz |]; A.pts_to_len a4; let mut a5 = [| z; 4sz |]; A.pts_to_len a5; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2;
  A.pts_to_len a3; A.pts_to_len a4; A.pts_to_len a5;

  point_mul_g a0 a1 a2 u1;
  point_mul a3 a4 a5 qx qy qz u2;
  point_add ox oy oz a0 a1 a2 a3 a4 a5;

  ()
}

#pop-options
