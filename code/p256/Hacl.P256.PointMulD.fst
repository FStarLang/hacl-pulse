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
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Impl.Limb
open Hacl.P256.Point
open Hacl.P256.PointMul

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn point_mul_double_g (ox oy oz: S.slice S64.t)
                      (u1 u2: S.slice S64.t)
                      (qx qy qz: S.slice S64.t)
                      (#vox #voy #voz: erased (Seq.seq S64.t))
                      (#p1: perm) (#v1: erased (Seq.seq S64.t))
                      (#p2: perm) (#v2: erased (Seq.seq S64.t))
                      (#pp: perm)
                      (#vqx #vqy #vqz: erased (Seq.seq S64.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz **
  S.pts_to u1 #p1 v1 ** S.pts_to u2 #p2 v2 **
  S.pts_to qx #pp vqx ** S.pts_to qy #pp vqy ** S.pts_to qz #pp vqz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length v1 == nl /\ bnd (vals v1) base /\
        Seq.length v2 == nl /\ bnd (vals v2) base /\ pt_ok vqx vqy vqz)
ensures exists* (wx wy wz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
  S.pts_to u1 #p1 v1 ** S.pts_to u2 #p2 v2 **
  S.pts_to qx #pp vqx ** S.pts_to qy #pp vqy ** S.pts_to qz #pp vqz **
  pure (pt_ok wx wy wz /\
        pt wx wy wz ==
          P.point_mul_double_g (eval (vals v1)) (eval (vals v2))
                               (pt vqx vqy vqz))
{
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let ax = S.from_array a0 16sz;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let ay = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let az = S.from_array a2 16sz;
  let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let cx = S.from_array a3 16sz;
  let mut a4 = [| z; 16sz |]; A.pts_to_len a4; let cy = S.from_array a4 16sz;
  let mut a5 = [| z; 16sz |]; A.pts_to_len a5; let cz = S.from_array a5 16sz;
  S.pts_to_len ax; S.pts_to_len ay; S.pts_to_len az;
  S.pts_to_len cx; S.pts_to_len cy; S.pts_to_len cz;

  point_mul_g ax ay az u1;
  point_mul cx cy cz qx qy qz u2;
  point_add ox oy oz ax ay az cx cy cz;

  S.to_array ax; S.to_array ay; S.to_array az;
  S.to_array cx; S.to_array cy; S.to_array cz;
}

#pop-options
