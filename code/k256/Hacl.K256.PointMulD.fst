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
module Hacl.K256.PointMulD

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum52
open Spec.K256.Field52
open Hacl.Impl.Limb4
open Hacl.K256.Point
open Hacl.K256.PointMul

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module GR = Spec.K256.Group
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Each half is only equivalent to the specification's multiple, so the
    sum is only equivalent to the specification's sum; that is what
    {!Spec.K256.Group.point_add_congr} says.  Stated as a lemma so that the
    Pulse function's own query never sees [peq] unfolded. *)
let sum_ok (a b: K.proj_point) (u1 u2: nat) (q: K.proj_point)
  : Lemma (requires GR.on_curve a /\ GR.on_curve b /\
                    GR.on_curve (K.point_mul_g u1) /\
                    GR.on_curve (K.point_mul u2 q) /\
                    GR.peq a (K.point_mul_g u1) /\
                    GR.peq b (K.point_mul u2 q))
          (ensures GR.on_curve (K.point_add a b) /\
                   GR.on_curve (K.point_mul_double_g u1 u2 q) /\
                   GR.peq (K.point_add a b)
                          (K.point_mul_double_g u1 u2 q))
  = GR.point_add_congr a (K.point_mul_g u1) b (K.point_mul u2 q);
    GR.point_add_on_curve a b;
    GR.point_add_on_curve (K.point_mul_g u1) (K.point_mul u2 q)

#pop-options

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
        Seq.length v1 == B4.nl /\ B4.bnd (L4.vals v1) B4.base /\
        Seq.length v2 == B4.nl /\ B4.bnd (L4.vals v2) B4.base /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to u1 #p1 v1 ** A.pts_to u2 #p2 v2 **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (K.point_mul_double_g (B4.eval (L4.vals v1))
                       (B4.eval (L4.vals v2)) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz)
               (K.point_mul_double_g (B4.eval (L4.vals v1))
                  (B4.eval (L4.vals v2)) (pt vqx vqy vqz)))
{
  let z = S64.zero;
  let mut a0 = [| z; 5sz |];
  Mem.track a0; A.pts_to_len a0; let mut a1 = [| z; 5sz |];
  Mem.track a1; A.pts_to_len a1; let mut a2 = [| z; 5sz |];
  Mem.track a2; A.pts_to_len a2; let mut a3 = [| z; 5sz |];
  Mem.track a3; A.pts_to_len a3; let mut a4 = [| z; 5sz |];
  Mem.track a4; A.pts_to_len a4; let mut a5 = [| z; 5sz |];
  Mem.track a5; A.pts_to_len a5; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2;
  A.pts_to_len a3; A.pts_to_len a4; A.pts_to_len a5;

  point_mul_g a0 a1 a2 u1;
  with g0 g1 g2. assert (A.pts_to a0 g0 ** A.pts_to a1 g1 ** A.pts_to a2 g2);
  point_mul a3 a4 a5 qx qy qz u2;
  with h0 h1 h2. assert (A.pts_to a3 h0 ** A.pts_to a4 h1 ** A.pts_to a5 h2);
  point_add ox oy oz a0 a1 a2 a3 a4 a5;
  sum_ok (pt g0 g1 g2) (pt h0 h1 h2) (B4.eval (L4.vals v1))
         (B4.eval (L4.vals v2)) (pt vqx vqy vqz);
  Mem.wipe a5 5sz;
  Mem.wipe a4 5sz;
  Mem.wipe a3 5sz;
  Mem.wipe a2 5sz;
  Mem.wipe a1 5sz;
  Mem.wipe a0 5sz;
  ()
}

#pop-options
