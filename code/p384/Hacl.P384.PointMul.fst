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

(** Scalar multiplication on P-384.

    The work is in {!Hacl.P384.PointWin}, a four-bit fixed window: four
    doublings and one addition per four bits of the scalar, with the table
    entry read by masking all sixteen, so the running time does not depend
    on the scalar.  This module is the face the rest of the library sees.

    Both entry points are stated up to [peq] rather than up to equality,
    because the window does the additions in a different order from the
    specification's ladder and so arrives at a different projective
    representative of the same point.  The callers discharge that where
    they leave projective coordinates. *)
module Hacl.P384.PointMul

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.P384.Field
open Hacl.P384.Point
open Hacl.P384.PointWin

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module GR = Spec.P384.Group
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn point_mul (ox oy oz: A.array S64.t) (qx qy qz: A.array S64.t)
             (ks: A.array S64.t)
             (#vox #voy #voz: erased (Seq.seq S64.t))
             (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
             (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6 /\
        Seq.length vk == 6 /\ pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul (num vk) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz) (P.point_mul (num vk) (pt vqx vqy vqz)))
{
  point_mul_win ox oy oz qx qy qz ks;
  ()
}

(** [out := [k] G]. *)
fn point_mul_g (ox oy oz: A.array S64.t) (ks: A.array S64.t)
               (#vox #voy #voz: erased (Seq.seq S64.t))
               (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ks #pk vk **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6 /\
        Seq.length vk == 6)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_g (num vk)) /\
        GR.peq (pt wx wy wz) (P.point_mul_g (num vk)))
{
  let z = S64.zero;
  let mut gx = [| z; 6sz |];
  Mem.track gx; A.pts_to_len gx; let mut gy = [| z; 6sz |];
  Mem.track gy; A.pts_to_len gy; let mut gz = [| z; 6sz |];
  Mem.track gz; A.pts_to_len gz;
  let cx = fgx ();
  let cy = fgy ();
  fcopy gx cx;
  fcopy gy cy;
  drop_table cx;
  drop_table cy;
  fone gz;
  with wgx wgy wgz. assert (A.pts_to gx wgx ** A.pts_to gy wgy ** A.pts_to gz wgz);
  assert (pure (pt wgx wgy wgz == P.g));
  GR.g_on_curve ();
  point_mul_win ox oy oz gx gy gz ks;
  Mem.wipe gz 6sz;
  Mem.wipe gy 6sz;
  Mem.wipe gx 6sz;
  ()
}

#pop-options
