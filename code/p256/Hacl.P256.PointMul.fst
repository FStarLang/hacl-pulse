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

(** Scalar multiplication.

    Four bits of the scalar at a time, with the table lookup done by
    reading every entry: the scalar is secret in signing and in key
    agreement, and the complete addition law means no case has to be
    special-cased, so the work is the same whatever the scalar is.

    The scalar arrives as four limbs rather than as bytes.  Reading bit
    [i] of a number is a statement that survives any choice of radix; the
    same statement about a byte string is not, and the specification is
    written the first way. *)
module Hacl.P256.PointMul

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.Impl.Table
open Hacl.P256.Field
open Hacl.P256.Point
open Hacl.P256.PointWin

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module GR = Spec.P256.Group
module Loops = Hacl.Spec.Loops

(** {2 The window}

    The work is in {!Hacl.P256.PointWin}; this module is the face the rest
    of the library sees.  Both entry points are stated up to [peq] rather
    than up to equality, because the window does the additions in a
    different order from the specification's ladder and so arrives at a
    different projective representative of the same point.  The callers
    discharge that where they leave projective coordinates. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn point_mul (ox oy oz: A.array S64.t) (qx qy qz: A.array S64.t)
             (ks: A.array S64.t)
             (#vox #voy #voz: erased (Seq.seq S64.t))
             (#pp: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
             (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vk == nl /\ bnd (vals vk) base /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul (eval (vals vk)) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz)
               (P.point_mul (eval (vals vk)) (pt vqx vqy vqz)))
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
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vk == nl /\ bnd (vals vk) base)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_g (eval (vals vk))) /\
        GR.peq (pt wx wy wz) (P.point_mul_g (eval (vals vk))))
{
  let z = S64.zero;
  let mut a1 = [| z; 4sz |]; A.pts_to_len a1; let mut a2 = [| z; 4sz |]; A.pts_to_len a2; let mut a3 = [| z; 4sz |]; A.pts_to_len a3; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  fone a3;
  (* [point_add] wants its three input coordinates at one permission, and
     the constant tables hand back one existential permission each.  A copy
     into owned buffers is cheaper than teaching the prover to split. *)
  let tx = fgx ();
  fcopy a1 tx;
  drop_table tx;
  let ty = fgy ();
  fcopy a2 ty;
  drop_table ty;
  GR.g_on_curve ();
  point_mul ox oy oz a1 a2 a3 ks;
  ()
}

#pop-options
