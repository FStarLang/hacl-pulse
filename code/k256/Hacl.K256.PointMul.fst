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
module Hacl.K256.PointMul

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum52
open Spec.K256.Field52
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.Impl.Table
open Hacl.K256.Field52
open Hacl.K256.Point
open Hacl.K256.PointWin

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module GR = Spec.K256.Group
module Loops = Hacl.Spec.Loops
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4
module MG = Hacl.K256.PointMulG

(** {2 The window}

    The work is in {!Hacl.K256.PointWin}; this module is the face the rest
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
        Seq.length vk == B4.nl /\ B4.bnd (L4.vals vk) B4.base /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (K.point_mul (B4.eval (L4.vals vk)) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz)
               (K.point_mul (B4.eval (L4.vals vk)) (pt vqx vqy vqz)))
{
  point_mul_win ox oy oz qx qy qz ks;
  ()
}

(** [out := [k] G].

    The generator is known at compile time, so this does not go through
    the variable-base window above: {!Hacl.K256.PointMulG} splits the
    scalar into four sixty-four-bit pieces and walks them against four
    compiled-in base points, sixty doublings where the ladder pays two
    hundred and fifty-six. *)
fn point_mul_g (ox oy oz: A.array S64.t) (ks: A.array S64.t)
               (#vox #voy #voz: erased (Seq.seq S64.t))
               (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vk == B4.nl /\ B4.bnd (L4.vals vk) B4.base)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (K.point_mul_g (B4.eval (L4.vals vk))) /\
        GR.peq (pt wx wy wz) (K.point_mul_g (B4.eval (L4.vals vk))))
{
  MG.point_mul_g_win ox oy oz ks;
}

#pop-options
