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

    Double-and-add, most significant bit first, with the choice made by a
    mask rather than a branch: the scalar is secret in signing and in key
    agreement, and the addition law is complete, so no doubling has to be
    special-cased and the loop is the same 256 iterations whatever the
    scalar is.

    The scalar arrives as sixteen limbs rather than as bytes.  Reading bit
    [i] of a number is a statement that survives any choice of radix; the
    same statement about a byte string is not, and the specification is
    written the first way. *)
module Hacl.P256.PointMul

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Impl.Limb
open Hacl.P256.Mont
open Hacl.Impl.Table
open Hacl.P256.Field
open Hacl.P256.Point
open Hacl.P256.PointStep

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module Loops = Hacl.Spec.Loops

(** {2 The loop}

    The accumulator lives in the output; the doubling and the sum need
    buffers of their own, because neither formula may write over an input. *)

(** The bound of the loop, as a comparison whose result already carries its
    meaning: under [--fuel 0] the literal [256sz] is [uint_to_t 256], and
    typing it needs [pow2 64], which the solver will not compute. *)
let lt256 (x: SZ.t) : (r: bool { r <==> SZ.v x < 256 }) = SZ.lt x 256sz

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn point_mul (ox oy oz: S.slice S64.t) (qx qy qz: S.slice S64.t)
             (ks: S.slice S64.t)
             (#vox #voy #voz: erased (Seq.seq S64.t))
             (#pp: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
             (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz **
  S.pts_to qx #pp vqx ** S.pts_to qy #pp vqy ** S.pts_to qz #pp vqz **
  S.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vk == nl /\ bnd (vals vk) base /\ pt_ok vqx vqy vqz)
ensures exists* (wx wy wz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
  S.pts_to qx #pp vqx ** S.pts_to qy #pp vqy ** S.pts_to qz #pp vqz **
  S.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\
        pt wx wy wz == P.point_mul (eval (vals vk)) (pt vqx vqy vqz))
{
  S.pts_to_len ox; S.pts_to_len oy; S.pts_to_len oz;
  let z = S64.zero;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let ux = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let uy = S.from_array a2 16sz;
  let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let uz = S.from_array a3 16sz;
  let mut a4 = [| z; 16sz |]; A.pts_to_len a4; let sx = S.from_array a4 16sz;
  let mut a5 = [| z; 16sz |]; A.pts_to_len a5; let sy = S.from_array a5 16sz;
  let mut a6 = [| z; 16sz |]; A.pts_to_len a6; let sz = S.from_array a6 16sz;
  S.pts_to_len ux; S.pts_to_len uy; S.pts_to_len uz;
  S.pts_to_len sx; S.pts_to_len sy; S.pts_to_len sz;

  set_infinity ox oy oz;
  Loops.repeati_g_zero (P.point_mul_at (eval (vals vk)) (pt vqx vqy vqz))
                       P.point_at_infinity;

  let mut i = 0sz;
  while (let vi = !i; lt256 vi)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
    pts_to i vi **
    S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
    S.pts_to ux wux ** S.pts_to uy wuy ** S.pts_to uz wuz **
    S.pts_to sx wsx ** S.pts_to sy wsy ** S.pts_to sz wsz **
    S.pts_to qx #pp vqx ** S.pts_to qy #pp vqy ** S.pts_to qz #pp vqz **
    S.pts_to ks #pk vk **
    pure (SZ.v vi <= 256 /\ pt_ok wx wy wz /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
          pt wx wy wz ==
            Loops.repeati_g (SZ.v vi)
              (P.point_mul_at (eval (vals vk)) (pt vqx vqy vqz))
              P.point_at_infinity)
  decreases (256 - SZ.v (!i))
  {
    let vi = !i;
    point_mul_step ox oy oz ux uy uz sx sy sz qx qy qz ks vi;
    with rx. assert (S.pts_to ox rx);
    with ry. assert (S.pts_to oy ry);
    with rz. assert (S.pts_to oz rz);
    Loops.unfold_repeati_g (SZ.v vi)
      (P.point_mul_at (eval (vals vk)) (pt vqx vqy vqz)) P.point_at_infinity;
    assert (pure (pt rx ry rz ==
                  Loops.repeati_g (SZ.v vi + 1)
                    (P.point_mul_at (eval (vals vk)) (pt vqx vqy vqz))
                    P.point_at_infinity));
    i := SZ.add vi 1sz;
  };

  with rx. assert (S.pts_to ox rx);
  with ry. assert (S.pts_to oy ry);
  with rz. assert (S.pts_to oz rz);
  assert (pure (pt rx ry rz ==
                Loops.repeati_g 256
                  (P.point_mul_at (eval (vals vk)) (pt vqx vqy vqz))
                  P.point_at_infinity));
  S.to_array ux; S.to_array uy; S.to_array uz;
  S.to_array sx; S.to_array sy; S.to_array sz;
}

(** [out := [k] G]. *)
fn point_mul_g (ox oy oz: S.slice S64.t) (ks: S.slice S64.t)
               (#vox #voy #voz: erased (Seq.seq S64.t))
               (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz ** S.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vk == nl /\ bnd (vals vk) base)
ensures exists* (wx wy wz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz ** S.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_mul_g (eval (vals vk)))
{
  let z = S64.zero;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let gx = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let gy = S.from_array a2 16sz;
  let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let gz = S.from_array a3 16sz;
  S.pts_to_len gx; S.pts_to_len gy; S.pts_to_len gz;
  fone gz;
  (* [point_add] wants its three input coordinates at one permission, and
     the constant tables hand back one existential permission each.  A copy
     into owned buffers is cheaper than teaching the prover to split. *)
  let tx = fgx ();
  fcopy gx tx;
  drop_table tx;
  let ty = fgy ();
  fcopy gy ty;
  drop_table ty;
  point_mul ox oy oz gx gy gz ks;
  S.to_array gx; S.to_array gy; S.to_array gz;
}

#pop-options
