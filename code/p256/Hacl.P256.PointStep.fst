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

(** One step of the double-and-add loop, and the point at infinity it
    starts from.

    These are in a module of their own because the cost of an SMT query
    grows faster than the number of definitions it can see, and the
    complete addition law is a great many definitions.  Splitting here
    takes the scalar multiplication from hours to minutes. *)
module Hacl.P256.PointStep

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Impl.Limb
open Hacl.P256.Mont
open Hacl.P256.Field
open Hacl.P256.Point

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 The point at infinity} *)

fn set_infinity (ox oy oz: S.slice S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
requires S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl)
ensures exists* (wx wy wz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_at_infinity)
{
  fzero ox;
  fone oy;
  fzero oz;
}

(** {2 One step}

    Double, add, and keep whichever the bit says.  The two candidates are
    both computed; the mask decides which is copied back. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 400"

fn point_mul_step (ox oy oz ux uy uz sx sy sz: S.slice S64.t)
                  (qx qy qz: S.slice S64.t) (ks: S.slice S64.t)
                  (n: SZ.t { SZ.v n < 256 })
                  (#vox #voy #voz: erased (Seq.seq S64.t))
                  (#vux #vuy #vuz: erased (Seq.seq S64.t))
                  (#vsx #vsy #vsz: erased (Seq.seq S64.t))
                  (#ppx #ppy #ppz: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
                  (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz **
  S.pts_to ux vux ** S.pts_to uy vuy ** S.pts_to uz vuz **
  S.pts_to sx vsx ** S.pts_to sy vsy ** S.pts_to sz vsz **
  S.pts_to qx #ppx vqx ** S.pts_to qy #ppy vqy ** S.pts_to qz #ppz vqz **
  S.pts_to ks #pk vk **
  pure (pt_ok vox voy voz /\ pt_ok vqx vqy vqz /\
        Seq.length vk == nl /\ bnd (vals vk) base /\
        Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\ Seq.length vsz == nl)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
  S.pts_to ux wux ** S.pts_to uy wuy ** S.pts_to uz wuz **
  S.pts_to sx wsx ** S.pts_to sy wsy ** S.pts_to sz wsz **
  S.pts_to qx #ppx vqx ** S.pts_to qy #ppy vqy ** S.pts_to qz #ppz vqz **
  S.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\
        Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
        pt wx wy wz ==
          P.point_mul_step (eval (vals vk)) (pt vqx vqy vqz) (SZ.v n)
                           (pt vox voy voz))
{
  let bi = SZ.sub 255sz n;
  let m = abit ks bi;
  let bb = hide (eval (vals vk) / pow2 (SZ.v bi) % 2 = 1);
  point_double ux uy uz ox oy oz;
  point_add sx sy sz ux uy uz qx qy qz;
  asel ox ux sx m bb;
  asel oy uy sy m bb;
  asel oz uz sz m bb;
}

#pop-options


#pop-options
