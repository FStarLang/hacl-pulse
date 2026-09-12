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

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 The point at infinity} *)

fn set_infinity (ox oy oz: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_at_infinity)
{
  fzero ox;
  fone oy;
  fzero oz;
}

(** {2 One step}

    Double, add, and keep whichever the bit says.  The two candidates are
    both computed; the mask decides which is copied back. *)

(** The one place the specification's own definition has to be unfolded.
    Doing it in a lemma, rather than by raising the fuel of the Pulse
    function, keeps [point_double] and [point_add] out of a query that
    already carries the whole field. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 20"
let step_def (k: nat) (p: P.proj_point) (i: nat { i < 256 }) (acc: P.proj_point)
  : Lemma (P.point_mul_step k p i acc ==
             (let d = P.point_double acc in
              if k / pow2 (255 - i) % 2 = 1 then P.point_add d p else d))
  = ()
#pop-options

(** [255 - n], as a subtraction whose result already carries its meaning:
    under [--fuel 0] the literal [255sz] is [uint_to_t 255], and typing that
    needs [pow2 64], which the solver will not compute here. *)
let sub255 (x: SZ.t { SZ.v x < 256 }) : (r: SZ.t { SZ.v r == 255 - SZ.v x }) =
  SZ.sub 255sz x

(** The masked select happens coordinate by coordinate, so what comes back
    is a triple of conditionals; the specification is a conditional of
    triples.  Pushing the case split out into a lemma of its own keeps it
    out of the query that carries the field. *)
let sel_pt (bb: bool) (ax ay az bx byy bz: Seq.seq S64.t)
  : Lemma (requires pt_ok ax ay az /\ pt_ok bx byy bz)
          (ensures (let cx = if bb then bx else ax in
                    let cy = if bb then byy else ay in
                    let cz = if bb then bz else az in
                    pt_ok cx cy cz /\
                    pt cx cy cz == (if bb then pt bx byy bz else pt ax ay az)))
  = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

fn point_mul_step (ox oy oz ux uy uz sx sy sz: A.array S64.t)
                  (qx qy qz: A.array S64.t) (ks: A.array S64.t)
                  (n: SZ.t { SZ.v n < 256 })
                  (#vox #voy #voz: erased (Seq.seq S64.t))
                  (#vux #vuy #vuz: erased (Seq.seq S64.t))
                  (#vsx #vsy #vsz: erased (Seq.seq S64.t))
                  (#pp: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
                  (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok vox voy voz /\ pt_ok vqx vqy vqz /\
        Seq.length vk == nl /\ bnd (vals vk) base /\
        Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\ Seq.length vsz == nl)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to qx #pp vqx ** A.pts_to qy #pp vqy ** A.pts_to qz #pp vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\
        Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
        pt wx wy wz ==
          P.point_mul_step (eval (vals vk)) (pt vqx vqy vqz) (SZ.v n)
                           (pt vox voy voz))
{
  let bi = sub255 n;
  let m = abit ks bi;
  let bb = hide (eval (vals vk) / pow2 (SZ.v bi) % 2 = 1);
  point_double ux uy uz ox oy oz;
  point_add sx sy sz ux uy uz qx qy qz;
  with wux wuy wuz. assert (A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz);
  with wsx wsy wsz. assert (A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz);
  asel ox ux sx m bb;
  asel oy uy sy m bb;
  asel oz uz sz m bb;
  sel_pt (reveal bb) wux wuy wuz wsx wsy wsz;
  step_def (eval (vals vk)) (pt vqx vqy vqz) (SZ.v n) (pt vox voy voz);
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  assert (pure (pt_ok wx wy wz));
  assert (pure (pt wx wy wz ==
    P.point_mul_step (eval (vals vk)) (pt vqx vqy vqz) (SZ.v n) (pt vox voy voz)));
}

#pop-options

#pop-options
