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

    Double-and-add, most significant bit first, with the choice made by a
    mask rather than a branch, so the loop is the same 384 iterations
    whatever the scalar is.  The addition law is complete, so no doubling
    has to be special-cased.  The loop is literally
    [Spec.P384.point_mul], which is what lets this file need no group law.

    Signing and ECDH multiply by secret scalars; the bit is read and used
    as a mask, never branched on. *)
module Hacl.P384.PointMul

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.P384.Field
open Hacl.P384.Point

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Loops = Hacl.Spec.Loops
module Mem = Hacl.Mem

(** The bound of the loop, as a comparison whose result already carries its
    meaning, so that the literal need not be typed under [--fuel 0]. *)
let lt384 (x: SZ.t) : (r: bool { r <==> SZ.v x < 384 }) = SZ.lt x 384sz

let top (n: SZ.t { SZ.v n < 384 }) : (r: SZ.t { SZ.v r == 383 - SZ.v n }) = SZ.sub 383sz n

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 The point at infinity} *)

fn set_infinity (ox oy oz: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_at_infinity)
{
  fzero ox;
  fone oy;
  fzero oz;
}

(** {2 One step}

    Double, add, and keep whichever the bit says.  Both candidates are
    computed; the mask decides which is copied back. *)

fn point_mul_step (ox oy oz ux uy uz sx sy sz: A.array S64.t)
                  (qx qy qz: A.array S64.t) (ks: A.array S64.t)
                  (n: SZ.t { SZ.v n < 384 })
                  (#vox #voy #voz: erased (Seq.seq S64.t))
                  (#vux #vuy #vuz: erased (Seq.seq S64.t))
                  (#vsx #vsy #vsz: erased (Seq.seq S64.t))
                  (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
                  (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok vox voy voz /\ pt_ok vqx vqy vqz /\ Seq.length vk == 6 /\
        Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\ Seq.length vsz == 6)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\
        Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
        Seq.length wsx == 6 /\ Seq.length wsy == 6 /\ Seq.length wsz == 6 /\
        pt wx wy wz ==
          P.point_mul_step (num vk) (pt vqx vqy vqz) (SZ.v n) (pt vox voy voz))
{
  let bi = top n;
  let m = get_bit ks bi;
  point_double ux uy uz ox oy oz;
  point_add sx sy sz ux uy uz qx qy qz;
  copy ox ux 6sz;
  copy oy uy 6sz;
  copy oz uz 6sz;
  cselect ox sx 6sz m (P.bit (num vk) (SZ.v bi));
  cselect oy sy 6sz m (P.bit (num vk) (SZ.v bi));
  cselect oz sz 6sz m (P.bit (num vk) (SZ.v bi));
}

(** {2 The loop}

    The accumulator lives in the output; the doubling and the sum need
    buffers of their own, because neither formula may write over an
    input. *)

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
        Seq.length vk == 6 /\ pt_ok vqx vqy vqz)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_mul (num vk) (pt vqx vqy vqz))
{
  let z = S64.zero;
  let mut ux = [| z; 6sz |];
  Mem.track ux; A.pts_to_len ux; let mut uy = [| z; 6sz |];
  Mem.track uy; A.pts_to_len uy; let mut uz = [| z; 6sz |];
  Mem.track uz; A.pts_to_len uz; let mut sx = [| z; 6sz |];
  Mem.track sx; A.pts_to_len sx; let mut sy = [| z; 6sz |];
  Mem.track sy; A.pts_to_len sy; let mut sz = [| z; 6sz |];
  Mem.track sz; A.pts_to_len sz;

  set_infinity ox oy oz;
  Loops.repeati_g_zero (P.point_mul_at (num vk) (pt vqx vqy vqz)) P.point_at_infinity;

  let mut i = 0sz;
  while (let vi = !i; lt384 vi)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
    A.pts_to ks #pk vk **
    pure (SZ.v vi <= 384 /\ pt_ok wx wy wz /\
          Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
          Seq.length wsx == 6 /\ Seq.length wsy == 6 /\ Seq.length wsz == 6 /\
          pt wx wy wz ==
            Loops.repeati_g (SZ.v vi) (P.point_mul_at (num vk) (pt vqx vqy vqz))
              P.point_at_infinity)
  decreases (384 - SZ.v (!i))
  {
    let vi = !i;
    point_mul_step ox oy oz ux uy uz sx sy sz qx qy qz ks vi;
    with rx. assert (A.pts_to ox rx);
    with ry. assert (A.pts_to oy ry);
    with rz. assert (A.pts_to oz rz);
    Loops.unfold_repeati_g (SZ.v vi)
      (P.point_mul_at (num vk) (pt vqx vqy vqz)) P.point_at_infinity;
    assert (pure (pt rx ry rz ==
                  Loops.repeati_g (SZ.v vi + 1)
                    (P.point_mul_at (num vk) (pt vqx vqy vqz))
                    P.point_at_infinity));
    i := SZ.add vi 1sz;
  };

  Mem.wipe sz 6sz;
  Mem.wipe sy 6sz;
  Mem.wipe sx 6sz;
  Mem.wipe uz 6sz;
  Mem.wipe uy 6sz;
  Mem.wipe ux 6sz;
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
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_mul_g (num vk))
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
  point_mul ox oy oz gx gy gz ks;
  Mem.wipe gz 6sz;
  Mem.wipe gy 6sz;
  Mem.wipe gx 6sz;
  ()
}

#pop-options
