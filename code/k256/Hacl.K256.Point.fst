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

(** The complete addition law for [a = 0].

    Renes--Costello--Batina 2016, Algorithms 7 and 9.  A point is three
    field elements passed side by side, exactly as in {!Hacl.P256.Point};
    and as there, the specification's in-place assignments have to go
    through a scratch element [aw], because a slice that is written needs
    full permission and one that is read needs a fraction.  A step whose
    two operands are the same element goes through [au] as well.  That is
    the whole difference between the listing below and the one in the
    paper.

    Dropping [a] from [-3] to [0] takes addition from twelve
    multiplications to twelve (the saving there is in the additions) and
    doubling from eight to six, and removes the constant [3] entirely: the
    only coefficient that appears is [3b = 21]. *)
module Hacl.K256.Point

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.K256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.K256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module K = Spec.K256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** {2 Points as three limb sequences} *)

let pt (x y z: Seq.seq S64.t) : GTot K.proj_point = (fev x, fev y, fev z)

let pt_ok (x y z: Seq.seq S64.t) : prop = felem x /\ felem y /\ felem z

(** {2 Addition} *)

fn point_add (ox oy oz: A.array S64.t)
             (x1 y1 z1: A.array S64.t) (x2 y2 z2: A.array S64.t)
             (#vox #voy #voz: erased (Seq.seq S64.t))
             (#p1: perm) (#vx1 #vy1 #vz1: erased (Seq.seq S64.t))
             (#p2: perm) (#vx2 #vy2 #vz2: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 ** A.pts_to z2 #p2 vz2 **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        pt_ok vx1 vy1 vz1 /\ pt_ok vx2 vy2 vz2)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 ** A.pts_to z2 #p2 vz2 **
  pure (pt_ok wx wy wz /\
        pt wx wy wz == K.point_add (pt vx1 vy1 vz1) (pt vx2 vy2 vz2))
{
  reveal_opaque (`%K.point_add) K.point_add;
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  let zz = S64.zero;
  let mut a0 = [| zz; 4sz |]; A.pts_to_len a0; let mut a1 = [| zz; 4sz |]; A.pts_to_len a1; let mut a2 = [| zz; 4sz |]; A.pts_to_len a2; let mut a3 = [| zz; 4sz |]; A.pts_to_len a3; let mut a4 = [| zz; 4sz |]; A.pts_to_len a4; let mut aw = [| zz; 4sz |]; A.pts_to_len aw; let mut au = [| zz; 4sz |]; A.pts_to_len au; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len aw; A.pts_to_len au;
  let bc = fb3 ();
  fmul a0 x1 x2;
  fmul a1 y1 y2;
  fmul a2 z1 z2;
  fadd a3 x1 y1;
  fadd a4 x2 y2;
  fmul aw a3 a4;
  fcopy a3 aw;
  fadd a4 a0 a1;
  fsub aw a3 a4;
  fcopy a3 aw;
  fadd a4 y1 z1;
  fadd ox y2 z2;
  fmul aw a4 ox;
  fcopy a4 aw;
  fadd ox a1 a2;
  fsub aw a4 ox;
  fcopy a4 aw;
  fadd ox x1 z1;
  fadd oy x2 z2;
  fmul aw ox oy;
  fcopy ox aw;
  fadd oy a0 a2;
  fsub aw ox oy;
  fcopy oy aw;
  fcopy au a0;
  fadd ox a0 au;
  fadd aw ox a0;
  fcopy a0 aw;
  fmul aw bc a2;
  fcopy a2 aw;
  fadd oz a1 a2;
  fsub aw a1 a2;
  fcopy a1 aw;
  fmul aw bc oy;
  fcopy oy aw;
  fmul ox a4 oy;
  fmul a2 a3 a1;
  fsub aw a2 ox;
  fcopy ox aw;
  fmul aw oy a0;
  fcopy oy aw;
  fmul aw a1 oz;
  fcopy a1 aw;
  fadd aw a1 oy;
  fcopy oy aw;
  fmul aw a0 a3;
  fcopy a0 aw;
  fmul aw oz a4;
  fcopy oz aw;
  fadd aw oz a0;
  fcopy oz aw;
  drop_table bc;
  ()
}

(** {2 Doubling} *)

fn point_double (ox oy oz: A.array S64.t) (x y z: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
                (#p1: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to x #p1 vx ** A.pts_to y #p1 vy ** A.pts_to z #p1 vz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        pt_ok vx vy vz)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to x #p1 vx ** A.pts_to y #p1 vy ** A.pts_to z #p1 vz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == K.point_double (pt vx vy vz))
{
  reveal_opaque (`%K.point_double) K.point_double;
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  let zz = S64.zero;
  let mut a0 = [| zz; 4sz |]; A.pts_to_len a0; let mut a1 = [| zz; 4sz |]; A.pts_to_len a1; let mut a2 = [| zz; 4sz |]; A.pts_to_len a2; let mut a3 = [| zz; 4sz |]; A.pts_to_len a3; let mut a4 = [| zz; 4sz |]; A.pts_to_len a4; let mut aw = [| zz; 4sz |]; A.pts_to_len aw; let mut au = [| zz; 4sz |]; A.pts_to_len au; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len aw; A.pts_to_len au;
  let bc = fb3 ();
  fsqr a0 y;
  fcopy au a0;
  fadd oz a0 au;
  fcopy au oz;
  fadd aw oz au;
  fcopy oz aw;
  fcopy au oz;
  fadd aw oz au;
  fcopy oz aw;
  fmul a1 y z;
  fsqr a2 z;
  fmul aw bc a2;
  fcopy a2 aw;
  fmul ox a2 oz;
  fadd oy a0 a2;
  fmul aw a1 oz;
  fcopy oz aw;
  fcopy au a2;
  fadd a1 a2 au;
  fadd aw a1 a2;
  fcopy a2 aw;
  fsub aw a0 a2;
  fcopy a0 aw;
  fmul aw a0 oy;
  fcopy oy aw;
  fadd aw ox oy;
  fcopy oy aw;
  fmul a1 x y;
  fmul ox a0 a1;
  fcopy au ox;
  fadd aw ox au;
  fcopy ox aw;
  drop_table bc;
  ()
}

#pop-options
