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

(** The complete addition law.

    Renes--Costello--Batina 2016, Algorithms 4 and 6, for [a = -3].  A point
    is three field elements passed side by side, as in [Hacl.Ed25519.Point]:
    no record, no aliasing conventions, just three slices the caller has
    already had to keep apart.

    The specification writes the formulas in place, reusing names; Pulse
    cannot, because a slice that is written needs full permission and one
    that is read needs a fraction, and the same slice cannot supply both.
    Each in-place step therefore goes through the scratch element [w], and
    each step whose two operands are the same element goes through [u].
    That is the whole difference between the listing below and the one in
    the paper, and it is why the two can be compared line by line. *)
module Hacl.P256.Point

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.P256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** {2 Points as three limb sequences} *)

let pt (x y z: Seq.seq S64.t) : GTot P.proj_point = (fev x, fev y, fev z)

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
        pt wx wy wz == P.point_add (pt vx1 vy1 vz1) (pt vx2 vy2 vz2))
{
  reveal_opaque (`%P.point_add) P.point_add;
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  let z = S64.zero;
  let mut a0 = [| z; 8sz |]; A.pts_to_len a0; let mut a1 = [| z; 8sz |]; A.pts_to_len a1; let mut a2 = [| z; 8sz |]; A.pts_to_len a2; let mut a3 = [| z; 8sz |]; A.pts_to_len a3; let mut a4 = [| z; 8sz |]; A.pts_to_len a4; let mut a5 = [| z; 8sz |]; A.pts_to_len a5; let mut aw = [| z; 8sz |]; A.pts_to_len aw; let mut au = [| z; 8sz |]; A.pts_to_len au; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len a5; A.pts_to_len aw; A.pts_to_len au;
  let bc = fb ();
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
  fadd a5 y2 z2;
  fmul aw a4 a5;
  fcopy a4 aw;
  fadd a5 a1 a2;
  fsub aw a4 a5;
  fcopy a4 aw;
  fadd ox x1 z1;
  fadd oy x2 z2;
  fmul aw ox oy;
  fcopy ox aw;
  fadd oy a0 a2;
  fsub aw ox oy;
  fcopy oy aw;
  fmul oz bc a2;
  fsub ox oy oz;
  fcopy au ox;
  fadd oz ox au;
  fadd aw ox oz;
  fcopy ox aw;
  fsub oz a1 ox;
  fadd aw a1 ox;
  fcopy ox aw;
  fmul aw bc oy;
  fcopy oy aw;
  fcopy au a2;
  fadd a1 a2 au;
  fadd aw a1 a2;
  fcopy a2 aw;
  fsub aw oy a2;
  fcopy oy aw;
  fsub aw oy a0;
  fcopy oy aw;
  fcopy au oy;
  fadd a1 oy au;
  fadd aw a1 oy;
  fcopy oy aw;
  fcopy au a0;
  fadd a1 a0 au;
  fadd aw a1 a0;
  fcopy a0 aw;
  fsub aw a0 a2;
  fcopy a0 aw;
  fmul a1 a4 oy;
  fmul a2 a0 oy;
  fmul oy ox oz;
  fadd aw oy a2;
  fcopy oy aw;
  fmul aw a3 ox;
  fcopy ox aw;
  fsub aw ox a1;
  fcopy ox aw;
  fmul aw a4 oz;
  fcopy oz aw;
  fmul a1 a3 a0;
  fadd aw oz a1;
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
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_double (pt vx vy vz))
{
  reveal_opaque (`%P.point_double) P.point_double;
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  let zz = S64.zero;
  let mut a0 = [| zz; 8sz |]; A.pts_to_len a0; let mut a1 = [| zz; 8sz |]; A.pts_to_len a1; let mut a2 = [| zz; 8sz |]; A.pts_to_len a2; let mut a3 = [| zz; 8sz |]; A.pts_to_len a3; let mut aw = [| zz; 8sz |]; A.pts_to_len aw; let mut au = [| zz; 8sz |]; A.pts_to_len au; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len aw; A.pts_to_len au;
  let bc = fb ();
  fcopy au x;
  fmul a0 x au;
  fcopy au y;
  fmul a1 y au;
  fcopy au z;
  fmul a2 z au;
  fmul a3 x y;
  fcopy au a3;
  fadd aw a3 au;
  fcopy a3 aw;
  fmul oz x z;
  fcopy au oz;
  fadd aw oz au;
  fcopy oz aw;
  fmul oy bc a2;
  fsub aw oy oz;
  fcopy oy aw;
  fcopy au oy;
  fadd ox oy au;
  fadd aw ox oy;
  fcopy oy aw;
  fsub ox a1 oy;
  fadd aw a1 oy;
  fcopy oy aw;
  fmul aw ox oy;
  fcopy oy aw;
  fmul aw ox a3;
  fcopy ox aw;
  fcopy au a2;
  fadd a3 a2 au;
  fadd aw a2 a3;
  fcopy a2 aw;
  fmul aw bc oz;
  fcopy oz aw;
  fsub aw oz a2;
  fcopy oz aw;
  fsub aw oz a0;
  fcopy oz aw;
  fcopy au oz;
  fadd a3 oz au;
  fadd aw oz a3;
  fcopy oz aw;
  fcopy au a0;
  fadd a3 a0 au;
  fadd aw a3 a0;
  fcopy a0 aw;
  fsub aw a0 a2;
  fcopy a0 aw;
  fmul aw a0 oz;
  fcopy a0 aw;
  fadd aw oy a0;
  fcopy oy aw;
  fmul a0 y z;
  fcopy au a0;
  fadd aw a0 au;
  fcopy a0 aw;
  fmul aw a0 oz;
  fcopy oz aw;
  fsub aw ox oz;
  fcopy ox aw;
  fmul oz a0 a1;
  fcopy au oz;
  fadd aw oz au;
  fcopy oz aw;
  fcopy au oz;
  fadd aw oz au;
  fcopy oz aw;
  drop_table bc;
  ()
}

#pop-options
