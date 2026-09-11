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

module S = Pulse.Lib.Slice
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

fn point_add (ox oy oz: S.slice S64.t)
             (x1 y1 z1: S.slice S64.t) (x2 y2 z2: S.slice S64.t)
             (#vox #voy #voz: erased (Seq.seq S64.t))
             (#p1: perm) (#vx1 #vy1 #vz1: erased (Seq.seq S64.t))
             (#p2: perm) (#vx2 #vy2 #vz2: erased (Seq.seq S64.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz **
  S.pts_to x1 #p1 vx1 ** S.pts_to y1 #p1 vy1 ** S.pts_to z1 #p1 vz1 **
  S.pts_to x2 #p2 vx2 ** S.pts_to y2 #p2 vy2 ** S.pts_to z2 #p2 vz2 **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        pt_ok vx1 vy1 vz1 /\ pt_ok vx2 vy2 vz2)
ensures exists* (wx wy wz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
  S.pts_to x1 #p1 vx1 ** S.pts_to y1 #p1 vy1 ** S.pts_to z1 #p1 vz1 **
  S.pts_to x2 #p2 vx2 ** S.pts_to y2 #p2 vy2 ** S.pts_to z2 #p2 vz2 **
  pure (pt_ok wx wy wz /\
        pt wx wy wz == P.point_add (pt vx1 vy1 vz1) (pt vx2 vy2 vz2))
{
  reveal_opaque (`%P.point_add) P.point_add;
  S.pts_to_len ox; S.pts_to_len oy; S.pts_to_len oz;
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let t0 = S.from_array a0 16sz;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let t1 = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let t2 = S.from_array a2 16sz;
  let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let t3 = S.from_array a3 16sz;
  let mut a4 = [| z; 16sz |]; A.pts_to_len a4; let t4 = S.from_array a4 16sz;
  let mut a5 = [| z; 16sz |]; A.pts_to_len a5; let t5 = S.from_array a5 16sz;
  let mut aw = [| z; 16sz |]; A.pts_to_len aw; let w = S.from_array aw 16sz;
  let mut au = [| z; 16sz |]; A.pts_to_len au; let u = S.from_array au 16sz;
  S.pts_to_len t0; S.pts_to_len t1; S.pts_to_len t2; S.pts_to_len t3;
  S.pts_to_len t4; S.pts_to_len t5; S.pts_to_len w; S.pts_to_len u;
  let bc = fb ();
  fmul t0 x1 x2;
  fmul t1 y1 y2;
  fmul t2 z1 z2;
  fadd t3 x1 y1;
  fadd t4 x2 y2;
  fmul w t3 t4;
  fcopy t3 w;
  fadd t4 t0 t1;
  fsub w t3 t4;
  fcopy t3 w;
  fadd t4 y1 z1;
  fadd t5 y2 z2;
  fmul w t4 t5;
  fcopy t4 w;
  fadd t5 t1 t2;
  fsub w t4 t5;
  fcopy t4 w;
  fadd ox x1 z1;
  fadd oy x2 z2;
  fmul w ox oy;
  fcopy ox w;
  fadd oy t0 t2;
  fsub w ox oy;
  fcopy oy w;
  fmul oz bc t2;
  fsub ox oy oz;
  fcopy u ox;
  fadd oz ox u;
  fadd w ox oz;
  fcopy ox w;
  fsub oz t1 ox;
  fadd w t1 ox;
  fcopy ox w;
  fmul w bc oy;
  fcopy oy w;
  fcopy u t2;
  fadd t1 t2 u;
  fadd w t1 t2;
  fcopy t2 w;
  fsub w oy t2;
  fcopy oy w;
  fsub w oy t0;
  fcopy oy w;
  fcopy u oy;
  fadd t1 oy u;
  fadd w t1 oy;
  fcopy oy w;
  fcopy u t0;
  fadd t1 t0 u;
  fadd w t1 t0;
  fcopy t0 w;
  fsub w t0 t2;
  fcopy t0 w;
  fmul t1 t4 oy;
  fmul t2 t0 oy;
  fmul oy ox oz;
  fadd w oy t2;
  fcopy oy w;
  fmul w t3 ox;
  fcopy ox w;
  fsub w ox t1;
  fcopy ox w;
  fmul w t4 oz;
  fcopy oz w;
  fmul t1 t3 t0;
  fadd w oz t1;
  fcopy oz w;
  drop_table bc;
  S.to_array t0; S.to_array t1; S.to_array t2; S.to_array t3;
  S.to_array t4; S.to_array t5; S.to_array w; S.to_array u;
}

(** {2 Doubling} *)

fn point_double (ox oy oz: S.slice S64.t) (x y z: S.slice S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
                (#p1: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz **
  S.pts_to x #p1 vx ** S.pts_to y #p1 vy ** S.pts_to z #p1 vz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        pt_ok vx vy vz)
ensures exists* (wx wy wz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz **
  S.pts_to x #p1 vx ** S.pts_to y #p1 vy ** S.pts_to z #p1 vz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_double (pt vx vy vz))
{
  reveal_opaque (`%P.point_double) P.point_double;
  S.pts_to_len ox; S.pts_to_len oy; S.pts_to_len oz;
  let zz = S64.zero;
  let mut a0 = [| zz; 16sz |]; A.pts_to_len a0; let t0 = S.from_array a0 16sz;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let t1 = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let t2 = S.from_array a2 16sz;
  let mut a3 = [| zz; 16sz |]; A.pts_to_len a3; let t3 = S.from_array a3 16sz;
  let mut aw = [| zz; 16sz |]; A.pts_to_len aw; let w = S.from_array aw 16sz;
  let mut au = [| zz; 16sz |]; A.pts_to_len au; let u = S.from_array au 16sz;
  S.pts_to_len t0; S.pts_to_len t1; S.pts_to_len t2; S.pts_to_len t3;
  S.pts_to_len w; S.pts_to_len u;
  let bc = fb ();
  fcopy u x;
  fmul t0 x u;
  fcopy u y;
  fmul t1 y u;
  fcopy u z;
  fmul t2 z u;
  fmul t3 x y;
  fcopy u t3;
  fadd w t3 u;
  fcopy t3 w;
  fmul oz x z;
  fcopy u oz;
  fadd w oz u;
  fcopy oz w;
  fmul oy bc t2;
  fsub w oy oz;
  fcopy oy w;
  fcopy u oy;
  fadd ox oy u;
  fadd w ox oy;
  fcopy oy w;
  fsub ox t1 oy;
  fadd w t1 oy;
  fcopy oy w;
  fmul w ox oy;
  fcopy oy w;
  fmul w ox t3;
  fcopy ox w;
  fcopy u t2;
  fadd t3 t2 u;
  fadd w t2 t3;
  fcopy t2 w;
  fmul w bc oz;
  fcopy oz w;
  fsub w oz t2;
  fcopy oz w;
  fsub w oz t0;
  fcopy oz w;
  fcopy u oz;
  fadd t3 oz u;
  fadd w oz t3;
  fcopy oz w;
  fcopy u t0;
  fadd t3 t0 u;
  fadd w t3 t0;
  fcopy t0 w;
  fsub w t0 t2;
  fcopy t0 w;
  fmul w t0 oz;
  fcopy t0 w;
  fadd w oy t0;
  fcopy oy w;
  fmul t0 y z;
  fcopy u t0;
  fadd w t0 u;
  fcopy t0 w;
  fmul w t0 oz;
  fcopy oz w;
  fsub w ox oz;
  fcopy ox w;
  fmul oz t0 t1;
  fcopy u oz;
  fadd w oz u;
  fcopy oz w;
  fcopy u oz;
  fadd w oz u;
  fcopy oz w;
  drop_table bc;
  S.to_array t0; S.to_array t1; S.to_array t2; S.to_array t3;
  S.to_array w; S.to_array u;
}

#pop-options
