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

    The specification writes the formulas in place, reusing names.  A slice
    that is written needs full permission and one that is read needs a
    fraction, so the same slice cannot be passed as both; the in-place
    steps call {!Hacl.P384.Field}'s [fadd1], [fmul2], ... instead (the digit
    names the operand the result replaces), and the steps whose two operands
    are the same element call [fdbl], [fdbl1] and [fsqr].  The listing below
    can therefore be compared with the paper line by line. *)
module Hacl.P384.Point

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.P384.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** {2 Points as three limb sequences} *)

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
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6 /\
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
  let mut a0 = [| z; 6sz |];
  Mem.track a0; A.pts_to_len a0; let mut a1 = [| z; 6sz |];
  Mem.track a1; A.pts_to_len a1; let mut a2 = [| z; 6sz |];
  Mem.track a2; A.pts_to_len a2; let mut a3 = [| z; 6sz |];
  Mem.track a3; A.pts_to_len a3; let mut a4 = [| z; 6sz |];
  Mem.track a4; A.pts_to_len a4; let mut a5 = [| z; 6sz |];
  Mem.track a5; A.pts_to_len a5;
  A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len a5;
  let bc = fb ();
  fmul a0 x1 x2;
  fmul a1 y1 y2;
  fmul a2 z1 z2;
  fadd a3 x1 y1;
  fadd a4 x2 y2;
  fmul1 a3 a4;
  fadd a4 a0 a1;
  fsub1 a3 a4;
  fadd a4 y1 z1;
  fadd a5 y2 z2;
  fmul1 a4 a5;
  fadd a5 a1 a2;
  fsub1 a4 a5;
  fadd ox x1 z1;
  fadd oy x2 z2;
  fmul1 ox oy;
  fadd oy a0 a2;
  fsub2 oy ox;
  fmul oz bc a2;
  fsub ox oy oz;
  fdbl oz ox;
  fadd1 ox oz;
  fsub oz a1 ox;
  fadd2 ox a1;
  fmul2 oy bc;
  fdbl a1 a2;
  fadd2 a2 a1;
  fsub1 oy a2;
  fsub1 oy a0;
  fdbl a1 oy;
  fadd2 oy a1;
  fdbl a1 a0;
  fadd2 a0 a1;
  fsub1 a0 a2;
  fmul a1 a4 oy;
  fmul a2 a0 oy;
  fmul oy ox oz;
  fadd1 oy a2;
  fmul2 ox a3;
  fsub1 ox a1;
  fmul2 oz a4;
  fmul a1 a3 a0;
  fadd1 oz a1;
  drop_table bc;
  Mem.wipe a5 6sz;
  Mem.wipe a4 6sz;
  Mem.wipe a3 6sz;
  Mem.wipe a2 6sz;
  Mem.wipe a1 6sz;
  Mem.wipe a0 6sz;
  ()
}

(** {2 Doubling} *)

fn point_double (ox oy oz: A.array S64.t) (x y z: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
                (#p1: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to x #p1 vx ** A.pts_to y #p1 vy ** A.pts_to z #p1 vz **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6 /\
        pt_ok vx vy vz)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to x #p1 vx ** A.pts_to y #p1 vy ** A.pts_to z #p1 vz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_double (pt vx vy vz))
{
  reveal_opaque (`%P.point_double) P.point_double;
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  let zz = S64.zero;
  let mut a0 = [| zz; 6sz |];
  Mem.track a0; A.pts_to_len a0; let mut a1 = [| zz; 6sz |];
  Mem.track a1; A.pts_to_len a1; let mut a2 = [| zz; 6sz |];
  Mem.track a2; A.pts_to_len a2; let mut a3 = [| zz; 6sz |];
  Mem.track a3; A.pts_to_len a3;
  A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
 
  let bc = fb ();
  fsqr a0 x;
  fsqr a1 y;
  fsqr a2 z;
  fmul a3 x y;
  fdbl1 a3;
  fmul oz x z;
  fdbl1 oz;
  fmul oy bc a2;
  fsub1 oy oz;
  fdbl ox oy;
  fadd2 oy ox;
  fsub ox a1 oy;
  fadd2 oy a1;
  fmul2 oy ox;
  fmul1 ox a3;
  fdbl a3 a2;
  fadd1 a2 a3;
  fmul2 oz bc;
  fsub1 oz a2;
  fsub1 oz a0;
  fdbl a3 oz;
  fadd1 oz a3;
  fdbl a3 a0;
  fadd2 a0 a3;
  fsub1 a0 a2;
  fmul1 a0 oz;
  fadd1 oy a0;
  fmul a0 y z;
  fdbl1 a0;
  fmul2 oz a0;
  fsub1 ox oz;
  fmul oz a0 a1;
  fdbl1 oz;
  fdbl1 oz;
  drop_table bc;
  Mem.wipe a3 6sz;
  Mem.wipe a2 6sz;
  Mem.wipe a1 6sz;
  Mem.wipe a0 6sz;
  ()
}

#pop-options
