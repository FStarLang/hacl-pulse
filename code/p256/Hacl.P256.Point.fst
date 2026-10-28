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
    steps call {!Hacl.P256.Field}'s [fadd1], [fmul2], ... instead (the digit
    names the operand the result replaces), and the steps whose two operands
    are the same element call [fdbl], [fdbl1] and [fsqr].  The listing below
    can therefore be compared with the paper line by line. *)
module Hacl.P256.Point

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.P256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module Mem = Hacl.Mem
module JS = Spec.P256.JacSv
module J = Spec.P256.Jac
module JK = Spec.P256.JacChecks

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
  let mut a0 = [| z; 4sz |];
  Mem.track a0; A.pts_to_len a0; let mut a1 = [| z; 4sz |];
  Mem.track a1; A.pts_to_len a1; let mut a2 = [| z; 4sz |];
  Mem.track a2; A.pts_to_len a2; let mut a3 = [| z; 4sz |];
  Mem.track a3; A.pts_to_len a3; let mut a4 = [| z; 4sz |];
  Mem.track a4; A.pts_to_len a4; let mut a5 = [| z; 4sz |];
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
  Mem.wipe a5 4sz;
  Mem.wipe a4 4sz;
  Mem.wipe a3 4sz;
  Mem.wipe a2 4sz;
  Mem.wipe a1 4sz;
  Mem.wipe a0 4sz;
  ()
}

(** Mixed addition, [(x2, y2)] affine: Algorithm 5, one multiplication and
    one temporary fewer than {!point_add}.  {!Spec.P256.JacChecks.j6}
    says it is {!point_add} with [Z2 = 1], so it is complete as well. *)
fn point_madd (ox oy oz: A.array S64.t)
              (x1 y1 z1: A.array S64.t) (x2 y2: A.array S64.t)
              (#vox #voy #voz: erased (Seq.seq S64.t))
              (#p1: perm) (#vx1 #vy1 #vz1: erased (Seq.seq S64.t))
              (#p2: perm) (#vx2 #vy2: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        pt_ok vx1 vy1 vz1 /\ felem vx2 /\ felem vy2)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 ** A.pts_to z1 #p1 vz1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
  pure (pt_ok wx wy wz /\
        pt wx wy wz == P.point_add (pt vx1 vy1 vz1) (fev vx2, fev vy2, P.fone))
{
  JK.j6 (fev vx1) (fev vy1) (fev vz1) (fev vx2) (fev vy2);
  reveal_opaque (`%JS.madd) JS.madd;
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  let z = S64.zero;
  let mut a0 = [| z; 4sz |];
  Mem.track a0; A.pts_to_len a0; let mut a1 = [| z; 4sz |];
  Mem.track a1; A.pts_to_len a1; let mut a2 = [| z; 4sz |];
  Mem.track a2; A.pts_to_len a2; let mut a3 = [| z; 4sz |];
  Mem.track a3; A.pts_to_len a3; let mut a4 = [| z; 4sz |];
  Mem.track a4; A.pts_to_len a4;
  A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4;
  let bc = fb ();
  fmul a0 x1 x2;
  fmul a1 y1 y2;
  fadd a3 x2 y2;
  fadd a4 x1 y1;
  fmul1 a3 a4;
  fadd a4 a0 a1;
  fsub1 a3 a4;
  fmul a4 y2 z1;
  fadd1 a4 y1;
  fmul oy x2 z1;
  fadd1 oy x1;
  fmul oz bc z1;
  fsub ox oy oz;
  fdbl oz ox;
  fadd1 ox oz;
  fsub oz a1 ox;
  fadd2 ox a1;
  fmul2 oy bc;
  fdbl a1 z1;
  fadd a2 a1 z1;
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
  Mem.wipe a4 4sz;
  Mem.wipe a3 4sz;
  Mem.wipe a2 4sz;
  Mem.wipe a1 4sz;
  Mem.wipe a0 4sz;
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
  let mut a0 = [| zz; 4sz |];
  Mem.track a0; A.pts_to_len a0; let mut a1 = [| zz; 4sz |];
  Mem.track a1; A.pts_to_len a1; let mut a2 = [| zz; 4sz |];
  Mem.track a2; A.pts_to_len a2; let mut a3 = [| zz; 4sz |];
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
  Mem.wipe a3 4sz;
  Mem.wipe a2 4sz;
  Mem.wipe a1 4sz;
  Mem.wipe a0 4sz;
  ()
}

#pop-options

(** {2 Jacobian coordinates}

    A run of doublings is cheaper in Jacobian coordinates
    ({!Spec.P256.JacSv}): eight multiplications to the complete formula's
    eleven.  These work in place and borrow their scratch from the caller,
    so a run of them allocates nothing; the specifications are written in
    the same order, which makes each proof a chain of equalities. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

fn jdouble (x y z t0 t1 t2: A.array S64.t)
           (#vx #vy #vz: erased (Seq.seq S64.t))
           (#v0 #v1 #v2: erased (Seq.seq S64.t))
requires
  A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz **
  A.pts_to t0 v0 ** A.pts_to t1 v1 ** A.pts_to t2 v2 **
  pure (Seq.length v0 == nl /\ Seq.length v1 == nl /\ Seq.length v2 == nl /\
        pt_ok vx vy vz)
ensures exists* (wx wy wz w0 w1 w2: Seq.seq S64.t).
  A.pts_to x wx ** A.pts_to y wy ** A.pts_to z wz **
  A.pts_to t0 w0 ** A.pts_to t1 w1 ** A.pts_to t2 w2 **
  pure (Seq.length w0 == nl /\ Seq.length w1 == nl /\ Seq.length w2 == nl /\
        pt_ok wx wy wz /\ pt wx wy wz == JS.jdouble (pt vx vy vz))
{
  reveal_opaque (`%JS.jdouble) JS.jdouble;
  fsqr t0 z;
  fsqr t1 y;
  fmul1 z y;
  fdbl1 z;
  fsub t2 x t0;
  fadd1 t0 x;
  fmul1 t0 t2;
  fdbl t2 t0;
  fadd1 t0 t2;
  fmul y x t1;
  fdbl1 y;
  fdbl1 y;
  fsqr1 t1;
  fdbl1 t1;
  fdbl1 t1;
  fdbl1 t1;
  fsqr x t0;
  fdbl t2 y;
  fsub1 x t2;
  fsub1 y x;
  fmul1 y t0;
  fsub1 y t1;
  A.pts_to_len t0; A.pts_to_len t1; A.pts_to_len t2;
  ()
}

let to_j_eq (x y z xs ys x' y': P.felem) (m: S64.t)
  : Lemma (requires (S64.v m == 0 \/ S64.v m == pow2 64 - 1) /\
                    (S64.v m == pow2 64 - 1 <==> z == P.fzero) /\
                    xs == P.fmul x z /\ ys == P.fmul y (P.fmul z z) /\
                    x' == (if S64.v m = 0 then xs else P.fone) /\
                    y' == (if S64.v m = 0 then ys else P.fone))
          (ensures (x', y', z) == J.to_j (x, y, z))
  = reveal_opaque (`%JS.tj) JS.tj

(** Homogeneous to Jacobian.  Infinity, [Z = 0], becomes {!Spec.P256.Jac.jinf}
    by a masked select, since whether the point is at infinity is secret. *)
fn to_j (x y z t0 t1: A.array S64.t)
        (#vx #vy #vz: erased (Seq.seq S64.t))
        (#v0 #v1: erased (Seq.seq S64.t))
requires
  A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz **
  A.pts_to t0 v0 ** A.pts_to t1 v1 **
  pure (Seq.length v0 == nl /\ Seq.length v1 == nl /\ pt_ok vx vy vz)
ensures exists* (wx wy w0 w1: Seq.seq S64.t).
  A.pts_to x wx ** A.pts_to y wy ** A.pts_to z vz **
  A.pts_to t0 w0 ** A.pts_to t1 w1 **
  pure (Seq.length w0 == nl /\ Seq.length w1 == nl /\
        pt_ok wx wy vz /\ pt wx wy vz == J.to_j (pt vx vy vz))
{
  fmul1 x z;
  with sx. assert (A.pts_to x sx);
  fsqr t0 z;
  fmul1 y t0;
  with sy. assert (A.pts_to y sy);
  let m = fzero_mask z;
  fone t1;
  fcsel x t1 m;
  fcsel y t1 m;
  with wx wy. assert (A.pts_to x wx ** A.pts_to y wy);
  to_j_eq (fev vx) (fev vy) (fev vz) (fev sx) (fev sy) (fev wx) (fev wy) m;
  A.pts_to_len t0; A.pts_to_len t1;
  ()
}

(** Jacobian to homogeneous. *)
fn to_h (x y z t0: A.array S64.t)
        (#vx #vy #vz: erased (Seq.seq S64.t))
        (#v0: erased (Seq.seq S64.t))
requires
  A.pts_to x vx ** A.pts_to y vy ** A.pts_to z vz ** A.pts_to t0 v0 **
  pure (Seq.length v0 == nl /\ pt_ok vx vy vz)
ensures exists* (wx wz w0: Seq.seq S64.t).
  A.pts_to x wx ** A.pts_to y vy ** A.pts_to z wz ** A.pts_to t0 w0 **
  pure (Seq.length w0 == nl /\ pt_ok wx vy wz /\
        pt wx vy wz == JS.to_h (pt vx vy vz))
{
  reveal_opaque (`%JS.to_h) JS.to_h;
  fmul1 x z;
  fsqr t0 z;
  fmul1 z t0;
  A.pts_to_len t0;
  ()
}

#pop-options
