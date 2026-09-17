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

(** Points as bytes.

    A raw point is [x || y], thirty-two big-endian bytes each.  Decoding
    also validates: a coordinate at or above the prime is not a coordinate,
    and a pair that does not satisfy the curve equation is not a point.
    That second test also rules out [(0, 0)] -- the affine stand-in for
    infinity -- because [b] is not zero, so there is no separate infinity
    check to write.  Apart from the shape of the curve equation this is
    {!Hacl.P256.Encode} line for line. *)
module Hacl.K256.Encode

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.K256.Field
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.K256.Field
open Hacl.K256.Inverse
open Hacl.K256.Point

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module K = Spec.K256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The curve equation}

    [y^2 = x^3 + 7].  Three field operations and a comparison: with [a = 0]
    the linear term that P-256 has to spell out is simply absent. *)

(** The right-hand side, [x^3 + b].  [compressed_to_raw] needs the value
    and not just the test, so it is written once here. *)
let rhs_of (x: K.felem) : K.felem =
  K.fadd (K.fmul (K.fmul x x) x) K.b_coeff

fn curve_rhs (out: A.array S64.t) (x: A.array S64.t)
             (#vo: erased (Seq.seq S64.t))
             (#px: perm) (#vx: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to x #px vx **
  pure (Seq.length vo == nl /\ felem vx)
ensures exists* (wo: Seq.seq S64.t).
  A.pts_to out wo ** A.pts_to x #px vx **
  pure (felem wo /\ fev wo == rhs_of (fev vx))
{
  A.pts_to_len out;
  let z = S64.zero;
  let mut a0 = [| z; 8sz |]; A.pts_to_len a0; let mut a1 = [| z; 8sz |]; A.pts_to_len a1; A.pts_to_len a0; A.pts_to_len a1;

  fsqr a0 x;
  fmul a1 a0 x;
  let bs = fb ();
  fadd out a1 bs;
  drop_table bs;

  ()
}

fn is_on_curve (x y: A.array S64.t)
               (#px: perm) (#vx: erased (Seq.seq S64.t))
               (#py: perm) (#vy: erased (Seq.seq S64.t))
requires A.pts_to x #px vx ** A.pts_to y #py vy ** pure (felem vx /\ felem vy)
returns r: bool
ensures A.pts_to x #px vx ** A.pts_to y #py vy **
  pure (r == K.is_on_curve (fev vx) (fev vy))
{
  let z = S64.zero;
  let mut a0 = [| z; 8sz |]; A.pts_to_len a0; let mut a1 = [| z; 8sz |]; A.pts_to_len a1; A.pts_to_len a0; A.pts_to_len a1;

  curve_rhs a1 x;
  fsqr a0 y;
  let r = feq a0 a1;

  r
}

(** {2 Reading a point}

    The two halves are validated separately and the curve test is only
    reached when both are in range; a caller who ignores the result gets
    whatever the partial decoding left behind, which is why the
    postcondition says nothing about the coordinates when [r] is false. *)

(** A Pulse [ensures] is elaborated with no [requires] in scope, so the
    length of the input cannot be assumed there; a total wrapper carries
    it instead. *)
let lpt (vb: Seq.seq S8.t) : GTot (option K.proj_point) =
  if Seq.length vb = 64 then K.load_point vb else None

fn load_point (ox oy oz: A.array S64.t) (b: A.array S8.t)
              (#vox #voy #voz: erased (Seq.seq S64.t))
              (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to b #pb vb **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vb == 64)
returns r: bool
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to b #pb vb **
  pure (pt_ok wx wy wz /\ r == Some? (lpt vb) /\
        (r ==> pt wx wy wz == Some?.v (lpt vb)))
{
  A.pts_to_len b;
  let xs = Sub.sub b 0sz 32sz;
  with vxs. assert (A.pts_to xs #pb vxs);
  A.pts_to_len xs;
  let okx = fload ox xs;
  Sub.unsub b 0 32 xs;
  with vb1. assert (A.pts_to b #pb vb1);
  A.pts_to_len b;
  assert (pure (Seq.equal vb1 vb));

  let ys = Sub.sub b 32sz 64sz;
  with vys. assert (A.pts_to ys #pb vys);
  A.pts_to_len ys;
  let oky = fload oy ys;
  Sub.unsub b 32 64 ys;
  with vb2. assert (A.pts_to b #pb vb2);
  A.pts_to_len b;
  assert (pure (Seq.equal vb2 vb));

  fone oz;
  if (okx && oky) {
    let r = is_on_curve ox oy;
    r
  } else {
    false
  }
}

(** {2 Leaving projective coordinates}

    One inversion.  At infinity [finv 0] is zero and this returns [(0, 0)],
    exactly as the specification does; every caller either checks for
    infinity first or is one for which [(0, 0)] is a rejecting answer. *)

fn to_aff_point (ox oy: A.array S64.t) (x y z: A.array S64.t)
                (#vox #voy: erased (Seq.seq S64.t))
                (#pp: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy **
  A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ pt_ok vx vy vz)
ensures exists* (wx wy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy **
  A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (felem wx /\ felem wy /\ (fev wx, fev wy) == K.to_aff_point (pt vx vy vz))
{
  A.pts_to_len ox; A.pts_to_len oy;
  let z0 = S64.zero;
  let mut a0 = [| z0; 8sz |]; A.pts_to_len a0; A.pts_to_len a0;
  finv a0 z;
  fmul ox x a0;
  fmul oy y a0;
  ()
}

(** {2 Writing a point}

    Affine coordinates, thirty-two bytes each. *)

fn store_point (b: A.array S8.t) (x y z: A.array S64.t)
               (#vb: erased (Seq.seq S8.t))
               (#pp: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires
  A.pts_to b vb ** A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (Seq.length vb == 64 /\ pt_ok vx vy vz)
ensures exists* (wb: Seq.seq S8.t).
  A.pts_to b wb ** A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (wb == K.store_point (pt vx vy vz))
{
  A.pts_to_len b;
  let z0 = S64.zero;
  let mut a0 = [| z0; 8sz |]; A.pts_to_len a0; let mut a1 = [| z0; 8sz |]; A.pts_to_len a1; A.pts_to_len a0; A.pts_to_len a1;
  to_aff_point a0 a1 x y z;
  with wax. assert (A.pts_to a0 wax);
  with way. assert (A.pts_to a1 way);

  let xs = Sub.sub b 0sz 32sz;
  A.pts_to_len xs;
  fstore xs a0;
  with vxs. assert (A.pts_to xs vxs);
  Sub.unsub b 0 32 xs;
  with vb1. assert (A.pts_to b vb1);
  A.pts_to_len b;
  assert (pure (Seq.equal (Seq.slice vb1 0 32) vxs));

  let ys = Sub.sub b 32sz 64sz;
  A.pts_to_len ys;
  fstore ys a1;
  with vys. assert (A.pts_to ys vys);
  Sub.unsub b 32 64 ys;
  with wb. assert (A.pts_to b wb);
  A.pts_to_len b;
  assert (pure (Seq.equal wb (Seq.append vxs vys)));

  ()
}

#pop-options
