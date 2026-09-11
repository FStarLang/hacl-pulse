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
    check to write. *)
module Hacl.P256.Encode

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.P256.Field
open Hacl.P256.Inverse
open Hacl.P256.Point

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The curve equation}

    [y^2 = x^3 - 3x + b].  Six field operations and a comparison; the
    coefficient [-3] is the one place in this library where it has to be
    written down, the addition formulas having folded it away. *)

fn is_on_curve (x y: S.slice S64.t)
               (#px: perm) (#vx: erased (Seq.seq S64.t))
               (#py: perm) (#vy: erased (Seq.seq S64.t))
requires S.pts_to x #px vx ** S.pts_to y #py vy ** pure (felem vx /\ felem vy)
returns r: bool
ensures S.pts_to x #px vx ** S.pts_to y #py vy **
  pure (r == P.is_on_curve (fev vx) (fev vy))
{
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let t0 = S.from_array a0 16sz;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let t1 = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let t2 = S.from_array a2 16sz;
  S.pts_to_len t0; S.pts_to_len t1; S.pts_to_len t2;

  fsqr t0 x;
  fmul t1 t0 x;
  let th = fthree ();
  fmul t2 th x;
  drop_table th;
  fsub t0 t1 t2;
  let bs = fb ();
  fadd t1 t0 bs;
  drop_table bs;
  fsqr t0 y;
  let r = feq t0 t1;

  S.to_array t0; S.to_array t1; S.to_array t2;
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
let lpt (vb: Seq.seq S8.t) : GTot (option P.proj_point) =
  if Seq.length vb = 64 then P.load_point vb else None

fn load_point (ox oy oz: S.slice S64.t) (b: S.slice S8.t)
              (#vox #voy #voz: erased (Seq.seq S64.t))
              (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy ** S.pts_to oz voz ** S.pts_to b #pb vb **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vb == 64)
returns r: bool
ensures exists* (wx wy wz: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy ** S.pts_to oz wz ** S.pts_to b #pb vb **
  pure (pt_ok wx wy wz /\ r == Some? (lpt vb) /\
        (r ==> pt wx wy wz == Some?.v (lpt vb)))
{
  S.pts_to_len b;
  let xs = S.subslice b 0sz 32sz;
  with vxs. assert (S.pts_to xs #pb vxs);
  S.pts_to_len xs;
  let okx = fload ox xs;
  unfold S.subslice_rest;
  S.join xs _ _;
  S.join _ _ b;
  with vb1. assert (S.pts_to b #pb vb1);
  S.pts_to_len b;
  assert (pure (Seq.equal vb1 vb));

  let ys = S.subslice b 32sz 64sz;
  with vys. assert (S.pts_to ys #pb vys);
  S.pts_to_len ys;
  let oky = fload oy ys;
  unfold S.subslice_rest;
  S.join ys _ _;
  S.join _ _ b;
  with vb2. assert (S.pts_to b #pb vb2);
  S.pts_to_len b;
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

fn to_aff_point (ox oy: S.slice S64.t) (x y z: S.slice S64.t)
                (#vox #voy: erased (Seq.seq S64.t))
                (#pp: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires
  S.pts_to ox vox ** S.pts_to oy voy **
  S.pts_to x #pp vx ** S.pts_to y #pp vy ** S.pts_to z #pp vz **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ pt_ok vx vy vz)
ensures exists* (wx wy: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to oy wy **
  S.pts_to x #pp vx ** S.pts_to y #pp vy ** S.pts_to z #pp vz **
  pure (felem wx /\ felem wy /\ (fev wx, fev wy) == P.to_aff_point (pt vx vy vz))
{
  S.pts_to_len ox; S.pts_to_len oy;
  let z0 = S64.zero;
  let mut a0 = [| z0; 16sz |]; A.pts_to_len a0; let zi = S.from_array a0 16sz;
  S.pts_to_len zi;
  finv zi z;
  fmul ox x zi;
  fmul oy y zi;
  S.to_array zi;
}

(** {2 Writing a point}

    Affine coordinates, thirty-two bytes each. *)

fn store_point (b: S.slice S8.t) (x y z: S.slice S64.t)
               (#vb: erased (Seq.seq S8.t))
               (#pp: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires
  S.pts_to b vb ** S.pts_to x #pp vx ** S.pts_to y #pp vy ** S.pts_to z #pp vz **
  pure (Seq.length vb == 64 /\ pt_ok vx vy vz)
ensures exists* (wb: Seq.seq S8.t).
  S.pts_to b wb ** S.pts_to x #pp vx ** S.pts_to y #pp vy ** S.pts_to z #pp vz **
  pure (wb == P.store_point (pt vx vy vz))
{
  S.pts_to_len b;
  let z0 = S64.zero;
  let mut a0 = [| z0; 16sz |]; A.pts_to_len a0; let ax = S.from_array a0 16sz;
  let mut a1 = [| z0; 16sz |]; A.pts_to_len a1; let ay = S.from_array a1 16sz;
  S.pts_to_len ax; S.pts_to_len ay;
  to_aff_point ax ay x y z;
  with wax. assert (S.pts_to ax wax);
  with way. assert (S.pts_to ay way);

  let xs = S.subslice b 0sz 32sz;
  S.pts_to_len xs;
  fstore xs ax;
  with vxs. assert (S.pts_to xs vxs);
  unfold S.subslice_rest;
  S.join xs _ _;
  S.join _ _ b;
  with vb1. assert (S.pts_to b vb1);
  S.pts_to_len b;
  assert (pure (Seq.equal (Seq.slice vb1 0 32) vxs));

  let ys = S.subslice b 32sz 64sz;
  S.pts_to_len ys;
  fstore ys ay;
  with vys. assert (S.pts_to ys vys);
  unfold S.subslice_rest;
  S.join ys _ _;
  S.join _ _ b;
  with wb. assert (S.pts_to b wb);
  S.pts_to_len b;
  assert (pure (Seq.equal wb (Seq.append vxs vys)));

  S.to_array ax; S.to_array ay;
}

#pop-options
