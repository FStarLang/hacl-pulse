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

(** Multiplying the generator, with six base points.

    {!Hacl.P256.PointMulG} at 384 bits.  The scalar splits into six
    sixty-four-bit pieces,

    {[ k = k0 + k1 2^64 + ... + k5 2^320 ]}

    so [k G] is [k0 G + k1 (2^64 G) + ... + k5 (2^320 G)], and the six
    pieces are walked together: sixteen rungs of four doublings and six
    additions, sixty doublings and ninety-six additions where the
    variable-base window in {!Hacl.P384.PointWin} pays three hundred and
    eighty-four doublings, ninety-six additions and a fifteen-addition
    table build.

    The six tables of sixteen multiples are compiled in:
    {!Spec.P384.Win0} .. {!Spec.P384.Win5} say what the ninety-six points
    are, {!Hacl.P384.Win0} .. {!Hacl.P384.Win5} hold their Montgomery
    limbs, and {!Hacl.P384.WinTable} is the bridge.  The scalar arithmetic
    is {!Spec.Group.Split6}. *)
module Hacl.P384.PointMulG

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.P384.Field
open Hacl.P384.Point
open Hacl.P384.PointWin

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module GR = Spec.P384.Group
module Split = Spec.Group.Split6
module W = Hacl.P384.PointWin
module Tbl = Hacl.Impl.Table
module T0 = Hacl.P384.Win0
module T1 = Hacl.P384.Win1
module T2 = Hacl.P384.Win2
module T3 = Hacl.P384.Win3
module T4 = Hacl.P384.Win4
module T5 = Hacl.P384.Win5
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The spec side} *)

(** The accumulator starts at nothing, which is [hi k 16]. *)
let hi_start (x y z: Seq.seq S64.t) (k: nat)
  : Lemma (requires W.oc P.g /\ pt x y z == P.point_at_infinity)
          (ensures W.rep x y z (Split.hi k 16) P.g)
  = W.zero_ok x y z P.g;
    Split.hi_top k

(** And ends at the scalar itself. *)
let hi_end (x y z: Seq.seq S64.t) (k: nat)
  : Lemma (requires W.oc P.g /\ W.rep x y z (Split.hi k 0) P.g /\ k < pow2 384)
          (ensures GR.on_curve (pt x y z) /\ GR.on_curve (P.point_mul_g k) /\
                   GR.peq (pt x y z) (P.point_mul_g k))
  = Split.hi_bot k;
    W.rep_cong x y z (Split.hi k 0) k P.g;
    W.win_done x y z P.g k

(** One rung's arithmetic: four doublings and six scaled digits make the
    next value of [hi]. *)
let rung_step (x y z: Seq.seq S64.t) (k: nat) (i: nat { i < 16 })
  : Lemma (requires
             W.rep x y z
               (16 * Split.hi k (i + 1) +
                Split.dig k 0 i * 1 +
                Split.dig k 1 i * (pow2 64) +
                Split.dig k 2 i * (pow2 128) +
                Split.dig k 3 i * (pow2 192) +
                Split.dig k 4 i * (pow2 256) +
                Split.dig k 5 i * (pow2 320)) P.g)
          (ensures W.rep x y z (Split.hi k i) P.g)
  = Split.hi_step k i;
    W.mul_one (Split.dig k 0 i)

(** The window index and the six bit positions it names: each is a legal
    argument to [get_digit] on six limbs, and fits in a [size_t]. *)
let shift_ok (i: nat { i < 16 })
  : Lemma (i * 4 >= 0 /\
           i * 4 + 0 < pow2 32 /\ (i * 4 + 0) / 64 < 6 /\ (i * 4 + 0) % 4 == 0 /\
           i * 4 + 64 < pow2 32 /\ (i * 4 + 64) / 64 < 6 /\ (i * 4 + 64) % 4 == 0 /\
           i * 4 + 128 < pow2 32 /\ (i * 4 + 128) / 64 < 6 /\ (i * 4 + 128) % 4 == 0 /\
           i * 4 + 192 < pow2 32 /\ (i * 4 + 192) / 64 < 6 /\ (i * 4 + 192) % 4 == 0 /\
           i * 4 + 256 < pow2 32 /\ (i * 4 + 256) / 64 < 6 /\ (i * 4 + 256) % 4 == 0 /\
           i * 4 + 320 < pow2 32 /\ (i * 4 + 320) / 64 < 6 /\ (i * 4 + 320) % 4 == 0 /\
           True)
  = assert_norm (pow2 32 > 384)

(** And that [get_digit]'s answer at that position is the digit the
    window wants. *)
let dig_at (k: nat) (i: nat { i < 16 }) (j: nat { j < 6 })
  : Lemma (Split.dig k j i == k / pow2 (i * 4 + 64 * j) % 16) = ()

#pop-options

(** {2 One rung} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

fn rung (ox oy oz ux uy uz sx sy sz: A.array S64.t)
        (t0x t0y t0z: A.array S64.t)
        (t1x t1y t1z: A.array S64.t)
        (t2x t2y t2z: A.array S64.t)
        (t3x t3y t3z: A.array S64.t)
        (t4x t4y t4z: A.array S64.t)
        (t5x t5y t5z: A.array S64.t)
        (d0 d1 d2 d3 d4 d5: S64.t)
        (k: erased nat) (i: erased (n: nat { n < 16 }))
        (#vox #voy #voz: erased (Seq.seq S64.t))
        (#vux #vuy #vuz: erased (Seq.seq S64.t))
        (#vsx #vsy #vsz: erased (Seq.seq S64.t))
        (#v0x #v0y #v0z: erased (Seq.seq S64.t))
        (#v1x #v1y #v1z: erased (Seq.seq S64.t))
        (#v2x #v2y #v2z: erased (Seq.seq S64.t))
        (#v3x #v3y #v3z: erased (Seq.seq S64.t))
        (#v4x #v4y #v4z: erased (Seq.seq S64.t))
        (#v5x #v5y #v5z: erased (Seq.seq S64.t))
        (#p0x #p0y #p0z #p1x #p1y #p1z #p2x #p2y #p2z: perm)
        (#p3x #p3y #p3z #p4x #p4y #p4z #p5x #p5y #p5z: perm)
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to t0x #p0x v0x ** A.pts_to t0y #p0y v0y ** A.pts_to t0z #p0z v0z **
  A.pts_to t1x #p1x v1x ** A.pts_to t1y #p1y v1y ** A.pts_to t1z #p1z v1z **
  A.pts_to t2x #p2x v2x ** A.pts_to t2y #p2y v2y ** A.pts_to t2z #p2z v2z **
  A.pts_to t3x #p3x v3x ** A.pts_to t3y #p3y v3y ** A.pts_to t3z #p3z v3z **
  A.pts_to t4x #p4x v4x ** A.pts_to t4y #p4y v4y ** A.pts_to t4z #p4z v4z **
  A.pts_to t5x #p5x v5x ** A.pts_to t5y #p5y v5y ** A.pts_to t5z #p5z v5z **
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\ Seq.length vsz == 6 /\
        Seq.length v0x == 96 /\ Seq.length v0y == 96 /\ Seq.length v0z == 96 /\
        Seq.length v1x == 96 /\ Seq.length v1y == 96 /\ Seq.length v1z == 96 /\
        Seq.length v2x == 96 /\ Seq.length v2y == 96 /\ Seq.length v2z == 96 /\
        Seq.length v3x == 96 /\ Seq.length v3y == 96 /\ Seq.length v3z == 96 /\
        Seq.length v4x == 96 /\ Seq.length v4y == 96 /\ Seq.length v4z == 96 /\
        Seq.length v5x == 96 /\ Seq.length v5y == 96 /\ Seq.length v5z == 96 /\
        W.oc P.g /\ W.pok vox voy voz /\
        W.rep vox voy voz (Split.hi k (reveal i + 1)) P.g /\
        W.tok v0x v0y v0z P.g (1) 16 /\
        W.tok v1x v1y v1z P.g (pow2 64) 16 /\
        W.tok v2x v2y v2z P.g (pow2 128) 16 /\
        W.tok v3x v3y v3z P.g (pow2 192) 16 /\
        W.tok v4x v4y v4z P.g (pow2 256) 16 /\
        W.tok v5x v5y v5z P.g (pow2 320) 16 /\
        S64.v d0 == Split.dig k 0 i /\
        S64.v d1 == Split.dig k 1 i /\
        S64.v d2 == Split.dig k 2 i /\
        S64.v d3 == Split.dig k 3 i /\
        S64.v d4 == Split.dig k 4 i /\
        S64.v d5 == Split.dig k 5 i /\
        True)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to t0x #p0x v0x ** A.pts_to t0y #p0y v0y ** A.pts_to t0z #p0z v0z **
  A.pts_to t1x #p1x v1x ** A.pts_to t1y #p1y v1y ** A.pts_to t1z #p1z v1z **
  A.pts_to t2x #p2x v2x ** A.pts_to t2y #p2y v2y ** A.pts_to t2z #p2z v2z **
  A.pts_to t3x #p3x v3x ** A.pts_to t3y #p3y v3y ** A.pts_to t3z #p3z v3z **
  A.pts_to t4x #p4x v4x ** A.pts_to t4y #p4y v4y ** A.pts_to t4z #p4z v4z **
  A.pts_to t5x #p5x v5x ** A.pts_to t5y #p5y v5y ** A.pts_to t5z #p5z v5z **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
        Seq.length wsx == 6 /\ Seq.length wsy == 6 /\ Seq.length wsz == 6 /\
        W.pok wx wy wz /\ W.rep wx wy wz (Split.hi k i) P.g)
{
  let e0 : erased nat = hide (16 * Split.hi k (reveal i + 1));
  W.win_dbl4 ox oy oz ux uy uz (hide P.g) (hide (Split.hi k (reveal i + 1)));
  W.mul_nat (Split.dig k 0 i) (1);
  W.win_add ox oy oz ux uy uz sx sy sz t0x t0y t0z d0
            (hide P.g) (hide (1)) e0 (hide (Split.dig k 0 i));
  let e1 : erased nat = hide (reveal e0 + Split.dig k 0 i * 1);
  W.mul_nat (Split.dig k 1 i) (pow2 64);
  W.win_add ox oy oz ux uy uz sx sy sz t1x t1y t1z d1
            (hide P.g) (hide (pow2 64)) e1 (hide (Split.dig k 1 i));
  let e2 : erased nat = hide (reveal e1 + Split.dig k 1 i * (pow2 64));
  W.mul_nat (Split.dig k 2 i) (pow2 128);
  W.win_add ox oy oz ux uy uz sx sy sz t2x t2y t2z d2
            (hide P.g) (hide (pow2 128)) e2 (hide (Split.dig k 2 i));
  let e3 : erased nat = hide (reveal e2 + Split.dig k 2 i * (pow2 128));
  W.mul_nat (Split.dig k 3 i) (pow2 192);
  W.win_add ox oy oz ux uy uz sx sy sz t3x t3y t3z d3
            (hide P.g) (hide (pow2 192)) e3 (hide (Split.dig k 3 i));
  let e4 : erased nat = hide (reveal e3 + Split.dig k 3 i * (pow2 192));
  W.mul_nat (Split.dig k 4 i) (pow2 256);
  W.win_add ox oy oz ux uy uz sx sy sz t4x t4y t4z d4
            (hide P.g) (hide (pow2 256)) e4 (hide (Split.dig k 4 i));
  let e5 : erased nat = hide (reveal e4 + Split.dig k 4 i * (pow2 256));
  W.mul_nat (Split.dig k 5 i) (pow2 320);
  W.win_add ox oy oz ux uy uz sx sy sz t5x t5y t5z d5
            (hide P.g) (hide (pow2 320)) e5 (hide (Split.dig k 5 i));
  let e6 : erased nat = hide (reveal e5 + Split.dig k 5 i * (pow2 320));
  with wx wy wz.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  rung_step wx wy wz k i;
  ()
}

#pop-options

(** {2 The loop}

    Sixteen rungs.  The accumulator starts at the point at infinity, which
    is [hi k 16], and after the rung at [i] it is [hi k i]; the last is
    [hi k 0], which is the scalar. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

let sz_fits (x: nat) : Lemma (requires x < pow2 32) (ensures SZ.fits x)
  = Hacl.SizeT.fits32 (); SZ.fits_u32_implies_fits x

fn win_loop (ox oy oz ux uy uz sx sy sz: A.array S64.t)
            (t0x t0y t0z: A.array S64.t)
            (t1x t1y t1z: A.array S64.t)
            (t2x t2y t2z: A.array S64.t)
            (t3x t3y t3z: A.array S64.t)
            (t4x t4y t4z: A.array S64.t)
            (t5x t5y t5z: A.array S64.t)
            (ks: A.array S64.t)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
            (#vsx #vsy #vsz: erased (Seq.seq S64.t))
            (#c0x #c0y #c0z: erased (Seq.seq S64.t))
            (#c1x #c1y #c1z: erased (Seq.seq S64.t))
            (#c2x #c2y #c2z: erased (Seq.seq S64.t))
            (#c3x #c3y #c3z: erased (Seq.seq S64.t))
            (#c4x #c4y #c4z: erased (Seq.seq S64.t))
            (#c5x #c5y #c5z: erased (Seq.seq S64.t))
            (#p0x #p0y #p0z #p1x #p1y #p1z #p2x #p2y #p2z: perm)
            (#p3x #p3y #p3z #p4x #p4y #p4z #p5x #p5y #p5z: perm)
            (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y ** A.pts_to t0z #p0z c0z **
  A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y ** A.pts_to t1z #p1z c1z **
  A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y ** A.pts_to t2z #p2z c2z **
  A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y ** A.pts_to t3z #p3z c3z **
  A.pts_to t4x #p4x c4x ** A.pts_to t4y #p4y c4y ** A.pts_to t4z #p4z c4z **
  A.pts_to t5x #p5x c5x ** A.pts_to t5y #p5y c5y ** A.pts_to t5z #p5z c5z **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6 /\
        Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\ Seq.length vsz == 6 /\
        Seq.length c0x == 96 /\ Seq.length c0y == 96 /\ Seq.length c0z == 96 /\
        Seq.length c1x == 96 /\ Seq.length c1y == 96 /\ Seq.length c1z == 96 /\
        Seq.length c2x == 96 /\ Seq.length c2y == 96 /\ Seq.length c2z == 96 /\
        Seq.length c3x == 96 /\ Seq.length c3y == 96 /\ Seq.length c3z == 96 /\
        Seq.length c4x == 96 /\ Seq.length c4y == 96 /\ Seq.length c4z == 96 /\
        Seq.length c5x == 96 /\ Seq.length c5y == 96 /\ Seq.length c5z == 96 /\
        W.tok c0x c0y c0z P.g (1) 16 /\
        W.tok c1x c1y c1z P.g (pow2 64) 16 /\
        W.tok c2x c2y c2z P.g (pow2 128) 16 /\
        W.tok c3x c3y c3z P.g (pow2 192) 16 /\
        W.tok c4x c4y c4z P.g (pow2 256) 16 /\
        W.tok c5x c5y c5z P.g (pow2 320) 16 /\
        Seq.length vk == 6)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y ** A.pts_to t0z #p0z c0z **
  A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y ** A.pts_to t1z #p1z c1z **
  A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y ** A.pts_to t2z #p2z c2z **
  A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y ** A.pts_to t3z #p3z c3z **
  A.pts_to t4x #p4x c4x ** A.pts_to t4y #p4y c4y ** A.pts_to t4z #p4z c4z **
  A.pts_to t5x #p5x c5x ** A.pts_to t5y #p5y c5y ** A.pts_to t5z #p5z c5z **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_g (W.kv vk)) /\
        GR.peq (pt wx wy wz) (P.point_mul_g (W.kv vk)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ks;
  W.kv_bnd vk;
  GR.g_on_curve ();
  W.oc_intro P.g;
  set_infinity ox oy oz;
  with o0x o0y o0z.
    assert (A.pts_to ox o0x ** A.pts_to oy o0y ** A.pts_to oz o0z);
  W.pok_intro o0x o0y o0z;
  hi_start o0x o0y o0z (W.kv vk);
  sz_fits 16; sz_fits 4;
  sz_fits 64;
  sz_fits 128;
  sz_fits 192;
  sz_fits 256;
  sz_fits 320;

  let mut i = 16sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
    A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y ** A.pts_to t0z #p0z c0z **
    A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y ** A.pts_to t1z #p1z c1z **
    A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y ** A.pts_to t2z #p2z c2z **
    A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y ** A.pts_to t3z #p3z c3z **
    A.pts_to t4x #p4x c4x ** A.pts_to t4y #p4y c4y ** A.pts_to t4z #p4z c4z **
    A.pts_to t5x #p5x c5x ** A.pts_to t5y #p5y c5y ** A.pts_to t5z #p5z c5z **
    A.pts_to ks #pk vk **
    pure (SZ.v vi <= 16 /\
          Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
          Seq.length wsx == 6 /\ Seq.length wsy == 6 /\ Seq.length wsz == 6 /\
          W.pok wx wy wz /\
          W.rep wx wy wz (Split.hi (W.kv vk) (SZ.v vi)) P.g)
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let i2 = SZ.sub vi 1sz;
    shift_ok (SZ.v i2);
    sz_fits (SZ.v i2 * 4);
    let sh = SZ.mul i2 4sz;
    sz_fits (SZ.v sh + 64);
    sz_fits (SZ.v sh + 128);
    sz_fits (SZ.v sh + 192);
    sz_fits (SZ.v sh + 256);
    sz_fits (SZ.v sh + 320);
    dig_at (W.kv vk) (SZ.v i2) 0;
    dig_at (W.kv vk) (SZ.v i2) 1;
    dig_at (W.kv vk) (SZ.v i2) 2;
    dig_at (W.kv vk) (SZ.v i2) 3;
    dig_at (W.kv vk) (SZ.v i2) 4;
    dig_at (W.kv vk) (SZ.v i2) 5;
    let d0 = get_digit ks sh;
    let d1 = get_digit ks (SZ.add sh 64sz);
    let d2 = get_digit ks (SZ.add sh 128sz);
    let d3 = get_digit ks (SZ.add sh 192sz);
    let d4 = get_digit ks (SZ.add sh 256sz);
    let d5 = get_digit ks (SZ.add sh 320sz);
    rung ox oy oz ux uy uz sx sy sz
         t0x t0y t0z
         t1x t1y t1z
         t2x t2y t2z
         t3x t3y t3z
         t4x t4y t4z
         t5x t5y t5z
         d0 d1 d2 d3 d4 d5 (hide (W.kv vk)) (hide (SZ.v i2));
    i := i2;
  };
  let vi = !i;
  W.sz_zero vi;
  with wx wy wz.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  W.pok_elim wx wy wz;
  hi_end wx wy wz (W.kv vk);
  ()
}

#pop-options

(** {2 The multiplication} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [point_mul_g_win o ks] is [o := [ks] G], up to [peq]. *)
fn point_mul_g_win (ox oy oz: A.array S64.t) (ks: A.array S64.t)
                   (#vox #voy #voz: erased (Seq.seq S64.t))
                   (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6 /\
        Seq.length vk == 6)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_g (num vk)) /\
        GR.peq (pt wx wy wz) (P.point_mul_g (num vk)))
{
  let z = S64.zero;
  let mut ux = [| z; 6sz |];
  Mem.track ux; A.pts_to_len ux;
  let mut uy = [| z; 6sz |];
  Mem.track uy; A.pts_to_len uy;
  let mut uz = [| z; 6sz |];
  Mem.track uz; A.pts_to_len uz;
  let mut sx = [| z; 6sz |];
  Mem.track sx; A.pts_to_len sx;
  let mut sy = [| z; 6sz |];
  Mem.track sy; A.pts_to_len sy;
  let mut sz = [| z; 6sz |];
  Mem.track sz; A.pts_to_len sz;

  T0.tbl_ok (); T1.tbl_ok (); T2.tbl_ok (); T3.tbl_ok (); T4.tbl_ok (); T5.tbl_ok ();

  let t0x = Tbl.table T0.tx_arr 96sz;
  let t0y = Tbl.table T0.ty_arr 96sz;
  let t0z = Tbl.table T0.tz_arr 96sz;
  let t1x = Tbl.table T1.tx_arr 96sz;
  let t1y = Tbl.table T1.ty_arr 96sz;
  let t1z = Tbl.table T1.tz_arr 96sz;
  let t2x = Tbl.table T2.tx_arr 96sz;
  let t2y = Tbl.table T2.ty_arr 96sz;
  let t2z = Tbl.table T2.tz_arr 96sz;
  let t3x = Tbl.table T3.tx_arr 96sz;
  let t3y = Tbl.table T3.ty_arr 96sz;
  let t3z = Tbl.table T3.tz_arr 96sz;
  let t4x = Tbl.table T4.tx_arr 96sz;
  let t4y = Tbl.table T4.ty_arr 96sz;
  let t4z = Tbl.table T4.tz_arr 96sz;
  let t5x = Tbl.table T5.tx_arr 96sz;
  let t5y = Tbl.table T5.ty_arr 96sz;
  let t5z = Tbl.table T5.tz_arr 96sz;

  win_loop ox oy oz ux uy uz sx sy sz
           t0x t0y t0z
           t1x t1y t1z
           t2x t2y t2z
           t3x t3y t3z
           t4x t4y t4z
           t5x t5y t5z
           ks;

  Tbl.drop_table t0x; Tbl.drop_table t0y; Tbl.drop_table t0z;
  Tbl.drop_table t1x; Tbl.drop_table t1y; Tbl.drop_table t1z;
  Tbl.drop_table t2x; Tbl.drop_table t2y; Tbl.drop_table t2z;
  Tbl.drop_table t3x; Tbl.drop_table t3y; Tbl.drop_table t3z;
  Tbl.drop_table t4x; Tbl.drop_table t4y; Tbl.drop_table t4z;
  Tbl.drop_table t5x; Tbl.drop_table t5y; Tbl.drop_table t5z;
  Mem.wipe sz 6sz;
  Mem.wipe sy 6sz;
  Mem.wipe sx 6sz;
  Mem.wipe uz 6sz;
  Mem.wipe uy 6sz;
  Mem.wipe ux 6sz;
  ()
}

#pop-options
