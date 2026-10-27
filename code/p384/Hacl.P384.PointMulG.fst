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

(** Multiplying the generator, with six base points and signed digits.

    {!Hacl.P256.PointMulG} at 384 bits, with Booth recoding.  The scalar
    splits into six sixty-four-bit pieces,

    {[ k = k0 + k1 2^64 + ... + k5 2^320 ]}

    so [k G] is [k0 G + k1 (2^64 G) + ... + k5 (2^320 G)], and each piece
    is written in thirteen signed five-bit digits between -16 and 16
    ({!Spec.Group.Booth6}).  The six pieces are walked together: thirteen
    rungs of five doublings and six signed additions, sixty-five doublings
    and seventy-eight additions.  A signed digit needs only the sixteen
    multiples [1 .. 16] of each base point: its magnitude selects one, its
    sign negates [y], and a zero digit adds and keeps the old value.

    The six tables are compiled in, affine:
    {!Spec.P384.Win0} .. {!Spec.P384.Win5} say what the points are,
    {!Hacl.P384.Win0} .. {!Hacl.P384.Win5} hold their Montgomery limbs,
    and {!Hacl.P384.WinTable} is the bridge.  The signed addition is
    {!Hacl.P384.PointBooth.win_sadd}. *)
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
open Hacl.P384.PointBooth

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module GR = Spec.P384.Group
module B = Spec.Group.Booth6
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

(** The accumulator starts at nothing, which is [h k 13]. *)
let h_start (x y z: Seq.seq S64.t) (k: nat)
  : Lemma (requires W.oc P.g /\ pt x y z == P.point_at_infinity)
          (ensures W.rep x y z (B.h k 13) P.g)
  = W.zero_ok x y z P.g;
    B.h_top k

(** And ends at the scalar itself. *)
let h_end (x y z: Seq.seq S64.t) (k: nat)
  : Lemma (requires W.oc P.g /\ W.rep x y z (B.h k 0) P.g /\ k < pow2 384)
          (ensures GR.on_curve (pt x y z) /\ GR.on_curve (P.point_mul_g k) /\
                   GR.peq (pt x y z) (P.point_mul_g k))
  = B.h_bot k;
    W.rep_cong x y z (B.h k 0) k P.g;
    W.win_done x y z P.g k

(** Limb [j] of the scalar is its [j]-th piece. *)
let limb_piece (vk: Seq.seq S64.t) (j: nat)
  : Lemma (requires j < Seq.length vk)
          (ensures S64.v (Seq.index vk j) == B.piece (num vk) j)
  = num_digit vk j

(** What one signed addition is told about its digit. *)
let digit_ok (k: nat) (i: nat) (j: nat { j < 6 }) (w mg sm: nat)
  : Lemma (requires w == B.win (B.piece k j) i /\
                    mg == (if w / 32 = 0 then (w + 1) / 2 else 32 - (w + 1) / 2) /\
                    (sm == 0 <==> w / 32 == 0))
          (ensures mg <= 16 /\
                   (sm == 0 ==> B.rv k i (j + 1) == B.rv k i j + mg * pow2 (64 * j)) /\
                   (sm <> 0 ==> B.rv k i j == B.rv k i (j + 1) + mg * pow2 (64 * j)))
  = B.rv_step k i j

let u32_zero (x: U32.t) : Lemma (requires U32.gt x 0ul == false)
                                (ensures U32.v x == 0) = ()

let n0 (_: unit) : Lemma (pow2 (64 * 0) == 1) = assert_norm (pow2 0 == 1)

#pop-options

(** {2 One piece's digit} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn piece_add (ox oy oz ux uy uz sx sy: A.array S64.t)
             (tx ty: A.array S64.t) (ks: A.array S64.t)
             (i: U32.t { U32.v i <= 12 }) (j: SZ.t { SZ.v j < 6 })
             (#vox #voy #voz: erased (Seq.seq S64.t))
             (#vux #vuy #vuz: erased (Seq.seq S64.t))
             (#vsx #vsy: erased (Seq.seq S64.t))
             (#ptx #pty: perm) (#vtx #vty: erased (Seq.seq S64.t))
             (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty **
  A.pts_to ks #pk vk **
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\
        Seq.length vtx == 96 /\ Seq.length vty == 96 /\
        Seq.length vk == 6 /\
        W.oc P.g /\ W.pok vox voy voz /\
        W.rep vox voy voz (B.rv (W.kv vk) (U32.v i) (SZ.v j)) P.g /\
        atok vtx vty P.g (pow2 (64 * SZ.v j)))
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty **
  A.pts_to ks #pk vk **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
        Seq.length wsx == 6 /\ Seq.length wsy == 6 /\
        W.pok wx wy wz /\
        W.rep wx wy wz (B.rv (W.kv vk) (U32.v i) (SZ.v j + 1)) P.g)
{
  A.pts_to_len ks;
  let l = ks.(j);
  limb_piece vk (SZ.v j);
  let w = bwin l i;
  let sm = bsgn w;
  let mg = bmag w;
  digit_ok (W.kv vk) (U32.v i) (SZ.v j) (S64.v w) (S64.v mg) (S64.v sm);
  win_sadd ox oy oz ux uy uz sx sy tx ty mg sm
           (hide P.g) (hide (pow2 (64 * SZ.v j)))
           (hide (B.rv (W.kv vk) (U32.v i) (SZ.v j)))
           (hide (B.rv (W.kv vk) (U32.v i) (SZ.v j + 1)));
  ()
}

#pop-options

(** {2 One rung} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn rung (ox oy oz ux uy uz sx sy: A.array S64.t)
        (t0x t0y t1x t1y t2x t2y t3x t3y t4x t4y t5x t5y: A.array S64.t)
        (ks: A.array S64.t) (i: U32.t { U32.v i <= 12 })
        (#vox #voy #voz: erased (Seq.seq S64.t))
        (#vux #vuy #vuz: erased (Seq.seq S64.t))
        (#vsx #vsy: erased (Seq.seq S64.t))
        (#v0x #v0y #v1x #v1y #v2x #v2y: erased (Seq.seq S64.t))
        (#v3x #v3y #v4x #v4y #v5x #v5y: erased (Seq.seq S64.t))
        (#p0x #p0y #p1x #p1y #p2x #p2y #p3x #p3y #p4x #p4y #p5x #p5y: perm)
        (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy **
  A.pts_to t0x #p0x v0x ** A.pts_to t0y #p0y v0y **
  A.pts_to t1x #p1x v1x ** A.pts_to t1y #p1y v1y **
  A.pts_to t2x #p2x v2x ** A.pts_to t2y #p2y v2y **
  A.pts_to t3x #p3x v3x ** A.pts_to t3y #p3y v3y **
  A.pts_to t4x #p4x v4x ** A.pts_to t4y #p4y v4y **
  A.pts_to t5x #p5x v5x ** A.pts_to t5y #p5y v5y **
  A.pts_to ks #pk vk **
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\
        Seq.length v0x == 96 /\ Seq.length v0y == 96 /\
        Seq.length v1x == 96 /\ Seq.length v1y == 96 /\
        Seq.length v2x == 96 /\ Seq.length v2y == 96 /\
        Seq.length v3x == 96 /\ Seq.length v3y == 96 /\
        Seq.length v4x == 96 /\ Seq.length v4y == 96 /\
        Seq.length v5x == 96 /\ Seq.length v5y == 96 /\
        Seq.length vk == 6 /\
        W.oc P.g /\ W.pok vox voy voz /\
        W.rep vox voy voz (B.h (W.kv vk) (U32.v i + 1)) P.g /\
        atok v0x v0y P.g (pow2 (64 * 0)) /\
        atok v1x v1y P.g (pow2 (64 * 1)) /\
        atok v2x v2y P.g (pow2 (64 * 2)) /\
        atok v3x v3y P.g (pow2 (64 * 3)) /\
        atok v4x v4y P.g (pow2 (64 * 4)) /\
        atok v5x v5y P.g (pow2 (64 * 5)))
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to t0x #p0x v0x ** A.pts_to t0y #p0y v0y **
  A.pts_to t1x #p1x v1x ** A.pts_to t1y #p1y v1y **
  A.pts_to t2x #p2x v2x ** A.pts_to t2y #p2y v2y **
  A.pts_to t3x #p3x v3x ** A.pts_to t3y #p3y v3y **
  A.pts_to t4x #p4x v4x ** A.pts_to t4y #p4y v4y **
  A.pts_to t5x #p5x v5x ** A.pts_to t5y #p5y v5y **
  A.pts_to ks #pk vk **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
        Seq.length wsx == 6 /\ Seq.length wsy == 6 /\
        W.pok wx wy wz /\ W.rep wx wy wz (B.h (W.kv vk) (U32.v i)) P.g)
{
  win_dbl5 ox oy oz ux uy uz (hide P.g) (hide (B.h (W.kv vk) (U32.v i + 1)));
  with ax ay az. assert (A.pts_to ox ax ** A.pts_to oy ay ** A.pts_to oz az);
  B.rv_start (W.kv vk) (U32.v i);
  W.rep_cong ax ay az (32 * B.h (W.kv vk) (U32.v i + 1))
             (B.rv (W.kv vk) (U32.v i) 0) P.g;
  piece_add ox oy oz ux uy uz sx sy t0x t0y ks i 0sz;
  piece_add ox oy oz ux uy uz sx sy t1x t1y ks i 1sz;
  piece_add ox oy oz ux uy uz sx sy t2x t2y ks i 2sz;
  piece_add ox oy oz ux uy uz sx sy t3x t3y ks i 3sz;
  piece_add ox oy oz ux uy uz sx sy t4x t4y ks i 4sz;
  piece_add ox oy oz ux uy uz sx sy t5x t5y ks i 5sz;
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  B.rv_end (W.kv vk) (U32.v i);
  W.rep_cong wx wy wz (B.rv (W.kv vk) (U32.v i) 6) (B.h (W.kv vk) (U32.v i)) P.g;
  ()
}

#pop-options

(** {2 The loop}

    Thirteen rungs.  The accumulator starts at the point at infinity,
    which is [h k 13], and after the rung at [i] it is [h k i]; the last
    is [h k 0], which is the scalar. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn win_loop (ox oy oz ux uy uz sx sy: A.array S64.t)
            (t0x t0y t1x t1y t2x t2y t3x t3y t4x t4y t5x t5y: A.array S64.t)
            (ks: A.array S64.t)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
            (#vsx #vsy: erased (Seq.seq S64.t))
            (#c0x #c0y #c1x #c1y #c2x #c2y: erased (Seq.seq S64.t))
            (#c3x #c3y #c4x #c4y #c5x #c5y: erased (Seq.seq S64.t))
            (#p0x #p0y #p1x #p1y #p2x #p2y #p3x #p3y #p4x #p4y #p5x #p5y: perm)
            (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy **
  A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y **
  A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y **
  A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y **
  A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y **
  A.pts_to t4x #p4x c4x ** A.pts_to t4y #p4y c4y **
  A.pts_to t5x #p5x c5x ** A.pts_to t5y #p5y c5y **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6 /\
        Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\
        Seq.length c0x == 96 /\ Seq.length c0y == 96 /\
        Seq.length c1x == 96 /\ Seq.length c1y == 96 /\
        Seq.length c2x == 96 /\ Seq.length c2y == 96 /\
        Seq.length c3x == 96 /\ Seq.length c3y == 96 /\
        Seq.length c4x == 96 /\ Seq.length c4y == 96 /\
        Seq.length c5x == 96 /\ Seq.length c5y == 96 /\
        atok c0x c0y P.g (pow2 (64 * 0)) /\
        atok c1x c1y P.g (pow2 (64 * 1)) /\
        atok c2x c2y P.g (pow2 (64 * 2)) /\
        atok c3x c3y P.g (pow2 (64 * 3)) /\
        atok c4x c4y P.g (pow2 (64 * 4)) /\
        atok c5x c5y P.g (pow2 (64 * 5)) /\
        Seq.length vk == 6)
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y **
  A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y **
  A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y **
  A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y **
  A.pts_to t4x #p4x c4x ** A.pts_to t4y #p4y c4y **
  A.pts_to t5x #p5x c5x ** A.pts_to t5y #p5y c5y **
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
  h_start o0x o0y o0z (W.kv vk);

  let mut i = 13ul;
  while (let vi = !i; U32.gt vi 0ul)
  invariant exists* (vi: U32.t)
                    (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
    A.pts_to sx wsx ** A.pts_to sy wsy **
    A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y **
    A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y **
    A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y **
    A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y **
    A.pts_to t4x #p4x c4x ** A.pts_to t4y #p4y c4y **
    A.pts_to t5x #p5x c5x ** A.pts_to t5y #p5y c5y **
    A.pts_to ks #pk vk **
    pure (U32.v vi <= 13 /\
          Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
          Seq.length wsx == 6 /\ Seq.length wsy == 6 /\
          W.pok wx wy wz /\
          W.rep wx wy wz (B.h (W.kv vk) (U32.v vi)) P.g)
  decreases (U32.v (!i))
  {
    let vi = !i;
    let i2 = U32.sub vi 1ul;
    rung ox oy oz ux uy uz sx sy
         t0x t0y t1x t1y t2x t2y t3x t3y t4x t4y t5x t5y ks i2;
    i := i2;
  };
  let vi = !i;
  u32_zero vi;
  with wx wy wz.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  W.pok_elim wx wy wz;
  h_end wx wy wz (W.kv vk);
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

  T0.tbl_ok (); T1.tbl_ok (); T2.tbl_ok (); T3.tbl_ok (); T4.tbl_ok (); T5.tbl_ok ();
  n0 ();

  let t0x = Tbl.table T0.tx_arr 96sz;
  let t0y = Tbl.table T0.ty_arr 96sz;
  let t1x = Tbl.table T1.tx_arr 96sz;
  let t1y = Tbl.table T1.ty_arr 96sz;
  let t2x = Tbl.table T2.tx_arr 96sz;
  let t2y = Tbl.table T2.ty_arr 96sz;
  let t3x = Tbl.table T3.tx_arr 96sz;
  let t3y = Tbl.table T3.ty_arr 96sz;
  let t4x = Tbl.table T4.tx_arr 96sz;
  let t4y = Tbl.table T4.ty_arr 96sz;
  let t5x = Tbl.table T5.tx_arr 96sz;
  let t5y = Tbl.table T5.ty_arr 96sz;

  win_loop ox oy oz ux uy uz sx sy
           t0x t0y t1x t1y t2x t2y t3x t3y t4x t4y t5x t5y ks;

  Tbl.drop_table t0x; Tbl.drop_table t0y;
  Tbl.drop_table t1x; Tbl.drop_table t1y;
  Tbl.drop_table t2x; Tbl.drop_table t2y;
  Tbl.drop_table t3x; Tbl.drop_table t3y;
  Tbl.drop_table t4x; Tbl.drop_table t4y;
  Tbl.drop_table t5x; Tbl.drop_table t5y;
  Mem.wipe sy 6sz;
  Mem.wipe sx 6sz;
  Mem.wipe uz 6sz;
  Mem.wipe uy 6sz;
  Mem.wipe ux 6sz;
  ()
}

#pop-options
