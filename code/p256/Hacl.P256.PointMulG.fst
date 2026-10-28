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

(** Multiplying the generator, with four base points and signed digits.

    Signing, key agreement and key generation all multiply a *known*
    point, and a known point can be preprocessed.  The scalar splits into
    four sixty-four-bit pieces,

    {[ k = k0 + k1 2^64 + k2 2^128 + k3 2^192 ]}

    so [k G] is [k0 G + k1 (2^64 G) + k2 (2^128 G) + k3 (2^192 G)], and
    each piece is written in thirteen signed five-bit digits between -16
    and 16 ({!Spec.Group.Booth4}).  The four pieces are walked together:
    thirteen rungs of five doublings and four signed additions,
    sixty-five doublings and fifty-two additions.  A signed digit needs
    only the sixteen multiples [1 .. 16] of each base point: its magnitude
    selects one, its sign negates [y], and a zero digit adds and keeps the
    old value.

    The four tables are compiled in, affine:
    {!Spec.P256.Win0} .. {!Spec.P256.Win3} say what the points are,
    {!Hacl.P256.Win0} .. {!Hacl.P256.Win3} hold their Montgomery limbs,
    and {!Hacl.P256.WinTable} is the bridge.  The signed addition is
    {!Hacl.P256.PointBooth.win_sadd}.  This is {!Hacl.P256.PointMulG} at
    four limbs. *)
module Hacl.P256.PointMulG

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.P256.Field
open Hacl.P256.Point
open Hacl.P256.PointStep
open Hacl.P256.PointWin
open Hacl.P256.PointBooth

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module GR = Spec.P256.Group
module B = Spec.Group.Booth4
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4
module Math = FStar.Math.Lemmas
module W = Hacl.P256.PointWin
module Tbl = Hacl.Impl.Table
module T0 = Hacl.P256.Win0
module T1 = Hacl.P256.Win1
module T2 = Hacl.P256.Win2
module T3 = Hacl.P256.Win3
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
  : Lemma (requires W.oc P.g /\ W.rep x y z (B.h k 0) P.g /\ k < pow2 256)
          (ensures GR.on_curve (pt x y z) /\ GR.on_curve (P.point_mul_g k) /\
                   GR.peq (pt x y z) (P.point_mul_g k))
  = B.h_bot k;
    W.rep_cong x y z (B.h k 0) k P.g;
    W.win_done x y z P.g k

(** Limb [j] of the scalar is its [j]-th piece. *)
let limb_piece (vk: Seq.seq S64.t) (j: nat)
  : Lemma (requires j < Seq.length vk)
          (ensures S64.v (Seq.index vk j) == B.piece (W.kv vk) j)
  = let s = L4.vals vk in
    let n = Seq.length s in
    let lo = B4.eval (Seq.slice s 0 j) in
    let hi = B4.eval (Seq.slice s (j + 1) n) in
    let x = Seq.index s j in
    B4.eval_at s j;
    L4.vals_bnd vk;
    assert (B4.bnd (Seq.slice s 0 j) B4.base);
    B4.eval_bnd (Seq.slice s 0 j);
    assert_norm (B4.base == pow2 64);
    Math.division_addition_lemma lo (pow2 (64 * j)) (x + B4.base * hi);
    Math.small_div lo (pow2 (64 * j));
    Math.lemma_mod_plus x hi B4.base;
    Math.small_mod x B4.base

(** What one signed addition is told about its digit. *)
let digit_ok (k: nat) (i: nat) (j: nat { j < 4 }) (w mg sm: nat)
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
             (i: U32.t { U32.v i <= 12 }) (j: SZ.t { SZ.v j < 4 })
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
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length vtx == 64 /\ Seq.length vty == 64 /\
        Seq.length vk == B4.nl /\
        W.oc P.g /\ W.pok vox voy voz /\
        W.rep vox voy voz (B.rv (W.kv vk) (U32.v i) (SZ.v j)) P.g /\
        atok vtx vty P.g (pow2 (64 * SZ.v j)))
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty **
  A.pts_to ks #pk vk **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\
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
        (t0x t0y t1x t1y t2x t2y t3x t3y: A.array S64.t)
        (ks: A.array S64.t) (i: U32.t { U32.v i <= 12 })
        (#vox #voy #voz: erased (Seq.seq S64.t))
        (#vux #vuy #vuz: erased (Seq.seq S64.t))
        (#vsx #vsy: erased (Seq.seq S64.t))
        (#v0x #v0y #v1x #v1y #v2x #v2y #v3x #v3y: erased (Seq.seq S64.t))
        (#p0x #p0y #p1x #p1y #p2x #p2y #p3x #p3y: perm)
        (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy **
  A.pts_to t0x #p0x v0x ** A.pts_to t0y #p0y v0y **
  A.pts_to t1x #p1x v1x ** A.pts_to t1y #p1y v1y **
  A.pts_to t2x #p2x v2x ** A.pts_to t2y #p2y v2y **
  A.pts_to t3x #p3x v3x ** A.pts_to t3y #p3y v3y **
  A.pts_to ks #pk vk **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length v0x == 64 /\ Seq.length v0y == 64 /\
        Seq.length v1x == 64 /\ Seq.length v1y == 64 /\
        Seq.length v2x == 64 /\ Seq.length v2y == 64 /\
        Seq.length v3x == 64 /\ Seq.length v3y == 64 /\
        Seq.length vk == B4.nl /\
        W.oc P.g /\ W.pok vox voy voz /\
        W.rep vox voy voz (B.h (W.kv vk) (U32.v i + 1)) P.g /\
        atok v0x v0y P.g (pow2 (64 * 0)) /\
        atok v1x v1y P.g (pow2 (64 * 1)) /\
        atok v2x v2y P.g (pow2 (64 * 2)) /\
        atok v3x v3y P.g (pow2 (64 * 3)))
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to t0x #p0x v0x ** A.pts_to t0y #p0y v0y **
  A.pts_to t1x #p1x v1x ** A.pts_to t1y #p1y v1y **
  A.pts_to t2x #p2x v2x ** A.pts_to t2y #p2y v2y **
  A.pts_to t3x #p3x v3x ** A.pts_to t3y #p3y v3y **
  A.pts_to ks #pk vk **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\
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
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  B.rv_end (W.kv vk) (U32.v i);
  W.rep_cong wx wy wz (B.rv (W.kv vk) (U32.v i) 4) (B.h (W.kv vk) (U32.v i)) P.g;
  ()
}

#pop-options

(** {2 The loop}

    Thirteen rungs.  The accumulator starts at the point at infinity,
    which is [h k 13], and after the rung at [i] it is [h k i]; the last
    is [h k 0], which is the scalar. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn win_loop (ox oy oz ux uy uz sx sy: A.array S64.t)
            (t0x t0y t1x t1y t2x t2y t3x t3y: A.array S64.t)
            (ks: A.array S64.t)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
            (#vsx #vsy: erased (Seq.seq S64.t))
            (#c0x #c0y #c1x #c1y #c2x #c2y: erased (Seq.seq S64.t))
            (#c3x #c3y: erased (Seq.seq S64.t))
            (#p0x #p0y #p1x #p1y #p2x #p2y #p3x #p3y: perm)
            (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy **
  A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y **
  A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y **
  A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y **
  A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length c0x == 64 /\ Seq.length c0y == 64 /\
        Seq.length c1x == 64 /\ Seq.length c1y == 64 /\
        Seq.length c2x == 64 /\ Seq.length c2y == 64 /\
        Seq.length c3x == 64 /\ Seq.length c3y == 64 /\
        atok c0x c0y P.g (pow2 (64 * 0)) /\
        atok c1x c1y P.g (pow2 (64 * 1)) /\
        atok c2x c2y P.g (pow2 (64 * 2)) /\
        atok c3x c3y P.g (pow2 (64 * 3)) /\
        Seq.length vk == B4.nl)
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to t0x #p0x c0x ** A.pts_to t0y #p0y c0y **
  A.pts_to t1x #p1x c1x ** A.pts_to t1y #p1y c1y **
  A.pts_to t2x #p2x c2x ** A.pts_to t2y #p2y c2y **
  A.pts_to t3x #p3x c3x ** A.pts_to t3y #p3y c3y **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_g (W.kv vk)) /\
        GR.peq (pt wx wy wz) (P.point_mul_g (W.kv vk)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ks;
  L4.vals_bnd vk;
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
    A.pts_to ks #pk vk **
    pure (U32.v vi <= 13 /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\
          W.pok wx wy wz /\
          W.rep wx wy wz (B.h (W.kv vk) (U32.v vi)) P.g)
  decreases (U32.v (!i))
  {
    let vi = !i;
    let i2 = U32.sub vi 1ul;
    rung ox oy oz ux uy uz sx sy
         t0x t0y t1x t1y t2x t2y t3x t3y ks i2;
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
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vk == B4.nl /\ B4.bnd (L4.vals vk) B4.base)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_g (B4.eval (L4.vals vk))) /\
        GR.peq (pt wx wy wz) (P.point_mul_g (B4.eval (L4.vals vk))))
{
  let z = S64.zero;
  let mut ux = [| z; 4sz |];
  Mem.track ux; A.pts_to_len ux;
  let mut uy = [| z; 4sz |];
  Mem.track uy; A.pts_to_len uy;
  let mut uz = [| z; 4sz |];
  Mem.track uz; A.pts_to_len uz;
  let mut sx = [| z; 4sz |];
  Mem.track sx; A.pts_to_len sx;
  let mut sy = [| z; 4sz |];
  Mem.track sy; A.pts_to_len sy;

  T0.tbl_ok (); T1.tbl_ok (); T2.tbl_ok (); T3.tbl_ok ();
  n0 ();

  let t0x = Tbl.table T0.tx_arr 64sz;
  let t0y = Tbl.table T0.ty_arr 64sz;
  let t1x = Tbl.table T1.tx_arr 64sz;
  let t1y = Tbl.table T1.ty_arr 64sz;
  let t2x = Tbl.table T2.tx_arr 64sz;
  let t2y = Tbl.table T2.ty_arr 64sz;
  let t3x = Tbl.table T3.tx_arr 64sz;
  let t3y = Tbl.table T3.ty_arr 64sz;

  win_loop ox oy oz ux uy uz sx sy
           t0x t0y t1x t1y t2x t2y t3x t3y ks;

  Tbl.drop_table t0x; Tbl.drop_table t0y;
  Tbl.drop_table t1x; Tbl.drop_table t1y;
  Tbl.drop_table t2x; Tbl.drop_table t2y;
  Tbl.drop_table t3x; Tbl.drop_table t3y;
  Mem.wipe sy 4sz;
  Mem.wipe sx 4sz;
  Mem.wipe uz 4sz;
  Mem.wipe uy 4sz;
  Mem.wipe ux 4sz;
  ()
}

#pop-options
