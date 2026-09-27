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

(** Multiplying the generator, with four base points.

    Signing and key generation multiply a *known* point, and a known point
    can be preprocessed.  The window in {!Hacl.K256.PointWin} walks the
    scalar four bits at a time and pays two hundred and fifty-six
    doublings for the walk; but if the scalar is split into four
    sixty-four-bit pieces

    {[ k = k0 + k1 2^64 + k2 2^128 + k3 2^192 ]}

    then

    {[ k G = k0 G + k1 (2^64 G) + k2 (2^128 G) + k3 (2^192 G) ]}

    and the four pieces can be walked *together*.  Sixteen rungs suffice,
    each one four doublings and four additions, because the same doubling
    chain serves all four pieces.  Sixty doublings and sixty-four
    additions replace two hundred and fifty-six and sixty-four.

    The three extra base points are compiled in
    ({!Spec.K256.Base}, {!Hacl.K256.Tables52}); their tables of sixteen
    multiples are built on entry, sixty more additions, which is still a
    large win and costs six field constants rather than a hundred and
    ninety-two.

    Everything below the rung is {!Hacl.K256.PointWin}'s, which is why
    that module's table layer carries a scale: entry [d] of the [j]-th
    table has to be described as the [d 2^{64j}]-th multiple of [G], not
    as the [d]-th multiple of [2^{64j} G], because it is [G] that the
    answer is a multiple of and there is no route from one reading to the
    other that does not go through [smul]'s associativity.

    This is {!Hacl.Ed25519.PointMulG} on a different curve; the scalar
    arithmetic the two share is {!Spec.Group.Split4}. *)
module Hacl.K256.PointMulG

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum52
open Spec.K256.Field52
open Spec.K256.Freeze
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.Impl.Table
open Hacl.K256.Field52
open Hacl.K256.Point
open Hacl.K256.PointStep
open Hacl.K256.PointWin

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module GR = Spec.K256.Group
module SM = Spec.K256.Smul
module Base = Spec.K256.Base
module Split = Spec.Group.Split4
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4
module Math = FStar.Math.Lemmas
module W = Hacl.K256.PointWin
module G = Pulse.Lib.GlobalArray
module Tbl = Hacl.Impl.Table
module KT52 = Hacl.K256.Tables52
module KT52G = Hacl.K256.Tables52G

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The spec side}

    Four facts about the base points, one about the scalar, and one that
    leaves the abstraction.  Each is stated as the Pulse function that
    uses it leaves its hypotheses. *)

let g_rep (x y z: Seq.seq S64.t)
  : Lemma (requires pt x y z == K.g) (ensures W.rep K.g 1 K.g)
  = GR.g_on_curve ();
    W.oc_intro K.g;
    W.rep_one K.g

let q1_rep (_: unit) : Lemma (W.rep Base.q1 (pow2 64) K.g)
  = reveal_opaque (`%W.rep) W.rep;
    Base.q1_ok ()

let q2_rep (_: unit) : Lemma (W.rep Base.q2 (pow2 128) K.g)
  = reveal_opaque (`%W.rep) W.rep;
    Base.q2_ok ()

let q3_rep (_: unit) : Lemma (W.rep Base.q3 (pow2 192) K.g)
  = reveal_opaque (`%W.rep) W.rep;
    Base.q3_ok ()

(** The accumulator starts at nothing, which is [hi k 16]. *)
let hi_start (k: nat)
  : Lemma (requires W.oc K.g)
          (ensures W.rep K.point_at_infinity (Split.hi k 16) K.g)
  = W.zero_ok K.g;
    Split.hi_top k

(** And ends at the scalar itself. *)
let hi_end (a: K.proj_point) (k: nat)
  : Lemma (requires W.oc K.g /\ W.rep a (Split.hi k 0) K.g /\ k < pow2 256)
          (ensures GR.on_curve a /\ GR.on_curve (K.point_mul_g k) /\
                   GR.peq a (K.point_mul_g k))
  = Split.hi_bot k;
    W.rep_cong a (Split.hi k 0) k K.g;
    W.win_done a K.g k

(** One rung's arithmetic: four doublings and four scaled digits make the
    next value of [hi].  The four products are exactly the four summands
    of [digs], so the only thing to say is that the first scale is one. *)
let rung_step (a: K.proj_point) (k: nat) (i: nat { i < 16 })
  : Lemma (requires
             W.rep a
               (16 * Split.hi k (i + 1) +
                Split.dig k 0 i * 1 +
                Split.dig k 1 i * pow2 64 +
                Split.dig k 2 i * pow2 128 +
                Split.dig k 3 i * pow2 192) K.g)
          (ensures W.rep a (Split.hi k i) K.g)
  = Split.hi_step k i;
    W.mul_one (Split.dig k 0 i)

(** The window index and the four bit positions it names: that each is a
    legal argument to [adigit], and that each fits in a [size_t].  Stated
    in one lemma because the loop body below asks for all twelve facts in
    a context that carries the addition law, where rederiving any of them
    costs more than the rung itself. *)
let shift_ok (i: nat { i < 16 })
  : Lemma (i * 4 >= 0 /\
           i * 4 < pow2 32 /\ i * 4 + 64 < pow2 32 /\
           i * 4 + 128 < pow2 32 /\ i * 4 + 192 < pow2 32 /\
           i * 4 < 256 /\ (i * 4) % 4 == 0 /\
           i * 4 + 64 < 256 /\ (i * 4 + 64) % 4 == 0 /\
           i * 4 + 128 < 256 /\ (i * 4 + 128) % 4 == 0 /\
           i * 4 + 192 < 256 /\ (i * 4 + 192) % 4 == 0)
  = assert_norm (pow2 32 > 256)

(** And that [adigit]'s answer at that position is the digit the window
    wants, which is one commutation of a product. *)
let dig_at (k: nat) (i: nat { i < 16 }) (j: nat { j < 4 })
  : Lemma (Split.dig k j i == k / pow2 (i * 4 + 64 * j) % 16) = ()

#pop-options

(** {2 Loading a base point}

    The coordinates are read-only tables, and the table build wants them
    at one permission, so they are copied in.  [z] is one for all four --
    the constants are stored affine. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

inline_for_extraction
fn load (a: A.array S64.t) (arr: G.static_array S64.t) (x: erased K.felem)
        (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\
        Seq.length (G.static_array_elems arr) == nl /\
        vals (G.static_array_elems arr) == limbs_of (reveal x))
ensures exists* (wa: Seq.seq S64.t).
  A.pts_to a wa ** pure (felem (vals wa) /\ fev (vals wa) == reveal x)
{
  let ct = fconst arr x;
  fcopy a ct;
  Tbl.drop_table ct;
}

#pop-options

(** {2 One rung}

    Four doublings, then one addition per base point.  The digits are
    secret, so each addition reads all sixteen entries of its table.

    Everything here is {!Hacl.K256.PointWin}'s except the bookkeeping:
    [win_dbl4] takes [hi k (i+1)] to [16 hi k (i+1)], and the four
    [win_add]s put back the four digits, each weighted by its table's
    scale.  That sum is [hi k i]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

fn rung (ox oy oz ux uy uz sx sy sz: A.array S64.t)
        (t0x t0y t0z: A.array S64.t)
        (t1x t1y t1z: A.array S64.t)
        (t2x t2y t2z: A.array S64.t)
        (t3x t3y t3z: A.array S64.t)
        (d0 d1 d2 d3: S64.t)
        (k: erased nat) (i: erased (n: nat { n < 16 }))
        (#vox #voy #voz: erased (Seq.seq S64.t))
        (#vux #vuy #vuz: erased (Seq.seq S64.t))
        (#vsx #vsy #vsz: erased (Seq.seq S64.t))
        (#v0x #v0y #v0z: erased (Seq.seq S64.t))
        (#v1x #v1y #v1z: erased (Seq.seq S64.t))
        (#v2x #v2y #v2z: erased (Seq.seq S64.t))
        (#v3x #v3y #v3z: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to t0x v0x ** A.pts_to t0y v0y ** A.pts_to t0z v0z **
  A.pts_to t1x v1x ** A.pts_to t1y v1y ** A.pts_to t1z v1z **
  A.pts_to t2x v2x ** A.pts_to t2y v2y ** A.pts_to t2z v2z **
  A.pts_to t3x v3x ** A.pts_to t3y v3y ** A.pts_to t3z v3z **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\ Seq.length vsz == nl /\
        Seq.length v0x == 80 /\ Seq.length v0y == 80 /\ Seq.length v0z == 80 /\
        Seq.length v1x == 80 /\ Seq.length v1y == 80 /\ Seq.length v1z == 80 /\
        Seq.length v2x == 80 /\ Seq.length v2y == 80 /\ Seq.length v2z == 80 /\
        Seq.length v3x == 80 /\ Seq.length v3y == 80 /\ Seq.length v3z == 80 /\
        W.oc K.g /\ pt_ok vox voy voz /\
        W.rep (pt vox voy voz) (Split.hi k (reveal i + 1)) K.g /\
        W.tok v0x v0y v0z K.g 1 16 /\
        W.tok v1x v1y v1z K.g (pow2 64) 16 /\
        W.tok v2x v2y v2z K.g (pow2 128) 16 /\
        W.tok v3x v3y v3z K.g (pow2 192) 16 /\
        S64.v d0 == Split.dig k 0 i /\ S64.v d1 == Split.dig k 1 i /\
        S64.v d2 == Split.dig k 2 i /\ S64.v d3 == Split.dig k 3 i)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to t0x v0x ** A.pts_to t0y v0y ** A.pts_to t0z v0z **
  A.pts_to t1x v1x ** A.pts_to t1y v1y ** A.pts_to t1z v1z **
  A.pts_to t2x v2x ** A.pts_to t2y v2y ** A.pts_to t2z v2z **
  A.pts_to t3x v3x ** A.pts_to t3y v3y ** A.pts_to t3z v3z **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
        pt_ok wx wy wz /\ W.rep (pt wx wy wz) (Split.hi k i) K.g)
{
  let e0 : erased nat = hide (Split.hi k (reveal i + 1));
  W.win_dbl4 ox oy oz ux uy uz (hide K.g) e0;
  W.mul_nat (Split.dig k 0 i) 1;
  W.win_add ox oy oz ux uy uz sx sy sz t0x t0y t0z d0
            (hide K.g) (hide 1) (hide (16 * reveal e0))
            (hide (Split.dig k 0 i));
  let e1 : erased nat = hide (16 * reveal e0 + Split.dig k 0 i * 1);
  W.mul_nat (Split.dig k 1 i) (pow2 64);
  W.win_add ox oy oz ux uy uz sx sy sz t1x t1y t1z d1
            (hide K.g) (hide (pow2 64)) e1 (hide (Split.dig k 1 i));
  let e2 : erased nat = hide (reveal e1 + Split.dig k 1 i * pow2 64);
  W.mul_nat (Split.dig k 2 i) (pow2 128);
  W.win_add ox oy oz ux uy uz sx sy sz t2x t2y t2z d2
            (hide K.g) (hide (pow2 128)) e2 (hide (Split.dig k 2 i));
  let e3 : erased nat = hide (reveal e2 + Split.dig k 2 i * pow2 128);
  W.mul_nat (Split.dig k 3 i) (pow2 192);
  W.win_add ox oy oz ux uy uz sx sy sz t3x t3y t3z d3
            (hide K.g) (hide (pow2 192)) e3 (hide (Split.dig k 3 i));
  with wx wy wz.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  rung_step (pt wx wy wz) k i;
  ()
}

#pop-options


(** {2 The four tables}

    The base points are staged through one triple of scratch arrays, since
    each is dead as soon as its table is built.  All four are stored
    affine, so [z] is one throughout.

    This is a function of its own, and so is the loop below.  Between them
    they name twenty-four arrays, and a verification condition mentioning
    twenty-four arrays, four tables of sixteen entries and the addition
    law is one the solver does not come back from; behind two contracts
    each half is routine. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"

fn build_tables (t0x t0y t0z: A.array S64.t)
                (t1x t1y t1z: A.array S64.t)
                (t2x t2y t2z: A.array S64.t)
                (t3x t3y t3z: A.array S64.t)
                (px py pz: A.array S64.t)
                (#v0x #v0y #v0z: erased (Seq.seq S64.t))
                (#v1x #v1y #v1z: erased (Seq.seq S64.t))
                (#v2x #v2y #v2z: erased (Seq.seq S64.t))
                (#v3x #v3y #v3z: erased (Seq.seq S64.t))
                (#vpx #vpy #vpz: erased (Seq.seq S64.t))
requires
  A.pts_to t0x v0x ** A.pts_to t0y v0y ** A.pts_to t0z v0z **
  A.pts_to t1x v1x ** A.pts_to t1y v1y ** A.pts_to t1z v1z **
  A.pts_to t2x v2x ** A.pts_to t2y v2y ** A.pts_to t2z v2z **
  A.pts_to t3x v3x ** A.pts_to t3y v3y ** A.pts_to t3z v3z **
  A.pts_to px vpx ** A.pts_to py vpy ** A.pts_to pz vpz **
  pure (Seq.length v0x == 80 /\ Seq.length v0y == 80 /\ Seq.length v0z == 80 /\
        Seq.length v1x == 80 /\ Seq.length v1y == 80 /\ Seq.length v1z == 80 /\
        Seq.length v2x == 80 /\ Seq.length v2y == 80 /\ Seq.length v2z == 80 /\
        Seq.length v3x == 80 /\ Seq.length v3y == 80 /\ Seq.length v3z == 80 /\
        Seq.length vpx == nl /\ Seq.length vpy == nl /\ Seq.length vpz == nl)
ensures exists* (c0x c0y c0z c1x c1y c1z
                 c2x c2y c2z c3x c3y c3z
                 wpx wpy wpz: Seq.seq S64.t).
  A.pts_to t0x c0x ** A.pts_to t0y c0y ** A.pts_to t0z c0z **
  A.pts_to t1x c1x ** A.pts_to t1y c1y ** A.pts_to t1z c1z **
  A.pts_to t2x c2x ** A.pts_to t2y c2y ** A.pts_to t2z c2z **
  A.pts_to t3x c3x ** A.pts_to t3y c3y ** A.pts_to t3z c3z **
  A.pts_to px wpx ** A.pts_to py wpy ** A.pts_to pz wpz **
  pure (Seq.length c0x == 80 /\ Seq.length c0y == 80 /\ Seq.length c0z == 80 /\
        Seq.length c1x == 80 /\ Seq.length c1y == 80 /\ Seq.length c1z == 80 /\
        Seq.length c2x == 80 /\ Seq.length c2y == 80 /\ Seq.length c2z == 80 /\
        Seq.length c3x == 80 /\ Seq.length c3y == 80 /\ Seq.length c3z == 80 /\
        W.tok c0x c0y c0z K.g 1 16 /\
        W.tok c1x c1y c1z K.g (pow2 64) 16 /\
        W.tok c2x c2y c2z K.g (pow2 128) 16 /\
        W.tok c3x c3y c3z K.g (pow2 192) 16)
{
  A.pts_to_len px; A.pts_to_len py; A.pts_to_len pz;
  GR.g_on_curve ();
  W.oc_intro K.g;

  load px KT52.gx_arr (hide K.g_x);
  load py KT52.gy_arr (hide K.g_y);
  fone pz;
  with g0 g1 g2.
    assert (A.pts_to px g0 ** A.pts_to py g1 ** A.pts_to pz g2);
  g_rep g0 g1 g2;
  W.build_table t0x t0y t0z px py pz (hide K.g) (hide 1);

  load px KT52G.q1x_arr (hide Base.q1x);
  load py KT52G.q1y_arr (hide Base.q1y);
  fone pz;
  with h0 h1 h2.
    assert (A.pts_to px h0 ** A.pts_to py h1 ** A.pts_to pz h2);
  q1_rep ();
  W.build_table t1x t1y t1z px py pz (hide K.g) (hide (pow2 64));

  load px KT52G.q2x_arr (hide Base.q2x);
  load py KT52G.q2y_arr (hide Base.q2y);
  fone pz;
  with k0 k1 k2.
    assert (A.pts_to px k0 ** A.pts_to py k1 ** A.pts_to pz k2);
  q2_rep ();
  W.build_table t2x t2y t2z px py pz (hide K.g) (hide (pow2 128));

  load px KT52G.q3x_arr (hide Base.q3x);
  load py KT52G.q3y_arr (hide Base.q3y);
  fone pz;
  with m0 m1 m2.
    assert (A.pts_to px m0 ** A.pts_to py m1 ** A.pts_to pz m2);
  q3_rep ();
  W.build_table t3x t3y t3z px py pz (hide K.g) (hide (pow2 192));
  ()
}

#pop-options

(** {2 The loop}

    Sixteen rungs.  The accumulator starts at the point at infinity, which
    is [hi k 16], and after the rung at [i] it is [hi k i]; the last is
    [hi k 0], which is the scalar. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

let sz_fits (x: nat) : Lemma (requires x < pow2 32) (ensures SZ.fits x)
  = Hacl.SizeT.fits32 (); SZ.fits_u32_implies_fits x

fn win_loop (ox oy oz ux uy uz sx sy sz: A.array S64.t)
            (t0x t0y t0z: A.array S64.t)
            (t1x t1y t1z: A.array S64.t)
            (t2x t2y t2z: A.array S64.t)
            (t3x t3y t3z: A.array S64.t)
            (ks: A.array S64.t)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
            (#vsx #vsy #vsz: erased (Seq.seq S64.t))
            (#c0x #c0y #c0z: erased (Seq.seq S64.t))
            (#c1x #c1y #c1z: erased (Seq.seq S64.t))
            (#c2x #c2y #c2z: erased (Seq.seq S64.t))
            (#c3x #c3y #c3z: erased (Seq.seq S64.t))
            (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to t0x c0x ** A.pts_to t0y c0y ** A.pts_to t0z c0z **
  A.pts_to t1x c1x ** A.pts_to t1y c1y ** A.pts_to t1z c1z **
  A.pts_to t2x c2x ** A.pts_to t2y c2y ** A.pts_to t2z c2z **
  A.pts_to t3x c3x ** A.pts_to t3y c3y ** A.pts_to t3z c3z **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\ Seq.length vsz == nl /\
        Seq.length c0x == 80 /\ Seq.length c0y == 80 /\ Seq.length c0z == 80 /\
        Seq.length c1x == 80 /\ Seq.length c1y == 80 /\ Seq.length c1z == 80 /\
        Seq.length c2x == 80 /\ Seq.length c2y == 80 /\ Seq.length c2z == 80 /\
        Seq.length c3x == 80 /\ Seq.length c3y == 80 /\ Seq.length c3z == 80 /\
        Seq.length vk == B4.nl /\ B4.bnd (L4.vals vk) B4.base /\
        W.tok c0x c0y c0z K.g 1 16 /\
        W.tok c1x c1y c1z K.g (pow2 64) 16 /\
        W.tok c2x c2y c2z K.g (pow2 128) 16 /\
        W.tok c3x c3y c3z K.g (pow2 192) 16)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to t0x c0x ** A.pts_to t0y c0y ** A.pts_to t0z c0z **
  A.pts_to t1x c1x ** A.pts_to t1y c1y ** A.pts_to t1z c1z **
  A.pts_to t2x c2x ** A.pts_to t2y c2y ** A.pts_to t2z c2z **
  A.pts_to t3x c3x ** A.pts_to t3y c3y ** A.pts_to t3z c3z **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (K.point_mul_g (W.kv vk)) /\
        GR.peq (pt wx wy wz) (K.point_mul_g (W.kv vk)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ks;
  W.kv_bnd vk;
  GR.g_on_curve ();
  W.oc_intro K.g;
  set_infinity ox oy oz;
  hi_start (W.kv vk);
  assert_norm (16 < pow2 32);
  assert_norm (64 < pow2 32);
  assert_norm (128 < pow2 32);
  assert_norm (192 < pow2 32);
  assert_norm (4 < pow2 32);
  sz_fits 16; sz_fits 64; sz_fits 128; sz_fits 192; sz_fits 4;

  let mut i = 16sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
    A.pts_to t0x c0x ** A.pts_to t0y c0y ** A.pts_to t0z c0z **
    A.pts_to t1x c1x ** A.pts_to t1y c1y ** A.pts_to t1z c1z **
    A.pts_to t2x c2x ** A.pts_to t2y c2y ** A.pts_to t2z c2z **
    A.pts_to t3x c3x ** A.pts_to t3y c3y ** A.pts_to t3z c3z **
    A.pts_to ks #pk vk **
    pure (SZ.v vi <= 16 /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
          pt_ok wx wy wz /\
          W.rep (pt wx wy wz) (Split.hi (W.kv vk) (SZ.v vi)) K.g)
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
    dig_at (W.kv vk) (SZ.v i2) 0; dig_at (W.kv vk) (SZ.v i2) 1;
    dig_at (W.kv vk) (SZ.v i2) 2; dig_at (W.kv vk) (SZ.v i2) 3;
    let d0 = adigit ks sh;
    let d1 = adigit ks (SZ.add sh 64sz);
    let d2 = adigit ks (SZ.add sh 128sz);
    let d3 = adigit ks (SZ.add sh 192sz);
    rung ox oy oz ux uy uz sx sy sz
         t0x t0y t0z t1x t1y t1z t2x t2y t2z t3x t3y t3z
         d0 d1 d2 d3 (hide (W.kv vk)) (hide (SZ.v i2));
    i := i2;
  };
  let vi = !i;
  W.sz_zero vi;
  with wx wy wz.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  hi_end (pt wx wy wz) (W.kv vk);
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
        GR.on_curve (K.point_mul_g (B4.eval (L4.vals vk))) /\
        GR.peq (pt wx wy wz) (K.point_mul_g (B4.eval (L4.vals vk))))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  let z = S64.zero;
  let mut px = [| z; 5sz |]; A.pts_to_len px;
  let mut py = [| z; 5sz |]; A.pts_to_len py;
  let mut pz = [| z; 5sz |]; A.pts_to_len pz;
  let mut ux = [| z; 5sz |]; A.pts_to_len ux;
  let mut uy = [| z; 5sz |]; A.pts_to_len uy;
  let mut uz = [| z; 5sz |]; A.pts_to_len uz;
  let mut sx = [| z; 5sz |]; A.pts_to_len sx;
  let mut sy = [| z; 5sz |]; A.pts_to_len sy;
  let mut sz = [| z; 5sz |]; A.pts_to_len sz;
  let mut t0x = [| z; 80sz |]; A.pts_to_len t0x;
  let mut t0y = [| z; 80sz |]; A.pts_to_len t0y;
  let mut t0z = [| z; 80sz |]; A.pts_to_len t0z;
  let mut t1x = [| z; 80sz |]; A.pts_to_len t1x;
  let mut t1y = [| z; 80sz |]; A.pts_to_len t1y;
  let mut t1z = [| z; 80sz |]; A.pts_to_len t1z;
  let mut t2x = [| z; 80sz |]; A.pts_to_len t2x;
  let mut t2y = [| z; 80sz |]; A.pts_to_len t2y;
  let mut t2z = [| z; 80sz |]; A.pts_to_len t2z;
  let mut t3x = [| z; 80sz |]; A.pts_to_len t3x;
  let mut t3y = [| z; 80sz |]; A.pts_to_len t3y;
  let mut t3z = [| z; 80sz |]; A.pts_to_len t3z;
  A.pts_to_len px; A.pts_to_len py; A.pts_to_len pz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz;
  A.pts_to_len t0x; A.pts_to_len t0y; A.pts_to_len t0z;
  A.pts_to_len t1x; A.pts_to_len t1y; A.pts_to_len t1z;
  A.pts_to_len t2x; A.pts_to_len t2y; A.pts_to_len t2z;
  A.pts_to_len t3x; A.pts_to_len t3y; A.pts_to_len t3z;

  build_tables t0x t0y t0z t1x t1y t1z t2x t2y t2z t3x t3y t3z px py pz;
  win_loop ox oy oz ux uy uz sx sy sz
           t0x t0y t0z t1x t1y t1z t2x t2y t2z t3x t3y t3z ks;
  ()
}

#pop-options
