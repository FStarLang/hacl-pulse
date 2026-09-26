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
    can be preprocessed.  The window in {!Hacl.Ed25519.PointWin} walks the
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
    ({!Spec.Ed25519.Base}, {!Hacl.Ed25519.Tables}); their tables of
    sixteen multiples are built on entry, sixty more additions, which is
    still a large win and costs nine field constants rather than two
    hundred and fifty-six.  Compiling the tables in as well is a further
    thirty per cent and is a change to this file's first twenty lines.

    Everything below the rung is {!Hacl.Ed25519.PointWin}'s, which is why
    that module's table layer carries a scale: entry [d] of the [j]-th
    table has to be described as the [d 2^{64j}]-th multiple of [G], not
    as the [d]-th multiple of [2^{64j} G], because it is [G] that the
    answer is a multiple of and there is no route from one reading to the
    other that does not go through [smul]'s associativity. *)
module Hacl.Ed25519.PointMulG

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum51
open Spec.Curve25519.Field
open Hacl.Curve25519.Field
open Hacl.Bignum.Base
open Hacl.Ed25519.Point

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module CF = Hacl.Curve25519.Field
module C = Spec.Curve25519
module E = Spec.Ed25519
module GR = Spec.Ed25519.Group
module SM = Spec.Ed25519.Smul
module Base = Spec.Ed25519.Base
module B = Hacl.Spec.Bytes
module Math = FStar.Math.Lemmas
module P = Hacl.Ed25519.Point
module W = Hacl.Ed25519.PointWin
module G = Pulse.Lib.GlobalArray
module Table = Hacl.Impl.Table
module Tables = Hacl.Ed25519.Tables

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The spec side}

    Four facts about the base points, one about the scalar, and one that
    leaves the abstraction.  Each is stated as the Pulse function that
    uses it leaves its hypotheses. *)

let g_rep (x y z t: Seq.seq S64.t)
  : Lemma (requires P.pt x y z t == E.g) (ensures W.rep x y z t 1 E.g)
  = GR.g_on_curve ();
    W.oc_intro E.g;
    W.rep_one x y z t

let b1_rep (x y z t: Seq.seq S64.t)
  : Lemma (requires P.pt x y z t == Base.b1)
          (ensures W.rep x y z t (pow2 64) E.g)
  = reveal_opaque (`%W.rep) W.rep;
    Base.b1_ok ()

let b2_rep (x y z t: Seq.seq S64.t)
  : Lemma (requires P.pt x y z t == Base.b2)
          (ensures W.rep x y z t (pow2 128) E.g)
  = reveal_opaque (`%W.rep) W.rep;
    Base.b2_ok ()

let b3_rep (x y z t: Seq.seq S64.t)
  : Lemma (requires P.pt x y z t == Base.b3)
          (ensures W.rep x y z t (pow2 192) E.g)
  = reveal_opaque (`%W.rep) W.rep;
    Base.b3_ok ()

(** The accumulator starts at nothing, which is [hi k 16]. *)
let hi_start (wx wy wz wt: Seq.seq S64.t) (k: nat)
  : Lemma (requires W.oc E.g /\ P.pt wx wy wz wt == E.point_at_infinity)
          (ensures W.rep wx wy wz wt (Base.hi k 16) E.g)
  = W.zero_ok wx wy wz wt E.g;
    Base.hi_top k

(** And ends at the scalar itself. *)
let hi_end (wx wy wz wt: Seq.seq S64.t) (k: Seq.lseq S8.t 32)
  : Lemma (requires W.oc E.g /\ W.pok wx wy wz wt /\
                    W.rep wx wy wz wt (Base.hi (B.le_nat k) 0) E.g)
          (ensures P.pt_ok wx wy wz wt /\ GR.on_curve (P.pt wx wy wz wt) /\
                   GR.on_curve (E.point_mul_g k) /\
                   E.point_equal (P.pt wx wy wz wt) (E.point_mul_g k))
  = B.le_nat_bound k;
    Base.hi_bot (B.le_nat k);
    W.rep_cong wx wy wz wt (Base.hi (B.le_nat k) 0) (B.le_nat k) E.g;
    W.rep_elim wx wy wz wt (B.le_nat k) E.g;
    W.pok_elim wx wy wz wt;
    W.win_done wx wy wz wt E.g k

(** One rung's arithmetic: four doublings and four scaled digits make the
    next value of [hi].  The four products are exactly the four summands
    of [digs], so the only thing to say is that the first scale is one. *)
let rung_step (wx wy wz wt: Seq.seq S64.t) (k: nat) (i: nat { i < 16 })
  : Lemma (requires
             W.rep wx wy wz wt
               (16 * Base.hi k (i + 1) +
                Base.dig k 0 i * 1 +
                Base.dig k 1 i * pow2 64 +
                Base.dig k 2 i * pow2 128 +
                Base.dig k 3 i * pow2 192) E.g)
          (ensures W.rep wx wy wz wt (Base.hi k i) E.g)
  = Base.hi_step k i;
    W.mul_one (Base.dig k 0 i)

(** The window index and the four bit positions it names. *)
let pos_ok (i: nat { i < 16 }) (j: nat { j < 4 })
  : Lemma (64 * j + 4 * i < 256 /\ (64 * j + 4 * i) % 4 == 0) = ()

#pop-options

(** {2 Loading a base point}

    The coordinates are read-only tables, and the table build wants them
    at one permission, so they are copied in.  [z] is one for all four --
    the constants are stored affine -- and only the generator needs a
    multiplication to recover [t]. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

inline_for_extraction
fn load (a: A.array S64.t) (arr: G.static_array S64.t)
        (#va: erased (Seq.seq S64.t))
requires A.pts_to a va **
  pure (Seq.length va == nl /\ Seq.length (G.static_array_elems arr) == nl)
ensures A.pts_to a (G.static_array_elems arr)
{
  let ct = Table.table arr 5sz;
  CF.copy a ct;
  Table.drop_table ct;
}

#pop-options

(** {2 One rung}

    Four doublings, then one addition per base point.  The digits are
    secret, so each addition reads all sixteen entries of its table.

    Everything here is {!Hacl.Ed25519.PointWin}'s except the bookkeeping:
    [win_dbl4] takes [hi k (i+1)] to [16 hi k (i+1)], and the four
    [win_add]s put back the four digits, each weighted by its table's
    scale.  That sum is [hi k i]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

fn rung (ox oy oz ot ux uy uz ut sx sy sz st: A.array S64.t)
        (t0x t0y t0z t0t: A.array S64.t)
        (t1x t1y t1z t1t: A.array S64.t)
        (t2x t2y t2z t2t: A.array S64.t)
        (t3x t3y t3z t3t: A.array S64.t)
        (d0 d1 d2 d3: S64.t)
        (k: erased nat) (i: erased (n: nat { n < 16 }))
        (#vox #voy #voz #vot: erased (Seq.seq S64.t))
        (#vux #vuy #vuz #vut: erased (Seq.seq S64.t))
        (#vsx #vsy #vsz #vst: erased (Seq.seq S64.t))
        (#v0x #v0y #v0z #v0t: erased (Seq.seq S64.t))
        (#v1x #v1y #v1z #v1t: erased (Seq.seq S64.t))
        (#v2x #v2y #v2z #v2t: erased (Seq.seq S64.t))
        (#v3x #v3y #v3z #v3t: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz ** A.pts_to st vst **
  A.pts_to t0x v0x ** A.pts_to t0y v0y **
  A.pts_to t0z v0z ** A.pts_to t0t v0t **
  A.pts_to t1x v1x ** A.pts_to t1y v1y **
  A.pts_to t1z v1z ** A.pts_to t1t v1t **
  A.pts_to t2x v2x ** A.pts_to t2y v2y **
  A.pts_to t2z v2z ** A.pts_to t2t v2t **
  A.pts_to t3x v3x ** A.pts_to t3y v3y **
  A.pts_to t3z v3z ** A.pts_to t3t v3t **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length vsz == nl /\ Seq.length vst == nl /\
        Seq.length v0x == 80 /\ Seq.length v0y == 80 /\
        Seq.length v0z == 80 /\ Seq.length v0t == 80 /\
        Seq.length v1x == 80 /\ Seq.length v1y == 80 /\
        Seq.length v1z == 80 /\ Seq.length v1t == 80 /\
        Seq.length v2x == 80 /\ Seq.length v2y == 80 /\
        Seq.length v2z == 80 /\ Seq.length v2t == 80 /\
        Seq.length v3x == 80 /\ Seq.length v3y == 80 /\
        Seq.length v3z == 80 /\ Seq.length v3t == 80 /\
        W.oc E.g /\ W.pok vox voy voz vot /\
        W.rep vox voy voz vot (Base.hi k (reveal i + 1)) E.g /\
        W.tok v0x v0y v0z v0t E.g 1 16 /\
        W.tok v1x v1y v1z v1t E.g (pow2 64) 16 /\
        W.tok v2x v2y v2z v2t E.g (pow2 128) 16 /\
        W.tok v3x v3y v3z v3t E.g (pow2 192) 16 /\
        S64.v d0 == Base.dig k 0 i /\ S64.v d1 == Base.dig k 1 i /\
        S64.v d2 == Base.dig k 2 i /\ S64.v d3 == Base.dig k 3 i)
ensures exists* (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
  A.pts_to t0x v0x ** A.pts_to t0y v0y **
  A.pts_to t0z v0z ** A.pts_to t0t v0t **
  A.pts_to t1x v1x ** A.pts_to t1y v1y **
  A.pts_to t1z v1z ** A.pts_to t1t v1t **
  A.pts_to t2x v2x ** A.pts_to t2y v2y **
  A.pts_to t2z v2z ** A.pts_to t2t v2t **
  A.pts_to t3x v3x ** A.pts_to t3y v3y **
  A.pts_to t3z v3z ** A.pts_to t3t v3t **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
        Seq.length wuz == nl /\ Seq.length wut == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\
        Seq.length wsz == nl /\ Seq.length wst == nl /\
        W.pok wx wy wz wt /\ W.rep wx wy wz wt (Base.hi k i) E.g)
{
  let e0 : erased nat = hide (Base.hi k (reveal i + 1));
  W.win_dbl4 ox oy oz ot ux uy uz ut (hide E.g) e0;
  W.win_add ox oy oz ot ux uy uz ut sx sy sz st t0x t0y t0z t0t d0
            (hide E.g) (hide 1) (hide (16 * reveal e0))
            (hide (Base.dig k 0 i));
  let e1 : erased nat = hide (16 * reveal e0 + Base.dig k 0 i * 1);
  W.win_add ox oy oz ot ux uy uz ut sx sy sz st t1x t1y t1z t1t d1
            (hide E.g) (hide (pow2 64)) e1 (hide (Base.dig k 1 i));
  let e2 : erased nat = hide (reveal e1 + Base.dig k 1 i * pow2 64);
  W.win_add ox oy oz ot ux uy uz ut sx sy sz st t2x t2y t2z t2t d2
            (hide E.g) (hide (pow2 128)) e2 (hide (Base.dig k 2 i));
  let e3 : erased nat = hide (reveal e2 + Base.dig k 2 i * pow2 128);
  W.win_add ox oy oz ot ux uy uz ut sx sy sz st t3x t3y t3z t3t d3
            (hide E.g) (hide (pow2 192)) e3 (hide (Base.dig k 3 i));
  with wx wy wz wt.
    assert (A.pts_to ox wx ** A.pts_to oy wy **
            A.pts_to oz wz ** A.pts_to ot wt);
  rung_step wx wy wz wt k i;
  ()
}

#pop-options


(** {2 The four tables}

    The base points are staged through one quadruple of scratch arrays,
    since each is dead as soon as its table is built.  The generator is
    the only one whose [t] has to be computed; the other three are stored
    affine, so [z] is one and [t] is a constant.

    This is a function of its own, and so is the loop below.  Between them
    they name thirty-two arrays, and a verification condition mentioning
    thirty-two arrays, four tables of sixteen entries and the addition law
    is one the solver does not come back from; behind two contracts each
    half is routine. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"

fn build_tables (t0x t0y t0z t0t: A.array S64.t)
                (t1x t1y t1z t1t: A.array S64.t)
                (t2x t2y t2z t2t: A.array S64.t)
                (t3x t3y t3z t3t: A.array S64.t)
                (px py pz pw: A.array S64.t)
                (#v0x #v0y #v0z #v0t: erased (Seq.seq S64.t))
                (#v1x #v1y #v1z #v1t: erased (Seq.seq S64.t))
                (#v2x #v2y #v2z #v2t: erased (Seq.seq S64.t))
                (#v3x #v3y #v3z #v3t: erased (Seq.seq S64.t))
                (#vpx #vpy #vpz #vpw: erased (Seq.seq S64.t))
requires
  A.pts_to t0x v0x ** A.pts_to t0y v0y **
  A.pts_to t0z v0z ** A.pts_to t0t v0t **
  A.pts_to t1x v1x ** A.pts_to t1y v1y **
  A.pts_to t1z v1z ** A.pts_to t1t v1t **
  A.pts_to t2x v2x ** A.pts_to t2y v2y **
  A.pts_to t2z v2z ** A.pts_to t2t v2t **
  A.pts_to t3x v3x ** A.pts_to t3y v3y **
  A.pts_to t3z v3z ** A.pts_to t3t v3t **
  A.pts_to px vpx ** A.pts_to py vpy **
  A.pts_to pz vpz ** A.pts_to pw vpw **
  pure (Seq.length v0x == 80 /\ Seq.length v0y == 80 /\
        Seq.length v0z == 80 /\ Seq.length v0t == 80 /\
        Seq.length v1x == 80 /\ Seq.length v1y == 80 /\
        Seq.length v1z == 80 /\ Seq.length v1t == 80 /\
        Seq.length v2x == 80 /\ Seq.length v2y == 80 /\
        Seq.length v2z == 80 /\ Seq.length v2t == 80 /\
        Seq.length v3x == 80 /\ Seq.length v3y == 80 /\
        Seq.length v3z == 80 /\ Seq.length v3t == 80 /\
        Seq.length vpx == nl /\ Seq.length vpy == nl /\
        Seq.length vpz == nl /\ Seq.length vpw == nl)
ensures exists* (c0x c0y c0z c0t c1x c1y c1z c1t
                 c2x c2y c2z c2t c3x c3y c3z c3t
                 wpx wpy wpz wpw: Seq.seq S64.t).
  A.pts_to t0x c0x ** A.pts_to t0y c0y **
  A.pts_to t0z c0z ** A.pts_to t0t c0t **
  A.pts_to t1x c1x ** A.pts_to t1y c1y **
  A.pts_to t1z c1z ** A.pts_to t1t c1t **
  A.pts_to t2x c2x ** A.pts_to t2y c2y **
  A.pts_to t2z c2z ** A.pts_to t2t c2t **
  A.pts_to t3x c3x ** A.pts_to t3y c3y **
  A.pts_to t3z c3z ** A.pts_to t3t c3t **
  A.pts_to px wpx ** A.pts_to py wpy **
  A.pts_to pz wpz ** A.pts_to pw wpw **
  pure (Seq.length c0x == 80 /\ Seq.length c0y == 80 /\
        Seq.length c0z == 80 /\ Seq.length c0t == 80 /\
        Seq.length c1x == 80 /\ Seq.length c1y == 80 /\
        Seq.length c1z == 80 /\ Seq.length c1t == 80 /\
        Seq.length c2x == 80 /\ Seq.length c2y == 80 /\
        Seq.length c2z == 80 /\ Seq.length c2t == 80 /\
        Seq.length c3x == 80 /\ Seq.length c3y == 80 /\
        Seq.length c3z == 80 /\ Seq.length c3t == 80 /\
        W.tok c0x c0y c0z c0t E.g 1 16 /\
        W.tok c1x c1y c1z c1t E.g (pow2 64) 16 /\
        W.tok c2x c2y c2z c2t E.g (pow2 128) 16 /\
        W.tok c3x c3y c3z c3t E.g (pow2 192) 16)
{
  A.pts_to_len px; A.pts_to_len py; A.pts_to_len pz; A.pts_to_len pw;
  GR.g_on_curve ();
  W.oc_intro E.g;

  load px Tables.gx_arr;
  load py Tables.gy_arr;
  Tables.gx_ok (); Tables.gy_ok ();
  assert_norm (1 < base);
  P.set_small pz 1uL;
  fmul pw px py;
  with g0 g1 g2 g3.
    assert (A.pts_to px g0 ** A.pts_to py g1 **
            A.pts_to pz g2 ** A.pts_to pw g3);
  W.pok_intro g0 g1 g2 g3;
  g_rep g0 g1 g2 g3;
  W.build_table t0x t0y t0z t0t px py pz pw (hide E.g) (hide 1);

  load px Tables.b1x_arr;
  load py Tables.b1y_arr;
  load pw Tables.b1t_arr;
  P.set_small pz 1uL;
  Tables.b1x_ok (); Tables.b1y_ok (); Tables.b1t_ok ();
  with h0 h1 h2 h3.
    assert (A.pts_to px h0 ** A.pts_to py h1 **
            A.pts_to pz h2 ** A.pts_to pw h3);
  W.pok_intro h0 h1 h2 h3;
  b1_rep h0 h1 h2 h3;
  W.build_table t1x t1y t1z t1t px py pz pw (hide E.g) (hide (pow2 64));

  load px Tables.b2x_arr;
  load py Tables.b2y_arr;
  load pw Tables.b2t_arr;
  P.set_small pz 1uL;
  Tables.b2x_ok (); Tables.b2y_ok (); Tables.b2t_ok ();
  with k0 k1 k2 k3.
    assert (A.pts_to px k0 ** A.pts_to py k1 **
            A.pts_to pz k2 ** A.pts_to pw k3);
  W.pok_intro k0 k1 k2 k3;
  b2_rep k0 k1 k2 k3;
  W.build_table t2x t2y t2z t2t px py pz pw (hide E.g) (hide (pow2 128));

  load px Tables.b3x_arr;
  load py Tables.b3y_arr;
  load pw Tables.b3t_arr;
  P.set_small pz 1uL;
  Tables.b3x_ok (); Tables.b3y_ok (); Tables.b3t_ok ();
  with m0 m1 m2 m3.
    assert (A.pts_to px m0 ** A.pts_to py m1 **
            A.pts_to pz m2 ** A.pts_to pw m3);
  W.pok_intro m0 m1 m2 m3;
  b3_rep m0 m1 m2 m3;
  W.build_table t3x t3y t3z t3t px py pz pw (hide E.g) (hide (pow2 192));
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

fn win_loop (ox oy oz ot ux uy uz ut sx sy sz st: A.array S64.t)
            (t0x t0y t0z t0t: A.array S64.t)
            (t1x t1y t1z t1t: A.array S64.t)
            (t2x t2y t2z t2t: A.array S64.t)
            (t3x t3y t3z t3t: A.array S64.t)
            (ks: A.array S8.t)
            (#vox #voy #voz #vot: erased (Seq.seq S64.t))
            (#vux #vuy #vuz #vut: erased (Seq.seq S64.t))
            (#vsx #vsy #vsz #vst: erased (Seq.seq S64.t))
            (#c0x #c0y #c0z #c0t: erased (Seq.seq S64.t))
            (#c1x #c1y #c1z #c1t: erased (Seq.seq S64.t))
            (#c2x #c2y #c2z #c2t: erased (Seq.seq S64.t))
            (#c3x #c3y #c3z #c3t: erased (Seq.seq S64.t))
            (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz ** A.pts_to st vst **
  A.pts_to t0x c0x ** A.pts_to t0y c0y **
  A.pts_to t0z c0z ** A.pts_to t0t c0t **
  A.pts_to t1x c1x ** A.pts_to t1y c1y **
  A.pts_to t1z c1z ** A.pts_to t1t c1t **
  A.pts_to t2x c2x ** A.pts_to t2y c2y **
  A.pts_to t2z c2z ** A.pts_to t2t c2t **
  A.pts_to t3x c3x ** A.pts_to t3y c3y **
  A.pts_to t3z c3z ** A.pts_to t3t c3t **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl /\
        Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length vsz == nl /\ Seq.length vst == nl /\
        Seq.length c0x == 80 /\ Seq.length c0y == 80 /\
        Seq.length c0z == 80 /\ Seq.length c0t == 80 /\
        Seq.length c1x == 80 /\ Seq.length c1y == 80 /\
        Seq.length c1z == 80 /\ Seq.length c1t == 80 /\
        Seq.length c2x == 80 /\ Seq.length c2y == 80 /\
        Seq.length c2z == 80 /\ Seq.length c2t == 80 /\
        Seq.length c3x == 80 /\ Seq.length c3y == 80 /\
        Seq.length c3z == 80 /\ Seq.length c3t == 80 /\
        W.tok c0x c0y c0z c0t E.g 1 16 /\
        W.tok c1x c1y c1z c1t E.g (pow2 64) 16 /\
        W.tok c2x c2y c2z c2t E.g (pow2 128) 16 /\
        W.tok c3x c3y c3z c3t E.g (pow2 192) 16)
ensures exists* (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
  A.pts_to t0x c0x ** A.pts_to t0y c0y **
  A.pts_to t0z c0z ** A.pts_to t0t c0t **
  A.pts_to t1x c1x ** A.pts_to t1y c1y **
  A.pts_to t1z c1z ** A.pts_to t1t c1t **
  A.pts_to t2x c2x ** A.pts_to t2y c2y **
  A.pts_to t2z c2z ** A.pts_to t2t c2t **
  A.pts_to t3x c3x ** A.pts_to t3y c3y **
  A.pts_to t3z c3z ** A.pts_to t3t c3t **
  A.pts_to ks #pk vk **
  pure (P.pt_ok wx wy wz wt /\ GR.on_curve (P.pt wx wy wz wt) /\
        E.point_equal (P.pt wx wy wz wt) (E.point_mul_g vk))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len ks;
  GR.g_on_curve ();
  W.oc_intro E.g;
  P.set_infinity ox oy oz ot;
  with o0x o0y o0z o0t.
    assert (A.pts_to ox o0x ** A.pts_to oy o0y **
            A.pts_to oz o0z ** A.pts_to ot o0t);
  W.pok_intro o0x o0y o0z o0t;
  hi_start o0x o0y o0z o0t (B.le_nat vk);

  let mut i = 16sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wt wux wuy wuz wut
                     wsx wsy wsz wst: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
    A.pts_to t0x c0x ** A.pts_to t0y c0y **
    A.pts_to t0z c0z ** A.pts_to t0t c0t **
    A.pts_to t1x c1x ** A.pts_to t1y c1y **
    A.pts_to t1z c1z ** A.pts_to t1t c1t **
    A.pts_to t2x c2x ** A.pts_to t2y c2y **
    A.pts_to t2z c2z ** A.pts_to t2t c2t **
    A.pts_to t3x c3x ** A.pts_to t3y c3y **
    A.pts_to t3z c3z ** A.pts_to t3t c3t **
    A.pts_to ks #pk vk **
    pure (SZ.v vi <= 16 /\ Seq.length vk == 32 /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\
          Seq.length wuz == nl /\ Seq.length wut == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\
          Seq.length wsz == nl /\ Seq.length wst == nl /\
          W.pok wx wy wz wt /\
          W.rep wx wy wz wt (Base.hi (B.le_nat vk) (SZ.v vi)) E.g)
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let i2 = SZ.sub vi 1sz;
    sz_fits (SZ.v i2 * 4);
    let sh = SZ.mul i2 4sz;
    sz_fits (SZ.v sh + 64);
    sz_fits (SZ.v sh + 128);
    sz_fits (SZ.v sh + 192);
    pos_ok (SZ.v i2) 0; pos_ok (SZ.v i2) 1;
    pos_ok (SZ.v i2) 2; pos_ok (SZ.v i2) 3;
    let d0 = W.nibble ks sh;
    let d1 = W.nibble ks (SZ.add sh 64sz);
    let d2 = W.nibble ks (SZ.add sh 128sz);
    let d3 = W.nibble ks (SZ.add sh 192sz);
    rung ox oy oz ot ux uy uz ut sx sy sz st
         t0x t0y t0z t0t t1x t1y t1z t1t
         t2x t2y t2z t2t t3x t3y t3z t3t
         d0 d1 d2 d3 (hide (B.le_nat vk)) (hide (SZ.v i2));
    i := i2;
  };
  let vi = !i;
  W.sz_zero vi;
  with wx wy wz wt.
    assert (A.pts_to ox wx ** A.pts_to oy wy **
            A.pts_to oz wz ** A.pts_to ot wt);
  hi_end wx wy wz wt vk;
  ()
}

#pop-options

(** {2 The multiplication} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [point_mul_g_win o ks] is [o := [ks] G], up to [point_equal]. *)
fn point_mul_g_win (ox oy oz ot: A.array S64.t) (ks: A.array S8.t)
                   (#vox #voy #voz #vot: erased (Seq.seq S64.t))
                   (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl)
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ks #pk vk **
  pure (P.pt_ok wx wy wz wt /\ GR.on_curve (P.pt wx wy wz wt) /\
        E.point_equal (P.pt wx wy wz wt) (E.point_mul_g vk))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  let z = S64.zero;
  let mut px = [| z; 5sz |]; A.pts_to_len px;
  let mut py = [| z; 5sz |]; A.pts_to_len py;
  let mut pz = [| z; 5sz |]; A.pts_to_len pz;
  let mut pw = [| z; 5sz |]; A.pts_to_len pw;
  let mut ux = [| z; 5sz |]; A.pts_to_len ux;
  let mut uy = [| z; 5sz |]; A.pts_to_len uy;
  let mut uz = [| z; 5sz |]; A.pts_to_len uz;
  let mut ut = [| z; 5sz |]; A.pts_to_len ut;
  let mut sx = [| z; 5sz |]; A.pts_to_len sx;
  let mut sy = [| z; 5sz |]; A.pts_to_len sy;
  let mut sz = [| z; 5sz |]; A.pts_to_len sz;
  let mut st = [| z; 5sz |]; A.pts_to_len st;
  let mut t0x = [| z; 80sz |]; A.pts_to_len t0x;
  let mut t0y = [| z; 80sz |]; A.pts_to_len t0y;
  let mut t0z = [| z; 80sz |]; A.pts_to_len t0z;
  let mut t0t = [| z; 80sz |]; A.pts_to_len t0t;
  let mut t1x = [| z; 80sz |]; A.pts_to_len t1x;
  let mut t1y = [| z; 80sz |]; A.pts_to_len t1y;
  let mut t1z = [| z; 80sz |]; A.pts_to_len t1z;
  let mut t1t = [| z; 80sz |]; A.pts_to_len t1t;
  let mut t2x = [| z; 80sz |]; A.pts_to_len t2x;
  let mut t2y = [| z; 80sz |]; A.pts_to_len t2y;
  let mut t2z = [| z; 80sz |]; A.pts_to_len t2z;
  let mut t2t = [| z; 80sz |]; A.pts_to_len t2t;
  let mut t3x = [| z; 80sz |]; A.pts_to_len t3x;
  let mut t3y = [| z; 80sz |]; A.pts_to_len t3y;
  let mut t3z = [| z; 80sz |]; A.pts_to_len t3z;
  let mut t3t = [| z; 80sz |]; A.pts_to_len t3t;
  A.pts_to_len px; A.pts_to_len py; A.pts_to_len pz; A.pts_to_len pw;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz; A.pts_to_len st;
  A.pts_to_len t0x; A.pts_to_len t0y; A.pts_to_len t0z; A.pts_to_len t0t;
  A.pts_to_len t1x; A.pts_to_len t1y; A.pts_to_len t1z; A.pts_to_len t1t;
  A.pts_to_len t2x; A.pts_to_len t2y; A.pts_to_len t2z; A.pts_to_len t2t;
  A.pts_to_len t3x; A.pts_to_len t3y; A.pts_to_len t3z; A.pts_to_len t3t;

  build_tables t0x t0y t0z t0t t1x t1y t1z t1t
               t2x t2y t2z t2t t3x t3y t3z t3t
               px py pz pw;
  win_loop ox oy oz ot ux uy uz ut sx sy sz st
           t0x t0y t0z t0t t1x t1y t1z t1t
           t2x t2y t2z t2t t3x t3y t3z t3t ks;
  ()
}

#pop-options
