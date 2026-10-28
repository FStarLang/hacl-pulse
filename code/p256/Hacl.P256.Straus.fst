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

(** The double multiplication [[u1] G + [u2] Q] of verification, on one
    doubling chain.

    Both scalars are read as fifty-two signed five-bit digits
    ({!Spec.Group.Booth4.hb}), the same digits {!Hacl.P256.PointMulV}
    uses.  Each rung doubles five times and then adds two entries: one
    from the affine table of [1 G .. 16 G] that the fixed-base comb
    already compiles in ({!Hacl.P256.Win0}), with a mixed addition, and
    one from the projective table of [1 Q .. 16 Q] built at the start.
    That is 255 doublings for the pair, where computing the two products
    separately costs 255 for [Q] and sixty-five more for [G].

    The code is the same constant-time code as the single
    multiplications -- every digit is read and every entry is selected
    with a mask -- though nothing here is secret.  What is new is only
    the invariant: the accumulator is equivalent to
    [lin2 a b G Q = [a] G + [b] Q] ({!Spec.Group.Smul.lin2}), not to a
    multiple of one point.  The five doublings are
    {!Hacl.P256.PointBooth.win_dbl5} itself, run against the current
    target [T = [a] G + [b] Q] as its base: it turns [1 T] into
    [32 T], and {!lin_32} turns that into [[32 a] G + [32 b] Q].

    This is {!Hacl.P384.Straus} at four limbs. *)
module Hacl.P256.Straus

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
open Hacl.P256.PointMulV

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module GR = Spec.P256.Group
module SM = Spec.P256.Smul
module G = Spec.Group.Smul
module B = Spec.Group.Booth4
module Tbl = Hacl.Impl.Table
module T0 = Hacl.P256.Win0
module Mem = Hacl.Mem
module Math = FStar.Math.Lemmas
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The invariant} *)

(** The record's fields are the curve's operations. *)
let pg_facts (_: unit)
  : Lemma (SM.pg.G.ok == GR.on_curve /\ SM.pg.G.eqv == GR.peq /\
           SM.pg.G.add == P.point_add /\ SM.pg.G.dbl == P.point_double /\
           SM.pg.G.zero == P.point_at_infinity)
  = assert_norm (SM.pg.G.ok == GR.on_curve /\ SM.pg.G.eqv == GR.peq /\
                 SM.pg.G.add == P.point_add /\ SM.pg.G.dbl == P.point_double /\
                 SM.pg.G.zero == P.point_at_infinity)

[@@"opaque_to_smt"]
let lin (a b: nat) (q: P.proj_point) : GTot P.proj_point = G.lin2 SM.pg a b P.g q

let lin_ok (a b: nat) (q: P.proj_point)
  : Lemma (requires GR.on_curve q) (ensures GR.on_curve (lin a b q))
  = reveal_opaque (`%lin) lin;
    GR.g_on_curve ();
    pg_facts ();
    G.lin2_ok SM.pg a b P.g q

(** The three things a rung does, at this curve. *)
let lin_dbl (m n: nat) (q s: P.proj_point)
  : Lemma (requires GR.on_curve q /\ GR.on_curve s /\ GR.peq s (lin m n q))
          (ensures GR.on_curve (P.point_double s) /\
                   GR.peq (P.point_double s) (lin (2 * m) (2 * n) q))
  = reveal_opaque (`%lin) lin;
    GR.g_on_curve ();
    pg_facts ();
    G.lin2_dbl SM.pg m n P.g q s

let lin_addl (m n d: nat) (q o e: P.proj_point)
  : Lemma (requires GR.on_curve q /\ GR.on_curve o /\ GR.on_curve e /\
                    GR.peq o (lin m n q) /\ GR.peq e (SM.smul d P.g))
          (ensures GR.on_curve (P.point_add o e) /\
                   GR.peq (P.point_add o e) (lin (m + d) n q))
  = reveal_opaque (`%lin) lin;
    GR.g_on_curve ();
    pg_facts ();
    G.lin2_addl SM.pg m n d P.g q o e

let lin_addr (m n d: nat) (q o e: P.proj_point)
  : Lemma (requires GR.on_curve q /\ GR.on_curve o /\ GR.on_curve e /\
                    GR.peq o (lin m n q) /\ GR.peq e (SM.smul d q))
          (ensures GR.on_curve (P.point_add o e) /\
                   GR.peq (P.point_add o e) (lin m (n + d) q))
  = reveal_opaque (`%lin) lin;
    GR.g_on_curve ();
    pg_facts ();
    G.lin2_addr SM.pg m n d P.g q o e

(** [srep x y z a b q]: the triple reads as a point on the curve
    equivalent to [[a] G + [b] Q].  Opaque for the same reason as
    {!Hacl.P256.PointWin.rep}. *)
[@@"opaque_to_smt"]
let srep (x y z: Seq.seq S64.t) (a b: nat) (q: P.proj_point) : prop =
  GR.on_curve (pt x y z) /\ GR.peq (pt x y z) (lin a b q)

(** One doubling of both coefficients. *)
let lin_dbl_step (n a b: nat) (q: P.proj_point)
  : Lemma (requires GR.on_curve q /\
                    GR.on_curve (SM.smul n (lin a b q)) /\
                    GR.peq (SM.smul n (lin a b q)) (lin (n * a) (n * b) q))
          (ensures GR.on_curve (SM.smul (2 * n) (lin a b q)) /\
                   GR.peq (SM.smul (2 * n) (lin a b q))
                          (lin ((2 * n) * a) ((2 * n) * b) q))
  = let t = lin a b q in
    let s = SM.smul n t in
    lin_ok a b q;
    GR.peq_refl s;
    SM.smul_dbl_congr n t s;
    lin_dbl (n * a) (n * b) q s;
    Math.paren_mul_right 2 n a;
    Math.paren_mul_right 2 n b;
    SM.smul_ok n t;
    SM.smul_ok (2 * n) t;
    lin_ok ((2 * n) * a) ((2 * n) * b) q;
    GR.point_double_on_curve s;
    GR.peq_sym (P.point_double s) (SM.smul (2 * n) t);
    GR.peq_trans (SM.smul (2 * n) t) (P.point_double s)
                 (lin ((2 * n) * a) ((2 * n) * b) q)

(** One copy of a combination is the combination. *)
let lin_one (a b: nat) (q: P.proj_point)
  : Lemma (requires GR.on_curve q)
          (ensures GR.on_curve (SM.smul 1 (lin a b q)) /\
                   GR.peq (SM.smul 1 (lin a b q)) (lin a b q))
  = lin_ok a b q;
    SM.smul_one (lin a b q);
    SM.smul_ok 1 (lin a b q)

let one_mul (a: nat) : Lemma (1 * a == a) = ()

let lin_one' (a b: nat) (q: P.proj_point)
  : Lemma (requires GR.on_curve q)
          (ensures GR.on_curve (SM.smul 1 (lin a b q)) /\
                   GR.peq (SM.smul 1 (lin a b q)) (lin (1 * a) (1 * b) q))
  = one_mul a;
    one_mul b;
    lin_one a b q

(** Thirty-two copies, five doublings at a time. *)
let lin_32 (a b: nat) (q: P.proj_point)
  : Lemma (requires GR.on_curve q)
          (ensures GR.on_curve (SM.smul 32 (lin a b q)) /\
                   GR.peq (SM.smul 32 (lin a b q)) (lin (32 * a) (32 * b) q))
  = lin_one' a b q;
    lin_dbl_step 1 a b q;
    lin_dbl_step 2 a b q;
    lin_dbl_step 4 a b q;
    lin_dbl_step 8 a b q;
    lin_dbl_step 16 a b q

(** Into and out of the single-base form {!win_dbl5} speaks. *)
let to_rep (x y z: Seq.seq S64.t) (a b: nat) (q: P.proj_point)
  : Lemma (requires srep x y z a b q /\ GR.on_curve q)
          (ensures oc (lin a b q) /\ rep x y z 1 (lin a b q))
  = reveal_opaque (`%srep) srep;
    reveal_opaque (`%rep) rep;
    let t = lin a b q in
    lin_ok a b q;
    oc_intro t;
    SM.smul_one t;
    SM.smul_ok 1 t;
    GR.peq_sym (SM.smul 1 t) t;
    GR.peq_trans (pt x y z) t (SM.smul 1 t)

let from_rep32 (x y z: Seq.seq S64.t) (a b: nat) (q: P.proj_point)
  : Lemma (requires rep x y z (32 * 1) (lin a b q) /\ GR.on_curve q)
          (ensures srep x y z (32 * a) (32 * b) q)
  = reveal_opaque (`%srep) srep;
    reveal_opaque (`%rep) rep;
    lin_32 a b q;
    lin_ok (32 * a) (32 * b) q;
    GR.peq_trans (pt x y z) (SM.smul 32 (lin a b q)) (lin (32 * a) (32 * b) q)

(** {2 Signed additions} *)

(** If [o = x + s] then [o - s = x]. *)
let neg_sub (x o s: P.proj_point)
  : Lemma (requires GR.on_curve x /\ GR.on_curve o /\ GR.on_curve s /\
                    GR.peq o (P.point_add x s))
          (ensures GR.on_curve (P.point_add o (P.point_negate s)) /\
                   GR.peq (P.point_add o (P.point_negate s)) x)
  = let ns = P.point_negate s in
    let as_ = P.point_add x s in
    GR.point_negate_on_curve s;
    GR.point_at_infinity_on_curve ();
    GR.point_add_on_curve x s;
    GR.peq_refl ns;
    GR.point_add_on_curve o ns;
    GR.point_add_on_curve as_ ns;
    GR.point_add_congr o as_ ns ns;
    GR.point_add_assoc_law x s ns;
    let sn = P.point_add s ns in
    GR.point_add_on_curve s ns;
    GR.point_add_on_curve ns s;
    GR.point_add_on_curve x sn;
    GR.point_add_comm_law s ns;
    GR.point_add_negate s;
    GR.peq_trans sn (P.point_add ns s) P.point_at_infinity;
    GR.peq_refl x;
    GR.point_add_congr x x sn P.point_at_infinity;
    GR.point_add_on_curve x P.point_at_infinity;
    GR.point_add_on_curve P.point_at_infinity x;
    GR.point_add_comm_law x P.point_at_infinity;
    GR.point_add_identity x;
    GR.peq_trans (P.point_add x sn) (P.point_add x P.point_at_infinity)
                 (P.point_add P.point_at_infinity x);
    GR.peq_trans (P.point_add x sn) (P.point_add P.point_at_infinity x) x;
    GR.peq_trans (P.point_add as_ ns) (P.point_add x sn) x;
    GR.peq_trans (P.point_add o ns) (P.point_add as_ ns) x

(** A digit of [u1]: the entry [s] is [[m] G], added or subtracted. *)
let sadd_l (o s u: P.proj_point) (q: P.proj_point) (a a' b m: nat) (neg: bool)
  : Lemma (requires GR.on_curve q /\ GR.on_curve o /\ GR.peq o (lin a b q) /\
                    GR.on_curve s /\ GR.peq s (SM.smul m P.g) /\
                    u == P.point_add o (if neg then P.point_negate s else s) /\
                    (not neg ==> a' == a + m) /\ (neg ==> a == a' + m))
          (ensures GR.on_curve u /\ GR.peq u (lin a' b q))
  = lin_ok a b q;
    lin_ok a' b q;
    if neg then begin
      let x = lin a' b q in
      GR.peq_refl x;
      lin_addl a' b m q x s;
      GR.point_add_on_curve x s;
      GR.peq_sym (P.point_add x s) (lin a b q);
      GR.peq_trans o (lin a b q) (P.point_add x s);
      neg_sub x o s
    end else
      lin_addl a b m q o s

(** A digit of [u2]: the entry [s] is [[m] Q]. *)
let sadd_r (o s u: P.proj_point) (q: P.proj_point) (a b b' m: nat) (neg: bool)
  : Lemma (requires GR.on_curve q /\ GR.on_curve o /\ GR.peq o (lin a b q) /\
                    GR.on_curve s /\ GR.peq s (SM.smul m q) /\
                    u == P.point_add o (if neg then P.point_negate s else s) /\
                    (not neg ==> b' == b + m) /\ (neg ==> b == b' + m))
          (ensures GR.on_curve u /\ GR.peq u (lin a b' q))
  = lin_ok a b q;
    lin_ok a b' q;
    if neg then begin
      let x = lin a b' q in
      GR.peq_refl x;
      lin_addr a b' m q x s;
      GR.point_add_on_curve x s;
      GR.peq_sym (P.point_add x s) (lin a b q);
      GR.peq_trans o (lin a b q) (P.point_add x s);
      neg_sub x o s
    end else
      lin_addr a b m q o s

(** The same two, at the limb level, in the shape the Pulse code leaves:
    a table entry [(ex, ey, ez)] at index [d], its [y] possibly negated
    into [sy].  Only meaningful when the digit [m] is not zero; a zero
    digit's sum is discarded by {!skeep}. *)
let sadd_g_ok (ox oy oz ex ey sy ux uy uz: Seq.seq S64.t) (ez: P.felem)
              (q: P.proj_point) (a a' b m d: nat) (neg: bool)
  : Lemma (requires
             GR.on_curve q /\ srep ox oy oz a b q /\
             GR.on_curve (fev ex, fev ey, ez) /\
             GR.peq (fev ex, fev ey, ez) (SM.smul ((d + 1) * 1) P.g) /\
             (m <> 0 ==> d + 1 == m) /\
             fev sy == (if neg then P.fsub P.fzero (fev ey) else fev ey) /\
             pt ux uy uz == P.point_add (pt ox oy oz) (fev ex, fev sy, ez) /\
             (not neg ==> a' == a + m * 1) /\ (neg ==> a == a' + m * 1))
          (ensures m <> 0 ==> srep ux uy uz a' b q)
  = if m <> 0 then begin
      reveal_opaque (`%srep) srep;
      fsub_zero (fev ey);
      sadd_l (pt ox oy oz) (fev ex, fev ey, ez) (pt ux uy uz) q a a' b m neg
    end

let sadd_q_ok (ox oy oz ex ey sy ux uy uz: Seq.seq S64.t) (ez: P.felem)
              (q: P.proj_point) (a b b' m d: nat) (neg: bool)
  : Lemma (requires
             GR.on_curve q /\ srep ox oy oz a b q /\
             GR.on_curve (fev ex, fev ey, ez) /\
             GR.peq (fev ex, fev ey, ez) (SM.smul ((d + 1) * 1) q) /\
             (m <> 0 ==> d + 1 == m) /\
             fev sy == (if neg then P.fsub P.fzero (fev ey) else fev ey) /\
             pt ux uy uz == P.point_add (pt ox oy oz) (fev ex, fev sy, ez) /\
             (not neg ==> b' == b + m * 1) /\ (neg ==> b == b' + m * 1))
          (ensures m <> 0 ==> srep ux uy uz a b' q)
  = if m <> 0 then begin
      reveal_opaque (`%srep) srep;
      fsub_zero (fev ey);
      sadd_r (pt ox oy oz) (fev ex, fev ey, ez) (pt ux uy uz) q a b b' m neg
    end

(** A zero digit changes neither coefficient. *)
let zero_dig (a a' m: nat) (neg: bool)
  : Lemma (requires (not neg ==> a' == a + m * 1) /\ (neg ==> a == a' + m * 1))
          (ensures m == 0 ==> a' == a)
  = ()

(** A zero digit keeps what was there. *)
let skeep (ox oy oz ux uy uz wx wy wz: Seq.seq S64.t) (q: P.proj_point)
          (a b a' b': nat) (zero: bool)
  : Lemma (requires srep ox oy oz a b q /\ (zero ==> a' == a /\ b' == b) /\
                    (not zero ==> srep ux uy uz a' b' q) /\
                    fev wx == (if zero then fev ox else fev ux) /\
                    fev wy == (if zero then fev oy else fev uy) /\
                    fev wz == (if zero then fev oz else fev uz))
          (ensures srep wx wy wz a' b' q)
  = reveal_opaque (`%srep) srep

(** {2 The two ends} *)

let lin_zero (q: P.proj_point)
  : Lemma (requires GR.on_curve q)
          (ensures GR.on_curve P.point_at_infinity /\
                   GR.peq P.point_at_infinity (lin 0 0 q))
  = reveal_opaque (`%lin) lin;
    GR.g_on_curve ();
    pg_facts ();
    G.lin2_zero SM.pg P.g q

let srep_zero (x y z: Seq.seq S64.t) (q: P.proj_point) (k1 k2: nat)
  : Lemma (requires GR.on_curve q /\ pt x y z == P.point_at_infinity /\
                    k1 < pow2 256 /\ k2 < pow2 256)
          (ensures srep x y z (32 * B.hb k1 52) (32 * B.hb k2 52) q)
  = hb_top52 k1;
    hb_top52 k2;
    lin_zero q;
    reveal_opaque (`%srep) (srep x y z 0 0 q);
    assert (srep x y z 0 0 q)

let srep_done (x y z: Seq.seq S64.t) (q: P.proj_point) (k1 k2: nat)
  : Lemma (requires GR.on_curve q /\ srep x y z k1 k2 q /\
                    k1 < pow2 256 /\ k2 < pow2 256)
          (ensures GR.on_curve (pt x y z) /\
                   GR.on_curve (P.point_mul_double_g k1 k2 q) /\
                   GR.peq (pt x y z) (P.point_mul_double_g k1 k2 q))
  = reveal_opaque (`%lin) lin;
    reveal_opaque (`%srep) srep;
    GR.g_on_curve ();
    SM.point_mul_is_smul k1 P.g;
    SM.point_mul_is_smul k2 q;
    SM.smul_ok k1 P.g;
    SM.smul_ok k2 q;
    let r = P.point_mul_double_g k1 k2 q in
    GR.point_add_on_curve (P.point_mul k1 P.g) (P.point_mul k2 q);
    GR.point_add_congr (P.point_mul k1 P.g) (SM.smul k1 P.g)
                       (P.point_mul k2 q) (SM.smul k2 q);
    lin_ok k1 k2 q;
    GR.peq_sym r (lin k1 k2 q);
    GR.peq_trans (pt x y z) (lin k1 k2 q) r

#pop-options

(** {2 The steps} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn sdbl5 (ox oy oz ux uy uz: A.array S64.t)
         (q: erased P.proj_point) (a b: erased nat)
         (#vox #voy #voz: erased (Seq.seq S64.t))
         (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == 4 /\ Seq.length vuy == 4 /\ Seq.length vuz == 4 /\
        pok vox voy voz /\ GR.on_curve (reveal q) /\
        srep vox voy voz a b (reveal q))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == 4 /\ Seq.length wuy == 4 /\ Seq.length wuz == 4 /\
        pok wx wy wz /\ srep wx wy wz (32 * reveal a) (32 * reveal b) (reveal q))
{
  to_rep vox voy voz a b q;
  win_dbl5 ox oy oz ux uy uz (hide (lin a b q)) (hide 1);
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  from_rep32 wx wy wz a b q;
  ()
}

(** A digit of [u1], against the affine table of [1 G .. 16 G]. *)
fn sadd_g (ox oy oz ux uy uz sx sy: A.array S64.t)
          (tx ty: A.array S64.t) (mag sm: S64.t)
          (q: erased P.proj_point) (a a' b: erased nat)
          (#vox #voy #voz: erased (Seq.seq S64.t))
          (#vux #vuy #vuz: erased (Seq.seq S64.t))
          (#vsx #vsy: erased (Seq.seq S64.t))
          (#ptx #pty: perm) (#vtx #vty: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty **
  pure (Seq.length vux == 4 /\ Seq.length vuy == 4 /\ Seq.length vuz == 4 /\
        Seq.length vsx == 4 /\ Seq.length vsy == 4 /\
        Seq.length vtx == 64 /\ Seq.length vty == 64 /\
        pok vox voy voz /\ GR.on_curve (reveal q) /\
        srep vox voy voz a b (reveal q) /\
        atok vtx vty P.g 1 /\
        S64.v mag <= 16 /\ is_mask sm /\
        (S64.v sm == 0 ==> reveal a' == reveal a + S64.v mag * 1) /\
        (S64.v sm <> 0 ==> reveal a == reveal a' + S64.v mag * 1))
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty **
  pure (Seq.length wux == 4 /\ Seq.length wuy == 4 /\ Seq.length wuz == 4 /\
        Seq.length wsx == 4 /\ Seq.length wsy == 4 /\
        pok wx wy wz /\ srep wx wy wz a' b (reveal q))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy;
  A.pts_to_len tx; A.pts_to_len ty;
  pok_elim vox voy voz;
  let m1 = S64.sub_mod mag (S64.classify 1uL);
  S64.logand_mask_low m1 4ul;
  let idx = S64.logand m1 (S64.mask_low 4ul);
  idx_ok (S64.v mag) (S64.v idx);
  let d : erased nat = hide (S64.v idx);
  entry_fits (reveal d);
  table_select sx tx 4sz idx d;
  table_select sy ty 4sz idx d;
  entry_def vtx (reveal d); entry_def vty (reveal d);
  with wsx wsy. assert (A.pts_to sx wsx ** A.pts_to sy wsy);
  atok_get vtx vty P.g 1 (reveal d);
  fzero ux;
  fsub uy ux sy;
  fcsel sy uy sm;
  with nsy. assert (A.pts_to sy nsy);
  point_madd ux uy uz ox oy oz sx sy;
  with u1x u1y u1z. assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z);
  sadd_g_ok vox voy voz wsx wsy nsy u1x u1y u1z P.fone (reveal q)
            (reveal a) (reveal a') (reveal b) (S64.v mag) (reveal d) (S64.v sm <> 0);
  let zm = S64.eq_mask mag S64.zero;
  let nz = S64.eq_mask zm S64.zero;
  fcsel ox ux nz; fcsel oy uy nz; fcsel oz uz nz;
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  zero_dig (reveal a) (reveal a') (S64.v mag) (S64.v sm <> 0);
  skeep vox voy voz u1x u1y u1z wx wy wz (reveal q)
        (reveal a) (reveal b) (reveal a') (reveal b) (S64.v mag = 0);
  pok_intro wx wy wz;
  ()
}

(** A digit of [u2], against the projective table of [1 Q .. 16 Q]. *)
fn sadd_q (ox oy oz ux uy uz sx sy sz: A.array S64.t)
          (tx ty tz: A.array S64.t) (mag sm: S64.t)
          (q: erased P.proj_point) (a b b': erased nat)
          (#vox #voy #voz: erased (Seq.seq S64.t))
          (#vux #vuy #vuz: erased (Seq.seq S64.t))
          (#vsx #vsy #vsz: erased (Seq.seq S64.t))
          (#ptx #pty #ptz: perm) (#vtx #vty #vtz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty ** A.pts_to tz #ptz vtz **
  pure (Seq.length vux == 4 /\ Seq.length vuy == 4 /\ Seq.length vuz == 4 /\
        Seq.length vsx == 4 /\ Seq.length vsy == 4 /\ Seq.length vsz == 4 /\
        Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        pok vox voy voz /\ GR.on_curve (reveal q) /\
        srep vox voy voz a b (reveal q) /\
        vtok vtx vty vtz (reveal q) 16 /\
        S64.v mag <= 16 /\ is_mask sm /\
        (S64.v sm == 0 ==> reveal b' == reveal b + S64.v mag * 1) /\
        (S64.v sm <> 0 ==> reveal b == reveal b' + S64.v mag * 1))
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty ** A.pts_to tz #ptz vtz **
  pure (Seq.length wux == 4 /\ Seq.length wuy == 4 /\ Seq.length wuz == 4 /\
        Seq.length wsx == 4 /\ Seq.length wsy == 4 /\ Seq.length wsz == 4 /\
        pok wx wy wz /\ srep wx wy wz a b' (reveal q))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  pok_elim vox voy voz;
  let m1 = S64.sub_mod mag (S64.classify 1uL);
  S64.logand_mask_low m1 4ul;
  let idx = S64.logand m1 (S64.mask_low 4ul);
  idx_ok (S64.v mag) (S64.v idx);
  let d : erased nat = hide (S64.v idx);
  entry_fits (reveal d);
  table_select sx tx 4sz idx d;
  table_select sy ty 4sz idx d;
  table_select sz tz 4sz idx d;
  entry_def vtx (reveal d); entry_def vty (reveal d); entry_def vtz (reveal d);
  with wsx wsy wsz. assert (A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz);
  vtok_get vtx vty vtz (reveal q) (reveal d);
  pok_elim wsx wsy wsz;
  fzero ux;
  fsub uy ux sy;
  fcsel sy uy sm;
  with nsy. assert (A.pts_to sy nsy);
  point_add ux uy uz ox oy oz sx sy sz;
  with u1x u1y u1z. assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z);
  sadd_q_ok vox voy voz wsx wsy nsy u1x u1y u1z (fev wsz) (reveal q)
            (reveal a) (reveal b) (reveal b') (S64.v mag) (reveal d) (S64.v sm <> 0);
  let zm = S64.eq_mask mag S64.zero;
  let nz = S64.eq_mask zm S64.zero;
  fcsel ox ux nz; fcsel oy uy nz; fcsel oz uz nz;
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  zero_dig (reveal b) (reveal b') (S64.v mag) (S64.v sm <> 0);
  skeep vox voy voz u1x u1y u1z wx wy wz (reveal q)
        (reveal a) (reveal b) (reveal a) (reveal b') (S64.v mag = 0);
  pok_intro wx wy wz;
  ()
}

#pop-options

(** {2 The ladder} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The rungs, from the top digits down.  On entry [o] is the point at
    infinity, as [[32 hb k1 52] G + [32 hb k2 52] Q]; on exit it is
    [[k1] G + [k2] Q]. *)
fn sloop (ox oy oz ux uy uz sx sy sz: A.array S64.t)
         (gx gy tx ty tz: A.array S64.t) (k1 k2: A.array S64.t)
         (q: erased P.proj_point)
         (#vox #voy #voz: erased (Seq.seq S64.t))
         (#vux #vuy #vuz: erased (Seq.seq S64.t))
         (#vsx #vsy #vsz: erased (Seq.seq S64.t))
         (#pgx #pgy: perm) (#cgx #cgy: erased (Seq.seq S64.t))
         (#vtx #vty #vtz: erased (Seq.seq S64.t))
         (#p1: perm) (#vk1: erased (Seq.seq S64.t))
         (#p2: perm) (#vk2: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to gx #pgx cgx ** A.pts_to gy #pgy cgy **
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to k1 #p1 vk1 ** A.pts_to k2 #p2 vk2 **
  pure (Seq.length vux == 4 /\ Seq.length vuy == 4 /\ Seq.length vuz == 4 /\
        Seq.length vsx == 4 /\ Seq.length vsy == 4 /\ Seq.length vsz == 4 /\
        Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        Seq.length cgx == 64 /\ Seq.length cgy == 64 /\
        Seq.length vk1 == 4 /\ Seq.length vk2 == 4 /\
        atok cgx cgy P.g 1 /\ vtok vtx vty vtz (reveal q) 16 /\
        GR.on_curve (reveal q) /\ pok vox voy voz /\
        srep vox voy voz (32 * B.hb (kv vk1) 52) (32 * B.hb (kv vk2) 52) (reveal q))
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to gx #pgx cgx ** A.pts_to gy #pgy cgy **
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to k1 #p1 vk1 ** A.pts_to k2 #p2 vk2 **
  pure (Seq.length wux == 4 /\ Seq.length wuy == 4 /\ Seq.length wuz == 4 /\
        Seq.length wsx == 4 /\ Seq.length wsy == 4 /\ Seq.length wsz == 4 /\
        pok wx wy wz /\ srep wx wy wz (kv vk1) (kv vk2) (reveal q))
{
  // The top digits go straight into the point at infinity.
  let w1 = vwin k1 51sz;
  let sm1 = bsgn w1;
  let mg1 = bmag w1;
  vdigit_ok (kv vk1) 52 (S64.v w1) (S64.v mg1) (S64.v sm1);
  sadd_g ox oy oz ux uy uz sx sy gx gy mg1 sm1 q
         (hide (32 * B.hb (kv vk1) 52)) (hide (B.hb (kv vk1) 51))
         (hide (32 * B.hb (kv vk2) 52));
  let w2 = vwin k2 51sz;
  let sm2 = bsgn w2;
  let mg2 = bmag w2;
  vdigit_ok (kv vk2) 52 (S64.v w2) (S64.v mg2) (S64.v sm2);
  sadd_q ox oy oz ux uy uz sx sy sz tx ty tz mg2 sm2 q
         (hide (B.hb (kv vk1) 51))
         (hide (32 * B.hb (kv vk2) 52)) (hide (B.hb (kv vk2) 51));

  let mut i = 51sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
    A.pts_to gx #pgx cgx ** A.pts_to gy #pgy cgy **
    A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
    A.pts_to k1 #p1 vk1 ** A.pts_to k2 #p2 vk2 **
    pure (SZ.v vi <= 51 /\
          Seq.length wux == 4 /\ Seq.length wuy == 4 /\ Seq.length wuz == 4 /\
          Seq.length wsx == 4 /\ Seq.length wsy == 4 /\ Seq.length wsz == 4 /\
          pok wx wy wz /\
          srep wx wy wz (B.hb (kv vk1) (SZ.v vi)) (B.hb (kv vk2) (SZ.v vi)) (reveal q))
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let i1 = SZ.sub vi 1sz;
    sdbl5 ox oy oz ux uy uz q
          (hide (B.hb (kv vk1) (SZ.v vi))) (hide (B.hb (kv vk2) (SZ.v vi)));
    let w1 = vwin k1 i1;
    let sm1 = bsgn w1;
    let mg1 = bmag w1;
    vdigit_ok (kv vk1) (SZ.v vi) (S64.v w1) (S64.v mg1) (S64.v sm1);
    sadd_g ox oy oz ux uy uz sx sy gx gy mg1 sm1 q
           (hide (32 * B.hb (kv vk1) (SZ.v vi))) (hide (B.hb (kv vk1) (SZ.v i1)))
           (hide (32 * B.hb (kv vk2) (SZ.v vi)));
    let w2 = vwin k2 i1;
    let sm2 = bsgn w2;
    let mg2 = bmag w2;
    vdigit_ok (kv vk2) (SZ.v vi) (S64.v w2) (S64.v mg2) (S64.v sm2);
    sadd_q ox oy oz ux uy uz sx sy sz tx ty tz mg2 sm2 q
           (hide (B.hb (kv vk1) (SZ.v i1)))
           (hide (32 * B.hb (kv vk2) (SZ.v vi))) (hide (B.hb (kv vk2) (SZ.v i1)));
    i := i1;
  };
  let vi = !i;
  sz_zero vi;
  hb_end (kv vk1);
  hb_end (kv vk2);
  ()
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [point_mul2 o q k1 k2] is [o := [k1] G + [k2] Q], up to [peq]. *)
fn point_mul2 (ox oy oz: A.array S64.t) (qx qy qz: A.array S64.t)
              (k1 k2: A.array S64.t)
              (#vox #voy #voz: erased (Seq.seq S64.t))
              (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
              (#p1: perm) (#vk1: erased (Seq.seq S64.t))
              (#p2: perm) (#vk2: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to k1 #p1 vk1 ** A.pts_to k2 #p2 vk2 **
  pure (Seq.length vox == 4 /\ Seq.length voy == 4 /\ Seq.length voz == 4 /\
        Seq.length vk1 == B4.nl /\ B4.bnd (L4.vals vk1) B4.base /\
        Seq.length vk2 == B4.nl /\ B4.bnd (L4.vals vk2) B4.base /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to k1 #p1 vk1 ** A.pts_to k2 #p2 vk2 **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul_double_g (B4.eval (L4.vals vk1)) (B4.eval (L4.vals vk2)) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz)
               (P.point_mul_double_g (B4.eval (L4.vals vk1)) (B4.eval (L4.vals vk2)) (pt vqx vqy vqz)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len k1; A.pts_to_len k2;
  L4.vals_bnd vk1; L4.vals_bnd vk2;
  kv_bnd vk1;
  kv_bnd vk2;
  oc_intro (pt vqx vqy vqz);
  let z = S64.zero;
  let mut tx = [| z; 64sz |];
  Mem.track tx; A.pts_to_len tx;
  let mut ty = [| z; 64sz |];
  Mem.track ty; A.pts_to_len ty;
  let mut tz = [| z; 64sz |];
  Mem.track tz; A.pts_to_len tz;
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
  let mut sz = [| z; 4sz |];
  Mem.track sz; A.pts_to_len sz;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz;

  pok_intro vqx vqy vqz;
  rep_one vqx vqy vqz (pt vqx vqy vqz);
  build_vtab tx ty tz qx qy qz (hide (pt vqx vqy vqz));
  T0.tbl_ok ();
  let gx = Tbl.table T0.tx_arr 64sz;
  let gy = Tbl.table T0.ty_arr 64sz;
  A.pts_to_len gx; A.pts_to_len gy;
  set_infinity ox oy oz;
  with o0x o0y o0z. assert (A.pts_to ox o0x ** A.pts_to oy o0y ** A.pts_to oz o0z);
  pok_intro o0x o0y o0z;
  srep_zero o0x o0y o0z (pt vqx vqy vqz) (kv vk1) (kv vk2);
  sloop ox oy oz ux uy uz sx sy sz gx gy tx ty tz k1 k2 (hide (pt vqx vqy vqz));
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  pok_elim wx wy wz;
  srep_done wx wy wz (pt vqx vqy vqz) (kv vk1) (kv vk2);
  Tbl.drop_table gx;
  Tbl.drop_table gy;
  Mem.wipe sz 4sz;
  Mem.wipe sy 4sz;
  Mem.wipe sx 4sz;
  Mem.wipe uz 4sz;
  Mem.wipe uy 4sz;
  Mem.wipe ux 4sz;
  Mem.wipe tz 64sz;
  Mem.wipe ty 64sz;
  Mem.wipe tx 64sz;
  ()
}

#pop-options
