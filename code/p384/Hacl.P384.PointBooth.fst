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

(** Signed digits for the fixed-base window.

    {!Hacl.P384.PointMulG} reads each sixty-four-bit piece of the scalar
    as thirteen signed five-bit digits ({!Spec.Group.Booth6}) against a
    table of the affine multiples [1 .. 16] of a base point.  This module
    has the pieces it is built from:

    - [aent] / [atok], what such a table holds: entry [d] is the
      [(d + 1)]-th multiple, with an implicit [z] of one;
    - [win_dbl5], five doublings;
    - [bwin], [bsgn], [bmag], a digit off a limb, branch-free;
    - [win_sadd], one signed addition: select the magnitude's entry,
      negate its [y] under the sign mask, add, and keep the old value
      when the digit is zero.

    The one new fact about the group is {!neg_add}: adding the negation of
    [d P] to [(e + d) P] is [e P]. *)
module Hacl.P384.PointBooth

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Bignum.Base
open Hacl.P384.Field
open Hacl.P384.Point
open Hacl.P384.PointWin

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module GR = Spec.P384.Group
module SM = Spec.P384.Smul
module B = Spec.Group.Booth6
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 What an affine table holds} *)

[@@"opaque_to_smt"]
let aent (tx ty: Seq.seq S64.t) (p: P.proj_point) (n d: nat) : prop =
  felem (entry tx d) /\ felem (entry ty d) /\
  GR.on_curve (fev (entry tx d), fev (entry ty d), P.fone) /\
  GR.peq (fev (entry tx d), fev (entry ty d), P.fone) (SM.smul ((d + 1) * n) p)

let atok (tx ty: Seq.seq S64.t) (p: P.proj_point) (n: nat) : prop =
  forall (d: nat). d < 16 ==> aent tx ty p n d

let aent_intro (tx ty: Seq.seq S64.t) (p: P.proj_point) (n d: nat)
  : Lemma (requires
             felem (entry tx d) /\ felem (entry ty d) /\
             GR.on_curve (fev (entry tx d), fev (entry ty d), P.fone) /\
             GR.peq (fev (entry tx d), fev (entry ty d), P.fone)
                    (SM.smul ((d + 1) * n) p))
          (ensures aent tx ty p n d)
  = reveal_opaque (`%aent) aent

(** Reading an entry back: an affine point, as a triple with [z = 1]. *)
let atok_get (tx ty: Seq.seq S64.t) (p: P.proj_point) (n d: nat)
  : Lemma (requires atok tx ty p n /\ d < 16)
          (ensures felem (entry tx d) /\ felem (entry ty d) /\
                   GR.on_curve (fev (entry tx d), fev (entry ty d), P.fone) /\
                   GR.peq (fev (entry tx d), fev (entry ty d), P.fone)
                          (SM.smul ((d + 1) * n) p))
  = reveal_opaque (`%aent) aent

(** {2 Subtracting a multiple} *)

let neg_add (p o s: P.proj_point) (e d: nat)
  : Lemma (requires GR.on_curve p /\ GR.on_curve o /\ GR.on_curve s /\
                    GR.peq o (SM.smul (e + d) p) /\ GR.peq s (SM.smul d p))
          (ensures GR.on_curve (P.point_add o (P.point_negate s)) /\
                   GR.peq (P.point_add o (P.point_negate s)) (SM.smul e p))
  = let a = SM.smul e p in
    let ns = P.point_negate s in
    SM.smul_ok e p;
    SM.smul_ok (e + d) p;
    GR.point_negate_on_curve s;
    GR.point_at_infinity_on_curve ();
    SM.smul_add_congr e d p a s;
    let as_ = P.point_add a s in
    GR.peq_sym as_ (SM.smul (e + d) p);
    GR.peq_trans o (SM.smul (e + d) p) as_;
    GR.peq_refl ns;
    GR.point_add_on_curve o ns;
    GR.point_add_on_curve as_ ns;
    GR.point_add_congr o as_ ns ns;
    GR.point_add_assoc_law a s ns;
    let sn = P.point_add s ns in
    GR.point_add_on_curve s ns;
    GR.point_add_on_curve ns s;
    GR.point_add_on_curve a sn;
    GR.point_add_comm_law s ns;
    GR.point_add_negate s;
    GR.peq_trans sn (P.point_add ns s) P.point_at_infinity;
    GR.peq_refl a;
    GR.point_add_congr a a sn P.point_at_infinity;
    GR.point_add_on_curve a P.point_at_infinity;
    GR.point_add_on_curve P.point_at_infinity a;
    GR.point_add_comm_law a P.point_at_infinity;
    GR.point_add_identity a;
    GR.peq_trans (P.point_add a sn) (P.point_add a P.point_at_infinity)
                 (P.point_add P.point_at_infinity a);
    GR.peq_trans (P.point_add a sn) (P.point_add P.point_at_infinity a) a;
    GR.peq_trans (P.point_add as_ ns) (P.point_add a sn) a;
    GR.peq_trans (P.point_add o ns) (P.point_add as_ ns) a

let fsub_zero (y: P.felem) : Lemma (P.fsub P.fzero y == P.fneg y) = ()

(** The selected entry is [(idx + 1) n]; when the digit is not zero that
    is its magnitude, and the sum is the next partial value. *)
let sadd_pos (ox oy oz ex ey sy ux uy uz: Seq.seq S64.t) (p: P.proj_point)
            (e e' m n: nat) (neg: bool)
  : Lemma (requires
             oc p /\ rep ox oy oz e p /\
             GR.on_curve (fev ex, fev ey, P.fone) /\
             GR.peq (fev ex, fev ey, P.fone) (SM.smul (m * n) p) /\
             fev sy == (if neg then P.fsub P.fzero (fev ey) else fev ey) /\
             pt ux uy uz == P.point_add (pt ox oy oz) (fev ex, fev sy, P.fone) /\
             (not neg ==> e' == e + m * n) /\ (neg ==> e == e' + m * n))
          (ensures rep ux uy uz e' p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    fsub_zero (fev ey);
    if neg then
      neg_add p (pt ox oy oz) (fev ex, fev ey, P.fone) e' (m * n)
    else
      SM.smul_add_congr e (m * n) p (pt ox oy oz) (fev ex, fev sy, P.fone)

let sadd_ok (ox oy oz ex ey sy ux uy uz: Seq.seq S64.t) (p: P.proj_point)
            (e e' m n d: nat) (neg: bool)
  : Lemma (requires
             oc p /\ rep ox oy oz e p /\
             GR.on_curve (fev ex, fev ey, P.fone) /\
             GR.peq (fev ex, fev ey, P.fone) (SM.smul ((d + 1) * n) p) /\
             (m <> 0 ==> d + 1 == m) /\
             fev sy == (if neg then P.fsub P.fzero (fev ey) else fev ey) /\
             pt ux uy uz == P.point_add (pt ox oy oz) (fev ex, fev sy, P.fone) /\
             (not neg ==> e' == e + m * n) /\ (neg ==> e == e' + m * n))
          (ensures m <> 0 ==> rep ux uy uz e' p)
  = if m <> 0 then
      sadd_pos ox oy oz ex ey sy ux uy uz p e e' m n neg

(** And a zero digit keeps what was there. *)
let keep_ok (ox oy oz ux uy uz wx wy wz: Seq.seq S64.t) (p: P.proj_point)
            (e e': nat) (zero: bool)
  : Lemma (requires rep ox oy oz e p /\ (zero ==> e' == e) /\
                    (not zero ==> rep ux uy uz e' p) /\
                    fev wx == (if zero then fev ox else fev ux) /\
                    fev wy == (if zero then fev oy else fev uy) /\
                    fev wz == (if zero then fev oz else fev uz))
          (ensures rep wx wy wz e' p)
  = if zero then rep_fcopy ox oy oz wx wy wz e' p
    else rep_fcopy ux uy uz wx wy wz e' p

(** {2 Digits} *)

let win_shr (l: nat) (i: pos)
  : Lemma (2 * l / pow2 (5 * i) == l / pow2 (5 * i - 1))
  = Math.pow2_plus 1 (5 * i - 1);
    assert_norm (pow2 1 == 2);
    Math.division_multiplication_lemma (2 * l) 2 (pow2 (5 * i - 1))

let win_zero (l: nat) : Lemma (requires l < pow2 64)
                              (ensures (2 * l) % pow2 64 % 64 == B.win l 0)
  = assert_norm (pow2 0 == 1);
    assert_norm (pow2 64 == 64 * pow2 58);
    Math.modulo_modulo_lemma (2 * l) 64 (pow2 58)

(** The six-bit window of a piece at digit [i]: the bits [5i - 1] up, or
    the piece shifted left by one at the bottom. *)
inline_for_extraction
let bwin (l: S64.t) (i: U32.t { U32.v i <= 12 })
  : r: S64.t { S64.v r == B.win (S64.v l) (U32.v i) }
  = S64.logand_mask_low (S64.shift_left l 1ul) 6ul;
    assert_norm (pow2 6 == 64);
    if U32.eq i 0ul then begin
      win_zero (S64.v l);
      S64.logand (S64.shift_left l 1ul) (S64.mask_low 6ul)
    end else begin
      let s = U32.sub (U32.mul 5ul i) 1ul in
      win_shr (S64.v l) (U32.v i);
      S64.logand_mask_low (S64.shift_right l s) 6ul;
      S64.logand (S64.shift_right l s) (S64.mask_low 6ul)
    end

(** The sign, as a mask. *)
inline_for_extraction
let bsgn (w: S64.t { S64.v w < 64 })
  : r: S64.t { is_mask r /\ (S64.v r == 0 <==> S64.v w / 32 == 0) }
  = assert_norm (pow2 5 == 32);
    S64.sub_mod S64.zero (S64.shift_right w 5ul)

(** And the magnitude. *)
inline_for_extraction
let bmag (w: S64.t { S64.v w < 64 })
  : r: S64.t { S64.v r == (if S64.v w / 32 = 0 then (S64.v w + 1) / 2
                          else 32 - (S64.v w + 1) / 2) }
  = assert_norm (pow2 1 == 2);
    let y = S64.shift_right (S64.add_mod w (S64.classify 1uL)) 1ul in
    S64.select (bsgn w) (S64.sub_mod (S64.classify 32uL) y) y

(** Which entry a magnitude selects: [m - 1], or the last when [m] is zero
    (which is then added and thrown away). *)
let idx_ok (m: nat) (x: nat)
  : Lemma (requires m <= 16 /\ x == (m - 1) % pow2 64 % pow2 4)
          (ensures (if m = 0 then x == 15 else x == m - 1))
  = assert_norm (pow2 4 == 16);
    assert_norm (pow2 64 == 16 * pow2 60);
    if m = 0 then Math.lemma_mod_plus (pow2 64 - 1) (-1) (pow2 64) else ();
    if m = 0 then Math.modulo_modulo_lemma (pow2 64 - 1) 16 (pow2 60) else ()

#pop-options

(** {2 Five doublings} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn win_dbl5 (ox oy oz ux uy uz: A.array S64.t)
            (p: erased P.proj_point) (e: erased nat)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        pok vox voy voz /\ oc (reveal p) /\
        rep vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
        pok wx wy wz /\ rep wx wy wz (32 * reveal e) (reveal p))
{
  win_jin ox oy oz ux uy uz p e;
  win_jdbl ox oy oz ux uy uz p e;
  with a1x a1y a1z. assert (A.pts_to ox a1x ** A.pts_to oy a1y ** A.pts_to oz a1z);
  jrs_cong a1x a1y a1z (2 * reveal e) (2 * reveal e) p;
  win_jdbl ox oy oz ux uy uz p (hide (2 * reveal e));
  with a2x a2y a2z. assert (A.pts_to ox a2x ** A.pts_to oy a2y ** A.pts_to oz a2z);
  jrs_cong a2x a2y a2z (2 * (2 * reveal e)) (4 * reveal e) p;
  win_jdbl ox oy oz ux uy uz p (hide (4 * reveal e));
  with a3x a3y a3z. assert (A.pts_to ox a3x ** A.pts_to oy a3y ** A.pts_to oz a3z);
  jrs_cong a3x a3y a3z (2 * (4 * reveal e)) (8 * reveal e) p;
  win_jdbl ox oy oz ux uy uz p (hide (8 * reveal e));
  with a4x a4y a4z. assert (A.pts_to ox a4x ** A.pts_to oy a4y ** A.pts_to oz a4z);
  jrs_cong a4x a4y a4z (2 * (8 * reveal e)) (16 * reveal e) p;
  win_jdbl ox oy oz ux uy uz p (hide (16 * reveal e));
  with a5x a5y a5z. assert (A.pts_to ox a5x ** A.pts_to oy a5y ** A.pts_to oz a5z);
  jrs_cong a5x a5y a5z (2 * (16 * reveal e)) (32 * reveal e) p;
  win_jout ox oy oz ux uy uz p (hide (32 * reveal e));
  ()
}

#pop-options

(** {2 One signed addition}

    [o] holds [e P]; afterwards it holds [e' P], where [e' = e + m n] for
    a positive digit and [e = e' + m n] for a negative one.  The table is
    the sixteen affine multiples [n P .. 16 n P]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn win_sadd (ox oy oz ux uy uz sx sy: A.array S64.t)
            (tx ty: A.array S64.t) (mag sm: S64.t)
            (p: erased P.proj_point) (n: erased nat)
            (e e': erased nat)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
            (#vsx #vsy: erased (Seq.seq S64.t))
            (#ptx #pty: perm) (#vtx #vty: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty **
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\
        Seq.length vtx == 96 /\ Seq.length vty == 96 /\
        pok vox voy voz /\ oc (reveal p) /\
        rep vox voy voz e (reveal p) /\
        atok vtx vty (reveal p) (reveal n) /\
        S64.v mag <= 16 /\ is_mask sm /\
        (S64.v sm == 0 ==> reveal e' == reveal e + S64.v mag * reveal n) /\
        (S64.v sm <> 0 ==> reveal e == reveal e' + S64.v mag * reveal n))
ensures exists* (wx wy wz wux wuy wuz wsx wsy: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
        Seq.length wsx == 6 /\ Seq.length wsy == 6 /\
        pok wx wy wz /\ rep wx wy wz (reveal e') (reveal p))
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
  table_select sx tx 6sz idx d;
  table_select sy ty 6sz idx d;
  entry_def vtx (reveal d); entry_def vty (reveal d);
  with wsx wsy. assert (A.pts_to sx wsx ** A.pts_to sy wsy);
  atok_get vtx vty (reveal p) (reveal n) (reveal d);
  fzero ux;
  fsub uy ux sy;
  fcsel sy uy sm;
  with nsy. assert (A.pts_to sy nsy);
  point_madd ux uy uz ox oy oz sx sy;
  with u1x u1y u1z. assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z);
  sadd_ok vox voy voz wsx wsy nsy u1x u1y u1z (reveal p)
          (reveal e) (reveal e') (S64.v mag) (reveal n) (reveal d) (S64.v sm <> 0);
  let zm = S64.eq_mask mag S64.zero;
  let nz = S64.eq_mask zm S64.zero;
  fcsel ox ux nz; fcsel oy uy nz; fcsel oz uz nz;
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  keep_ok vox voy voz u1x u1y u1z wx wy wz (reveal p)
          (reveal e) (reveal e') (S64.v mag = 0);
  pok_intro wx wy wz;
  ()
}

#pop-options
