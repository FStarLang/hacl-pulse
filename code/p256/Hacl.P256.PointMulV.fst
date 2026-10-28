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

(** Variable-base multiplication with signed five-bit digits.

    The whole 256-bit scalar is read as fifty-two Booth digits in
    [-16 .. 16] ({!Spec.Group.Booth4.hb}, at [a = k]), against a table of
    the projective multiples [1 .. 16] of the point.  That is fifty-two
    additions and 255 doublings, against the four-bit window's sixty-four
    and 256: the top digit is added into the point at infinity directly,
    with no doublings in front of it.

    A digit's six-bit window starts at bit [5 i - 1], so unlike a four-bit
    one it can straddle two limbs; {!vwin} reads both.  The signed addition
    is {!Hacl.P256.PointBooth}'s, with the entry's [z] selected rather than
    fixed at one.  This is {!Hacl.P384.PointMulV} at four limbs. *)
module Hacl.P256.PointMulV

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
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
module SM = Spec.P256.Smul
module B = Spec.Group.Booth4
module Mem = Hacl.Mem
module Math = FStar.Math.Lemmas
module SB = Spec.Bignum
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4
module L64 = Hacl.Impl.Limb64

(** {2 Digits} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let p64 () : Lemma (pow2 64 == 64 * pow2 58) = assert_norm (pow2 64 == 64 * pow2 58)

(** Reducing modulo [2^64] first does not change a residue modulo 64. *)
let mod64 (z: nat) : Lemma (z % pow2 64 % 64 == z % 64)
  = p64 (); Math.modulo_modulo_lemma z 64 (pow2 58)

(** The bottom window: [2k mod 64] is twice the low limb, shifted. *)
let win_bot (k l: nat)
  : Lemma (requires l == k / wt 0 % pow2 64)
          (ensures (2 * l) % pow2 64 % 64 == B.win k 0)
  = assert_norm (pow2 0 == 1);
    assert_norm (wt 0 == 1);
    mod64 (2 * l);
    Math.euclidean_division_definition k (pow2 64);
    assert_norm (2 * pow2 64 == 64 * pow2 59);
    Math.lemma_mod_plus (2 * l) (pow2 59 * (k / pow2 64)) 64

(** The window at digit [i > 0] is the six bits of [k] at [5 i - 1]. *)
let win_pos (k: nat) (i: pos)
  : Lemma (B.win k i == k / pow2 (5 * i - 1) % 64)
  = win_shr k i

(** [n / 2^(64 q)] is its low limb plus [2^64] times the rest. *)
let limb_split (n: nat) (q: nat)
  : Lemma (n / wt q == n / wt q % pow2 64 + pow2 64 * (n / wt (q + 1)))
  = wt_succ q;
    Math.division_multiplication_lemma n (wt q) (pow2 64);
    Math.euclidean_division_definition (n / wt q) (pow2 64)

(** Six bits that cross into the next limb: [lo >> r] plus the next limb
    shifted up into the space above it, all modulo [2^64]. *)
let straddle (n: nat) (q: nat) (r: nat { 59 <= r /\ r < 64 }) (lo hi: nat)
  : Lemma (requires lo == n / wt q % pow2 64 /\ hi == n / wt (q + 1) % pow2 64)
          (ensures n / pow2 (64 * q + r) % 64 ==
                   (lo / pow2 r + hi * pow2 (64 - r) % pow2 64) % pow2 64 % 64)
  = let x = n / wt q in
    let y = n / wt (q + 1) in
    limb_split n q;
    shift_num n q r;
    assert_norm (rad == 64);
    Math.pow2_plus r (64 - r);
    Math.paren_mul_right (pow2 r) (pow2 (64 - r)) y;
    Math.lemma_div_plus lo (pow2 (64 - r) * y) (pow2 r);
    assert (x / pow2 r == lo / pow2 r + pow2 (64 - r) * y);
    let a = lo / pow2 r in
    mod64 (a + hi * pow2 (64 - r) % pow2 64);
    mod64 (hi * pow2 (64 - r));
    Math.lemma_mod_plus_distr_r a (hi * pow2 (64 - r) % pow2 64) 64;
    Math.lemma_mod_plus_distr_r a (hi * pow2 (64 - r)) 64;
    Math.euclidean_division_definition y (pow2 64);
    Math.pow2_plus (64 - r) 64;
    Math.pow2_plus 6 (58 + (64 - r));
    assert_norm (pow2 6 == 64);
    let c = pow2 (64 - r) * y in
    Math.distributivity_add_right (pow2 (64 - r)) hi (pow2 64 * (y / pow2 64));
    Math.paren_mul_right (pow2 (64 - r)) (pow2 64) (y / pow2 64);
    Math.paren_mul_right 64 (pow2 (58 + (64 - r))) (y / pow2 64);
    Math.lemma_mod_plus (pow2 (64 - r) * hi) (pow2 (58 + (64 - r)) * (y / pow2 64)) 64;
    Math.lemma_mod_plus_distr_r a c 64;
    Math.lemma_mod_plus_distr_r a (pow2 (64 - r) * hi) 64

(** P-256 reads its scalar with {!Spec.Bignum4}, whose [eval] is
    {!Spec.Bignum.eval} by another name; the digit lemmas below are stated
    over the latter, as {!Hacl.Bignum.Base.num}. *)
#push-options "--fuel 1 --ifuel 0"
let rec eval_bridge (s: Seq.seq nat)
  : Lemma (ensures SB.eval s == B4.eval s) (decreases Seq.length s)
  = if Seq.length s = 0 then () else eval_bridge (Seq.slice s 1 (Seq.length s))
#pop-options

let kv_num (vk: Seq.seq S64.t) : Lemma (kv vk == num vk)
  = Seq.lemma_eq_intro (L4.vals vk) (L64.vals vk);
    eval_bridge (L4.vals vk)

let top_limb (n: nat) : Lemma (requires n < pow2 256) (ensures n / wt 4 % pow2 64 == 0)
  = assert_norm (wt 4 == pow2 256); Math.small_div n (pow2 256)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let lv (vk: Seq.seq S64.t) (j: nat) : GTot nat =
  if j < Seq.length vk then S64.v (Seq.index vk j) else 0

(** Digit zero: twice the low limb, modulo 64. *)
let vwin_zero (vk: Seq.seq S64.t)
  : Lemma (requires Seq.length vk == 4)
          (ensures (2 * lv vk 0) % pow2 64 % 64 == B.win (num vk) 0)
  = num_digit vk 0;
    assert_norm (base == pow2 64);
    win_bot (num vk) (lv vk 0)

(** A window inside one limb. *)
let win_in (vk: Seq.seq S64.t) (i: pos { i <= 51 })
  : Lemma (requires Seq.length vk == 4 /\ (5 * i - 1) % 64 < 59)
          (ensures lv vk ((5 * i - 1) / 64) / pow2 ((5 * i - 1) % 64) % 64 ==
                   B.win (num vk) i)
  = win_pos (num vk) i;
    assert_norm (pow2 6 == 64);
    num_bits_at vk (5 * i - 1) 6

(** A window across two limbs, the upper one zero above the scalar. *)
let win_cross (vk: Seq.seq S64.t) (i: pos { i <= 51 })
  : Lemma (requires Seq.length vk == 4 /\ 59 <= (5 * i - 1) % 64)
          (ensures (let q = (5 * i - 1) / 64 in
                    let r = (5 * i - 1) % 64 in
                    (lv vk q / pow2 r + lv vk (q + 1) * pow2 (64 - r) % pow2 64)
                      % pow2 64 % 64 == B.win (num vk) i))
  = let s = 5 * i - 1 in
    let q = s / 64 in
    let r = s % 64 in
    win_pos (num vk) i;
    split_index s;
    assert_norm (rad == 64);
    assert_norm (base == pow2 64);
    num_digit vk q;
    if q + 1 < 4 then num_digit vk (q + 1)
    else begin
      L4.vals_bnd vk;
      kv_bnd vk;
      kv_num vk;
      top_limb (num vk)
    end;
    straddle (num vk) q r (lv vk q) (lv vk (q + 1))

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [vwin ks i] is the window of digit [i]: six bits at [5 i - 1], with a
    zero below the scalar. *)
inline_for_extraction
fn vwin (ks: A.array S64.t) (i: SZ.t { SZ.v i <= 51 })
        (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires A.pts_to ks #pk vk ** pure (Seq.length vk == 4)
returns w: S64.t
ensures A.pts_to ks #pk vk ** pure (S64.v w == B.win (kv vk) (SZ.v i))
{
  A.pts_to_len ks;
  kv_num vk;
  if (i = 0sz) {
    let l = ks.(0sz);
    vwin_zero vk;
    S64.logand_mask_low (S64.shift_left l 1ul) 6ul;
    assert_norm (pow2 6 == 64);
    S64.logand (S64.shift_left l 1ul) (S64.mask_low 6ul)
  } else {
    let s = SZ.sub (SZ.mul 5sz i) 1sz;
    let q = SZ.div s 64sz;
    let r = SZ.rem s 64sz;
    let lo = ks.(q);
    let rr = SZ.sizet_to_uint32 r;
    let x = S64.shift_right lo rr;
    assert_norm (pow2 6 == 64);
    if (SZ.lt r 59sz) {
      win_in vk (SZ.v i);
      S64.logand_mask_low x 6ul;
      S64.logand x (S64.mask_low 6ul)
    } else {
      win_cross vk (SZ.v i);
      let hi = if (SZ.lt q 3sz) { ks.(SZ.add q 1sz) } else { S64.zero };
      let t = S64.add_mod x (S64.shift_left hi (U32.sub 64ul rr));
      S64.logand_mask_low t 6ul;
      S64.logand t (S64.mask_low 6ul)
    }
  }
}

#pop-options

(** {2 The table}

    Entry [d] is [(d + 1) Q], projective, so that a magnitude [m] in
    [1 .. 16] selects entry [m - 1].  The bookkeeping is
    {!Hacl.P256.PointWin}'s, shifted by one. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

[@@"opaque_to_smt"]
let vent (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (d: nat) : prop =
  pok (entry tx d) (entry ty d) (entry tz d) /\
  rep (entry tx d) (entry ty d) (entry tz d) (d + 1) p

let vent_intro (tx ty tz sx sy sz: Seq.seq S64.t) (p: P.proj_point) (d: nat)
  : Lemma (requires entry tx d == sx /\ entry ty d == sy /\
                    entry tz d == sz /\ pok sx sy sz /\ rep sx sy sz (d + 1) p)
          (ensures vent tx ty tz p d)
  = reveal_opaque (`%vent) vent

let vent_eq (tx ty tz tx' ty' tz': Seq.seq S64.t) (p: P.proj_point) (d: nat)
  : Lemma (requires vent tx ty tz p d /\ entry tx' d == entry tx d /\
                    entry ty' d == entry ty d /\ entry tz' d == entry tz d)
          (ensures vent tx' ty' tz' p d)
  = reveal_opaque (`%vent) vent

let vtok (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (upto: nat) : prop =
  forall (d: nat). d < upto ==> vent tx ty tz p d

let vent_same (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (e dd: nat)
  : Lemma (requires vent tx ty tz p e /\ dd == e)
          (ensures vent tx ty tz p dd)
  = ()

(** What the signed addition needs of the entry it selected. *)
let vtok_get (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (d: nat)
  : Lemma (requires vtok tx ty tz p 16 /\ d < 16)
          (ensures pok (entry tx d) (entry ty d) (entry tz d) /\
                   GR.on_curve (fev (entry tx d), fev (entry ty d), fev (entry tz d)) /\
                   GR.peq (fev (entry tx d), fev (entry ty d), fev (entry tz d))
                          (SM.smul ((d + 1) * 1) p))
  = assert (vent tx ty tz p d);
    reveal_opaque (`%vent) vent;
    rep_elim (entry tx d) (entry ty d) (entry tz d) (d + 1) p;
    smul_cong (d + 1) ((d + 1) * 1) p

#push-options "--ifuel 1 --z3rlimit 100"
let vtok_extend (tx ty tz tx' ty' tz': Seq.seq S64.t) (p: P.proj_point) (e: nat)
  : Lemma (requires vtok tx ty tz p e /\ e < 16 /\ vent tx' ty' tz' p e /\
                    (forall (dd: nat). dd < e ==>
                       (entry tx' dd == entry tx dd /\
                        entry ty' dd == entry ty dd /\
                        entry tz' dd == entry tz dd)))
          (ensures vtok tx' ty' tz' p (e + 1))
  = introduce forall (dd: nat). dd < e + 1 ==> vent tx' ty' tz' p dd
    with introduce _ ==> _
    with (if dd < e then vent_eq tx ty tz tx' ty' tz' p dd
                    else vent_same tx' ty' tz' p e dd)
#pop-options

let sz_fifteen (x: SZ.t) : Lemma (requires SZ.lt x 15sz == false /\ SZ.v x <= 15)
                                  (ensures SZ.v x == 15) = ()

let vtok_zero (tx ty tz: Seq.seq S64.t) (p: P.proj_point) : Lemma (vtok tx ty tz p 0) = ()

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Store [c], which is [(d + 1) Q], as entry [d]. *)
fn store_ent (tx ty tz: A.array S64.t) (cx cy cz: A.array S64.t)
             (p: erased P.proj_point) (d: SZ.t { SZ.v d < 16 })
             (#vtx #vty #vtz: erased (Seq.seq S64.t))
             (#vcx #vcy #vcz: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to cx vcx ** A.pts_to cy vcy ** A.pts_to cz vcz **
  pure (Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        pok vcx vcy vcz /\ rep vcx vcy vcz (SZ.v d + 1) (reveal p) /\
        vtok vtx vty vtz (reveal p) (SZ.v d))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
  A.pts_to cx vcx ** A.pts_to cy vcy ** A.pts_to cz vcz **
  pure (Seq.length wx == 64 /\ Seq.length wy == 64 /\ Seq.length wz == 64 /\
        vtok wx wy wz (reveal p) (SZ.v d + 1))
{
  pok_elim vcx vcy vcz;
  store_off (SZ.v d);
  store3 tx ty tz cx cy cz (SZ.mul d 4sz);
  with wx wy wz. assert (A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz);
  tbl_shape vtx wx vcx (SZ.v d);
  tbl_shape vty wy vcy (SZ.v d);
  tbl_shape vtz wz vcz (SZ.v d);
  vent_intro wx wy wz vcx vcy vcz (reveal p) (SZ.v d);
  vtok_extend vtx vty vtz wx wy wz (reveal p) (SZ.v d);
  ()
}

(** [build_vtab t q] fills the table with [Q .. 16 Q]. *)
fn build_vtab (tx ty tz: A.array S64.t) (qx qy qz: A.array S64.t)
              (p: erased P.proj_point)
              (#vtx #vty #vtz: erased (Seq.seq S64.t))
              (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        pok vqx vqy vqz /\ oc (reveal p) /\ rep vqx vqy vqz 1 (reveal p))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (Seq.length wx == 64 /\ Seq.length wy == 64 /\ Seq.length wz == 64 /\
        vtok wx wy wz (reveal p) 16)
{
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  pok_elim vqx vqy vqz;
  let z = S64.zero;
  let mut cx = [| z; 4sz |];
  Mem.track cx; A.pts_to_len cx;
  let mut cy = [| z; 4sz |];
  Mem.track cy; A.pts_to_len cy;
  let mut cz = [| z; 4sz |];
  Mem.track cz; A.pts_to_len cz;
  let mut nx = [| z; 4sz |];
  Mem.track nx; A.pts_to_len nx;
  let mut ny = [| z; 4sz |];
  Mem.track ny; A.pts_to_len ny;
  let mut nz = [| z; 4sz |];
  Mem.track nz; A.pts_to_len nz;
  A.pts_to_len cx; A.pts_to_len cy; A.pts_to_len cz;
  A.pts_to_len nx; A.pts_to_len ny; A.pts_to_len nz;

  fcopy cx qx; fcopy cy qy; fcopy cz qz;
  with c0x c0y c0z. assert (A.pts_to cx c0x ** A.pts_to cy c0y ** A.pts_to cz c0z);
  pok_intro c0x c0y c0z;
  rep_fcopy vqx vqy vqz c0x c0y c0z 1 (reveal p);
  vtok_zero vtx vty vtz (reveal p);

  let mut d = 0sz;
  while (let vd = !d; SZ.lt vd 15sz)
  invariant exists* (vd: SZ.t)
                    (wx wy wz wcx wcy wcz wnx wny wnz: Seq.seq S64.t).
    pts_to d vd **
    A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
    A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz **
    A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
    pure (SZ.v vd <= 15 /\
          Seq.length wx == 64 /\ Seq.length wy == 64 /\ Seq.length wz == 64 /\
          Seq.length wnx == 4 /\ Seq.length wny == 4 /\ Seq.length wnz == 4 /\
          pok wcx wcy wcz /\
          rep wcx wcy wcz (SZ.v vd + 1) (reveal p) /\
          vtok wx wy wz (reveal p) (SZ.v vd))
  decreases (15 - SZ.v (!d))
  {
    let vd = !d;
    with wx wy wz. assert (A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz);
    with wcx wcy wcz. assert (A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz);
    store_ent tx ty tz cx cy cz p vd;
    pok_elim wcx wcy wcz;
    point_add nx ny nz cx cy cz qx qy qz;
    with wnx wny wnz. assert (A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz);
    add_ok wcx wcy wcz vqx vqy vqz wnx wny wnz (reveal p) (SZ.v vd + 1) 1;
    fcopy cx nx; fcopy cy ny; fcopy cz nz;
    with c1x c1y c1z. assert (A.pts_to cx c1x ** A.pts_to cy c1y ** A.pts_to cz c1z);
    pok_intro c1x c1y c1z;
    rep_fcopy wnx wny wnz c1x c1y c1z (SZ.v vd + 1 + 1) (reveal p);
    d := SZ.add vd 1sz;
  };
  let vd = !d;
  sz_fifteen vd;
  with wx wy wz. assert (A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz);
  with wcx wcy wcz. assert (A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz);
  store_ent tx ty tz cx cy cz p vd;
  Mem.wipe nz 4sz;
  Mem.wipe ny 4sz;
  Mem.wipe nx 4sz;
  Mem.wipe cz 4sz;
  Mem.wipe cy 4sz;
  Mem.wipe cx 4sz;
  ()
}

#pop-options

(** A zero digit leaves the multiple where it was. *)
let zero_keep (e e' m: nat) (neg: bool)
  : Lemma (requires (not neg ==> e' == e + m * 1) /\ (neg ==> e == e' + m * 1))
          (ensures m == 0 ==> e' == e)
  = ()

(** {2 One signed addition}

    {!Hacl.P256.PointBooth.win_sadd}, with a projective entry. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn vsadd (ox oy oz ux uy uz sx sy sz: A.array S64.t)
         (tx ty tz: A.array S64.t) (mag sm: S64.t)
         (p: erased P.proj_point) (e e': erased nat)
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
        pok vox voy voz /\ oc (reveal p) /\
        rep vox voy voz e (reveal p) /\
        vtok vtx vty vtz (reveal p) 16 /\
        S64.v mag <= 16 /\ is_mask sm /\
        (S64.v sm == 0 ==> reveal e' == reveal e + S64.v mag * 1) /\
        (S64.v sm <> 0 ==> reveal e == reveal e' + S64.v mag * 1))
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty ** A.pts_to tz #ptz vtz **
  pure (Seq.length wux == 4 /\ Seq.length wuy == 4 /\ Seq.length wuz == 4 /\
        Seq.length wsx == 4 /\ Seq.length wsy == 4 /\ Seq.length wsz == 4 /\
        pok wx wy wz /\ rep wx wy wz (reveal e') (reveal p))
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
  vtok_get vtx vty vtz (reveal p) (reveal d);
  pok_elim wsx wsy wsz;
  fzero ux;
  fsub uy ux sy;
  fcsel sy uy sm;
  with nsy. assert (A.pts_to sy nsy);
  point_add ux uy uz ox oy oz sx sy sz;
  with u1x u1y u1z. assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z);
  sadd_ok vox voy voz wsx wsy nsy u1x u1y u1z (fev wsz) (reveal p)
          (reveal e) (reveal e') (S64.v mag) 1 (reveal d) (S64.v sm <> 0);
  let zm = S64.eq_mask mag S64.zero;
  let nz = S64.eq_mask zm S64.zero;
  fcsel ox ux nz; fcsel oy uy nz; fcsel oz uz nz;
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  zero_keep (reveal e) (reveal e') (S64.v mag) (S64.v sm <> 0);
  keep_ok vox voy voz u1x u1y u1z wx wy wz (reveal p)
          (reveal e) (reveal e') (S64.v mag = 0);
  pok_intro wx wy wz;
  ()
}

#pop-options

(** {2 The ladder} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** Above the top digit there is nothing. *)
let hb_top52 (k: nat) : Lemma (requires k < pow2 256) (ensures B.hb k 52 == 0)
  = assert_norm (pow2 (5 * 52) == 16 * pow2 256);
    Math.small_div (2 * k) (pow2 (5 * 52));
    assert_norm (1 / 2 == 0)

(** What one signed addition is told about digit [i - 1]. *)
let vdigit_ok (k: nat) (i: pos) (w mg sm: nat)
  : Lemma (requires w == B.win k (i - 1) /\
                    mg == (if w / 32 = 0 then (w + 1) / 2 else 32 - (w + 1) / 2) /\
                    (sm == 0 <==> w / 32 == 0))
          (ensures mg <= 16 /\
                   (sm == 0 ==> B.hb k (i - 1) == 32 * B.hb k i + mg * 1) /\
                   (sm <> 0 ==> 32 * B.hb k i == B.hb k (i - 1) + mg * 1))
  = B.hb_step k (i - 1)

let rep_infinity (x y z: Seq.seq S64.t) (p: P.proj_point) (k: nat)
  : Lemma (requires oc p /\ pt x y z == P.point_at_infinity /\ k < pow2 256)
          (ensures rep x y z (32 * B.hb k 52) p)
  = zero_ok x y z p;
    hb_top52 k;
    rep_cong x y z 0 (32 * B.hb k 52) p

let hb_end (k: nat) : Lemma (B.hb k 0 == k) = B.hb_bot k

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** [point_mul_vb o q ks] is [o := [ks] Q], up to [peq]. *)
fn point_mul_vb (ox oy oz: A.array S64.t) (qx qy qz: A.array S64.t)
                (ks: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
                (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
                (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == 4 /\ Seq.length voy == 4 /\ Seq.length voz == 4 /\
        Seq.length vk == B4.nl /\ B4.bnd (L4.vals vk) B4.base /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (P.point_mul (kv vk) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz) (P.point_mul (kv vk) (pt vqx vqy vqz)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ks;
  L4.vals_bnd vk;
  kv_bnd vk;
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
  set_infinity ox oy oz;
  with o0x o0y o0z. assert (A.pts_to ox o0x ** A.pts_to oy o0y ** A.pts_to oz o0z);
  pok_intro o0x o0y o0z;
  rep_infinity o0x o0y o0z (pt vqx vqy vqz) (kv vk);

  // The top digit goes straight into the point at infinity.
  let w0 = vwin ks 51sz;
  let sm0 = bsgn w0;
  let mg0 = bmag w0;
  vdigit_ok (kv vk) 52 (S64.v w0) (S64.v mg0) (S64.v sm0);
  vsadd ox oy oz ux uy uz sx sy sz tx ty tz mg0 sm0
        (hide (pt vqx vqy vqz))
        (hide (32 * B.hb (kv vk) 52)) (hide (B.hb (kv vk) 51));

  let mut i = 51sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wux wuy wuz wsx wsy wsz
                     wtx wty wtz: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
    A.pts_to tx wtx ** A.pts_to ty wty ** A.pts_to tz wtz **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
    A.pts_to ks #pk vk **
    pure (SZ.v vi <= 51 /\
          Seq.length wux == 4 /\ Seq.length wuy == 4 /\ Seq.length wuz == 4 /\
          Seq.length wsx == 4 /\ Seq.length wsy == 4 /\ Seq.length wsz == 4 /\
          Seq.length wtx == 64 /\ Seq.length wty == 64 /\ Seq.length wtz == 64 /\
          vtok wtx wty wtz (pt vqx vqy vqz) 16 /\
          pok wx wy wz /\
          rep wx wy wz (B.hb (kv vk) (SZ.v vi)) (pt vqx vqy vqz))
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let i1 = SZ.sub vi 1sz;
    win_dbl5 ox oy oz ux uy uz (hide (pt vqx vqy vqz))
             (hide (B.hb (kv vk) (SZ.v vi)));
    let w = vwin ks i1;
    let sm = bsgn w;
    let mg = bmag w;
    vdigit_ok (kv vk) (SZ.v vi) (S64.v w) (S64.v mg) (S64.v sm);
    vsadd ox oy oz ux uy uz sx sy sz tx ty tz mg sm
          (hide (pt vqx vqy vqz))
          (hide (32 * B.hb (kv vk) (SZ.v vi))) (hide (B.hb (kv vk) (SZ.v i1)));
    i := i1;
  };
  let vi = !i;
  sz_zero vi;
  hb_end (kv vk);
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  rep_cong wx wy wz (B.hb (kv vk) 0) (kv vk) (pt vqx vqy vqz);
  pok_elim wx wy wz;
  win_done wx wy wz (pt vqx vqy vqz) (kv vk);
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
