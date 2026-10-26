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

(** ECDSA verification on P-384.

    Nothing here is secret: the message, the signature and the public key
    are all published.  Comparisons are therefore declassified to booleans.
    Both inverses -- of [s] mod [n] and of [z] for the final affine
    coordinate -- are the fixed addition chains of {!Hacl.P384.QInverse}
    and {!Hacl.P384.Inverse}, which are faster than any generic
    exponentiation, variable-time or not.

    The scalars mod [n] are plain numbers handled by the generic bignum
    layer; the curve arithmetic is in Montgomery form. *)
module Hacl.P384.Verify

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Spec.Bytes
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Impl.Copy
open Hacl.Bignum.Base
open Hacl.Bignum.Montgomery
open Hacl.Bignum.Convert
open Hacl.P384.Tables
open Hacl.P384.Lemmas
open Hacl.P384.Field
open Hacl.P384.Point
open Hacl.P384.PointMul

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module GR = Spec.P384.Group
module MA = Spec.ModArith
module Math = FStar.Math.Lemmas
module Mem = Hacl.Mem
module Inv = Hacl.P384.Inverse
module QI = Hacl.P384.QInverse
module Declassify = Hacl.Secret.Declassify

(** {2 Total wrappers}

    An [ensures] is elaborated without the [requires] in scope, so the
    length and range conditions travel inside these. *)

let half (vs: Seq.seq S8.t) (off: nat) : GTot nat =
  if Seq.length vs = 96 && off <= 48 then be_nat (Seq.slice vs off (off + 48)) else 0

let lp_ok (vp: Seq.seq S8.t) : GTot bool =
  Seq.length vp = 96 && Some? (P.load_point vp)

let lp (vp: Seq.seq S8.t) : GTot P.proj_point =
  if lp_ok vp then Some?.v (P.load_point vp) else P.point_at_infinity

(** {2 Leaving projective coordinates}

    {!Hacl.P384.PointMul} returns a triple equivalent to the specification's,
    not equal to it.  These are the places that difference is discharged:
    equivalent points on the curve are at infinity together and have the
    same affine coordinates, hence the same encoding. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"
let lp_on_curve (vp: Seq.seq S8.t)
  : Lemma (requires lp_ok vp) (ensures GR.on_curve (lp vp))
  = let xs = Seq.slice vp 0 48 in
    let ys = Seq.slice vp 48 96 in
    match P.load_felem xs, P.load_felem ys with
    | Some x, Some y -> GR.on_curve_affine x y
    | _ -> ()
#pop-options

let peq_out (p q: P.proj_point)
  : Lemma (requires GR.on_curve p /\ GR.on_curve q /\ GR.peq p q)
          (ensures P.is_point_at_infinity p == P.is_point_at_infinity q /\
                   P.to_aff_point p == P.to_aff_point q /\
                   P.store_point p == P.store_point q)
  = GR.peq_is_point_at_infinity p q;
    GR.peq_to_aff_point p q

let add_out (a b c ga gb: P.proj_point)
  : Lemma (requires GR.on_curve a /\ GR.on_curve b /\ GR.on_curve ga /\
                    GR.on_curve gb /\ GR.peq a ga /\ GR.peq b gb /\
                    c == P.point_add a b)
          (ensures P.is_point_at_infinity c ==
                     P.is_point_at_infinity (P.point_add ga gb) /\
                   P.to_aff_point c == P.to_aff_point (P.point_add ga gb))
  = GR.point_add_on_curve a b;
    GR.point_add_on_curve ga gb;
    GR.point_add_congr a ga b gb;
    peq_out c (P.point_add ga gb)

let core_spec (m r s: P.qelem) (q: P.proj_point) : GTot bool =
  let sinv = P.qinv s in
  let u1 = P.qmul sinv m in
  let u2 = P.qmul sinv r in
  let res = P.point_mul_double_g u1 u2 q in
  if P.is_point_at_infinity res then false
  else (let (rx, _) = P.to_aff_point res in rx % P.order = r)

let core_w (m r s: nat) (q: P.proj_point) : GTot bool =
  if m < P.order && r < P.order && s < P.order then core_spec m r s q else false

let vfy (m: nat) (vp vs: Seq.seq S8.t) : GTot bool =
  if m < P.order && Seq.length vp = 96 && Seq.length vs = 96
  then P.ecdsa_verify_msg_as_qelem m vp vs else false

let mul_bound (a b n w: nat)
  : Lemma (requires a < n /\ b < n /\ n <= w) (ensures a * b < n * w)
  = Math.lemma_mult_le_right b a n;
    Math.lemma_mult_lt_left n b w;
    Math.swap_mul a b

let six_bnd (v: Seq.seq S64.t)
  : Lemma (requires Seq.length v == 6) (ensures num v < wt 6)
  = pre_bnd v 6; pre_full v

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Arithmetic modulo either prime} *)

fn mulmod (res a b nm r2: A.array S64.t) (mu: S64.t)
          (#vres: erased (Seq.seq S64.t))
          (#pa #pb #pn #pr: perm) (#va #vb #vr2: erased (Seq.seq S64.t))
          (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         A.pts_to nm #pn vn ** A.pts_to r2 #pr vr2 **
  pure (Seq.length vres == 6 /\ Seq.length va == 6 /\ Seq.length vb == 6 /\
        Seq.length vn == 6 /\ Seq.length vr2 == 6 /\
        num va < num vn /\ num vb < num vn /\
        num vr2 == (wt 6 * wt 6) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to nm #pn vn ** A.pts_to r2 #pr vr2 **
  pure (Seq.length v == 6 /\ num v == (num va * num vb) % num vn)
{
  facts ();
  six_bnd vn;
  mul_bound (num va) (num vb) (num vn) (wt 6);
  let z = S64.zero;
  let mut wide = [| z; 12sz |];
  Mem.track wide; A.pts_to_len wide; let mut acc = [| z; 6sz |];
  Mem.track acc; A.pts_to_len acc;
  mul wide a b 6sz;
  modulo res wide acc r2 nm 6sz mu;
  Mem.wipe acc 6sz;
  Mem.wipe wide 12sz;
  ()
}

fn reduce (res a nm r2: A.array S64.t) (mu: S64.t)
          (#vres: erased (Seq.seq S64.t))
          (#pa #pn #pr: perm) (#va #vr2: erased (Seq.seq S64.t))
          (#vn: erased (s: Seq.seq S64.t { 0 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va **
         A.pts_to nm #pn vn ** A.pts_to r2 #pr vr2 **
  pure (Seq.length vres == 6 /\ Seq.length va == 6 /\
        Seq.length vn == 6 /\ Seq.length vr2 == 6 /\
        num vr2 == (wt 6 * wt 6) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va **
  A.pts_to nm #pn vn ** A.pts_to r2 #pr vr2 **
  pure (Seq.length v == 6 /\ num v == num va % num vn)
{
  facts ();
  six_bnd va;
  Math.lemma_mult_le_right (wt 6) 1 (num vn);
  let z = S64.zero;
  let mut wide = [| z; 12sz |];
  Mem.track wide; A.pts_to_len wide; let mut acc = [| z; 6sz |];
  Mem.track acc; A.pts_to_len acc;
  embed wide a 6sz;
  modulo res wide acc r2 nm 6sz mu;
  Mem.wipe acc 6sz;
  Mem.wipe wide 12sz;
  ()
}

(** {2 Decoding} *)

fn load_half (out: A.array S64.t) (src: A.array S8.t) (off: SZ.t)
             (#vo: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to src #ps vs **
  pure (Seq.length vo == 6 /\ Seq.length vs == 96 /\ SZ.v off <= 48)
ensures exists* (w: Seq.seq S64.t).
  A.pts_to out w ** A.pts_to src #ps vs **
  pure (Seq.length w == 6 /\ num w == half vs (SZ.v off))
{
  facts ();
  let z8 = S8.classify 0uy;
  let mut d = [| z8; 48sz |];
  Mem.track d; A.pts_to_len d;
  copy_range d 0sz src off 48sz;
  with vd. assert (A.pts_to d vd);
  assert (pure (Seq.equal vd (Seq.slice vs (SZ.v off) (SZ.v off + 48))));
  from_bytes_be out 6sz d;
  Mem.wipe d 48sz;
  ()
}

fn load_coord (out: A.array S64.t) (src: A.array S8.t) (off: SZ.t)
              (#vo: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to src #ps vs **
  pure (Seq.length vo == 6 /\ Seq.length vs == 96 /\ SZ.v off <= 48)
returns r: bool
ensures exists* (w: Seq.seq S64.t).
  A.pts_to out w ** A.pts_to src #ps vs **
  pure (felem w /\ r == (half vs (SZ.v off) < P.prime) /\
        (r ==> fev w == half vs (SZ.v off)))
{
  facts ();
  let z8 = S8.classify 0uy;
  let mut d = [| z8; 48sz |];
  Mem.track d; A.pts_to_len d;
  copy_range d 0sz src off 48sz;
  with vd. assert (A.pts_to d vd);
  assert (pure (Seq.equal vd (Seq.slice vs (SZ.v off) (SZ.v off + 48))));
  let r = fload out d;
  Mem.wipe d 48sz;
  r
}

(** [y^2 = x^3 - 3x + b], computed exactly as [Spec.P384.is_on_curve]
    writes it. *)
fn on_curve (x y: A.array S64.t)
            (#px: perm) (#vx: erased (Seq.seq S64.t))
            (#py: perm) (#vy: erased (Seq.seq S64.t))
requires A.pts_to x #px vx ** A.pts_to y #py vy ** pure (felem vx /\ felem vy)
returns r: bool
ensures A.pts_to x #px vx ** A.pts_to y #py vy **
  pure (r == P.is_on_curve (fev vx) (fev vy))
{
  let z = S64.zero;
  let mut y2 = [| z; 6sz |];
  Mem.track y2; A.pts_to_len y2; let mut x2 = [| z; 6sz |];
  Mem.track x2; A.pts_to_len x2; let mut x3 = [| z; 6sz |];
  Mem.track x3; A.pts_to_len x3; let mut tx = [| z; 6sz |];
  Mem.track tx; A.pts_to_len tx; let mut u = [| z; 6sz |];
  Mem.track u; A.pts_to_len u; let mut v = [| z; 6sz |];
  Mem.track v; A.pts_to_len v;
  fsqr y2 y;
  fsqr x2 x;
  fmul x3 x2 x;
  let th = fthree ();
  fmul tx th x;
  drop_table th;
  fsub u x3 tx;
  let bc = fb ();
  fadd v u bc;
  drop_table bc;
  let r = feq y2 v;
  Mem.wipe v 6sz;
  Mem.wipe u 6sz;
  Mem.wipe tx 6sz;
  Mem.wipe x3 6sz;
  Mem.wipe x2 6sz;
  Mem.wipe y2 6sz;
  r
}

#push-options "--ifuel 2"
fn load_point (qx qy qz: A.array S64.t) (pk: A.array S8.t)
              (#vqx #vqy #vqz: erased (Seq.seq S64.t))
              (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to qx vqx ** A.pts_to qy vqy ** A.pts_to qz vqz ** A.pts_to pk #pp vp **
  pure (Seq.length vqx == 6 /\ Seq.length vqy == 6 /\ Seq.length vqz == 6 /\
        Seq.length vp == 96)
returns r: bool
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to qx wx ** A.pts_to qy wy ** A.pts_to qz wz ** A.pts_to pk #pp vp **
  pure (pt_ok wx wy wz /\ r == lp_ok vp /\ (r ==> pt wx wy wz == lp vp))
{
  let okx = load_coord qx pk 0sz;
  let oky = load_coord qy pk 48sz;
  fone qz;
  if (okx && oky) {
    on_curve qx qy
  } else {
    false
  }
}
#pop-options

(** {2 Scalars} *)

fn scalar_ok (a: A.array S64.t) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** pure (Seq.length va == 6)
returns r: bool
ensures A.pts_to a #pa va ** pure (r == (0 < num va && num va < P.order))
{
  facts ();
  let qm = qms ();
  let lt = lt_mask a qm 6sz;
  drop_table qm;
  let z = S64.zero;
  let mut zz = [| z; 6sz |];
  Mem.track zz; A.pts_to_len zz;
  zero zz 6sz;
  with vz. assert (A.pts_to zz vz);
  num_zero vz;
  let eq = eq_mask a zz 6sz;
  Mem.wipe zz 6sz;
  let b1 = U64.eq (Declassify.u64 lt) 18446744073709551615uL;
  let b2 = U64.eq (Declassify.u64 eq) 18446744073709551615uL;
  (b1 && not b2)
}

#pop-options

(** {2 The verification equation} *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"

(** Whether the affine [x] of [(cx : _ : cz)], reduced mod [n], is [r]. *)
fn check_x (cx cz r: A.array S64.t)
           (#px: perm) (#vcx: erased (Seq.seq S64.t))
           (#pz: perm) (#vcz: erased (Seq.seq S64.t))
           (#pr: perm) (#vr: erased (Seq.seq S64.t))
requires A.pts_to cx #px vcx ** A.pts_to cz #pz vcz ** A.pts_to r #pr vr **
  pure (felem vcx /\ felem vcz /\ Seq.length vr == 6)
returns b: bool
ensures A.pts_to cx #px vcx ** A.pts_to cz #pz vcz ** A.pts_to r #pr vr **
  pure (b == (P.fmul (fev vcx) (P.finv (fev vcz)) % P.order = num vr))
{
  facts ();
  let z = S64.zero;
  let qm = qms ();
  let q2 = qr2 ();
  let mut zi = [| z; 6sz |];
  Mem.track zi; A.pts_to_len zi; let mut xm = [| z; 6sz |];
  Mem.track xm; A.pts_to_len xm; let mut xa = [| z; 6sz |];
  Mem.track xa; A.pts_to_len xa; let mut xr = [| z; 6sz |];
  Mem.track xr; A.pts_to_len xr;
  Inv.finv zi cz;
  fmul xm cx zi;
  ffrom xa xm;
  with vxa. assert (A.pts_to xa vxa);
  assert (pure (num vxa == P.fmul (fev vcx) (P.finv (fev vcz))));
  reduce xr xa qm q2 qmu;
  with vxr. assert (A.pts_to xr vxr);
  assert (pure (num vxr == num vxa % P.order));
  let em = eq_mask xr r 6sz;
  let b = U64.eq (Declassify.u64 em) 18446744073709551615uL;
  Mem.wipe xr 6sz;
  Mem.wipe xa 6sz;
  Mem.wipe xm 6sz;
  Mem.wipe zi 6sz;
  drop_table q2;
  drop_table qm;
  b
}


fn verify_core (m r s qx qy qz: A.array S64.t)
               (#pm: perm) (#vm: erased (Seq.seq S64.t))
               (#pr: perm) (#vr: erased (Seq.seq S64.t))
               (#ps: perm) (#vs: erased (Seq.seq S64.t))
               (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
requires A.pts_to m #pm vm ** A.pts_to r #pr vr ** A.pts_to s #ps vs **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (Seq.length vm == 6 /\ Seq.length vr == 6 /\ Seq.length vs == 6 /\
        num vm < P.order /\ num vr < P.order /\ num vs < P.order /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
returns b: bool
ensures A.pts_to m #pm vm ** A.pts_to r #pr vr ** A.pts_to s #ps vs **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (b == core_w (num vm) (num vr) (num vs) (pt vqx vqy vqz))
{
  facts ();
  let z = S64.zero;
  let mut si = [| z; 6sz |];
  Mem.track si; A.pts_to_len si; let mut u1 = [| z; 6sz |];
  Mem.track u1; A.pts_to_len u1; let mut u2 = [| z; 6sz |];
  Mem.track u2; A.pts_to_len u2;
  let mut ax = [| z; 6sz |];
  Mem.track ax; A.pts_to_len ax; let mut ay = [| z; 6sz |];
  Mem.track ay; A.pts_to_len ay; let mut az = [| z; 6sz |];
  Mem.track az; A.pts_to_len az;
  let mut bx = [| z; 6sz |];
  Mem.track bx; A.pts_to_len bx; let mut by_ = [| z; 6sz |];
  Mem.track by_; A.pts_to_len by_; let mut bz = [| z; 6sz |];
  Mem.track bz; A.pts_to_len bz;
  let mut cx = [| z; 6sz |];
  Mem.track cx; A.pts_to_len cx; let mut cy = [| z; 6sz |];
  Mem.track cy; A.pts_to_len cy; let mut cz = [| z; 6sz |];
  Mem.track cz; A.pts_to_len cz;

  (* u1 = m / s, u2 = r / s, mod n *)
  let qm = qms ();
  let q2 = qr2 ();
  QI.qinv_plain si s;
  with vsi. assert (A.pts_to si vsi);
  assert (pure (num vsi == P.qinv (num vs)));
  mulmod u1 si m qm q2 qmu;
  mulmod u2 si r qm q2 qmu;
  with vu1. assert (A.pts_to u1 vu1);
  with vu2. assert (A.pts_to u2 vu2);
  assert (pure (num vu1 == P.qmul (P.qinv (num vs)) (num vm)));
  assert (pure (num vu2 == P.qmul (P.qinv (num vs)) (num vr)));

  (* [u1] G + [u2] Q *)
  point_mul_g ax ay az u1;
  point_mul bx by_ bz qx qy qz u2;
  with wax way waz. assert (A.pts_to ax wax ** A.pts_to ay way ** A.pts_to az waz);
  with wbx wby wbz. assert (A.pts_to bx wbx ** A.pts_to by_ wby ** A.pts_to bz wbz);
  point_add cx cy cz ax ay az bx by_ bz;
  with wcx wcy wcz. assert (A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz);
  add_out (pt wax way waz) (pt wbx wby wbz) (pt wcx wcy wcz)
          (P.point_mul_g (num vu1)) (P.point_mul (num vu2) (pt vqx vqy vqz));
  assert (pure (P.point_mul_double_g (num vu1) (num vu2) (pt vqx vqy vqz) ==
                P.point_add (P.point_mul_g (num vu1))
                            (P.point_mul (num vu2) (pt vqx vqy vqz))));

  let inf = fis_zero cz;
  let res = if inf { false } else { check_x cx cz r };
  drop_table q2;
  drop_table qm;
  Mem.wipe cz 6sz;
  Mem.wipe cy 6sz;
  Mem.wipe cx 6sz;
  Mem.wipe bz 6sz;
  Mem.wipe by_ 6sz;
  Mem.wipe bx 6sz;
  Mem.wipe az 6sz;
  Mem.wipe ay 6sz;
  Mem.wipe ax 6sz;
  Mem.wipe u2 6sz;
  Mem.wipe u1 6sz;
  Mem.wipe si 6sz;
  res
}

(** [verify m pk sig] checks the raw signature [r || s] on the message
    representative [m] under the raw public key [x || y]. *)
fn verify (m: A.array S64.t) (pk sg: A.array S8.t)
          (#pm: perm) (#vm: erased (Seq.seq S64.t))
          (#pp: perm) (#vp: erased (Seq.seq S8.t))
          (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to m #pm vm ** A.pts_to pk #pp vp ** A.pts_to sg #ps vs **
  pure (Seq.length vm == 6 /\ num vm < P.order /\
        Seq.length vp == 96 /\ Seq.length vs == 96)
returns b: bool
ensures A.pts_to m #pm vm ** A.pts_to pk #pp vp ** A.pts_to sg #ps vs **
  pure (b == vfy (num vm) vp vs)
{
  let z = S64.zero;
  let mut r = [| z; 6sz |];
  Mem.track r; A.pts_to_len r; let mut s = [| z; 6sz |];
  Mem.track s; A.pts_to_len s;
  let mut qx = [| z; 6sz |];
  Mem.track qx; A.pts_to_len qx; let mut qy = [| z; 6sz |];
  Mem.track qy; A.pts_to_len qy; let mut qz = [| z; 6sz |];
  Mem.track qz; A.pts_to_len qz;
  load_half r sg 0sz;
  load_half s sg 48sz;
  let okr = scalar_ok r;
  let oks = scalar_ok s;
  let okp = load_point qx qy qz pk;
  let res = if (okr && oks && okp) {
    lp_on_curve vp;
    verify_core m r s qx qy qz
  } else { false };
  Mem.wipe qz 6sz;
  Mem.wipe qy 6sz;
  Mem.wipe qx 6sz;
  Mem.wipe s 6sz;
  Mem.wipe r 6sz;
  res
}

#pop-options
