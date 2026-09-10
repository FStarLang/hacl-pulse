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

(** Comparing and encoding field elements.

    Two things this file needs that the ladder never did.  The first is a
    *decision*: is this field element zero, is that one equal to this one,
    is its least significant bit set?  Curve25519 only ever had to compare
    a scalar multiplication's output against zero; Ed25519 has to branch on
    the answer, because verification succeeds or fails and decompression
    can fail too.  The comparisons are still done on masks and only the
    final bit is declassified, which is what [Hacl.Secret.Declassify] is
    for.

    The second is that both halves of a comparison have to be *reduced*
    first: a field element has many limb representations and only the
    frozen one is unique.  [Spec.Ed25519.Scalar.limbs_unique] is the lemma
    that turns "same value" into "same limbs", and it is what lets a
    comparison be a loop over sixteen [eq_mask]s. *)
module Hacl.Ed25519.Encoding

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Spec.Bytes
open Spec.Curve25519.Field
open Hacl.Curve25519.Field
open Hacl.Curve25519.Inverse

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Cast = Hacl.Secret.Cast
module Declassify = Hacl.Secret.Declassify
module C = Spec.Curve25519
module E = Spec.Ed25519
module Sc = Spec.Ed25519.Scalar
module P = Hacl.Ed25519.Point

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Two facts about the frozen representation} *)

(** A number below [2^255] has at most fifteen bits in its top limb, which
    is what leaves room for the sign bit of a compressed point. *)
let top_limb (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ eval s < pow2 255)
          (ensures Seq.index s 15 < pow2 15)
  = eval_at s 15;
    Seq.lemma_eq_intro (Seq.slice s 16 16) (Seq.empty #nat);
    eval_empty (Seq.slice s 16 16);
    Math.pow2_plus 240 15;
    assert_norm (rad * 15 == 240)

(** The parity of a number is the parity of its least significant limb,
    the radix being even. *)
let parity (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval s % 2 == Seq.index s 0 % 2)
  = eval_at s 0;
    Seq.lemma_eq_intro (Seq.slice s 0 0) (Seq.empty #nat);
    eval_empty (Seq.slice s 0 0);
    assert_norm (rad * 0 == 0);
    assert_norm (pow2 0 == 1);
    assert_norm (base == 2 * 32768);
    Math.lemma_mod_plus (Seq.index s 0) (32768 * eval (Seq.slice s 1 nl)) 2

(** Writing the sign bit into the top limb adds [2^255] to the value. *)
let set_top (s: Seq.seq nat) (b: nat { b < 2 })
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ eval s < pow2 255)
          (ensures (let s' = Seq.upd s 15 (Seq.index s 15 + b * pow2 15) in
                    bnd s' base /\ eval s' == eval s + b * pow2 255))
  = top_limb s;
    let x : nat = Seq.index s 15 + b * pow2 15 in
    let s' = Seq.upd s 15 x in
    eval_upd s 15 x;
    assert_norm (rad * 15 == 240);
    Math.distributivity_add_right (pow2 240) (Seq.index s 15) (b * pow2 15);
    Math.paren_mul_right (pow2 240) b (pow2 15);
    Math.swap_mul (pow2 240) b;
    Math.paren_mul_right b (pow2 240) (pow2 15);
    Math.pow2_plus 240 15;
    assert (eval s' + pow2 240 * Seq.index s 15 ==
            eval s + pow2 240 * Seq.index s 15 + b * pow2 255);
    assert_norm (pow2 15 + pow2 15 == pow2 16);
    assert_norm (base == pow2 16);
    assert (bnd s' base)

(** Two reduced elements with the same value have the same limbs. *)
let frozen_unique (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl /\
                    bnd a base /\ bnd b base /\ eval a == eval b)
          (ensures a == b)
  = Sc.limbs_unique a (eval a); Sc.limbs_unique b (eval b)

(** {2 Deciding} *)

(** [a = b] as field elements.  [u] and [v] take the reduced copies and [w]
    is the scratch that [freeze] wants. *)

#push-options "--z3rlimit 200"

fn feq (a b u v w: S.slice S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
       (#vu: erased (Seq.seq S64.t)) (#vv: erased (Seq.seq S64.t))
       (#vw: erased (Seq.seq S64.t))
requires S.pts_to a #pa va ** S.pts_to b #pb vb **
  S.pts_to u vu ** S.pts_to v vv ** S.pts_to w vw **
  pure (felem (vals va) /\ felem (vals vb) /\
        Seq.length vu == nl /\ Seq.length vv == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu wv ww: Seq.seq S64.t).
  S.pts_to a #pa va ** S.pts_to b #pb vb **
  S.pts_to u wu ** S.pts_to v wv ** S.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length wv == nl /\ Seq.length ww == nl /\
        r == (fev (vals va) = fev (vals vb)))
{
  S.pts_to_len u; S.pts_to_len v;
  copy u a;
  copy v b;
  freeze u w;
  freeze v w;
  with xu. assert (S.pts_to u xu);
  with xv. assert (S.pts_to v xv);
  assert (pure (eval (vals xu) == fev (vals va) /\ eval (vals xv) == fev (vals vb)));

  let mut m = S64.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (mm: S64.t) (ww: Seq.seq S64.t).
    pts_to i vi ** pts_to m mm ** S.pts_to a #pa va ** S.pts_to b #pb vb **
    S.pts_to u xu ** S.pts_to v xv ** S.pts_to w ww **
    pure (SZ.v vi <= 16 /\ Seq.length ww == nl /\
          (if (forall (k: nat). k < SZ.v vi ==>
                 Seq.index (vals xu) k == Seq.index (vals xv) k)
           then S64.v mm == pow2 64 - 1 else S64.v mm == 0))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let mm = !m;
    let xa = S.(u.(vi));
    let xb = S.(v.(vi));
    let e = S64.eq_mask xa xb;
    UInt.logand_lemma_1 #64 (S64.v e);
    UInt.logand_lemma_2 #64 (S64.v e);
    UInt.logand_commutative #64 (S64.v mm) (S64.v e);
    m := S64.logand mm e;
    i := SZ.add vi 1sz;
  };
  let mm = !m;
  assert_norm ((pow2 64 - 1) % pow2 8 == pow2 8 - 1);
  let m8 = Cast.u64_to_u8 mm;
  let r = Declassify.bool_of_mask m8;
  Classical.move_requires (Seq.lemma_eq_intro (vals xu)) (vals xv);
  Classical.move_requires (frozen_unique (vals xu)) (vals xv);
  r
}

#pop-options

(** [a = 0] as a field element. *)
fn fzerop (a u w: S.slice S64.t)
          (#pa: perm) (#va: erased (Seq.seq S64.t))
          (#vu: erased (Seq.seq S64.t)) (#vw: erased (Seq.seq S64.t))
requires S.pts_to a #pa va ** S.pts_to u vu ** S.pts_to w vw **
  pure (felem (vals va) /\ Seq.length vu == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu ww: Seq.seq S64.t).
  S.pts_to a #pa va ** S.pts_to u wu ** S.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length ww == nl /\
        r == (fev (vals va) = 0))
{
  S.pts_to_len u;
  let z = S64.zero;
  let mut az = [| z; 16sz |]; A.pts_to_len az; let zb = S.from_array az 16sz;
  let mut ay = [| z; 16sz |]; A.pts_to_len ay; let yb = S.from_array ay 16sz;
  S.pts_to_len zb; S.pts_to_len yb;
  P.set_small zb 0uL;
  let r = feq a zb u yb w;
  S.to_array zb; S.to_array yb;
  r
}

(** The least significant bit. *)
fn fodd (a u w: S.slice S64.t)
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#vu: erased (Seq.seq S64.t)) (#vw: erased (Seq.seq S64.t))
requires S.pts_to a #pa va ** S.pts_to u vu ** S.pts_to w vw **
  pure (felem (vals va) /\ Seq.length vu == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu ww: Seq.seq S64.t).
  S.pts_to a #pa va ** S.pts_to u wu ** S.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length ww == nl /\
        r == (fev (vals va) % 2 = 1))
{
  S.pts_to_len u;
  copy u a;
  freeze u w;
  with xu. assert (S.pts_to u xu);
  parity (vals xu);
  let x0 = S.(u.(0sz));
  UInt.logand_mask #64 (S64.v x0) 1;
  let bit = S64.logand x0 (S64.classify 1uL);
  let e = S64.eq_mask bit (S64.classify 1uL);
  assert_norm ((pow2 64 - 1) % pow2 8 == pow2 8 - 1);
  let m8 = Cast.u64_to_u8 e;
  Declassify.bool_of_mask m8
}

(** {2 Compression}

    Normalise by the inverse of [Z], keep [y], and hide the least
    significant bit of [x] in the bit that [y < 2^255 - 19] leaves free. *)

#push-options "--z3rlimit 300"

fn point_compress (out: S.slice S8.t) (x y z t: S.slice S64.t)
                  (#vout: erased (Seq.seq S8.t)) (#pp: perm)
                  (#vx: erased (Seq.seq S64.t)) (#vy: erased (Seq.seq S64.t))
                  (#vz: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires S.pts_to out vout **
  S.pts_to x #pp vx ** S.pts_to y #pp vy **
  S.pts_to z #pp vz ** S.pts_to t #pp vt **
  pure (Seq.length vout == 32 /\ P.pt_ok vx vy vz vt)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' **
  S.pts_to x #pp vx ** S.pts_to y #pp vy **
  S.pts_to z #pp vz ** S.pts_to t #pp vt **
  pure (vout' == E.point_compress (P.pt vx vy vz vt))
{
  S.pts_to_len out;
  let zz = S64.zero;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let iz = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let nx = S.from_array a2 16sz;
  let mut a3 = [| zz; 16sz |]; A.pts_to_len a3; let ny = S.from_array a3 16sz;
  let mut a4 = [| zz; 16sz |]; A.pts_to_len a4; let sc = S.from_array a4 16sz;
  let mut a5 = [| zz; 31sz |]; A.pts_to_len a5; let tw = S.from_array a5 31sz;
  S.pts_to_len iz; S.pts_to_len nx; S.pts_to_len ny;
  S.pts_to_len sc; S.pts_to_len tw;

  finv iz z;
  fmul nx x iz tw;
  fmul ny y iz tw;
  freeze nx sc;
  freeze ny sc;
  with ux. assert (S.pts_to nx ux);
  with uy. assert (S.pts_to ny uy);
  C.prime_gt_one ();
  assert_norm (C.prime < pow2 255);

  parity (vals ux);
  let x0 = S.(nx.(0sz));
  UInt.logand_mask #64 (S64.v x0) 1;
  let bit = S64.logand x0 (S64.classify 1uL);
  assert (pure (S64.v bit == eval (vals ux) % 2));

  let hi = S.(ny.(15sz));
  top_limb (vals uy);
  assert_norm (pow2 15 + pow2 15 < pow2 64);
  Math.small_mod (S64.v bit * pow2 15) (pow2 64);
  let w = addw hi (S64.shift_left bit 15ul);
  S.((ny.(15sz) <- w));
  with uy'. assert (S.pts_to ny uy');
  vals_upd uy 15 w;
  set_top (vals uy) (eval (vals ux) % 2);

  store out ny;
  assert_norm (pow2 255 + pow2 255 == pow2 256);
  S.to_array iz; S.to_array nx; S.to_array ny;
  S.to_array sc; S.to_array tw;
}

#pop-options

(** {2 Projective equality}

    [(x1 : z1)] and [(x2 : z2)] are the same affine coordinate when
    [x1 z2 = x2 z1], which costs two multiplications rather than the
    inversion that normalising both would. *)

#push-options "--z3rlimit 300"

fn point_equal (x1 y1 z1 t1 x2 y2 z2 t2: S.slice S64.t)
               (#p1: perm)
               (#vx1: erased (Seq.seq S64.t)) (#vy1: erased (Seq.seq S64.t))
               (#vz1: erased (Seq.seq S64.t)) (#vt1: erased (Seq.seq S64.t))
               (#p2: perm)
               (#vx2: erased (Seq.seq S64.t)) (#vy2: erased (Seq.seq S64.t))
               (#vz2: erased (Seq.seq S64.t)) (#vt2: erased (Seq.seq S64.t))
requires
  S.pts_to x1 #p1 vx1 ** S.pts_to y1 #p1 vy1 **
  S.pts_to z1 #p1 vz1 ** S.pts_to t1 #p1 vt1 **
  S.pts_to x2 #p2 vx2 ** S.pts_to y2 #p2 vy2 **
  S.pts_to z2 #p2 vz2 ** S.pts_to t2 #p2 vt2 **
  pure (P.pt_ok vx1 vy1 vz1 vt1 /\ P.pt_ok vx2 vy2 vz2 vt2)
returns r: bool
ensures
  S.pts_to x1 #p1 vx1 ** S.pts_to y1 #p1 vy1 **
  S.pts_to z1 #p1 vz1 ** S.pts_to t1 #p1 vt1 **
  S.pts_to x2 #p2 vx2 ** S.pts_to y2 #p2 vy2 **
  S.pts_to z2 #p2 vz2 ** S.pts_to t2 #p2 vt2 **
  pure (r == E.point_equal (P.pt vx1 vy1 vz1 vt1) (P.pt vx2 vy2 vz2 vt2))
{
  let zz = S64.zero;
  let mut a1 = [| zz; 16sz |]; A.pts_to_len a1; let p = S.from_array a1 16sz;
  let mut a2 = [| zz; 16sz |]; A.pts_to_len a2; let q = S.from_array a2 16sz;
  let mut a3 = [| zz; 16sz |]; A.pts_to_len a3; let u = S.from_array a3 16sz;
  let mut a4 = [| zz; 16sz |]; A.pts_to_len a4; let v = S.from_array a4 16sz;
  let mut a5 = [| zz; 16sz |]; A.pts_to_len a5; let w = S.from_array a5 16sz;
  let mut a6 = [| zz; 31sz |]; A.pts_to_len a6; let tw = S.from_array a6 31sz;
  S.pts_to_len p; S.pts_to_len q; S.pts_to_len u;
  S.pts_to_len v; S.pts_to_len w; S.pts_to_len tw;

  fmul p x1 z2 tw;
  fmul q x2 z1 tw;
  let e1 = feq p q u v w;
  fmul p y1 z2 tw;
  fmul q y2 z1 tw;
  let e2 = feq p q u v w;

  S.to_array p; S.to_array q; S.to_array u;
  S.to_array v; S.to_array w; S.to_array tw;
  e1 && e2
}

#pop-options

#pop-options
