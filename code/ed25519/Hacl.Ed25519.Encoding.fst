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
open Hacl.Ed25519.Sqrt

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
module Table = Hacl.Impl.Table
module Tables = Hacl.Ed25519.Tables

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

(** Reducing a number below twice the prime leaves it alone exactly when
    it was already reduced. *)
let mod_iff_lt (x: nat)
  : Lemma (requires x < 2 * C.prime)
          (ensures (x % C.prime = x) == (x < C.prime))
  = C.prime_gt_one ();
    if x < C.prime then Math.small_mod x C.prime
    else begin
      Math.lemma_mod_sub x C.prime 1;
      Math.small_mod (x - C.prime) C.prime
    end

(** {2 Deciding} *)

(** [a = b] as field elements.  [u] and [v] take the reduced copies and [w]
    is the scratch that [freeze] wants. *)

#push-options "--z3rlimit 200"

fn limbs_eq (a b: S.slice S64.t)
            (#pa: perm) (#va: erased (Seq.seq S64.t))
            (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
returns r: bool
ensures S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (r == (eval (vals va) = eval (vals vb)))
{
  S.pts_to_len a; S.pts_to_len b;
  let mut m = S64.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (mm: S64.t).
    pts_to i vi ** pts_to m mm ** S.pts_to a #pa va ** S.pts_to b #pb vb **
    pure (SZ.v vi <= 16 /\
          (if (forall (k: nat). k < SZ.v vi ==>
                 Seq.index (vals va) k == Seq.index (vals vb) k)
           then S64.v mm == pow2 64 - 1 else S64.v mm == 0))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let mm = !m;
    let xa = S.(a.(vi));
    let xb = S.(b.(vi));
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
  Classical.move_requires (Seq.lemma_eq_intro (vals va)) (vals vb);
  Classical.move_requires (frozen_unique (vals va)) (vals vb);
  r
}

(** [a = b] as field elements.  [u] and [v] take the reduced copies and [w]
    is the scratch that [freeze] wants. *)
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
  limbs_eq u v
}

(** Is the value this sequence of limbs denotes already below the prime?
    Reducing it does not change it exactly when it is. *)
fn flt_prime (a u w: S.slice S64.t)
             (#pa: perm) (#va: erased (Seq.seq S64.t))
             (#vu: erased (Seq.seq S64.t)) (#vw: erased (Seq.seq S64.t))
requires S.pts_to a #pa va ** S.pts_to u vu ** S.pts_to w vw **
  pure (Seq.length va == nl /\ bnd (vals va) base /\ eval (vals va) < pow2 255 /\
        Seq.length vu == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu ww: Seq.seq S64.t).
  S.pts_to a #pa va ** S.pts_to u wu ** S.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length ww == nl /\
        r == (eval (vals va) < C.prime))
{
  S.pts_to_len u;
  assert_norm (base <= lim);
  copy u a;
  freeze u w;
  with xu. assert (S.pts_to u xu);
  assert_norm (pow2 255 < 2 * C.prime);
  mod_iff_lt (eval (vals va));
  limbs_eq u a
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


(** A public choice between two field elements.  Pulse joins the two
    branches of an [if] against a stated postcondition, not against each
    other, so a conditional copy has to be a function of its own. *)
fn fselect (out a b: S.slice S64.t) (c: bool)
           (#vout: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires S.pts_to out vout ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ Seq.length va == nl /\ Seq.length vb == nl)
ensures exists* (w: Seq.seq S64.t).
  S.pts_to out w ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  pure (w == (if c then reveal va else reveal vb))
{
  if c { copy out a } else { copy out b }
}

(** Negate, or do not. *)
fn fneg_if (a: S.slice S64.t) (c: bool) (#va: erased (Seq.seq S64.t))
requires S.pts_to a va ** pure (felem (vals va))
ensures exists* (w: Seq.seq S64.t).
  S.pts_to a w **
  pure (felem (vals w) /\
        fev (vals w) == (if c then C.fsub 0 (fev (vals va)) else fev (vals va)))
{
  if c {
    S.pts_to_len a;
    let zz = S64.zero;
    let mut k1 = [| zz; 16sz |]; A.pts_to_len k1; let kb = S.from_array k1 16sz;
    let mut k2 = [| zz; 16sz |]; A.pts_to_len k2; let f1 = S.from_array k2 16sz;
    S.pts_to_len kb; S.pts_to_len f1;
    P.set_small kb 0uL;
    copy f1 a;
    fsub a kb f1;
    S.to_array kb;
    S.to_array f1
  } else {
    ()
  }
}


(** {2 Decompression}

    Recovering [x] from [y] is a square root of [(y^2 - 1)/(d y^2 + 1)],
    and there are three ways for it to fail: the denominator vanishes, the
    quotient is not a square, or the root is zero and the sign bit asks for
    the negative zero that does not exist.  None of the three is secret --
    a compressed point is public -- so the failures are collected into
    ordinary booleans and the arithmetic runs unconditionally, which is
    both simpler and faster than branching out early.

    [ox] receives the candidate; the caller looks at the result before
    using it. *)

(** What [recover_x] decides, in three steps.

    Stating it in one lemma does not work: the query has to see the
    two hundred and fifty-five bit literals [d] and [sqrt_m1] *and* do a
    five-way case analysis, and Z3 will not finish.  Split so that no
    single query does both -- [body] is [recover_x] with the constants
    abstracted, [body_eq] names the values the code computes, and
    [body3_char] is pure boolean reasoning -- the whole thing is under a
    second. *)

#push-options "--fuel 0 --ifuel 2 --z3rlimit 50"

let body (dd sm y: C.elem) (sign: nat { sign < 2 }) : option C.elem =
  let v = C.fadd (C.fmul dd (C.fmul y y)) C.one in
  if v = 0 then None
  else
    let w = C.fmul (C.fsub (C.fmul y y) C.one) (C.finv v) in
    let x1 = E.modp_sqrt w in
    let x2 = C.fmul x1 sm in
    if C.fmul x1 x1 = w then
      (if x1 = 0 && sign = 1 then None
       else if x1 % 2 = sign then Some x1 else Some (C.fsub 0 x1))
    else if C.fmul x2 x2 = w then
      (if x2 = 0 && sign = 1 then None
       else if x2 % 2 = sign then Some x2 else Some (C.fsub 0 x2))
    else None

let body_ok (y: C.elem) (sign: nat { sign < 2 })
  : Lemma (E.recover_x y sign == body E.d E.sqrt_m1 y sign) = ()

(** The same thing once the three tests have been made. *)
let body3 (sign: nat { sign < 2 }) (x1 x2: C.elem) (vzero ok1 ok2: bool)
  : option C.elem =
  if vzero then None
  else if ok1 then
    (if x1 = 0 && sign = 1 then None
     else if x1 % 2 = sign then Some x1 else Some (C.fsub 0 x1))
  else if ok2 then
    (if x2 = 0 && sign = 1 then None
     else if x2 % 2 = sign then Some x2 else Some (C.fsub 0 x2))
  else None

let body_eq (dd sm y: C.elem) (sign: nat { sign < 2 })
            (u v w x1 x2: C.elem) (vzero ok1 ok2: bool)
  : Lemma (requires
             u == C.fsub (C.fmul y y) C.one /\
             v == C.fadd (C.fmul dd (C.fmul y y)) C.one /\
             vzero == (v = 0) /\ w == C.fmul u (C.finv v) /\
             x1 == E.modp_sqrt w /\ ok1 == (C.fmul x1 x1 = w) /\
             x2 == C.fmul x1 sm /\ ok2 == (C.fmul x2 x2 = w))
          (ensures body dd sm y sign == body3 sign x1 x2 vzero ok1 ok2)
  = ()

let body3_char (sign: nat { sign < 2 }) (x1 x2 xr: C.elem)
               (vzero ok1 ok2 xzero xodd: bool)
  : Lemma (requires xr == (if ok1 then x1 else x2) /\
                    xzero == (xr = 0) /\ xodd == (xr % 2 = 1))
          (ensures
             (let ok = not vzero && (ok1 || ok2) && not (xzero && sign = 1) in
              let res = if xodd = (sign = 1) then xr else C.fsub 0 xr in
              match body3 sign x1 x2 vzero ok1 ok2 with
              | None -> ok == false
              | Some x -> ok == true /\ res == x))
  = Math.lemma_mod_lt xr 2

#pop-options

(** {2 Decompression}

    Recovering [x] from [y] is a square root of [(y^2 - 1)/(d y^2 + 1)],
    and there are three ways for it to fail: the denominator vanishes, the
    quotient is not a square, or the root is zero and the sign bit asks for
    the negative zero that does not exist.  None of the three is secret --
    a compressed point is public -- so the failures are collected into
    ordinary booleans and the arithmetic runs unconditionally, which is
    both simpler and faster than branching out early.

    [ox] receives the candidate; the caller looks at the result before
    using it. *)

#push-options "--fuel 0 --ifuel 2 --z3rlimit 200"

fn recover_x (ox yb: S.slice S64.t) (sign: bool)
             (#vox: erased (Seq.seq S64.t))
             (#py: perm) (#vy: erased (Seq.seq S64.t))
requires S.pts_to ox vox ** S.pts_to yb #py vy **
  pure (Seq.length vox == nl /\ felem (vals vy))
returns ok: bool
ensures exists* (wx: Seq.seq S64.t).
  S.pts_to ox wx ** S.pts_to yb #py vy **
  pure (Seq.length wx == nl /\
        (match E.recover_x (fev (vals vy)) (if sign then 1 else 0) with
         | None -> ok == false
         | Some x -> ok == true /\ felem (vals wx) /\ fev (vals wx) == x))
{
  S.pts_to_len ox;
  let zz = S64.zero;
  let mut b1 = [| zz; 16sz |]; A.pts_to_len b1; let y2 = S.from_array b1 16sz;
  let mut b2 = [| zz; 16sz |]; A.pts_to_len b2; let uu = S.from_array b2 16sz;
  let mut b3 = [| zz; 16sz |]; A.pts_to_len b3; let vv = S.from_array b3 16sz;
  let mut b4 = [| zz; 16sz |]; A.pts_to_len b4; let ww = S.from_array b4 16sz;
  let mut b5 = [| zz; 16sz |]; A.pts_to_len b5; let xs = S.from_array b5 16sz;
  let mut b6 = [| zz; 16sz |]; A.pts_to_len b6; let k = S.from_array b6 16sz;
  let mut b7 = [| zz; 16sz |]; A.pts_to_len b7; let f1 = S.from_array b7 16sz;
  let mut b8 = [| zz; 16sz |]; A.pts_to_len b8; let f2 = S.from_array b8 16sz;
  let mut b9 = [| zz; 16sz |]; A.pts_to_len b9; let f3 = S.from_array b9 16sz;
  let mut ba = [| zz; 31sz |]; A.pts_to_len ba; let tw = S.from_array ba 31sz;
  S.pts_to_len y2; S.pts_to_len uu; S.pts_to_len vv; S.pts_to_len ww;
  S.pts_to_len xs; S.pts_to_len k; S.pts_to_len f1; S.pts_to_len f2;
  S.pts_to_len f3; S.pts_to_len tw;

  P.set_small k 1uL;
  C.prime_gt_one ();

  (* y2 = y^2, u = y2 - 1, v = d y2 + 1 *)
  copy f1 yb;
  fmul y2 f1 yb tw;
  fsub uu y2 k;
  with su. assert (S.pts_to uu su);
  let dt = Table.table Tables.d_arr 16sz;
  Tables.d_ok ();
  fmul vv dt y2 tw;
  Table.drop_table dt;
  copy f1 vv;
  fadd vv f1 k;
  with sv. assert (S.pts_to vv sv);

  let vzero = fzerop vv f1 f2;

  (* w = u / v *)
  finv ww vv;
  copy f1 ww;
  fmul ww uu f1 tw;
  with sw. assert (S.pts_to ww sw);

  (* the first candidate, w^((p+3)/8) *)
  fsqrt xs ww;
  with sx1. assert (S.pts_to xs sx1);
  copy f1 xs;
  fmul y2 f1 xs tw;
  let ok1 = feq y2 ww f1 f2 f3;

  (* the second, that one times sqrt(-1) *)
  let sm = Table.table Tables.sqrtm1_arr 16sz;
  Tables.sqrtm1_ok ();
  copy f1 xs;
  fmul uu f1 sm tw;
  Table.drop_table sm;
  with sx2. assert (S.pts_to uu sx2);
  copy f1 uu;
  fmul y2 f1 uu tw;
  let ok2 = feq y2 ww f1 f2 f3;

  fselect ox xs uu ok1;
  with sxr. assert (S.pts_to ox sxr);

  let xzero = fzerop ox f1 f2;
  let xodd = fodd ox f1 f2;

  fneg_if ox (xodd <> sign);
  with wx. assert (S.pts_to ox wx);

  let ok = (not vzero) && (ok1 || ok2) && (not (xzero && sign));
  body_ok (fev (vals vy)) (if sign then 1 else 0);
  body_eq E.d E.sqrt_m1 (fev (vals vy)) (if sign then 1 else 0)
          (fev (vals su)) (fev (vals sv)) (fev (vals sw))
          (fev (vals sx1)) (fev (vals sx2)) vzero ok1 ok2;
  body3_char (if sign then 1 else 0) (fev (vals sx1)) (fev (vals sx2))
             (fev (vals sxr)) vzero ok1 ok2 xzero xodd;
  assert (pure (match E.recover_x (fev (vals vy)) (if sign then 1 else 0) with
                | None -> ok == false
                | Some x -> ok == true /\ felem (vals wx) /\
                            fev (vals wx) == x));

  S.to_array y2; S.to_array uu; S.to_array vv; S.to_array ww;
  S.to_array xs; S.to_array k; S.to_array f1; S.to_array f2;
  S.to_array f3; S.to_array tw;
  ok
}

#pop-options

#pop-options
