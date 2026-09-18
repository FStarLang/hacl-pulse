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

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
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
    assert_norm (base == 2 * 1125899906842624);
    Math.lemma_mod_plus (Seq.index s 0) (1125899906842624 * eval (Seq.slice s 1 nl)) 2

(** Writing the sign bit.  At radix [2^51] bit [255] is one past the top of
    the fifth limb, so the bit goes into the top *byte* rather than the top
    limb: byte [31] of a number below [2^255] is below [2^7], and adding
    [b * 2^7] to it adds [b * 2^255] to the number.  Every other byte is
    untouched, because [b * 2^255] is a multiple of [2^(8i+8)] for [i < 31]. *)
let set_top_byte (v: nat) (b: nat { b < 2 }) (i: nat { i < 32 })
  : Lemma (requires v < pow2 255)
          (ensures S8.v (Seq.index (nat_to_le 32 (v + b * pow2 255)) i) ==
                   (if i = 31 then S8.v (Seq.index (nat_to_le 32 v) 31) + b * 128
                              else S8.v (Seq.index (nat_to_le 32 v) i)))
  = nat_to_le_index 32 v i;
    nat_to_le_index 32 (v + b * pow2 255) i;
    if i = 31 then begin
      assert_norm (8 * 31 == 248);
      assert_norm (pow2 255 == 128 * pow2 248);
      Math.paren_mul_right b 128 (pow2 248);
      Math.lemma_div_plus v (b * 128) (pow2 248);
      Math.lemma_div_lt_nat v 255 248;
      assert_norm (pow2 (255 - 248) == 128);
      Math.small_mod (v / pow2 248 + b * 128) 256
    end else begin
      let e : nat = 255 - 8 * i in
      Math.pow2_plus (8 * i) e;
      Math.paren_mul_right b (pow2 e) (pow2 (8 * i));
      Math.lemma_div_plus v (b * pow2 e) (pow2 (8 * i));
      Math.pow2_plus 8 (e - 8);
      Math.paren_mul_right b 256 (pow2 (e - 8));
      Math.swap_mul 256 (pow2 (e - 8));
      Math.paren_mul_right b (pow2 (e - 8)) 256;
      Math.lemma_mod_plus (v / pow2 (8 * i)) (b * pow2 (e - 8)) 256
    end

(** The whole byte string, from the index-wise statement. *)
let set_top_bytes (v: nat) (b: nat { b < 2 }) (o: Seq.seq S8.t)
  : Lemma (requires v < pow2 255 /\ Seq.length o == 32 /\
                    (forall (i: nat). i < 32 ==>
                       S8.v (Seq.index o i) ==
                         (if i = 31 then S8.v (Seq.index (nat_to_le 32 v) 31) + b * 128
                                    else S8.v (Seq.index (nat_to_le 32 v) i))))
          (ensures o == nat_to_le 32 (v + b * pow2 255))
  = let aux (i: nat { i < 32 })
      : Lemma (Seq.index o i == Seq.index (nat_to_le 32 (v + b * pow2 255)) i)
      = set_top_byte v b i;
        S8.v_extensional (Seq.index o i)
                         (Seq.index (nat_to_le 32 (v + b * pow2 255)) i) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro o (nat_to_le 32 (v + b * pow2 255))

(** Two reduced elements with the same value have the same limbs. *)
let frozen_unique (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl /\
                    bnd a base /\ bnd b base /\ eval a == eval b)
          (ensures a == b)
  = limbs_unique a (eval a); limbs_unique b (eval b)

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

fn limbs_eq (a b: A.array S64.t)
            (#pa: perm) (#va: erased (Seq.seq S64.t))
            (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (eval (vals va) = eval (vals vb)))
{
  A.pts_to_len a; A.pts_to_len b;
  let mut m = S64.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 5sz)
  invariant exists* (vi: SZ.t) (mm: S64.t).
    pts_to i vi ** pts_to m mm ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= 5 /\
          (if (forall (k: nat). k < SZ.v vi ==>
                 Seq.index (vals va) k == Seq.index (vals vb) k)
           then S64.v mm == pow2 64 - 1 else S64.v mm == 0))
  decreases (5 - SZ.v (!i))
  {
    let vi = !i;
    let mm = !m;
    let xa = A.(a.(vi));
    let xb = A.(b.(vi));
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
fn feq (a b u v w: A.array S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
       (#vu: erased (Seq.seq S64.t)) (#vv: erased (Seq.seq S64.t))
       (#vw: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to u vu ** A.pts_to v vv ** A.pts_to w vw **
  pure (felem (vals va) /\ felem (vals vb) /\
        Seq.length vu == nl /\ Seq.length vv == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu wv ww: Seq.seq S64.t).
  A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to u wu ** A.pts_to v wv ** A.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length wv == nl /\ Seq.length ww == nl /\
        r == (fev (vals va) = fev (vals vb)))
{
  A.pts_to_len u; A.pts_to_len v;
  copy u a;
  copy v b;
  freeze u w;
  freeze v w;
  limbs_eq u v
}

(** Is the value this sequence of limbs denotes already below the prime?
    Reducing it does not change it exactly when it is. *)
fn flt_prime (a u w: A.array S64.t)
             (#pa: perm) (#va: erased (Seq.seq S64.t))
             (#vu: erased (Seq.seq S64.t)) (#vw: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to u vu ** A.pts_to w vw **
  pure (Seq.length va == nl /\ bnd (vals va) base /\ eval (vals va) < pow2 255 /\
        Seq.length vu == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu ww: Seq.seq S64.t).
  A.pts_to a #pa va ** A.pts_to u wu ** A.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length ww == nl /\
        r == (eval (vals va) < C.prime))
{
  A.pts_to_len u;
  assert_norm (base <= lim);
  copy u a;
  freeze u w;
  with xu. assert (A.pts_to u xu);
  assert_norm (pow2 255 < 2 * C.prime);
  mod_iff_lt (eval (vals va));
  limbs_eq u a
}

#pop-options

(** [a = 0] as a field element. *)
fn fzerop (a u w: A.array S64.t)
          (#pa: perm) (#va: erased (Seq.seq S64.t))
          (#vu: erased (Seq.seq S64.t)) (#vw: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to u vu ** A.pts_to w vw **
  pure (felem (vals va) /\ Seq.length vu == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu ww: Seq.seq S64.t).
  A.pts_to a #pa va ** A.pts_to u wu ** A.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length ww == nl /\
        r == (fev (vals va) = 0))
{
  A.pts_to_len u;
  let z = S64.zero;
  let mut az = [| z; 5sz |]; A.pts_to_len az; let mut ay = [| z; 5sz |]; A.pts_to_len ay; A.pts_to_len az; A.pts_to_len ay;
  P.set_small az 0uL;
  let r = feq a az u ay w;
  r
}

(** The least significant bit. *)
fn fodd (a u w: A.array S64.t)
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#vu: erased (Seq.seq S64.t)) (#vw: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to u vu ** A.pts_to w vw **
  pure (felem (vals va) /\ Seq.length vu == nl /\ Seq.length vw == nl)
returns r: bool
ensures exists* (wu ww: Seq.seq S64.t).
  A.pts_to a #pa va ** A.pts_to u wu ** A.pts_to w ww **
  pure (Seq.length wu == nl /\ Seq.length ww == nl /\
        r == (fev (vals va) % 2 = 1))
{
  A.pts_to_len u;
  copy u a;
  freeze u w;
  with xu. assert (A.pts_to u xu);
  parity (vals xu);
  let x0 = A.(u.(0sz));
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

fn point_compress (out: A.array S8.t) (x y z t: A.array S64.t)
                  (#vout: erased (Seq.seq S8.t)) (#pp: perm)
                  (#vx: erased (Seq.seq S64.t)) (#vy: erased (Seq.seq S64.t))
                  (#vz: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S64.t))
requires A.pts_to out vout **
  A.pts_to x #pp vx ** A.pts_to y #pp vy **
  A.pts_to z #pp vz ** A.pts_to t #pp vt **
  pure (Seq.length vout == 32 /\ P.pt_ok vx vy vz vt)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' **
  A.pts_to x #pp vx ** A.pts_to y #pp vy **
  A.pts_to z #pp vz ** A.pts_to t #pp vt **
  pure (vout' == E.point_compress (P.pt vx vy vz vt))
{
  A.pts_to_len out;
  let zz = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut a1 = [| zz; 5sz |]; A.pts_to_len a1; let mut a2 = [| zz; 5sz |]; A.pts_to_len a2; let mut a3 = [| zz; 5sz |]; A.pts_to_len a3; let mut a4 = [| zz; 5sz |]; A.pts_to_len a4; let mut a5 = [| z128; 9sz |]; A.pts_to_len a5; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len a5;

  finv a1 z;
  fmul a2 x a1 a5;
  fmul a3 y a1 a5;
  freeze a2 a4;
  freeze a3 a4;
  with ux. assert (A.pts_to a2 ux);
  with uy. assert (A.pts_to a3 uy);
  C.prime_gt_one ();
  assert_norm (C.prime < pow2 255);

  parity (vals ux);
  let x0 = A.(a2.(0sz));
  UInt.logand_mask #64 (S64.v x0) 1;
  let bit = S64.logand x0 (S64.classify 1uL);
  assert (pure (S64.v bit == eval (vals ux) % 2));

  store out a3;
  with vo. assert (A.pts_to out vo);
  A.pts_to_len out;
  let b31 = A.(out.(31sz));
  nat_to_le_index 32 (eval (vals uy)) 31;
  assert_norm (8 * 31 == 248);
  Math.lemma_div_lt_nat (eval (vals uy)) 255 248;
  assert_norm (pow2 (255 - 248) == 128);
  Math.small_mod (eval (vals uy) / pow2 248) 256;
  assert (pure (S8.v b31 < 128));
  assert_norm (pow2 7 == 128);
  Math.small_mod (S64.v bit * 128) (pow2 64);
  let sh = S64.shift_left bit 7ul;
  let sb = Cast.u64_to_u8 sh;
  assert_norm (128 + 128 == 256);
  Math.small_mod (S8.v b31 + S8.v sb) 256;
  let w = S8.add_mod b31 sb;
  A.((out.(31sz) <- w));
  with vo'. assert (A.pts_to out vo');
  assert (pure (forall (i: nat). i < 32 ==>
                  S8.v (Seq.index vo' i) ==
                    (if i = 31 then S8.v (Seq.index (nat_to_le 32 (eval (vals uy))) 31) +
                                    (eval (vals ux) % 2) * 128
                               else S8.v (Seq.index (nat_to_le 32 (eval (vals uy))) i))));
  set_top_bytes (eval (vals uy)) (eval (vals ux) % 2) vo';
  assert_norm (pow2 255 + pow2 255 == pow2 256);
  ()
}

#pop-options

(** {2 Projective equality}

    [(x1 : z1)] and [(x2 : z2)] are the same affine coordinate when
    [x1 z2 = x2 z1], which costs two multiplications rather than the
    inversion that normalising both would. *)

#push-options "--z3rlimit 300"

fn point_equal (x1 y1 z1 t1 x2 y2 z2 t2: A.array S64.t)
               (#p1: perm)
               (#vx1: erased (Seq.seq S64.t)) (#vy1: erased (Seq.seq S64.t))
               (#vz1: erased (Seq.seq S64.t)) (#vt1: erased (Seq.seq S64.t))
               (#p2: perm)
               (#vx2: erased (Seq.seq S64.t)) (#vy2: erased (Seq.seq S64.t))
               (#vz2: erased (Seq.seq S64.t)) (#vt2: erased (Seq.seq S64.t))
requires
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 **
  A.pts_to z1 #p1 vz1 ** A.pts_to t1 #p1 vt1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
  A.pts_to z2 #p2 vz2 ** A.pts_to t2 #p2 vt2 **
  pure (P.pt_ok vx1 vy1 vz1 vt1 /\ P.pt_ok vx2 vy2 vz2 vt2)
returns r: bool
ensures
  A.pts_to x1 #p1 vx1 ** A.pts_to y1 #p1 vy1 **
  A.pts_to z1 #p1 vz1 ** A.pts_to t1 #p1 vt1 **
  A.pts_to x2 #p2 vx2 ** A.pts_to y2 #p2 vy2 **
  A.pts_to z2 #p2 vz2 ** A.pts_to t2 #p2 vt2 **
  pure (r == E.point_equal (P.pt vx1 vy1 vz1 vt1) (P.pt vx2 vy2 vz2 vt2))
{
  let zz = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut a1 = [| zz; 5sz |]; A.pts_to_len a1; let mut a2 = [| zz; 5sz |]; A.pts_to_len a2; let mut a3 = [| zz; 5sz |]; A.pts_to_len a3; let mut a4 = [| zz; 5sz |]; A.pts_to_len a4; let mut a5 = [| zz; 5sz |]; A.pts_to_len a5; let mut a6 = [| z128; 9sz |]; A.pts_to_len a6; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len a5; A.pts_to_len a6;

  fmul a1 x1 z2 a6;
  fmul a2 x2 z1 a6;
  let e1 = feq a1 a2 a3 a4 a5;
  fmul a1 y1 z2 a6;
  fmul a2 y2 z1 a6;
  let e2 = feq a1 a2 a3 a4 a5;

  e1 && e2
}

#pop-options

(** A public choice between two field elements.  Pulse joins the two
    branches of an [if] against a stated postcondition, not against each
    other, so a conditional copy has to be a function of its own. *)
fn fselect (out a b: A.array S64.t) (c: bool)
           (#vout: erased (Seq.seq S64.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == nl /\ Seq.length va == nl /\ Seq.length vb == nl)
ensures exists* (w: Seq.seq S64.t).
  A.pts_to out w ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (w == (if c then reveal va else reveal vb))
{
  if c { copy out a } else { copy out b }
}

(** Negate, or do not. *)
fn fneg_if (a: A.array S64.t) (c: bool) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (felem (vals va))
ensures exists* (w: Seq.seq S64.t).
  A.pts_to a w **
  pure (felem (vals w) /\
        fev (vals w) == (if c then C.fsub 0 (fev (vals va)) else fev (vals va)))
{
  if c {
    A.pts_to_len a;
    let zz = S64.zero;
    let mut k1 = [| zz; 5sz |]; A.pts_to_len k1;
    let mut k2 = [| zz; 5sz |]; A.pts_to_len k2;
    P.set_small k1 0uL;
    copy k2 a;
    fsub a k1 k2
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

fn recover_x (ox yb: A.array S64.t) (sign: bool)
             (#vox: erased (Seq.seq S64.t))
             (#py: perm) (#vy: erased (Seq.seq S64.t))
requires A.pts_to ox vox ** A.pts_to yb #py vy **
  pure (Seq.length vox == nl /\ felem (vals vy))
returns ok: bool
ensures exists* (wx: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to yb #py vy **
  pure (Seq.length wx == nl /\
        (match E.recover_x (fev (vals vy)) (if sign then 1 else 0) with
         | None -> ok == false
         | Some x -> ok == true /\ felem (vals wx) /\ fev (vals wx) == x))
{
  A.pts_to_len ox;
  let zz = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut b1 = [| zz; 5sz |]; A.pts_to_len b1; let mut b2 = [| zz; 5sz |]; A.pts_to_len b2; let mut b3 = [| zz; 5sz |]; A.pts_to_len b3; let mut b4 = [| zz; 5sz |]; A.pts_to_len b4; let mut b5 = [| zz; 5sz |]; A.pts_to_len b5; let mut b6 = [| zz; 5sz |]; A.pts_to_len b6; let mut b7 = [| zz; 5sz |]; A.pts_to_len b7; let mut b8 = [| zz; 5sz |]; A.pts_to_len b8; let mut b9 = [| zz; 5sz |]; A.pts_to_len b9; let mut ba = [| z128; 9sz |]; A.pts_to_len ba; A.pts_to_len b1; A.pts_to_len b2; A.pts_to_len b3; A.pts_to_len b4;
  A.pts_to_len b5; A.pts_to_len b6; A.pts_to_len b7; A.pts_to_len b8;
  A.pts_to_len b9; A.pts_to_len ba;

  assert_norm (1 < base);
  P.set_small b6 1uL;
  C.prime_gt_one ();

  (* b1 = y^2, u = b1 - 1, v = d b1 + 1 *)
  copy b7 yb;
  fmul b1 b7 yb ba;
  fsub b2 b1 b6;
  with su. assert (A.pts_to b2 su);
  let dt = Table.table Tables.d_arr 5sz;
  Tables.d_ok ();
  fmul b3 dt b1 ba;
  Table.drop_table dt;
  copy b7 b3;
  fadd b3 b7 b6;
  with sv. assert (A.pts_to b3 sv);

  let vzero = fzerop b3 b7 b8;

  (* w = u / v *)
  finv b4 b3;
  copy b7 b4;
  fmul b4 b2 b7 ba;
  with sw. assert (A.pts_to b4 sw);

  (* the first candidate, w^((p+3)/8) *)
  fsqrt b5 b4;
  with sx1. assert (A.pts_to b5 sx1);
  copy b7 b5;
  fmul b1 b7 b5 ba;
  let ok1 = feq b1 b4 b7 b8 b9;

  (* the second, that one times sqrt(-1) *)
  let sm = Table.table Tables.sqrtm1_arr 5sz;
  Tables.sqrtm1_ok ();
  copy b7 b5;
  fmul b2 b7 sm ba;
  Table.drop_table sm;
  with sx2. assert (A.pts_to b2 sx2);
  copy b7 b2;
  fmul b1 b7 b2 ba;
  let ok2 = feq b1 b4 b7 b8 b9;

  fselect ox b5 b2 ok1;
  with sxr. assert (A.pts_to ox sxr);

  let xzero = fzerop ox b7 b8;
  let xodd = fodd ox b7 b8;

  fneg_if ox (xodd <> sign);
  with wx. assert (A.pts_to ox wx);

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

  ok
}

#pop-options

#pop-options

(** The sign bit is the top bit of the last byte, which is bit [255] of the
    number the thirty-two bytes encode. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"

let sign_bit (s: Seq.seq S8.t { Seq.length s == 32 })
  : Lemma (le_nat s / pow2 255 == S8.v (Seq.index s 31) / pow2 7)
  = let lo = le_nat (Seq.slice s 0 31) in
    let hi = le_nat (Seq.slice s 31 32) in
    le_nat_split s 31;
    le_nat_bound (Seq.slice s 0 31);
    le_nat_cons s 31;
    assert (hi == S8.v (Seq.index s 31));
    Math.pow2_plus 248 7;
    Math.small_div lo (pow2 248);
    Math.lemma_div_plus lo hi (pow2 248);
    assert ((lo + pow2 248 * hi) / pow2 248 == hi);
    Math.division_multiplication_lemma (lo + pow2 248 * hi) (pow2 248) (pow2 7)

#pop-options

(** {2 Decompression}

    The inverse of [point_compress]: read [y] and the sign of [x] from the
    bytes, then solve the curve equation for [x].  Three things can go
    wrong -- [y] may not be a field element, the equation may have no
    solution, and the sign bit may ask for a negative zero -- and all three
    are public, so the answer comes back as an ordinary boolean.

    The coordinates are only meaningful when that boolean is [true]. *)

#push-options "--fuel 0 --ifuel 2 --z3rlimit 800"

fn point_decompress (ox oy oz ot: A.array S64.t) (s: A.array S8.t)
                    (#vox: erased (Seq.seq S64.t)) (#voy: erased (Seq.seq S64.t))
                    (#voz: erased (Seq.seq S64.t)) (#vot: erased (Seq.seq S64.t))
                    (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ot vot ** A.pts_to s #ps vs **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl)
returns ok: bool
ensures exists* (wx: Seq.seq S64.t) (wy: Seq.seq S64.t)
                (wz: Seq.seq S64.t) (wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ot wt ** A.pts_to s #ps vs **
  pure (Seq.length wx == nl /\ Seq.length wy == nl /\
        Seq.length wz == nl /\ Seq.length wt == nl /\
        (match E.point_decompress vs with
         | None -> ok == false
         | Some p -> ok == true /\ P.pt_ok wx wy wz wt /\ P.pt wx wy wz wt == p))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len s;
  let zz = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut c1 = [| zz; 5sz |]; A.pts_to_len c1; let mut c2 = [| zz; 5sz |]; A.pts_to_len c2; let mut c3 = [| z128; 9sz |]; A.pts_to_len c3; A.pts_to_len c1; A.pts_to_len c2; A.pts_to_len c3;

  load oy s;
  with wy0. assert (A.pts_to oy wy0);
  assert (pure (ble (vals wy0) (base - 1)));
  assert_norm (base - 1 <= lim);
  ble_mono (vals wy0) (base - 1) lim;

  let b31 = A.(s.(31sz));
  let sb = S8.shift_right b31 7ul;
  let m = S8.eq_mask sb (S8.classify 1uy);
  let sign = Declassify.bool_of_mask m;
  sign_bit vs;
  Math.lemma_div_lt_nat (S8.v b31) 8 7;
  assert_norm (pow2 1 == 2);
  assert (pure (S8.v sb == S8.v (Seq.index vs 31) / pow2 7));
  assert_norm (U8.v 1uy == 1);
  assert (pure (sign == (S8.v sb = 1)));
  assert (pure (S8.v sb < 2));
  assert (pure ((if sign then 1 else 0) == le_nat vs / pow2 255));

  let lt = flt_prime oy c1 c2;

  if lt {
    Math.modulo_lemma (eval (vals wy0)) C.prime;
    let ok = recover_x ox oy sign;
    if ok {
      assert_norm (1 < base);
      P.set_small oz 1uL;
      copy c1 ox;
      fmul ot c1 oy c3;
      true
    } else {
      false
    }
  } else {
    false
  }
}

#pop-options
