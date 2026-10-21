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

(** The number-theoretic transforms and the pointwise product of ML-DSA,
    eight coefficients at a time, with AVX2.

    {2 Arithmetic}

    A coefficient stays a canonical word below [q] in every lane, so lane
    [j] of a vector is literally the specification's value, and the lane
    arithmetic is {!Hacl.Impl.MLDSA.Zq}'s, transcribed:

    - the conditional subtraction is an unsigned minimum: for [x < 2q],
      [x - q] wraps above [x] exactly when [x < q];
    - Shoup's multiplication by a tabulated root wants the high half of a
      thirty-two-bit product, which {!Hacl.Vec256.Lane32.mulhi32} gives,
      and the low halves of two, which wrap but whose difference is known
      to be below [2q];
    - the general product is Montgomery's, in the form that subtracts:
      with [t = (a b) q^-1 mod 2^32], the low halves of [a b] and [t q]
      are equal, so [(a b - t q) / 2^32] is the difference of the high
      halves, lies in [(-q, q)], and is [a b 2^-32] modulo [q]; one Shoup
      step by [2^32 mod q] then undoes the [2^-32].

    {2 Layers}

    A layer of half-width [len >= 8] is the scalar code with [c] stepping
    by eight: the two vectors at [lo + c] and [lo + len + c] are eight
    independent butterflies under one broadcast root, and {!part} is the
    same invariant.  The last three layers (half-widths four, two and one)
    stay inside sixteen coefficients, so they are done together, two
    vectors at a time: before each one, a shuffle puts the upper input of
    every butterfly in the lane of [y] that corresponds to its lower input's
    lane of [x], and after it, the same shuffle (each is its own inverse)
    puts the coefficients back.  The roots then differ from lane to lane;
    they are eight consecutive entries of the table, permuted. *)
module Hacl.Impl.MLDSA.NTT.Vec256

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.NTT
open Hacl.Impl.MLDSA.Zq
open Hacl.MLDSA.Tables
open Hacl.Impl.MLDSA.NTT

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module T = Hacl.Impl.Table
module HSZ = Hacl.SizeT
module V = Hacl.Vec256
module L = Hacl.Vec256.Lane32
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Lane arithmetic} *)

let vlt (x: V.t) (m: nat) : prop = forall (i: nat). i < 8 ==> S32.v (V.lane x i) < m

inline_for_extraction
let vq () : r: V.t { forall (i: nat). i < 8 ==> S32.v (V.lane r i) == q } = V.bcast qw

let min_csub (x y: S32.t)
  : Lemma (requires S32.v x < 2 * q /\ S32.v y == q)
          (ensures (let d = S32.sub_mod x y in
                    S32.v (if S32.v x <= S32.v d then x else d) == S32.v x % q))
  = assert_norm (2 * q < pow2 32);
    if S32.v x >= q then begin
      Math.small_mod (S32.v x - q) (pow2 32);
      Math.small_mod (S32.v x - q) q;
      Math.lemma_mod_plus (S32.v x - q) 1 q
    end else begin
      Math.lemma_mod_plus (S32.v x - q) 1 (pow2 32);
      Math.small_mod (S32.v x - q + pow2 32) (pow2 32);
      Math.small_mod (S32.v x) q
    end

inline_for_extraction
let vcsub (x: V.t { vlt x (2 * q) })
  : r: V.t { vlt r q /\
             (forall (i: nat). i < 8 ==> S32.v (V.lane r i) == S32.v (V.lane x i) % q) }
  = let qv = vq () in
    let d = L.sub32 x qv in
    let r = L.minu32 x d in
    let aux (i: nat { i < 8 })
                             : Lemma (ensures S32.v (V.lane r i) == S32.v (V.lane x i) % q)
      = min_csub (V.lane x i) (V.lane qv i) in
    Classical.forall_intro aux;
    r

let add_lane (x y s: S32.t)
  : Lemma (requires S32.v x < q /\ S32.v y < q /\ S32.v s == (S32.v x + S32.v y) % pow2 32)
          (ensures S32.v s == S32.v x + S32.v y /\ S32.v s < 2 * q)
  = assert_norm (2 * q < pow2 32);
    Math.small_mod (S32.v x + S32.v y) (pow2 32)

inline_for_extraction
let vadd (x: V.t { vlt x q }) (y: V.t { vlt y q })
  : r: V.t { vlt r q /\
             (forall (i: nat). i < 8 ==>
                S32.v (V.lane r i) == add (S32.v (V.lane x i)) (S32.v (V.lane y i))) }
  = let s = V.add32 x y in
    let aux (i: nat { i < 8 })
                             : Lemma (ensures S32.v (V.lane s i) == S32.v (V.lane x i) + S32.v (V.lane y i) /\
                                      S32.v (V.lane s i) < 2 * q)
      = add_lane (V.lane x i) (V.lane y i) (V.lane s i) in
    Classical.forall_intro aux;
    vcsub s

let sub_lane (x y qq s u: S32.t)
  : Lemma (requires S32.v x < q /\ S32.v y < q /\ S32.v qq == q /\
                    S32.v s == (S32.v x + S32.v qq) % pow2 32 /\
                    S32.v u == (S32.v s - S32.v y) % pow2 32)
          (ensures S32.v u == S32.v x + q - S32.v y /\ S32.v u < 2 * q)
  = assert_norm (2 * q < pow2 32);
    Math.small_mod (S32.v x + q) (pow2 32);
    Math.small_mod (S32.v x + q - S32.v y) (pow2 32)

inline_for_extraction
let vsub (x: V.t { vlt x q }) (y: V.t { vlt y q })
  : r: V.t { vlt r q /\
             (forall (i: nat). i < 8 ==>
                S32.v (V.lane r i) == sub (S32.v (V.lane x i)) (S32.v (V.lane y i))) }
  = let qv = vq () in
    let s = V.add32 x qv in
    let u = L.sub32 s y in
    let aux (i: nat { i < 8 })
                             : Lemma (ensures S32.v (V.lane u i) == S32.v (V.lane x i) + q - S32.v (V.lane y i) /\
                                      S32.v (V.lane u i) < 2 * q)
      = sub_lane (V.lane x i) (V.lane y i) (V.lane qv i) (V.lane s i) (V.lane u i) in
    Classical.forall_intro aux;
    vcsub u

(** [(A mod p - B mod p) mod p = A - B] when [0 <= A - B < p]. *)
let wrap_diff (a b: int) (p: pos)
  : Lemma (requires 0 <= a - b /\ a - b < p)
          (ensures ((a % p) - (b % p)) % p == a - b)
  = Math.lemma_mod_plus_distr_l a (- (b % p)) p;
    Math.lemma_mod_sub_distr a b p;
    Math.small_mod (a - b) p

let shoup_lane (y z zs qq t lo1 lo2 r: S32.t)
  : Lemma (requires S32.v y < q /\ S32.v z < q /\ S32.v zs == shoup_of (S32.v z) /\
                    S32.v qq == q /\
                    S32.v t == (S32.v y * S32.v zs) / pow2 32 /\
                    S32.v lo1 == (S32.v y * S32.v z) % pow2 32 /\
                    S32.v lo2 == (S32.v t * S32.v qq) % pow2 32 /\
                    S32.v r == (S32.v lo1 - S32.v lo2) % pow2 32)
          (ensures S32.v r < 2 * q /\ S32.v r % q == mul (S32.v z) (S32.v y))
  = shoup_bound (S32.v y) (S32.v z) (S32.v zs);
    assert_norm (2 * q < pow2 32);
    wrap_diff (S32.v y * S32.v z) (S32.v t * q) (pow2 32);
    Math.lemma_mod_sub (S32.v y * S32.v z) q (S32.v t);
    Math.swap_mul (S32.v t) q;
    Math.swap_mul (S32.v y) (S32.v z)

let vshoup_pre (z zs: V.t) : prop =
  vlt z q /\ (forall (i: nat). i < 8 ==> S32.v (V.lane zs i) == shoup_of (S32.v (V.lane z i)))

(** [z y], lane by lane, for roots [z] with companions [zs]. *)
inline_for_extraction
let vshoup (y: V.t { vlt y q }) (z: V.t) (zs: V.t { vshoup_pre z zs })
  : r: V.t { vlt r q /\
             (forall (i: nat). i < 8 ==>
                S32.v (V.lane r i) == mul (S32.v (V.lane z i)) (S32.v (V.lane y i))) }
  = let qv = vq () in
    let t = L.mulhi32 y zs in
    let lo1 = L.mullo32 y z in
    let lo2 = L.mullo32 t qv in
    let r = L.sub32 lo1 lo2 in
    let aux (i: nat { i < 8 })
                             : Lemma (ensures S32.v (V.lane r i) < 2 * q /\
                                      S32.v (V.lane r i) % q ==
                                        mul (S32.v (V.lane z i)) (S32.v (V.lane y i)))
      = shoup_lane (V.lane y i) (V.lane z i) (V.lane zs i) (V.lane qv i)
                   (V.lane t i) (V.lane lo1 i) (V.lane lo2 i) (V.lane r i) in
    Classical.forall_intro aux;
    vcsub r

(** {3 The general product} *)

let qinv : nat = 58728449

let low_agree (lo: nat) (t: nat)
  : Lemma (requires lo < pow2 32 /\ t == (lo * qinv) % pow2 32)
          (ensures (t * q) % pow2 32 == lo)
  = let p = pow2 32 in
    assert_norm (qinv * q == 1 + 114592 * pow2 32);
    Math.lemma_mod_mul_distr_l (lo * qinv) q p;
    Math.paren_mul_right lo qinv q;
    Math.distributivity_add_right lo 1 (114592 * p);
    Math.paren_mul_right lo 114592 p;
    Math.lemma_mod_plus lo (lo * 114592) p;
    Math.small_mod lo p

let hi_diff (ab tq: nat)
  : Lemma (requires ab % pow2 32 == tq % pow2 32)
          (ensures ab - tq == (ab / pow2 32 - tq / pow2 32) * pow2 32)
  = Math.lemma_div_mod ab (pow2 32);
    Math.lemma_div_mod tq (pow2 32);
    Math.distributivity_sub_left (ab / pow2 32) (tq / pow2 32) (pow2 32)

let wrap_small (d: int) (qq: nat) (s r: nat)
  : Lemma (requires - q < d /\ d < q /\ qq == q /\
                    s == d % pow2 32 /\ r == (s + qq) % pow2 32)
          (ensures r == d + q)
  = assert_norm (2 * q < pow2 32);
    Math.lemma_mod_plus_distr_l d q (pow2 32);
    Math.small_mod (d + q) (pow2 32)

let mont_final (ab tv h: nat) (d: int)
  : Lemma (requires ab - tv * q == d * pow2 32 /\ tv < pow2 32 /\ h == d + q)
          (ensures h % q == (ab * rinv) % q)
  = let p = pow2 32 in
    Math.distributivity_add_left d q p;
    assert (h * p == ab + (p - tv) * q);
    Math.lemma_mod_plus ab (p - tv) q;
    mont_congr ab (h * p) h

let mont_lane (a b qi qq lo t hi th s r: S32.t)
  : Lemma (requires S32.v a < q /\ S32.v b < q /\ S32.v qi == qinv /\ S32.v qq == q /\
                    S32.v lo == (S32.v a * S32.v b) % pow2 32 /\
                    S32.v t == (S32.v lo * S32.v qi) % pow2 32 /\
                    S32.v hi == (S32.v a * S32.v b) / pow2 32 /\
                    S32.v th == (S32.v t * S32.v qq) / pow2 32 /\
                    S32.v s == (S32.v hi - S32.v th) % pow2 32 /\
                    S32.v r == (S32.v s + S32.v qq) % pow2 32)
          (ensures S32.v r < 2 * q /\ S32.v r % q == (S32.v a * S32.v b * rinv) % q)
  = let p = pow2 32 in
    let ab = S32.v a * S32.v b in
    let tv = S32.v t in
    let tq = tv * q in
    low_agree (S32.v lo) tv;
    hi_diff ab tq;
    prod_lt (S32.v a) (S32.v b);
    Math.lemma_mult_lt_right q tv p;
    Math.swap_mul tv q;
    KZ.div_lt tq q p;
    KZ.div_lt ab q p;
    let d = S32.v hi - S32.v th in
    wrap_small d (S32.v qq) (S32.v s) (S32.v r);
    mont_final ab tv (S32.v r) d

let mont_mul (a b: zq) (r: nat)
  : Lemma (requires r < 2 * q /\ r % q == (a * b * rinv) % q)
          (ensures mul 4193792 (r % q) == mul a b)
  = mul_undo (a * b)

(** [a b], lane by lane. *)
inline_for_extraction
let vmul (a: V.t { vlt a q }) (b: V.t { vlt b q })
  : r: V.t { vlt r q /\
             (forall (i: nat). i < 8 ==>
                S32.v (V.lane r i) == mul (S32.v (V.lane a i)) (S32.v (V.lane b i))) }
  = let qv = vq () in
    let qi = V.bcast (S32.classify 58728449ul) in
    let lo = L.mullo32 a b in
    let t = L.mullo32 lo qi in
    let hi = L.mulhi32 a b in
    let th = L.mulhi32 t qv in
    let s = L.sub32 hi th in
    let u = V.add32 s qv in
    let aux (i: nat { i < 8 })
                             : Lemma (ensures S32.v (V.lane u i) < 2 * q /\
                                      S32.v (V.lane u i) % q ==
                                        (S32.v (V.lane a i) * S32.v (V.lane b i) * rinv) % q)
      = mont_lane (V.lane a i) (V.lane b i) (V.lane qi i) (V.lane qv i) (V.lane lo i)
                  (V.lane t i) (V.lane hi i) (V.lane th i) (V.lane s i) (V.lane u i) in
    Classical.forall_intro aux;
    let m = vcsub u in
    let rv = V.bcast rmod in
    let rs = V.bcast rmod_shoup in
    let r = vshoup m rv rs in
    let aux2 (i: nat { i < 8 })
                              : Lemma (ensures S32.v (V.lane r i) ==
                                         mul (S32.v (V.lane a i)) (S32.v (V.lane b i)))
      = mont_mul (S32.v (V.lane a i)) (S32.v (V.lane b i)) (S32.v (V.lane u i)) in
    Classical.forall_intro aux2;
    r

(** {2 Eight coefficients of a polynomial} *)

(** Lane [j] of [x] is coefficient [k + j] of [p]. *)
let at8 (x: V.t) (p: poly) (k: nat) : prop =
  k + 8 <= n /\ (forall (j: nat). j < 8 ==> S32.v (V.lane x j) == Seq.index p (k + j))

let at8_lt (x: V.t) (p: poly) (k: nat)
  : Lemma (requires at8 x p k) (ensures vlt x q)
  = ()

let at8_intro (x: V.t) (p: poly) (k: nat)
  : Lemma (requires k + 8 <= n /\
                    S32.v (V.lane x 0) == Seq.index p k /\
                    S32.v (V.lane x 1) == Seq.index p (k + 1) /\
                    S32.v (V.lane x 2) == Seq.index p (k + 2) /\
                    S32.v (V.lane x 3) == Seq.index p (k + 3) /\
                    S32.v (V.lane x 4) == Seq.index p (k + 4) /\
                    S32.v (V.lane x 5) == Seq.index p (k + 5) /\
                    S32.v (V.lane x 6) == Seq.index p (k + 6) /\
                    S32.v (V.lane x 7) == Seq.index p (k + 7))
          (ensures at8 x p k)
  = let aux (j: nat { j < 8 }) : Lemma (S32.v (V.lane x j) == Seq.index p (k + j))
      = assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7) in
    Classical.forall_intro aux

(** What {!Hacl.Vec256.Lane32.store_at} says, as a relation. *)
let stored (v v': Seq.seq zqt) (i: nat) (x: V.t) : prop =
  Seq.length v' == Seq.length v /\
  (forall (k: nat). k < Seq.length v ==>
     Seq.index v' k == (if i <= k && k < i + 8 then V.lane x (k - i) else Seq.index v k))

(** {2 The pointwise product} *)

let prod_step8 (va vb v v': Seq.seq zqt) (i: nat) (x y r: V.t)
  : Lemma (requires Seq.length va == n /\ Seq.length vb == n /\ Seq.length v == n /\ i + 8 <= n /\
                    (forall (k: nat). k < i ==>
                       S32.v (Seq.index v k) == prod_val (Seq.index va k) (Seq.index vb k)) /\
                    (forall (j: nat). j < 8 ==> V.lane x j == Seq.index va (i + j)) /\
                    (forall (j: nat). j < 8 ==> V.lane y j == Seq.index vb (i + j)) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane r j) == mul (S32.v (V.lane x j)) (S32.v (V.lane y j))) /\
                    stored v v' i r)
          (ensures Seq.length v' == n /\
                   (forall (k: nat). k < i + 8 ==>
                      S32.v (Seq.index v' k) == prod_val (Seq.index va k) (Seq.index vb k)))
  = reveal_opaque (`%prod_val) prod_val;
    let aux (k: nat { k < i + 8 })
      : Lemma (S32.v (Seq.index v' k) == prod_val (Seq.index va k) (Seq.index vb k))
      = if k >= i then begin
          assert (V.lane x (k - i) == Seq.index va (i + (k - i)));
          assert (V.lane y (k - i) == Seq.index vb (i + (k - i)));
          assert (S32.v (V.lane r (k - i)) ==
                    mul (S32.v (V.lane x (k - i))) (S32.v (V.lane y (k - i))))
        end in
    Classical.forall_intro aux

let step8 (i: nat)
  : Lemma (requires i % 8 == 0 /\ i < n) (ensures i + 8 <= n /\ (i + 8) % 8 == 0)
  = Math.lemma_mod_plus i 1 8;
    Math.lemma_div_mod i 8;
    Math.lemma_div_lt_nat i 8 5

let loop_exit8 (vi: SZ.t)
  : Lemma (requires false == SZ.lt vi 256sz /\ SZ.v vi <= n) (ensures SZ.v vi == n)
  = ()

(** [dst <- a * b], coefficient by coefficient.  Uses AVX2. *)
inline_for_extraction
fn multiply_ (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n)
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == poly_mul (as_poly va) (as_poly vb))
{
  A.pts_to_len dst;
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= n /\ SZ.v vi % 8 == 0 /\ Seq.length v == n /\
          Seq.length va == n /\ Seq.length vb == n /\
          (forall (k: nat). k < SZ.v vi ==>
             S32.v (Seq.index v k) == prod_val (Seq.index va k) (Seq.index vb k)))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    step8 (SZ.v vi);
    with v. assert (A.pts_to dst v);
    let x = L.load_at a vi;
    let y = L.load_at b vi;
    let r = vmul x y;
    assert pure (forall (j: nat). j < 8 ==>
                   S32.v (V.lane r j) == mul (S32.v (V.lane x j)) (S32.v (V.lane y j)));
    L.store_at dst vi r;
    with v'. assert (A.pts_to dst v');
    prod_step8 va vb v v' (SZ.v vi) x y r;
    i := SZ.add vi 8sz;
  };
  with (vi: SZ.t) (v: Seq.seq zqt). assert (pts_to i vi ** A.pts_to dst v);
  loop_exit8 vi;
  prod_done va vb v (SZ.v vi);
  ()
}

(** {2 The scaling by [256^-1]} *)

let scale_step8 (w v v': Seq.seq zqt) (i: nat) (x c r: V.t)
  : Lemma (requires Seq.length w == n /\ Seq.length v == n /\ i + 8 <= n /\
                    (forall (k: nat). k < i ==> S32.v (Seq.index v k) == scale_val (Seq.index w k)) /\
                    (forall (k: nat). i <= k /\ k < n ==> Seq.index v k == Seq.index w k) /\
                    (forall (j: nat). j < 8 ==> V.lane x j == Seq.index v (i + j)) /\
                    (forall (j: nat). j < 8 ==> S32.v (V.lane c j) == inv_256) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane r j) == mul (S32.v (V.lane c j)) (S32.v (V.lane x j))) /\
                    stored v v' i r)
          (ensures Seq.length v' == n /\
                   (forall (k: nat). k < i + 8 ==> S32.v (Seq.index v' k) == scale_val (Seq.index w k)) /\
                   (forall (k: nat). i + 8 <= k /\ k < n ==> Seq.index v' k == Seq.index w k))
  = reveal_opaque (`%scale_val) scale_val;
    let aux (k: nat { k < i + 8 })
      : Lemma (S32.v (Seq.index v' k) == scale_val (Seq.index w k))
      = if k >= i then begin
          assert (V.lane x (k - i) == Seq.index v (i + (k - i)));
          assert (S32.v (V.lane c (k - i)) == inv_256);
          assert (S32.v (V.lane r (k - i)) ==
                    mul (S32.v (V.lane c (k - i))) (S32.v (V.lane x (k - i))))
        end in
    Classical.forall_intro aux

inline_for_extraction
fn scale_ (f: A.array zqt) (#w: erased (Seq.seq zqt))
requires A.pts_to f w ** pure (Seq.length w == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length w == n /\ Seq.length v == n /\
              as_poly v == poly_scale inv_256 (as_poly w))
{
  A.pts_to_len f;
  let ci = V.bcast (S32.classify 8347681ul);
  let cs = V.bcast (S32.classify 4278190082ul);
  assert_norm (shoup_of 8347681 == 4278190082);
  assert_norm (8347681 < q);
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to f v **
    pure (SZ.v vi <= n /\ SZ.v vi % 8 == 0 /\ Seq.length v == n /\ Seq.length w == n /\
          (forall (k: nat). k < SZ.v vi ==> S32.v (Seq.index v k) == scale_val (Seq.index w k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < n ==> Seq.index v k == Seq.index w k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    step8 (SZ.v vi);
    with v. assert (A.pts_to f v);
    let x = L.load_at f vi;
    let r = vshoup x ci cs;
    L.store_at f vi r;
    with v'. assert (A.pts_to f v');
    scale_step8 w v v' (SZ.v vi) x ci r;
    i := SZ.add vi 8sz;
  };
  with (vi: SZ.t) (v: Seq.seq zqt). assert (pts_to i vi ** A.pts_to f v);
  loop_exit8 vi;
  scale_done w v (SZ.v vi);
  ()
}

(** {2 The layers of half-width eight and more} *)

let step8_le (c len: nat)
  : Lemma (requires c % 8 == 0 /\ len % 8 == 0 /\ c < len) (ensures c + 8 <= len /\ (c + 8) % 8 == 0)
  = Math.lemma_mod_plus c 1 8;
    Math.lemma_div_mod c 8;
    Math.lemma_div_mod len 8;
    if c / 8 >= len / 8 then Math.lemma_mult_le_left 8 (len / 8) (c / 8)
    else Math.lemma_mult_le_left 8 (c / 8 + 1) (len / 8)

let len8 (e: nat)
  : Lemma (requires 3 <= e) (ensures pow2 e % 8 == 0 /\ 8 <= pow2 e)
  = Math.pow2_plus 3 (e - 3);
    assert_norm (pow2 3 == 8);
    Math.cancel_mul_mod (pow2 (e - 3)) 8;
    Math.pow2_le_compat e 3

let part_read8 (res: poly) (vs v: Seq.seq zqt) (lo len c: nat) (x y: V.t)
  : Lemma (requires Seq.length v == n /\ part res vs v lo len c /\ c + 8 <= len /\ lo + 2 * len <= n /\
                    (forall (j: nat). j < 8 ==> V.lane x j == Seq.index v (lo + c + j)) /\
                    (forall (j: nat). j < 8 ==> V.lane y j == Seq.index v (lo + len + c + j)))
          (ensures Seq.length vs == n /\ Seq.length v == n /\
                   (forall (j: nat). j < 8 ==>
                      S32.v (V.lane x j) == S32.v (Seq.index vs (lo + c + j)) /\
                      S32.v (V.lane y j) == S32.v (Seq.index vs (lo + len + c + j))))
  = reveal_opaque (`%part) (part res vs v lo len c)

let part_step8 (res: poly) (vs v v1 v2: Seq.seq zqt) (lo len c: nat) (a d: V.t)
  : Lemma (requires Seq.length v == n /\ Seq.length vs == n /\
                    part res vs v lo len c /\ c + 8 <= len /\ lo + 2 * len <= n /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane a j) == Seq.index res (lo + c + j) /\
                       S32.v (V.lane d j) == Seq.index res (lo + len + c + j)) /\
                    stored v v1 (lo + c) a /\ stored v1 v2 (lo + len + c) d)
          (ensures Seq.length v2 == n /\ part res vs v2 lo len (c + 8))
  = reveal_opaque (`%part) (part res vs v lo len c);
    let aux (k: nat { k < n })
      : Lemma (S32.v (Seq.index v2 k) ==
                 (if in_done lo len (c + 8) k then Seq.index res k else S32.v (Seq.index vs k)))
      = if lo + len + c <= k && k < lo + len + c + 8 then
          assert (S32.v (V.lane d (k - (lo + len + c))) ==
                    Seq.index res (lo + len + c + (k - (lo + len + c))))
        else if lo + c <= k && k < lo + c + 8 then
          assert (S32.v (V.lane a (k - (lo + c))) == Seq.index res (lo + c + (k - (lo + c))))
    in
    Classical.forall_intro aux;
    reveal_opaque (`%part) (part res vs v2 lo len (c + 8))

(** [lo] is the start of block [b] of the layer of half-width [2^e]; kept
    opaque, because the product in it sends the solver astray in the
    presence of the lane quantifiers. *)
[@@"opaque_to_smt"]
let blk (e: nat) (b lo: nat) : prop = lo == b * pow2 (e + 1)

let blk_intro (e: nat) (b lo: nat)
  : Lemma (requires lo == b * pow2 (e + 1)) (ensures blk e b lo)
  = reveal_opaque (`%blk) (blk e b lo)

(** The roots of a block, opaque for the same reason. *)
[@@"opaque_to_smt"]
let root (e: nat { e <= 7 }) (lo: nat) (z: nat) : prop = lo < n /\ z == zetas (zidx e lo)

[@@"opaque_to_smt"]
let root_inv (e: nat { e <= 7 }) (lo: nat) (z: nat) : prop = lo < n /\ z == zetas (zidx_inv e lo)

let ntt_pair_at (e: nat { e <= 7 }) (f: poly) (b lo len c i k: nat) (z: zq)
  : Lemma (requires root e lo z /\ blk e b lo /\ len == pow2 e /\ c < len /\ lo + 2 * len <= n /\
                    i == lo + c /\ k == lo + len + c)
          (ensures i < n /\ k < n /\
                   Seq.index (ntt_layer e f) i == add (Seq.index f i) (mul z (Seq.index f k)) /\
                   Seq.index (ntt_layer e f) k == sub (Seq.index f i) (mul z (Seq.index f k)))
  = reveal_opaque (`%blk) (blk e b lo); reveal_opaque (`%root) (root e lo z); ntt_pair e f b c

let intt_pair_at (e: nat { e <= 7 }) (f: poly) (b lo len c i k: nat) (z: zq)
  : Lemma (requires root_inv e lo z /\ blk e b lo /\ len == pow2 e /\ c < len /\ lo + 2 * len <= n /\
                    i == lo + c /\ k == lo + len + c)
          (ensures i < n /\ k < n /\
                   Seq.index (intt_layer e f) i == add (Seq.index f i) (Seq.index f k) /\
                   Seq.index (intt_layer e f) k == mul z (sub (Seq.index f k) (Seq.index f i)))
  = reveal_opaque (`%blk) (blk e b lo); reveal_opaque (`%root_inv) (root_inv e lo z); intt_pair e f b c

let ntt_lanes (e: nat { e <= 7 }) (vs: Seq.seq zqt) (b c lo len: nat) (zv: zq) (x y z t a d: V.t)
  : Lemma (requires Seq.length vs == n /\ blk e b lo /\ len == pow2 e /\ root e lo zv /\
                    c + 8 <= len /\ lo + 2 * len <= n /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane x j) == S32.v (Seq.index vs (lo + c + j)) /\
                       S32.v (V.lane y j) ==
                         S32.v (Seq.index vs (lo + len + c + j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane z j) == zv) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane t j) == mul (S32.v (V.lane z j)) (S32.v (V.lane y j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane a j) == add (S32.v (V.lane x j)) (S32.v (V.lane t j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane d j) == sub (S32.v (V.lane x j)) (S32.v (V.lane t j))))
          (ensures (let res = ntt_layer e (as_poly vs) in
                    forall (j: nat). j < 8 ==>
                      S32.v (V.lane a j) == Seq.index res (lo + c + j) /\
                      S32.v (V.lane d j) == Seq.index res (lo + len + c + j)))
  = let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane a j) == Seq.index (ntt_layer e (as_poly vs)) (lo + c + j) /\
               S32.v (V.lane d j) == Seq.index (ntt_layer e (as_poly vs)) (lo + len + c + j))
      = let f = as_poly vs in
        let i = lo + c + j in
        let k = lo + len + c + j in
        ntt_pair_at e f b lo len (c + j) i k zv;
        as_poly_index vs i;
        as_poly_index vs k;
        let zj = S32.v (V.lane z j) in
        let yj = S32.v (V.lane y j) in
        let tj = S32.v (V.lane t j) in
        let xj = S32.v (V.lane x j) in
        assert (xj == S32.v (Seq.index vs i));
        assert (yj == S32.v (Seq.index vs k));
        assert (zj == zv);
        assert (tj == mul zj yj);
        assert (S32.v (V.lane a j) == add xj tj);
        assert (S32.v (V.lane d j) == sub xj tj)
    in
    Classical.forall_intro aux

let intt_lanes (e: nat { e <= 7 }) (vs: Seq.seq zqt) (b c lo len: nat) (zv: zq) (x y z s a d: V.t)
  : Lemma (requires Seq.length vs == n /\ blk e b lo /\ len == pow2 e /\ root_inv e lo zv /\
                    c + 8 <= len /\ lo + 2 * len <= n /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane x j) == S32.v (Seq.index vs (lo + c + j)) /\
                       S32.v (V.lane y j) ==
                         S32.v (Seq.index vs (lo + len + c + j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane z j) == zv) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane a j) == add (S32.v (V.lane x j)) (S32.v (V.lane y j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane s j) == sub (S32.v (V.lane y j)) (S32.v (V.lane x j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane d j) == mul (S32.v (V.lane z j)) (S32.v (V.lane s j))))
          (ensures (let res = intt_layer e (as_poly vs) in
                    forall (j: nat). j < 8 ==>
                      S32.v (V.lane a j) == Seq.index res (lo + c + j) /\
                      S32.v (V.lane d j) == Seq.index res (lo + len + c + j)))
  = let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane a j) == Seq.index (intt_layer e (as_poly vs)) (lo + c + j) /\
               S32.v (V.lane d j) == Seq.index (intt_layer e (as_poly vs)) (lo + len + c + j))
      = let f = as_poly vs in
        let i = lo + c + j in
        let k = lo + len + c + j in
        intt_pair_at e f b lo len (c + j) i k zv;
        as_poly_index vs i;
        as_poly_index vs k;
        let zj = S32.v (V.lane z j) in
        let yj = S32.v (V.lane y j) in
        let sj = S32.v (V.lane s j) in
        let xj = S32.v (V.lane x j) in
        assert (xj == S32.v (Seq.index vs i));
        assert (yj == S32.v (Seq.index vs k));
        assert (zj == zv);
        assert (sj == sub yj xj);
        assert (S32.v (V.lane a j) == add xj yj);
        assert (S32.v (V.lane d j) == mul zj sj)
    in
    Classical.forall_intro aux

(** One vector of butterflies of a block, as a pure function, so that its
    proof does not see the loop around it. *)
inline_for_extraction
let ntt_bf (x y zv zsv: V.t) (e: Ghost.erased nat) (vs: Ghost.erased (Seq.seq zqt))
           (b c lo len: Ghost.erased nat) (z: Ghost.erased zq)
  : Pure (V.t & V.t)
    (requires reveal e <= 7 /\ Seq.length vs == n /\ blk e b lo /\ len == pow2 e /\ root e lo z /\
              c + 8 <= len /\ lo + 2 * len <= n /\ vshoup_pre zv zsv /\
              (forall (j: nat). j < 8 ==>
                 S32.v (V.lane x j) == S32.v (Seq.index vs (lo + c + j)) /\
                 S32.v (V.lane y j) == S32.v (Seq.index vs (lo + len + c + j))) /\
              (forall (j: nat). j < 8 ==> S32.v (V.lane zv j) == reveal z))
    (ensures fun r -> reveal e <= 7 /\ Seq.length vs == n /\
              (forall (j: nat). j < 8 ==> S32.v (V.lane (fst r) j) < q /\ S32.v (V.lane (snd r) j) < q) /\
              (forall (j: nat). j < 8 ==>
                 S32.v (V.lane (fst r) j) == Seq.index (ntt_layer e (as_poly vs)) (lo + c + j) /\
                 S32.v (V.lane (snd r) j) == Seq.index (ntt_layer e (as_poly vs)) (lo + len + c + j)))
  = assert (vlt x q /\ vlt y q);
    let t = vshoup y zv zsv in
    let a = vadd x t in
    let d = vsub x t in
    ntt_lanes (reveal e) vs b c lo len z x y zv t a d;
    (a, d)

inline_for_extraction
let intt_bf (x y zv zsv: V.t) (e: Ghost.erased nat) (vs: Ghost.erased (Seq.seq zqt))
            (b c lo len: Ghost.erased nat) (z: Ghost.erased zq)
  : Pure (V.t & V.t)
    (requires reveal e <= 7 /\ Seq.length vs == n /\ blk e b lo /\ len == pow2 e /\ root_inv e lo z /\
              c + 8 <= len /\ lo + 2 * len <= n /\ vshoup_pre zv zsv /\
              (forall (j: nat). j < 8 ==>
                 S32.v (V.lane x j) == S32.v (Seq.index vs (lo + c + j)) /\
                 S32.v (V.lane y j) == S32.v (Seq.index vs (lo + len + c + j))) /\
              (forall (j: nat). j < 8 ==> S32.v (V.lane zv j) == reveal z))
    (ensures fun r -> reveal e <= 7 /\ Seq.length vs == n /\
              (forall (j: nat). j < 8 ==> S32.v (V.lane (fst r) j) < q /\ S32.v (V.lane (snd r) j) < q) /\
              (forall (j: nat). j < 8 ==>
                 S32.v (V.lane (fst r) j) == Seq.index (intt_layer e (as_poly vs)) (lo + c + j) /\
                 S32.v (V.lane (snd r) j) == Seq.index (intt_layer e (as_poly vs)) (lo + len + c + j)))
  = assert (vlt x q /\ vlt y q);
    let a = vadd x y in
    let s = vsub y x in
    let d = vshoup s zv zsv in
    intt_lanes (reveal e) vs b c lo len z x y zv s a d;
    (a, d)

let root_intro (e: nat { e <= 7 }) (b lo: nat) (zi: nat { zi < 256 }) (z: zq)
  : Lemma (requires lo == b * pow2 (e + 1) /\ lo < n /\ zi == pow2 (7 - e) + b /\ z == zetas zi)
          (ensures blk e b lo /\ root e lo z)
  = block_fits e b;
    reveal_opaque (`%blk) (blk e b lo);
    reveal_opaque (`%root) (root e lo z)

let root_inv_intro (e: nat { e <= 7 }) (b lo: nat) (zi: nat { zi < 256 }) (z: zq)
  : Lemma (requires lo == b * pow2 (e + 1) /\ lo < n /\ zi == 2 * pow2 (7 - e) - 1 - b /\
                    z == zetas zi)
          (ensures blk e b lo /\ root_inv e lo z)
  = block_fits e b;
    reveal_opaque (`%blk) (blk e b lo);
    reveal_opaque (`%root_inv) (root_inv e lo z)

(** The two halves of a vector of butterflies, written back. *)
inline_for_extraction
fn store_bf (f: A.array zqt) (lo len c: SZ.t) (r: (V.t & V.t))
            (res: erased poly) (#vs #v: erased (Seq.seq zqt))
requires A.pts_to f v **
         pure (Seq.length v == n /\ Seq.length vs == n /\
               part res vs v (SZ.v lo) (SZ.v len) (SZ.v c) /\
               SZ.v c + 8 <= SZ.v len /\ SZ.v lo + 2 * SZ.v len <= n /\
               (forall (j: nat). j < 8 ==> S32.v (V.lane (fst r) j) < q /\ S32.v (V.lane (snd r) j) < q) /\
               (forall (j: nat). j < 8 ==>
                  S32.v (V.lane (fst r) j) == Seq.index res (SZ.v lo + SZ.v c + j) /\
                  S32.v (V.lane (snd r) j) == Seq.index res (SZ.v lo + SZ.v len + SZ.v c + j)))
ensures exists* v2. A.pts_to f v2 **
        pure (Seq.length v2 == n /\ part res vs v2 (SZ.v lo) (SZ.v len) (SZ.v c + 8))
{
  A.pts_to_len f;
  let a = fst r;
  let d = snd r;
  let i = SZ.add lo c;
  let k = SZ.add i len;
  L.store_at f i a;
  with v1. assert (A.pts_to f v1);
  L.store_at f k d;
  with v2. assert (A.pts_to f v2);
  part_step8 res vs v v1 v2 (SZ.v lo) (SZ.v len) (SZ.v c) a d;
  assert pure (Seq.length v2 == n /\ part res vs v2 (SZ.v lo) (SZ.v len) (SZ.v c + 8));
}

(** One block of Cooley-Tukey butterflies under the root [z], eight at a
    time. *)
inline_for_extraction
fn ntt_block8 (f: A.array zqt) (lo len: SZ.t) (zv zsv: V.t)
              (#e: erased nat) (#b: erased nat) (#z: erased zq) (#vs #vf: erased (Seq.seq zqt))
requires A.pts_to f vf **
         pure (reveal e <= 7 /\ 3 <= reveal e /\ SZ.v len == pow2 (reveal e) /\
               Seq.length vs == n /\ Seq.length vf == n /\
               blk (reveal e) (reveal b) (SZ.v lo) /\ root (reveal e) (SZ.v lo) (reveal z) /\
               SZ.v lo + 2 * SZ.v len <= n /\ vshoup_pre zv zsv /\
               (forall (j: nat). j < 8 ==> S32.v (V.lane zv j) == reveal z) /\
               part (ntt_layer (reveal e) (as_poly vs)) vs vf (SZ.v lo) (SZ.v len) 0)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              part (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v len))
{
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  len8 (reveal e);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc len)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to f v **
    pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
          SZ.v vc <= SZ.v len /\ SZ.v vc % 8 == 0 /\
          part (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc))
  decreases (SZ.v len - SZ.v (!c))
  {
    let vc = !c;
    step8_le (SZ.v vc) (SZ.v len);
    with v. assert (A.pts_to f v);
    SZ.fits_u32_implies_fits (SZ.v lo + SZ.v len + SZ.v vc);
    let i = SZ.add lo vc;
    let k = SZ.add i len;
    let x = L.load_at f i;
    let y = L.load_at f k;
    part_read8 (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc) x y;
    let r = ntt_bf x y zv zsv e vs b (SZ.v vc) (SZ.v lo) (SZ.v len) z;
    store_bf f lo len vc r (ntt_layer (reveal e) (as_poly vs)) #vs;
    c := SZ.add vc 8sz;
  };
}


(** One block of Gentleman-Sande butterflies, eight at a time. *)
inline_for_extraction
fn intt_block8 (f: A.array zqt) (lo len: SZ.t) (zv zsv: V.t)
               (#e: erased nat) (#b: erased nat) (#z: erased zq) (#vs #vf: erased (Seq.seq zqt))
requires A.pts_to f vf **
         pure (reveal e <= 7 /\ 3 <= reveal e /\ SZ.v len == pow2 (reveal e) /\
               Seq.length vs == n /\ Seq.length vf == n /\
               blk (reveal e) (reveal b) (SZ.v lo) /\ root_inv (reveal e) (SZ.v lo) (reveal z) /\
               SZ.v lo + 2 * SZ.v len <= n /\ vshoup_pre zv zsv /\
               (forall (j: nat). j < 8 ==> S32.v (V.lane zv j) == reveal z) /\
               part (intt_layer (reveal e) (as_poly vs)) vs vf (SZ.v lo) (SZ.v len) 0)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              part (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v len))
{
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  len8 (reveal e);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc len)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to f v **
    pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
          SZ.v vc <= SZ.v len /\ SZ.v vc % 8 == 0 /\
          part (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc))
  decreases (SZ.v len - SZ.v (!c))
  {
    let vc = !c;
    step8_le (SZ.v vc) (SZ.v len);
    with v. assert (A.pts_to f v);
    SZ.fits_u32_implies_fits (SZ.v lo + SZ.v len + SZ.v vc);
    let i = SZ.add lo vc;
    let k = SZ.add i len;
    let x = L.load_at f i;
    let y = L.load_at f k;
    part_read8 (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v lo) (SZ.v len) (SZ.v vc) x y;
    let r = intt_bf x y zv zsv e vs b (SZ.v vc) (SZ.v lo) (SZ.v len) z;
    store_bf f lo len vc r (intt_layer (reveal e) (as_poly vs)) #vs;
    c := SZ.add vc 8sz;
  };
}

(** [f <- ntt_layer e f], for [e >= 3]. *)
inline_for_extraction
fn ntt_layer8 (f: A.array zqt) (len half: SZ.t)
              (#e: erased nat) (#vs: erased (Seq.seq zqt))
requires A.pts_to f vs **
         pure (reveal e <= 7 /\ 3 <= reveal e /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == ntt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 256sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 256sz;
  with ps. assert (A.pts_to zst #ps zeta_shoup_table);
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  Math.pow2_plus 1 (reveal e);
  assert_norm (pow2 1 == 2);
  Math.pow2_le_compat 8 (reveal e + 1);
  assert_norm (pow2 8 == 256);
  let dbl = SZ.add len len;
  part_start (ntt_layer (reveal e) (as_poly vs)) vs (SZ.v len);
  let mut lo = 0sz;
  let mut b = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vb: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to b vb ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
          SZ.v vlo <= n /\ SZ.v vlo == SZ.v vb * pow2 (reveal e + 1) /\
          part (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len) 0)
  decreases (n - SZ.v (!lo))
  {
    let vlo = !lo;
    let vb = !b;
    block_fits (reveal e) (SZ.v vb);
    SZ.fits_u32_implies_fits (SZ.v half + SZ.v vb);
    let zi = SZ.add half vb;
    let z = A.(zt.(zi));
    let zs = A.(zst.(zi));
    root_intro (reveal e) (SZ.v vb) (SZ.v vlo) (SZ.v zi) (S32.v z);
    let zv = V.bcast z;
    let zsv = V.bcast zs;
    ntt_block8 f vlo len zv zsv #e #(SZ.v vb) #(S32.v z) #vs;
    with v. assert (A.pts_to f v);
    part_next (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len);
    Math.distributivity_add_left (SZ.v vb) 1 (pow2 (reveal e + 1));
    lo := SZ.add vlo dbl;
    b := SZ.add vb 1sz;
  };
  with v. assert (A.pts_to f v);
  part_done (ntt_layer (reveal e) (as_poly vs)) vs v (SZ.v len);
  T.drop_table zst;
  T.drop_table zt;
}

(** [f <- intt_layer e f], for [e >= 3]. *)
inline_for_extraction
fn intt_layer8 (f: A.array zqt) (len half: SZ.t)
               (#e: erased nat) (#vs: erased (Seq.seq zqt))
requires A.pts_to f vs **
         pure (reveal e <= 7 /\ 3 <= reveal e /\
               SZ.v len == pow2 (reveal e) /\ SZ.v half == pow2 (7 - reveal e) /\
               Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == intt_layer (reveal e) (as_poly vs))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 256sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 256sz;
  with ps. assert (A.pts_to zst #ps zeta_shoup_table);
  HSZ.fits32 ();
  assert_norm (256 < pow2 32);
  Math.pow2_plus 1 (reveal e);
  assert_norm (pow2 1 == 2);
  Math.pow2_le_compat 8 (reveal e + 1);
  assert_norm (pow2 8 == 256);
  Math.pow2_le_compat 7 (7 - reveal e);
  assert_norm (pow2 7 == 128);
  let dbl = SZ.add len len;
  let top = SZ.sub (SZ.add half half) 1sz;
  part_start (intt_layer (reveal e) (as_poly vs)) vs (SZ.v len);
  let mut lo = 0sz;
  let mut b = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vb: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to b vb ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (reveal e <= 7 /\ Seq.length vs == n /\ Seq.length v == n /\
          SZ.v vlo <= n /\ SZ.v vlo == SZ.v vb * pow2 (reveal e + 1) /\
          part (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len) 0)
  decreases (n - SZ.v (!lo))
  {
    let vlo = !lo;
    let vb = !b;
    block_fits (reveal e) (SZ.v vb);
    let zi = SZ.sub top vb;
    let z = A.(zt.(zi));
    let zs = A.(zst.(zi));
    root_inv_intro (reveal e) (SZ.v vb) (SZ.v vlo) (SZ.v zi) (S32.v z);
    let zv = V.bcast z;
    let zsv = V.bcast zs;
    intt_block8 f vlo len zv zsv #e #(SZ.v vb) #(S32.v z) #vs;
    with v. assert (A.pts_to f v);
    part_next (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v vlo) (SZ.v len);
    Math.distributivity_add_left (SZ.v vb) 1 (pow2 (reveal e + 1));
    lo := SZ.add vlo dbl;
    b := SZ.add vb 1sz;
  };
  with v. assert (A.pts_to f v);
  part_done (intt_layer (reveal e) (as_poly vs)) vs v (SZ.v len);
  T.drop_table zst;
  T.drop_table zt;
}

(** {2 The last three layers}

    Group [g] is the sixteen coefficients from [lo = 16 g]; in each of the
    layers of half-width four, two and one, its butterflies pair
    coefficients of the same group. *)

(** One butterfly of a layer, named by its lower end [t]. *)
let small_pair (e: nat { e <= 7 }) (f: poly) (t: nat)
  : Lemma (requires t + pow2 e < n /\ (t / pow2 e) % 2 == 0)
          (ensures t + pow2 e < n /\
                   Seq.index (ntt_layer e f) t ==
                     add (Seq.index f t) (mul (zetas (zidx e t)) (Seq.index f (t + pow2 e))) /\
                   Seq.index (ntt_layer e f) (t + pow2 e) ==
                     sub (Seq.index f t) (mul (zetas (zidx e t)) (Seq.index f (t + pow2 e))) /\
                   Seq.index (intt_layer e f) t ==
                     add (Seq.index f t) (Seq.index f (t + pow2 e)) /\
                   Seq.index (intt_layer e f) (t + pow2 e) ==
                     mul (zetas (zidx_inv e t)) (sub (Seq.index f (t + pow2 e)) (Seq.index f t)))
  = let len = pow2 e in
    ntt_layer_index e f t;
    ntt_layer_index e f (t + len);
    intt_layer_index e f t;
    intt_layer_index e f (t + len);
    Math.lemma_div_plus t 1 len;
    Math.pow2_plus e 1;
    assert_norm (pow2 1 == 2);
    Math.division_multiplication_lemma t len 2;
    Math.division_multiplication_lemma (t + len) len 2;
    assert ((t + len) / pow2 (e + 1) == t / pow2 (e + 1));
    assert (zidx e (t + len) == zidx e t);
    assert (zidx_inv e (t + len) == zidx_inv e t)

(** Where the roots of group [lo] are, and which half a coefficient is in. *)
let small_idx (e: nat { e <= 2 }) (lo: nat) (r: nat { r < 16 })
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n)
          (ensures lo + r < n /\
                   zidx e (lo + r) == pow2 (7 - e) + lo / pow2 (e + 1) + r / pow2 (e + 1) /\
                   zidx_inv e (lo + r) == pow2 (8 - e) - 1 - lo / pow2 (e + 1) - r / pow2 (e + 1) /\
                   ((lo + r) / pow2 e) % 2 == (r / pow2 e) % 2)
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8);
    let k = lo / 16 in
    Math.lemma_div_mod lo 16;
    let d = pow2 (e + 1) in
    let h = pow2 e in
    assert (lo == (16 / d * k) * d);
    Math.lemma_div_plus r (16 / d * k) d;
    Math.cancel_mul_div (16 / d * k) d;
    assert (lo == (16 / h * k) * h);
    Math.lemma_div_plus r (16 / h * k) h;
    assert (16 / h * k == 2 * ((8 / h) * k));
    Math.lemma_mod_plus (r / h) ((8 / h) * k) 2

(** Group [lo] of [p], as two vectors. *)
let grp (a b: V.t) (p: poly) (lo: nat) : prop =
  lo + 16 <= n /\
  (forall (j: nat). j < 8 ==> S32.v (V.lane a j) == Seq.index p (lo + j) /\
                              S32.v (V.lane b j) == Seq.index p (lo + 8 + j))

(** Where, in its group, the lower end of the butterfly in lane [j] is,
    once the group has been shuffled for the layer of half-width [2^e]. *)
let pos (e: nat { e <= 2 }) (j: nat { j < 8 }) : r: nat { r + pow2 e < 16 } =
  assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4);
  if e = 2 then (if j < 4 then j else j + 4)
  else if e = 1 then (if j < 2 then j else if j < 4 then j + 6 else if j < 6 then j else j + 6)
  else (if j < 2 then 2 * j else if j < 4 then 2 * j + 4 else if j < 6 then 2 * j - 4 else 2 * j)

let pos_ok (e: nat { e <= 2 }) (j: nat { j < 8 })
  : Lemma ((pos e j / pow2 e) % 2 == 0 /\ pos e j + pow2 e < 16)
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4);
    assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)

(** The butterflies of group [lo], lower ends in [x], upper in [y]. *)
let pair_at (e: nat { e <= 2 }) (x y: V.t) (p: poly) (lo: nat) : prop =
  lo % 16 == 0 /\ lo + 16 <= n /\
  (forall (j: nat). j < 8 ==>
     S32.v (V.lane x j) == Seq.index p (lo + pos e j) /\
     S32.v (V.lane y j) == Seq.index p (lo + pos e j + pow2 e))

let pair_lt (e: nat { e <= 2 }) (x y: V.t) (p: poly) (lo: nat)
  : Lemma (requires pair_at e x y p lo) (ensures vlt x q /\ vlt y q)
  = ()

let small_ntt_lanes (e: nat { e <= 2 }) (p: poly) (lo: nat) (x y z t a d: V.t)
  : Lemma (requires pair_at e x y p lo /\
                    (forall (j: nat). j < 8 ==> S32.v (V.lane z j) == zetas (zidx e (lo + pos e j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane t j) == mul (S32.v (V.lane z j)) (S32.v (V.lane y j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane a j) == add (S32.v (V.lane x j)) (S32.v (V.lane t j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane d j) == sub (S32.v (V.lane x j)) (S32.v (V.lane t j))))
          (ensures pair_at e a d (ntt_layer e p) lo)
  = let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane a j) == Seq.index (ntt_layer e p) (lo + pos e j) /\
               S32.v (V.lane d j) == Seq.index (ntt_layer e p) (lo + pos e j + pow2 e))
      = pos_ok e j;
        small_idx e lo (pos e j);
        small_pair e p (lo + pos e j)
    in
    Classical.forall_intro aux

let small_intt_lanes (e: nat { e <= 2 }) (p: poly) (lo: nat) (x y z s a d: V.t)
  : Lemma (requires pair_at e x y p lo /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane z j) == zetas (zidx_inv e (lo + pos e j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane a j) == add (S32.v (V.lane x j)) (S32.v (V.lane y j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane s j) == sub (S32.v (V.lane y j)) (S32.v (V.lane x j))) /\
                    (forall (j: nat). j < 8 ==>
                       S32.v (V.lane d j) == mul (S32.v (V.lane z j)) (S32.v (V.lane s j))))
          (ensures pair_at e a d (intt_layer e p) lo)
  = let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane a j) == Seq.index (intt_layer e p) (lo + pos e j) /\
               S32.v (V.lane d j) == Seq.index (intt_layer e p) (lo + pos e j + pow2 e))
      = pos_ok e j;
        small_idx e lo (pos e j);
        small_pair e p (lo + pos e j)
    in
    Classical.forall_intro aux

(** {3 The shuffles} *)

let shuf2_in (a b: V.t) (p: poly) (lo: nat) (x y: V.t)
  : Lemma (requires lo % 16 == 0 /\ grp a b p lo /\ x == V.lo128 a b /\ y == V.hi128 a b)
          (ensures pair_at 2 x y p lo /\ vlt x q /\ vlt y q)
  = assert_norm (pow2 2 == 4);
    let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane x j) == Seq.index p (lo + pos 2 j) /\
               S32.v (V.lane y j) == Seq.index p (lo + pos 2 j + pow2 2))
      = assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let shuf2_out (x y: V.t) (p: poly) (lo: nat) (a b: V.t)
  : Lemma (requires pair_at 2 x y p lo /\ a == V.lo128 x y /\ b == V.hi128 x y)
          (ensures grp a b p lo)
  = assert_norm (pow2 2 == 4);
    let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane a j) == Seq.index p (lo + j) /\
               S32.v (V.lane b j) == Seq.index p (lo + 8 + j))
      = assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let shuf1_in (a b: V.t) (p: poly) (lo: nat) (x y: V.t)
  : Lemma (requires lo % 16 == 0 /\ grp a b p lo /\ x == V.unpacklo64 a b /\ y == V.unpackhi64 a b)
          (ensures pair_at 1 x y p lo /\ vlt x q /\ vlt y q)
  = assert_norm (pow2 1 == 2);
    let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane x j) == Seq.index p (lo + pos 1 j) /\
               S32.v (V.lane y j) == Seq.index p (lo + pos 1 j + pow2 1))
      = assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let shuf1_out (x y: V.t) (p: poly) (lo: nat) (a b: V.t)
  : Lemma (requires pair_at 1 x y p lo /\ a == V.unpacklo64 x y /\ b == V.unpackhi64 x y)
          (ensures grp a b p lo)
  = assert_norm (pow2 1 == 2);
    let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane a j) == Seq.index p (lo + j) /\
               S32.v (V.lane b j) == Seq.index p (lo + 8 + j))
      = assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let shuf0_in (a b: V.t) (p: poly) (lo: nat) (u w x y: V.t)
  : Lemma (requires lo % 16 == 0 /\ grp a b p lo /\
                    u == V.unpacklo32 a b /\ w == V.unpackhi32 a b /\
                    x == V.unpacklo32 u w /\ y == V.unpackhi32 u w)
          (ensures pair_at 0 x y p lo /\ vlt x q /\ vlt y q)
  = assert_norm (pow2 0 == 1);
    let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane x j) == Seq.index p (lo + pos 0 j) /\
               S32.v (V.lane y j) == Seq.index p (lo + pos 0 j + pow2 0))
      = assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let shuf0_out (x y: V.t) (p: poly) (lo: nat) (a b: V.t)
  : Lemma (requires pair_at 0 x y p lo /\ a == V.unpacklo32 x y /\ b == V.unpackhi32 x y)
          (ensures grp a b p lo)
  = assert_norm (pow2 0 == 1);
    let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane a j) == Seq.index p (lo + j) /\
               S32.v (V.lane b j) == Seq.index p (lo + 8 + j))
      = assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

(** {3 The roots}

    Eight consecutive entries of the tables, from [base], permuted. *)
let ztab (zl zsl: V.t) (base: nat) : prop =
  base + 8 <= 256 /\
  (forall (j: nat). j < 8 ==> V.lane zl j == Seq.index zeta_table (base + j) /\
                              V.lane zsl j == Seq.index zeta_shoup_table (base + j))

let sel8 (i0 i1 i2 i3 i4 i5 i6 i7: nat) (j: nat { j < 8 }) : nat =
  if j = 0 then i0 else if j = 1 then i1 else if j = 2 then i2 else if j = 3 then i3
  else if j = 4 then i4 else if j = 5 then i5 else if j = 6 then i6 else i7

let perm_lane (a: V.t) (i0 i1 i2 i3 i4 i5 i6 i7: (i: U32.t { U32.v i < 8 }))
  : Lemma (forall (j: nat). j < 8 ==>
             sel8 (U32.v i0) (U32.v i1) (U32.v i2) (U32.v i3)
                  (U32.v i4) (U32.v i5) (U32.v i6) (U32.v i7) j < 8 /\
             V.lane (L.perm32 a i0 i1 i2 i3 i4 i5 i6 i7) j ==
             V.lane a (sel8 (U32.v i0) (U32.v i1) (U32.v i2) (U32.v i3)
                            (U32.v i4) (U32.v i5) (U32.v i6) (U32.v i7) j))
  = let r = L.perm32 a i0 i1 i2 i3 i4 i5 i6 i7 in
    let aux (j: nat { j < 8 })
      : Lemma (sel8 (U32.v i0) (U32.v i1) (U32.v i2) (U32.v i3)
                    (U32.v i4) (U32.v i5) (U32.v i6) (U32.v i7) j < 8 /\
               V.lane r j ==
               V.lane a (sel8 (U32.v i0) (U32.v i1) (U32.v i2) (U32.v i3)
                              (U32.v i4) (U32.v i5) (U32.v i6) (U32.v i7) j))
      = if j = 0 then () else if j = 1 then () else if j = 2 then () else if j = 3 then ()
        else if j = 4 then () else if j = 5 then () else if j = 6 then () else ()
    in
    Classical.forall_intro aux

(** The permuted roots are entries of the tables. *)
let perm_tab (base: nat) (zl zsl: V.t) (i0 i1 i2 i3 i4 i5 i6 i7: (i: U32.t { U32.v i < 8 }))
  : Lemma (requires ztab zl zsl base)
          (ensures (let z = L.perm32 zl i0 i1 i2 i3 i4 i5 i6 i7 in
                    let zs = L.perm32 zsl i0 i1 i2 i3 i4 i5 i6 i7 in
                    forall (j: nat). j < 8 ==>
                      (let k = sel8 (U32.v i0) (U32.v i1) (U32.v i2) (U32.v i3)
                                    (U32.v i4) (U32.v i5) (U32.v i6) (U32.v i7) j in
                       k < 8 /\ base + k < 256 /\
                       V.lane z j == Seq.index zeta_table (base + k) /\
                       V.lane zs j == Seq.index zeta_shoup_table (base + k))))
  = let z = L.perm32 zl i0 i1 i2 i3 i4 i5 i6 i7 in
    let zs = L.perm32 zsl i0 i1 i2 i3 i4 i5 i6 i7 in
    perm_lane zl i0 i1 i2 i3 i4 i5 i6 i7;
    perm_lane zsl i0 i1 i2 i3 i4 i5 i6 i7

(** ... and those are the roots the layer wants, once the indices are right. *)
let perm_roots (base: nat) (z zs: V.t) (k: (j: nat { j < 8 }) -> nat) (zi: (j: nat { j < 8 }) -> GTot nat)
  : Lemma (requires (forall (j: nat). j < 8 ==>
                       k j < 8 /\ base + k j < 256 /\ base + k j == zi j /\
                       V.lane z j == Seq.index zeta_table (base + k j) /\
                       V.lane zs j == Seq.index zeta_shoup_table (base + k j)))
          (ensures vshoup_pre z zs /\
                   (forall (j: nat). j < 8 ==> zi j < 256 /\ S32.v (V.lane z j) == zetas (zi j)))
  = let aux (j: nat { j < 8 })
      : Lemma (zi j < 256 /\ S32.v (V.lane z j) == zetas (zi j) /\ S32.v (V.lane z j) < q /\
               S32.v (V.lane zs j) == shoup_of (S32.v (V.lane z j)))
      = zeta_table_index (base + k j);
        zeta_shoup_table_index (base + k j)
    in
    Classical.forall_intro aux

let zperm_ntt2_idx (lo base: nat)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 32 + lo / 8)
          (ensures forall (j: nat). j < 8 ==> base + sel8 0 0 0 0 1 1 1 1 j == zidx 2 (lo + pos 2 j))
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\
                 pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256);
    let aux (j: nat { j < 8 }) : Lemma (base + sel8 0 0 0 0 1 1 1 1 j == zidx 2 (lo + pos 2 j))
      = small_idx 2 lo (pos 2 j);
        assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let zperm_ntt2 (lo base: nat) (zl zsl z zs: V.t)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 32 + lo / 8 /\ ztab zl zsl base /\
                    z == L.perm32 zl 0ul 0ul 0ul 0ul 1ul 1ul 1ul 1ul /\ zs == L.perm32 zsl 0ul 0ul 0ul 0ul 1ul 1ul 1ul 1ul)
          (ensures vshoup_pre z zs /\
                   (forall (j: nat). j < 8 ==> S32.v (V.lane z j) == zetas (zidx 2 (lo + pos 2 j))))
  = perm_tab base zl zsl 0ul 0ul 0ul 0ul 1ul 1ul 1ul 1ul;
    zperm_ntt2_idx lo base;
    perm_roots base z zs (sel8 0 0 0 0 1 1 1 1) (fun j -> zidx 2 (lo + pos 2 j))

let zperm_ntt1_idx (lo base: nat)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 64 + lo / 4)
          (ensures forall (j: nat). j < 8 ==> base + sel8 0 0 2 2 1 1 3 3 j == zidx 1 (lo + pos 1 j))
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\
                 pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256);
    let aux (j: nat { j < 8 }) : Lemma (base + sel8 0 0 2 2 1 1 3 3 j == zidx 1 (lo + pos 1 j))
      = small_idx 1 lo (pos 1 j);
        assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let zperm_ntt1 (lo base: nat) (zl zsl z zs: V.t)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 64 + lo / 4 /\ ztab zl zsl base /\
                    z == L.perm32 zl 0ul 0ul 2ul 2ul 1ul 1ul 3ul 3ul /\ zs == L.perm32 zsl 0ul 0ul 2ul 2ul 1ul 1ul 3ul 3ul)
          (ensures vshoup_pre z zs /\
                   (forall (j: nat). j < 8 ==> S32.v (V.lane z j) == zetas (zidx 1 (lo + pos 1 j))))
  = perm_tab base zl zsl 0ul 0ul 2ul 2ul 1ul 1ul 3ul 3ul;
    zperm_ntt1_idx lo base;
    perm_roots base z zs (sel8 0 0 2 2 1 1 3 3) (fun j -> zidx 1 (lo + pos 1 j))

let zperm_ntt0_idx (lo base: nat)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 128 + lo / 2)
          (ensures forall (j: nat). j < 8 ==> base + sel8 0 1 4 5 2 3 6 7 j == zidx 0 (lo + pos 0 j))
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\
                 pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256);
    let aux (j: nat { j < 8 }) : Lemma (base + sel8 0 1 4 5 2 3 6 7 j == zidx 0 (lo + pos 0 j))
      = small_idx 0 lo (pos 0 j);
        assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let zperm_ntt0 (lo base: nat) (zl zsl z zs: V.t)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 128 + lo / 2 /\ ztab zl zsl base /\
                    z == L.perm32 zl 0ul 1ul 4ul 5ul 2ul 3ul 6ul 7ul /\ zs == L.perm32 zsl 0ul 1ul 4ul 5ul 2ul 3ul 6ul 7ul)
          (ensures vshoup_pre z zs /\
                   (forall (j: nat). j < 8 ==> S32.v (V.lane z j) == zetas (zidx 0 (lo + pos 0 j))))
  = perm_tab base zl zsl 0ul 1ul 4ul 5ul 2ul 3ul 6ul 7ul;
    zperm_ntt0_idx lo base;
    perm_roots base z zs (sel8 0 1 4 5 2 3 6 7) (fun j -> zidx 0 (lo + pos 0 j))

let zperm_intt2_idx (lo base: nat)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 62 - lo / 8)
          (ensures forall (j: nat). j < 8 ==> base + sel8 1 1 1 1 0 0 0 0 j == zidx_inv 2 (lo + pos 2 j))
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\
                 pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256);
    let aux (j: nat { j < 8 }) : Lemma (base + sel8 1 1 1 1 0 0 0 0 j == zidx_inv 2 (lo + pos 2 j))
      = small_idx 2 lo (pos 2 j);
        assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let zperm_intt2 (lo base: nat) (zl zsl z zs: V.t)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 62 - lo / 8 /\ ztab zl zsl base /\
                    z == L.perm32 zl 1ul 1ul 1ul 1ul 0ul 0ul 0ul 0ul /\ zs == L.perm32 zsl 1ul 1ul 1ul 1ul 0ul 0ul 0ul 0ul)
          (ensures vshoup_pre z zs /\
                   (forall (j: nat). j < 8 ==> S32.v (V.lane z j) == zetas (zidx_inv 2 (lo + pos 2 j))))
  = perm_tab base zl zsl 1ul 1ul 1ul 1ul 0ul 0ul 0ul 0ul;
    zperm_intt2_idx lo base;
    perm_roots base z zs (sel8 1 1 1 1 0 0 0 0) (fun j -> zidx_inv 2 (lo + pos 2 j))

let zperm_intt1_idx (lo base: nat)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 124 - lo / 4)
          (ensures forall (j: nat). j < 8 ==> base + sel8 3 3 1 1 2 2 0 0 j == zidx_inv 1 (lo + pos 1 j))
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\
                 pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256);
    let aux (j: nat { j < 8 }) : Lemma (base + sel8 3 3 1 1 2 2 0 0 j == zidx_inv 1 (lo + pos 1 j))
      = small_idx 1 lo (pos 1 j);
        assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let zperm_intt1 (lo base: nat) (zl zsl z zs: V.t)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 124 - lo / 4 /\ ztab zl zsl base /\
                    z == L.perm32 zl 3ul 3ul 1ul 1ul 2ul 2ul 0ul 0ul /\ zs == L.perm32 zsl 3ul 3ul 1ul 1ul 2ul 2ul 0ul 0ul)
          (ensures vshoup_pre z zs /\
                   (forall (j: nat). j < 8 ==> S32.v (V.lane z j) == zetas (zidx_inv 1 (lo + pos 1 j))))
  = perm_tab base zl zsl 3ul 3ul 1ul 1ul 2ul 2ul 0ul 0ul;
    zperm_intt1_idx lo base;
    perm_roots base z zs (sel8 3 3 1 1 2 2 0 0) (fun j -> zidx_inv 1 (lo + pos 1 j))

let zperm_intt0_idx (lo base: nat)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 248 - lo / 2)
          (ensures forall (j: nat). j < 8 ==> base + sel8 7 6 3 2 5 4 1 0 j == zidx_inv 0 (lo + pos 0 j))
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\
                 pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256);
    let aux (j: nat { j < 8 }) : Lemma (base + sel8 7 6 3 2 5 4 1 0 j == zidx_inv 0 (lo + pos 0 j))
      = small_idx 0 lo (pos 0 j);
        assert (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
    in
    Classical.forall_intro aux

let zperm_intt0 (lo base: nat) (zl zsl z zs: V.t)
  : Lemma (requires lo % 16 == 0 /\ lo + 16 <= n /\ base == 248 - lo / 2 /\ ztab zl zsl base /\
                    z == L.perm32 zl 7ul 6ul 3ul 2ul 5ul 4ul 1ul 0ul /\ zs == L.perm32 zsl 7ul 6ul 3ul 2ul 5ul 4ul 1ul 0ul)
          (ensures vshoup_pre z zs /\
                   (forall (j: nat). j < 8 ==> S32.v (V.lane z j) == zetas (zidx_inv 0 (lo + pos 0 j))))
  = perm_tab base zl zsl 7ul 6ul 3ul 2ul 5ul 4ul 1ul 0ul;
    zperm_intt0_idx lo base;
    perm_roots base z zs (sel8 7 6 3 2 5 4 1 0) (fun j -> zidx_inv 0 (lo + pos 0 j))

inline_for_extraction
let ntt_s2 (a b zl zsl: V.t) (p: Ghost.erased poly) (lo: Ghost.erased nat)
  : Pure (V.t & V.t)
    (requires lo % 16 == 0 /\ grp a b p lo /\ ztab zl zsl (32 + lo / 8))
    (ensures fun r -> grp (fst r) (snd r) (ntt_layer 2 p) lo)
  = assert_norm (pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2);
    let x = V.lo128 a b in
    let y = V.hi128 a b in
    shuf2_in a b p lo x y;
    let z = L.perm32 zl 0ul 0ul 0ul 0ul 1ul 1ul 1ul 1ul in
    let zs = L.perm32 zsl 0ul 0ul 0ul 0ul 1ul 1ul 1ul 1ul in
    zperm_ntt2 lo (32 + lo / 8) zl zsl z zs;
    let t = vshoup y z zs in
    let a' = vadd x t in
    let d' = vsub x t in
    small_ntt_lanes 2 p lo x y z t a' d';
    let a2 = V.lo128 a' d' in
    let b2 = V.hi128 a' d' in
    shuf2_out a' d' (ntt_layer 2 p) lo a2 b2;
    (a2, b2)

inline_for_extraction
let ntt_s1 (a b zl zsl: V.t) (p: Ghost.erased poly) (lo: Ghost.erased nat)
  : Pure (V.t & V.t)
    (requires lo % 16 == 0 /\ grp a b p lo /\ ztab zl zsl (64 + lo / 4))
    (ensures fun r -> grp (fst r) (snd r) (ntt_layer 1 p) lo)
  = assert_norm (pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2);
    let x = V.unpacklo64 a b in
    let y = V.unpackhi64 a b in
    shuf1_in a b p lo x y;
    let z = L.perm32 zl 0ul 0ul 2ul 2ul 1ul 1ul 3ul 3ul in
    let zs = L.perm32 zsl 0ul 0ul 2ul 2ul 1ul 1ul 3ul 3ul in
    zperm_ntt1 lo (64 + lo / 4) zl zsl z zs;
    let t = vshoup y z zs in
    let a' = vadd x t in
    let d' = vsub x t in
    small_ntt_lanes 1 p lo x y z t a' d';
    let a2 = V.unpacklo64 a' d' in
    let b2 = V.unpackhi64 a' d' in
    shuf1_out a' d' (ntt_layer 1 p) lo a2 b2;
    (a2, b2)

inline_for_extraction
let ntt_s0 (a b zl zsl: V.t) (p: Ghost.erased poly) (lo: Ghost.erased nat)
  : Pure (V.t & V.t)
    (requires lo % 16 == 0 /\ grp a b p lo /\ ztab zl zsl (128 + lo / 2))
    (ensures fun r -> grp (fst r) (snd r) (ntt_layer 0 p) lo)
  = assert_norm (pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2);
    let u = V.unpacklo32 a b in
    let w = V.unpackhi32 a b in
    let x = V.unpacklo32 u w in
    let y = V.unpackhi32 u w in
    shuf0_in a b p lo u w x y;
    let z = L.perm32 zl 0ul 1ul 4ul 5ul 2ul 3ul 6ul 7ul in
    let zs = L.perm32 zsl 0ul 1ul 4ul 5ul 2ul 3ul 6ul 7ul in
    zperm_ntt0 lo (128 + lo / 2) zl zsl z zs;
    let t = vshoup y z zs in
    let a' = vadd x t in
    let d' = vsub x t in
    small_ntt_lanes 0 p lo x y z t a' d';
    let a2 = V.unpacklo32 a' d' in
    let b2 = V.unpackhi32 a' d' in
    shuf0_out a' d' (ntt_layer 0 p) lo a2 b2;
    (a2, b2)

inline_for_extraction
let intt_s2 (a b zl zsl: V.t) (p: Ghost.erased poly) (lo: Ghost.erased nat)
  : Pure (V.t & V.t)
    (requires lo % 16 == 0 /\ grp a b p lo /\ ztab zl zsl (62 - lo / 8))
    (ensures fun r -> grp (fst r) (snd r) (intt_layer 2 p) lo)
  = assert_norm (pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2);
    let x = V.lo128 a b in
    let y = V.hi128 a b in
    shuf2_in a b p lo x y;
    let z = L.perm32 zl 1ul 1ul 1ul 1ul 0ul 0ul 0ul 0ul in
    let zs = L.perm32 zsl 1ul 1ul 1ul 1ul 0ul 0ul 0ul 0ul in
    zperm_intt2 lo (62 - lo / 8) zl zsl z zs;
    let a' = vadd x y in
    let s = vsub y x in
    let d' = vshoup s z zs in
    small_intt_lanes 2 p lo x y z s a' d';
    let a2 = V.lo128 a' d' in
    let b2 = V.hi128 a' d' in
    shuf2_out a' d' (intt_layer 2 p) lo a2 b2;
    (a2, b2)

inline_for_extraction
let intt_s1 (a b zl zsl: V.t) (p: Ghost.erased poly) (lo: Ghost.erased nat)
  : Pure (V.t & V.t)
    (requires lo % 16 == 0 /\ grp a b p lo /\ ztab zl zsl (124 - lo / 4))
    (ensures fun r -> grp (fst r) (snd r) (intt_layer 1 p) lo)
  = assert_norm (pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2);
    let x = V.unpacklo64 a b in
    let y = V.unpackhi64 a b in
    shuf1_in a b p lo x y;
    let z = L.perm32 zl 3ul 3ul 1ul 1ul 2ul 2ul 0ul 0ul in
    let zs = L.perm32 zsl 3ul 3ul 1ul 1ul 2ul 2ul 0ul 0ul in
    zperm_intt1 lo (124 - lo / 4) zl zsl z zs;
    let a' = vadd x y in
    let s = vsub y x in
    let d' = vshoup s z zs in
    small_intt_lanes 1 p lo x y z s a' d';
    let a2 = V.unpacklo64 a' d' in
    let b2 = V.unpackhi64 a' d' in
    shuf1_out a' d' (intt_layer 1 p) lo a2 b2;
    (a2, b2)

inline_for_extraction
let intt_s0 (a b zl zsl: V.t) (p: Ghost.erased poly) (lo: Ghost.erased nat)
  : Pure (V.t & V.t)
    (requires lo % 16 == 0 /\ grp a b p lo /\ ztab zl zsl (248 - lo / 2))
    (ensures fun r -> grp (fst r) (snd r) (intt_layer 0 p) lo)
  = assert_norm (pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2);
    let u = V.unpacklo32 a b in
    let w = V.unpackhi32 a b in
    let x = V.unpacklo32 u w in
    let y = V.unpackhi32 u w in
    shuf0_in a b p lo u w x y;
    let z = L.perm32 zl 7ul 6ul 3ul 2ul 5ul 4ul 1ul 0ul in
    let zs = L.perm32 zsl 7ul 6ul 3ul 2ul 5ul 4ul 1ul 0ul in
    zperm_intt0 lo (248 - lo / 2) zl zsl z zs;
    let a' = vadd x y in
    let s = vsub y x in
    let d' = vshoup s z zs in
    small_intt_lanes 0 p lo x y z s a' d';
    let a2 = V.unpacklo32 a' d' in
    let b2 = V.unpackhi32 a' d' in
    shuf0_out a' d' (intt_layer 0 p) lo a2 b2;
    (a2, b2)

(** {3 The group loop} *)

(** Groups below [lo] of [v] are those of [res]; the rest are still those
    of [vs]. *)
[@@"opaque_to_smt"]
let gdone (res: poly) (vs v: Seq.seq zqt) (lo: nat) : prop =
  Seq.length vs == n /\ Seq.length v == n /\ lo <= n /\
  (forall (k: nat). k < lo ==> S32.v (Seq.index v k) == Seq.index res k) /\
  (forall (k: nat). lo <= k /\ k < n ==> Seq.index v k == Seq.index vs k)

let gdone_start (res: poly) (vs: Seq.seq zqt)
  : Lemma (requires Seq.length vs == n) (ensures gdone res vs vs 0)
  = reveal_opaque (`%gdone) gdone

let gdone_load (res: poly) (vs v: Seq.seq zqt) (lo: nat) (a b: V.t)
  : Lemma (requires gdone res vs v lo /\ Seq.length vs == n /\ Seq.length v == n /\ lo + 16 <= n /\
                    (forall (j: nat). j < 8 ==> V.lane a j == Seq.index v (lo + j)) /\
                    (forall (j: nat). j < 8 ==> V.lane b j == Seq.index v (lo + 8 + j)))
          (ensures grp a b (as_poly vs) lo)
  = reveal_opaque (`%gdone) gdone

let gdone_store (res: poly) (vs v v1 v2: Seq.seq zqt) (lo: nat) (a b: V.t)
  : Lemma (requires gdone res vs v lo /\ grp a b res lo /\
                    stored v v1 lo a /\ stored v1 v2 (lo + 8) b)
          (ensures gdone res vs v2 (lo + 16) /\ Seq.length v2 == n)
  = reveal_opaque (`%gdone) gdone

let gdone_done (res: poly) (vs v: Seq.seq zqt) (lo: nat)
  : Lemma (requires gdone res vs v lo /\ lo == n)
          (ensures Seq.length v == n /\ as_poly v == res)
  = reveal_opaque (`%gdone) gdone;
    as_poly_intro v res

let grp_lt (a b: V.t) (p: poly) (lo: nat)
  : Lemma (requires grp a b p lo)
          (ensures (forall (j: nat). j < 8 ==> S32.v (V.lane a j) < q) /\
                   (forall (j: nat). j < 8 ==> S32.v (V.lane b j) < q))
  = ()

let ztab_intro (zl zsl: V.t) (i base: nat)
  : Lemma (requires i == base /\ base + 8 <= 256 /\
                    (forall (j: nat). j < 8 ==> V.lane zl j == Seq.index zeta_table (i + j)) /\
                    (forall (j: nat). j < 8 ==> V.lane zsl j == Seq.index zeta_shoup_table (i + j)))
          (ensures ztab zl zsl base)
  = ()

let grp_step (lo g: nat)
  : Lemma (requires lo == 16 * g /\ lo < n)
          (ensures lo % 16 == 0 /\ lo + 16 <= n /\ lo / 8 == 2 * g /\ lo / 4 == 4 * g /\
                   lo / 2 == 8 * g /\ 16 * g + 16 == 16 * (g + 1) /\ g < 16)
  = Math.cancel_mul_mod g 16;
    Math.lemma_div_plus 0 (2 * g) 8;
    Math.lemma_div_plus 0 (4 * g) 4;
    Math.lemma_div_plus 0 (8 * g) 2

inline_for_extraction
fn load_tab (zt: A.array zqt) (zst: A.array S32.t) (i: SZ.t) (base: erased nat)
            (#pz #ps: perm)
requires A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
         pure (SZ.v i == reveal base /\ reveal base + 8 <= 256)
returns r: (V.t & V.t)
ensures A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
        pure (ztab (fst r) (snd r) base)
{
  let zl = L.load_at zt i;
  let zs = L.load_word_at zst i;
  ztab_intro zl zs (SZ.v i) base;
  (zl, zs)
}

inline_for_extraction
fn load_grp (f: A.array zqt) (lo: SZ.t) (res: erased poly) (#vs #v: erased (Seq.seq zqt))
requires A.pts_to f v **
         pure (gdone res vs v (SZ.v lo) /\ Seq.length vs == n /\ Seq.length v == n /\ SZ.v lo + 16 <= n)
returns r: (V.t & V.t)
ensures A.pts_to f v ** pure (Seq.length vs == n /\ grp (fst r) (snd r) (as_poly vs) (SZ.v lo))
{
  A.pts_to_len f;
  let a = L.load_at f lo;
  let b = L.load_at f (SZ.add lo 8sz);
  gdone_load res vs v (SZ.v lo) a b;
  (a, b)
}

inline_for_extraction
fn store_grp (f: A.array zqt) (lo: SZ.t) (res: erased poly) (r: (V.t & V.t))
             (#vs #v: erased (Seq.seq zqt))
requires A.pts_to f v **
         pure (gdone res vs v (SZ.v lo) /\ Seq.length vs == n /\ Seq.length v == n /\ SZ.v lo + 16 <= n /\
               grp (fst r) (snd r) res (SZ.v lo))
ensures exists* v2. A.pts_to f v2 **
        pure (gdone res vs v2 (SZ.v lo + 16) /\ Seq.length v2 == n)
{
  A.pts_to_len f;
  grp_lt (fst r) (snd r) res (SZ.v lo);
  L.store_at f lo (fst r);
  with v1. assert (A.pts_to f v1);
  L.store_at f (SZ.add lo 8sz) (snd r);
  with v2. assert (A.pts_to f v2);
  gdone_store res vs v v1 v2 (SZ.v lo) (fst r) (snd r);
  assert pure (gdone res vs v2 (SZ.v lo + 16) /\ Seq.length v2 == n);
}

(** [f <- ntt_layer 0 (ntt_layer 1 (ntt_layer 2 f))], sixteen coefficients
    at a time. *)
inline_for_extraction
fn ntt_small (f: A.array zqt) (#vs: erased (Seq.seq zqt))
requires A.pts_to f vs ** pure (Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == ntt_layer 0 (ntt_layer 1 (ntt_layer 2 (as_poly vs))))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 256sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 256sz;
  with ps. assert (A.pts_to zst #ps zeta_shoup_table);
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let res : erased poly = hide (ntt_layer 0 (ntt_layer 1 (ntt_layer 2 (as_poly vs))));
  gdone_start res vs;
  let mut lo = 0sz;
  let mut g = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vg: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to g vg ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (Seq.length vs == n /\ Seq.length v == n /\
          SZ.v vlo <= n /\ SZ.v vlo == 16 * SZ.v vg /\ gdone res vs v (SZ.v vlo))
  decreases (n - SZ.v (!lo))
  {
    let vlo = !lo;
    let vg = !g;
    grp_step (SZ.v vlo) (SZ.v vg);
    let nlo = SZ.add vlo 16sz;
    let ng = SZ.add vg 1sz;
    assert pure (SZ.v nlo == 16 * SZ.v ng /\ SZ.v nlo <= n /\ SZ.v nlo == SZ.v vlo + 16);
    let g2 = SZ.add vg vg;
    let g4 = SZ.add g2 g2;
    let g8 = SZ.add g4 g4;
    let i2 = SZ.add 32sz g2;
    let i1 = SZ.add 64sz g4;
    let i0 = SZ.add 128sz g8;
    assert pure (SZ.v i2 == 32 + SZ.v vlo / 8 /\ SZ.v i1 == 64 + SZ.v vlo / 4 /\
                 SZ.v i0 == 128 + SZ.v vlo / 2 /\ SZ.v i0 + 8 <= 256);
    let t2 = load_tab zt zst i2 (32 + SZ.v vlo / 8);
    let t1 = load_tab zt zst i1 (64 + SZ.v vlo / 4);
    let t0 = load_tab zt zst i0 (128 + SZ.v vlo / 2);
    let p0 : erased poly = hide (as_poly vs);
    let p1 : erased poly = hide (ntt_layer 2 p0);
    let p2 : erased poly = hide (ntt_layer 1 p1);
    let r = load_grp f vlo res #vs;
    let r2 = ntt_s2 (fst r) (snd r) (fst t2) (snd t2) p0 (SZ.v vlo);
    let r1 = ntt_s1 (fst r2) (snd r2) (fst t1) (snd t1) p1 (SZ.v vlo);
    let r0 = ntt_s0 (fst r1) (snd r1) (fst t0) (snd t0) p2 (SZ.v vlo);
    store_grp f vlo res r0 #vs;
    lo := nlo;
    g := ng;
  };
  with (vlo: SZ.t) (v: Seq.seq zqt). assert (pts_to lo vlo ** A.pts_to f v);
  gdone_done res vs v (SZ.v vlo);
  T.drop_table zst;
  T.drop_table zt;
}

(** [f <- intt_layer 2 (intt_layer 1 (intt_layer 0 f))], sixteen
    coefficients at a time. *)
inline_for_extraction
fn intt_small (f: A.array zqt) (#vs: erased (Seq.seq zqt))
requires A.pts_to f vs ** pure (Seq.length vs == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vs == n /\ Seq.length v == n /\
              as_poly v == intt_layer 2 (intt_layer 1 (intt_layer 0 (as_poly vs))))
{
  A.pts_to_len f;
  let zt = T.table zeta_arr 256sz;
  with pz. assert (A.pts_to zt #pz zeta_table);
  let zst = T.table zeta_shoup_arr 256sz;
  with ps. assert (A.pts_to zst #ps zeta_shoup_table);
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let res : erased poly = hide (intt_layer 2 (intt_layer 1 (intt_layer 0 (as_poly vs))));
  gdone_start res vs;
  let mut lo = 0sz;
  let mut g = 0sz;
  while (let vlo = !lo; SZ.lt vlo 256sz)
  invariant exists* (vlo vg: SZ.t) (v: Seq.seq zqt).
    pts_to lo vlo ** pts_to g vg ** A.pts_to f v **
    A.pts_to zt #pz zeta_table ** A.pts_to zst #ps zeta_shoup_table **
    pure (Seq.length vs == n /\ Seq.length v == n /\
          SZ.v vlo <= n /\ SZ.v vlo == 16 * SZ.v vg /\ gdone res vs v (SZ.v vlo))
  decreases (n - SZ.v (!lo))
  {
    let vlo = !lo;
    let vg = !g;
    grp_step (SZ.v vlo) (SZ.v vg);
    let nlo = SZ.add vlo 16sz;
    let ng = SZ.add vg 1sz;
    assert pure (SZ.v nlo == 16 * SZ.v ng /\ SZ.v nlo <= n /\ SZ.v nlo == SZ.v vlo + 16);
    let g2 = SZ.add vg vg;
    let g4 = SZ.add g2 g2;
    let g8 = SZ.add g4 g4;
    let i0 = SZ.sub 248sz g8;
    let i1 = SZ.sub 124sz g4;
    let i2 = SZ.sub 62sz g2;
    assert pure (SZ.v i2 == 62 - SZ.v vlo / 8 /\ SZ.v i1 == 124 - SZ.v vlo / 4 /\
                 SZ.v i0 == 248 - SZ.v vlo / 2 /\ SZ.v i2 >= 32);
    let t0 = load_tab zt zst i0 (248 - SZ.v vlo / 2);
    let t1 = load_tab zt zst i1 (124 - SZ.v vlo / 4);
    let t2 = load_tab zt zst i2 (62 - SZ.v vlo / 8);
    let p0 : erased poly = hide (as_poly vs);
    let p1 : erased poly = hide (intt_layer 0 p0);
    let p2 : erased poly = hide (intt_layer 1 p1);
    let r = load_grp f vlo res #vs;
    let r0 = intt_s0 (fst r) (snd r) (fst t0) (snd t0) p0 (SZ.v vlo);
    let r1 = intt_s1 (fst r0) (snd r0) (fst t1) (snd t1) p1 (SZ.v vlo);
    let r2 = intt_s2 (fst r1) (snd r1) (fst t2) (snd t2) p2 (SZ.v vlo);
    store_grp f vlo res r2 #vs;
    lo := nlo;
    g := ng;
  };
  with (vlo: SZ.t) (v: Seq.seq zqt). assert (pts_to lo vlo ** A.pts_to f v);
  gdone_done res vs v (SZ.v vlo);
  T.drop_table zst;
  T.drop_table zt;
}

(** {2 The transforms} *)

(** [f <- NTT(f)], in place.  Uses AVX2. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn ntt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
requires A.pts_to f vf ** pure (Seq.length vf == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == ntt (as_poly vf))
{
  A.pts_to_len f;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  ntt_layer8 f 128sz 1sz #7;
  with v1. assert (A.pts_to f v1);
  ntt_layer8 f 64sz 2sz #6;
  with v2. assert (A.pts_to f v2);
  ntt_layer8 f 32sz 4sz #5;
  with v3. assert (A.pts_to f v3);
  ntt_layer8 f 16sz 8sz #4;
  with v4. assert (A.pts_to f v4);
  ntt_layer8 f 8sz 16sz #3;
  with v5. assert (A.pts_to f v5);
  ntt_small f;
  with v8. assert (A.pts_to f v8);
  ntt_compose (as_poly vf) (as_poly v1) (as_poly v2) (as_poly v3) (as_poly v4)
    (as_poly v5) (ntt_layer 2 (as_poly v5)) (ntt_layer 1 (ntt_layer 2 (as_poly v5))) (as_poly v8);
  ()
}

(** [f <- NTT^-1(f)], in place.  Uses AVX2. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn intt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
requires A.pts_to f vf ** pure (Seq.length vf == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == intt (as_poly vf))
{
  A.pts_to_len f;
  assert_norm (pow2 7 == 128 /\ pow2 6 == 64 /\ pow2 5 == 32 /\ pow2 4 == 16 /\
               pow2 3 == 8 /\ pow2 2 == 4 /\ pow2 1 == 2 /\ pow2 0 == 1);
  intt_small f;
  with u3. assert (A.pts_to f u3);
  intt_layer8 f 8sz 16sz #3;
  with u4. assert (A.pts_to f u4);
  intt_layer8 f 16sz 8sz #4;
  with u5. assert (A.pts_to f u5);
  intt_layer8 f 32sz 4sz #5;
  with u6. assert (A.pts_to f u6);
  intt_layer8 f 64sz 2sz #6;
  with u7. assert (A.pts_to f u7);
  intt_layer8 f 128sz 1sz #7;
  with w. assert (A.pts_to f w);
  intt_compose (as_poly vf) (intt_layer 0 (as_poly vf)) (intt_layer 1 (intt_layer 0 (as_poly vf)))
    (as_poly u3) (as_poly u4) (as_poly u5) (as_poly u6) (as_poly u7) (as_poly w);
  scale_ f;
}

(** [dst <- a * b], coefficient by coefficient.  Uses AVX2. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn multiply (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n)
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == poly_mul (as_poly va) (as_poly vb))
{
  multiply_ dst a b
}

#pop-options
