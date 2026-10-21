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


(** Vectors and matrices of polynomials, stored flat: entry [i] of a vector
    is coefficients [256 i] to [256 i + 255], and a [k x l] matrix is [k]
    rows of [l]-vectors.  The structure follows {!Hacl.Impl.MLKEM.Vec}. *)
module Hacl.Impl.MLDSA.Vec

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.NTT
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Poly
open Hacl.Impl.MLDSA.VecLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub
module HSZ = Hacl.SizeT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The largest flat length used: a [8 x 7] matrix. *)
let max_len : nat = 56 * n

(** {2 Elementwise operations} *)

(** [a <- a + b], coefficient by coefficient. *)
fn add_inplace (a b: A.array zqt) (len: SZ.t)
               (#va: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq zqt))
requires A.pts_to a va ** A.pts_to b #p vb **
         pure (Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\ SZ.v len <= max_len)
ensures exists* v. A.pts_to a v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v len /\ Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\
        (forall (t: nat). t < SZ.v len ==>
           S32.v (Seq.index v t) == add (S32.v (Seq.index va t)) (S32.v (Seq.index vb t))))
{
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (max_len < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\ SZ.v len <= max_len /\
          (forall (t: nat). t < SZ.v vi ==>
             S32.v (Seq.index v t) == add (S32.v (Seq.index va t)) (S32.v (Seq.index vb t))) /\
          (forall (t: nat). SZ.v vi <= t /\ t < SZ.v len ==> Seq.index v t == Seq.index va t))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.(a.(vi) <- zq_add x y);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
}

(** [a <- a - b]. *)
fn sub_inplace (a b: A.array zqt) (len: SZ.t)
               (#va: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq zqt))
requires A.pts_to a va ** A.pts_to b #p vb **
         pure (Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\ SZ.v len <= max_len)
ensures exists* v. A.pts_to a v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v len /\ Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\
        (forall (t: nat). t < SZ.v len ==>
           S32.v (Seq.index v t) == sub (S32.v (Seq.index va t)) (S32.v (Seq.index vb t))))
{
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (max_len < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\ SZ.v len <= max_len /\
          (forall (t: nat). t < SZ.v vi ==>
             S32.v (Seq.index v t) == sub (S32.v (Seq.index va t)) (S32.v (Seq.index vb t))) /\
          (forall (t: nat). SZ.v vi <= t /\ t < SZ.v len ==> Seq.index v t == Seq.index va t))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.(a.(vi) <- zq_sub x y);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
}

(** [a <- -a]. *)
fn neg_inplace (a: A.array zqt) (len: SZ.t) (#va: erased (Seq.seq zqt))
requires A.pts_to a va ** pure (Seq.length va == SZ.v len /\ SZ.v len <= max_len)
ensures exists* v. A.pts_to a v **
  pure (Seq.length v == SZ.v len /\ Seq.length va == SZ.v len /\
        (forall (t: nat). t < SZ.v len ==> S32.v (Seq.index v t) == neg (S32.v (Seq.index va t))))
{
  A.pts_to_len a;
  HSZ.fits32 ();
  assert_norm (max_len < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to a v **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          Seq.length va == SZ.v len /\ SZ.v len <= max_len /\
          (forall (t: nat). t < SZ.v vi ==> S32.v (Seq.index v t) == neg (S32.v (Seq.index va t))) /\
          (forall (t: nat). SZ.v vi <= t /\ t < SZ.v len ==> Seq.index v t == Seq.index va t))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    A.(a.(vi) <- zq_neg x);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
}

fn zero_range (dst: A.array zqt) (len: SZ.t) (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 ** pure (Seq.length v0 == SZ.v len /\ SZ.v len <= max_len)
ensures exists* v. A.pts_to dst v **
  pure (Seq.length v == SZ.v len /\ (forall (t: nat). t < SZ.v len ==> S32.v (Seq.index v t) == 0))
{
  A.pts_to_len dst;
  HSZ.fits32 ();
  assert_norm (max_len < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\ SZ.v len <= max_len /\
          (forall (t: nat). t < SZ.v vi ==> S32.v (Seq.index v t) == 0))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    A.(dst.(vi) <- S32.classify 0ul);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
}

(** {2 Entry by entry} *)

#push-options "--z3rlimit 200"

fn vec_ntt_impl (v: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                (#vv: erased (Seq.seq zqt))
requires A.pts_to v vv ** pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length vv == SZ.v k * n)
ensures exists* w. A.pts_to v w **
  pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length w == SZ.v k * n /\
        Seq.length vv == SZ.v k * n /\ as_zqs w == vec_ntt #(SZ.v k) (as_zqs vv))
{
  A.pts_to_len v;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt).
    pts_to i vi ** A.pts_to v w **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 8 /\
          Seq.length w == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S32.v (Seq.index w t) == Seq.index (vec_ntt #(SZ.v k) (as_zqs vv)) t) /\
          (forall (t: nat). SZ.v vi * n <= t /\ t < SZ.v k * n ==> Seq.index w t == Seq.index vv t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    with w0. assert (A.pts_to v w0);
    Seq.lemma_eq_intro (Seq.slice w0 (SZ.v lo) (SZ.v hi)) (Seq.slice vv (SZ.v lo) (SZ.v hi));
    as_zqs_at (SZ.v k) vv (SZ.v vi);
    let blk = Sub.sub v lo hi;
    ntt_inplace blk;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub v (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to v w1);
    ntt_entry_step (SZ.v k) (SZ.v vi) vv w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to v w);
  entry_done (SZ.v k) w (vec_ntt #(SZ.v k) (as_zqs vv));
  ()
}

fn vec_intt_impl (v: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 (#vv: erased (Seq.seq zqt))
requires A.pts_to v vv ** pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length vv == SZ.v k * n)
ensures exists* w. A.pts_to v w **
  pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length w == SZ.v k * n /\
        Seq.length vv == SZ.v k * n /\ as_zqs w == vec_intt #(SZ.v k) (as_zqs vv))
{
  A.pts_to_len v;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt).
    pts_to i vi ** A.pts_to v w **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 8 /\
          Seq.length w == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S32.v (Seq.index w t) == Seq.index (vec_intt #(SZ.v k) (as_zqs vv)) t) /\
          (forall (t: nat). SZ.v vi * n <= t /\ t < SZ.v k * n ==> Seq.index w t == Seq.index vv t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    with w0. assert (A.pts_to v w0);
    Seq.lemma_eq_intro (Seq.slice w0 (SZ.v lo) (SZ.v hi)) (Seq.slice vv (SZ.v lo) (SZ.v hi));
    as_zqs_at (SZ.v k) vv (SZ.v vi);
    let blk = Sub.sub v lo hi;
    intt_inplace blk;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub v (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to v w1);
    intt_entry_step (SZ.v k) (SZ.v vi) vv w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to v w);
  entry_done (SZ.v k) w (vec_intt #(SZ.v k) (as_zqs vv));
  ()
}

(** [dst <- c * v], entry by entry, in the NTT domain. *)
fn vec_scale_impl (dst c v: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  (#vd: erased (Seq.seq zqt)) (#pc #pv: perm) (#vc #vv: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to c #pc vc ** A.pts_to v #pv vv **
         pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length vd == SZ.v k * n /\
               Seq.length vc == n /\ Seq.length vv == SZ.v k * n)
ensures exists* w. A.pts_to dst w ** A.pts_to c #pc vc ** A.pts_to v #pv vv **
  pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length w == SZ.v k * n /\ Seq.length vc == n /\
        Seq.length vv == SZ.v k * n /\
        as_zqs w == vec_scale #(SZ.v k) (as_poly vc) (as_zqs vv))
{
  A.pts_to_len dst;
  A.pts_to_len c;
  A.pts_to_len v;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst w ** A.pts_to c #pc vc ** A.pts_to v #pv vv **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 8 /\ Seq.length vc == n /\
          Seq.length w == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S32.v (Seq.index w t) == Seq.index (vec_scale #(SZ.v k) (as_poly vc) (as_zqs vv)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    with w0. assert (A.pts_to dst w0);
    as_zqs_at (SZ.v k) vv (SZ.v vi);
    let bd = Sub.sub dst lo hi;
    let bv = Sub.sub v lo hi;
    multiply bd c bv;
    with b1. assert (A.pts_to bd b1);
    Sub.unsub_id v (SZ.v lo) (SZ.v hi) bv;
    Sub.unsub dst (SZ.v lo) (SZ.v hi) bd;
    with w1. assert (A.pts_to dst w1);
    scale_entry_step (SZ.v k) (SZ.v vi) (as_poly vc) vv w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to dst w);
  entry_done (SZ.v k) w (vec_scale #(SZ.v k) (as_poly vc) (as_zqs vv));
  ()
}

(** {2 The dot product and the matrix-vector product} *)

fn dot_impl (dst u v tmp: A.array zqt) ([@@@FStar.Attributes.monomorphize] l: SZ.t)
            (#vd: erased (Seq.seq zqt)) (#pu #pv: perm) (#vu #vv #vt: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to u #pu vu ** A.pts_to v #pv vv ** A.pts_to tmp vt **
         pure (1 <= SZ.v l /\ SZ.v l <= 8 /\ Seq.length vd == n /\
               Seq.length vu == SZ.v l * n /\ Seq.length vv == SZ.v l * n /\ Seq.length vt == n)
ensures exists* w c. A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv ** A.pts_to tmp c **
  pure (1 <= SZ.v l /\ SZ.v l <= 8 /\ Seq.length w == n /\ Seq.length c == n /\
        Seq.length vu == SZ.v l * n /\ Seq.length vv == SZ.v l * n /\
        as_poly w == dot #(SZ.v l) (as_zqs vu) (as_zqs vv))
{
  A.pts_to_len dst;
  A.pts_to_len u;
  A.pts_to_len v;
  A.pts_to_len tmp;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  zero_range dst 256sz;
  with d0. assert (A.pts_to dst d0);
  as_poly_intro d0 poly_zero;
  dot_acc_zero #(SZ.v l) (as_zqs vu) (as_zqs vv);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi l)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt) (c: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv ** A.pts_to tmp c **
    pure (SZ.v vi <= SZ.v l /\ 1 <= SZ.v l /\ SZ.v l <= 8 /\
          Seq.length w == n /\ Seq.length c == n /\
          Seq.length vu == SZ.v l * n /\ Seq.length vv == SZ.v l * n /\
          as_poly w == dot_acc #(SZ.v l) (as_zqs vu) (as_zqs vv) (SZ.v vi))
  decreases (SZ.v l - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v l);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    as_zqs_at (SZ.v l) vu (SZ.v vi);
    as_zqs_at (SZ.v l) vv (SZ.v vi);
    let bu = Sub.sub u lo hi;
    let bv = Sub.sub v lo hi;
    multiply tmp bu bv;
    Sub.unsub_id u (SZ.v lo) (SZ.v hi) bu;
    Sub.unsub_id v (SZ.v lo) (SZ.v hi) bv;
    with c. assert (A.pts_to tmp c);
    with d. assert (A.pts_to dst d);
    add_inplace dst tmp 256sz;
    with w1. assert (A.pts_to dst w1);
    dot_step_done #(SZ.v l) (as_zqs vu) (as_zqs vv) (SZ.v vi) d c w1;
    i := SZ.add vi 1sz;
  };
  dot_acc_full #(SZ.v l) (as_zqs vu) (as_zqs vv);
  ()
}

(** [dst <- m v], [m] a [k x l] matrix, [v] an [l]-vector, all in the NTT
    domain. *)
fn mat_vec_mul_impl (dst m v tmp: A.array zqt)
                    ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                    (#vd: erased (Seq.seq zqt)) (#pm #pv: perm)
                    (#vm #vv #vt: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to m #pm vm ** A.pts_to v #pv vv ** A.pts_to tmp vt **
         pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ 1 <= SZ.v l /\ SZ.v l <= 7 /\
               Seq.length vd == SZ.v k * n /\ Seq.length vm == SZ.v k * SZ.v l * n /\
               Seq.length vv == SZ.v l * n /\ Seq.length vt == n)
ensures exists* w c. A.pts_to dst w ** A.pts_to m #pm vm ** A.pts_to v #pv vv ** A.pts_to tmp c **
  pure (1 <= SZ.v k /\ SZ.v k <= 8 /\ 1 <= SZ.v l /\ SZ.v l <= 7 /\
        Seq.length w == SZ.v k * n /\ Seq.length c == n /\
        Seq.length vm == SZ.v k * SZ.v l * n /\ Seq.length vv == SZ.v l * n /\
        as_zqs w == mat_vec_mul #(SZ.v k) #(SZ.v l) (as_zqs vm) (as_zqs vv))
{
  A.pts_to_len dst;
  A.pts_to_len m;
  A.pts_to_len v;
  A.pts_to_len tmp;
  HSZ.fits32 ();
  assert_norm (8 * 7 * n < pow2 32);
  Math.paren_mul_right (SZ.v k) (SZ.v l) n;
  Math.lemma_mult_le_right n (SZ.v l) 7;
  let ln = SZ.mul l 256sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt) (c: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst w ** A.pts_to m #pm vm ** A.pts_to v #pv vv ** A.pts_to tmp c **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 8 /\ 1 <= SZ.v l /\ SZ.v l <= 7 /\
          Seq.length w == SZ.v k * n /\ Seq.length c == n /\
          Seq.length vm == SZ.v k * SZ.v l * n /\ Seq.length vv == SZ.v l * n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S32.v (Seq.index w t) ==
               Seq.index (mat_vec_mul #(SZ.v k) #(SZ.v l) (as_zqs vm) (as_zqs vv)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    Math.lemma_mult_le_right (SZ.v l * n) (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi * (SZ.v l * n) + SZ.v l * n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let rlo = SZ.mul vi ln;
    let rhi = SZ.add rlo ln;
    as_zqs_row (SZ.v k) (SZ.v l) vm (SZ.v vi);
    with w0. assert (A.pts_to dst w0);
    let row = Sub.sub m rlo rhi;
    let blk = Sub.sub dst lo hi;
    dot_impl blk row v tmp l;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub_id m (SZ.v rlo) (SZ.v rhi) row;
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    mv_entry_step (SZ.v k) (SZ.v l) (SZ.v vi) vm vv w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to dst w);
  entry_done (SZ.v k) w (mat_vec_mul #(SZ.v k) #(SZ.v l) (as_zqs vm) (as_zqs vv));
  ()
}

#pop-options

#pop-options
