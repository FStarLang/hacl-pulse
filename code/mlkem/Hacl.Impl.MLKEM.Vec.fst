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

(** Vectors of polynomials.

    A [k]-vector is one array of [k * 256] coefficients, laid out the way
    {!Spec.MLKEM.Zq.pvec} is, so entry [i] is the sub-array starting at
    [256 i] and nothing is ever copied to get at it.  Addition and
    subtraction do not care about the block structure at all -- they are
    elementwise over the whole array -- so they are stated for a length,
    and the same code serves a polynomial and a vector.

    The transforms do care, and the shape of every loop that does is the
    same: the invariant says that the coefficients below [256 i] are
    already those of the answer and the rest are still the input, and
    {!flat_index} is what turns a statement about entry [i] into a
    statement about coefficient [256 i + j]. *)
module Hacl.Impl.MLKEM.Vec

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.Poly
open Hacl.Impl.MLKEM.VecLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S16 = Hacl.Secret.UInt16
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub
module HSZ = Hacl.SizeT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Elementwise addition and subtraction} *)

(** [a <- a + b], coefficient by coefficient, over [len] of them. *)
fn add_inplace (a b: A.array zqt) (len: SZ.t)
               (#va: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq zqt))
requires A.pts_to a va ** A.pts_to b #p vb **
         pure (Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\
               SZ.v len <= 4 * n)
ensures exists* v. A.pts_to a v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v len /\ Seq.length va == SZ.v len /\
        Seq.length vb == SZ.v len /\
        (forall (t: nat). t < SZ.v len ==>
           S16.v (Seq.index v t) == add (S16.v (Seq.index va t)) (S16.v (Seq.index vb t))))
{
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\
          (forall (t: nat). t < SZ.v vi ==>
             S16.v (Seq.index v t) == add (S16.v (Seq.index va t)) (S16.v (Seq.index vb t))) /\
          SZ.v len <= 4 * n /\
          (forall (t: nat). SZ.v vi <= t /\ t < SZ.v len ==>
             Seq.index v t == Seq.index va t))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((a.(vi) <- zq_add x y));
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
}

(** [a <- a - b]. *)
fn sub_inplace (a b: A.array zqt) (len: SZ.t)
               (#va: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq zqt))
requires A.pts_to a va ** A.pts_to b #p vb **
         pure (Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\
               SZ.v len <= 4 * n)
ensures exists* v. A.pts_to a v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v len /\ Seq.length va == SZ.v len /\
        Seq.length vb == SZ.v len /\
        (forall (t: nat). t < SZ.v len ==>
           S16.v (Seq.index v t) == sub (S16.v (Seq.index va t)) (S16.v (Seq.index vb t))))
{
  A.pts_to_len a;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len /\
          (forall (t: nat). t < SZ.v vi ==>
             S16.v (Seq.index v t) == sub (S16.v (Seq.index va t)) (S16.v (Seq.index vb t))) /\
          SZ.v len <= 4 * n /\
          (forall (t: nat). SZ.v vi <= t /\ t < SZ.v len ==>
             Seq.index v t == Seq.index va t))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((a.(vi) <- zq_sub x y));
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
}

(** {2 The transform, entry by entry} *)

#push-options "--z3rlimit 200"

(** [v <- NTT(v)] on each of the [k] entries. *)
fn vec_ntt_impl (v tmp: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                (#vv #vt: erased (Seq.seq zqt))
requires A.pts_to v vv ** A.pts_to tmp vt **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vv == SZ.v k * n /\ Seq.length vt == n)
ensures exists* w u. A.pts_to v w ** A.pts_to tmp u **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == SZ.v k * n /\
        Seq.length vv == SZ.v k * n /\ Seq.length u == n /\
        as_zqs w == vec_ntt #(SZ.v k) (as_zqs vv))
{
  A.pts_to_len v;
  A.pts_to_len tmp;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt) (u: Seq.seq zqt).
    pts_to i vi ** A.pts_to v w ** A.pts_to tmp u **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length w == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
          Seq.length u == n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index w t) ==
               Seq.index (vec_ntt #(SZ.v k) (as_zqs vv)) t) /\
          (forall (t: nat). SZ.v vi * n <= t /\ t < SZ.v k * n ==>
             Seq.index w t == Seq.index vv t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    with w0. assert (A.pts_to v w0);
    Seq.lemma_eq_intro (Seq.slice w0 (SZ.v lo) (SZ.v hi))
                       (Seq.slice vv (SZ.v lo) (SZ.v hi));
    assert (pure (Seq.slice w0 (SZ.v lo) (SZ.v hi) ==
                  Seq.slice vv (SZ.v lo) (SZ.v hi)));
    as_zqs_at (SZ.v k) vv (SZ.v vi);
    assert (pure (as_poly (Seq.slice w0 (SZ.v lo) (SZ.v hi)) ==
                  vec_at #(SZ.v k) (as_zqs vv) (SZ.v vi)));
    let blk = Sub.sub v lo hi;
    ntt_inplace blk tmp;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub v (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to v w1);
    ntt_entry_step (SZ.v k) (SZ.v vi) vv w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to v w);
  ntt_entry_done (SZ.v k) vv w;
  assert (pure (as_zqs w == vec_ntt #(SZ.v k) (as_zqs vv)));
}

(** [v <- NTT^-1(v)] on each of the [k] entries. *)
fn vec_intt_impl (v tmp: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                (#vv #vt: erased (Seq.seq zqt))
requires A.pts_to v vv ** A.pts_to tmp vt **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vv == SZ.v k * n /\ Seq.length vt == n)
ensures exists* w u. A.pts_to v w ** A.pts_to tmp u **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == SZ.v k * n /\
        Seq.length vv == SZ.v k * n /\ Seq.length u == n /\
        as_zqs w == vec_intt #(SZ.v k) (as_zqs vv))
{
  A.pts_to_len v;
  A.pts_to_len tmp;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt) (u: Seq.seq zqt).
    pts_to i vi ** A.pts_to v w ** A.pts_to tmp u **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length w == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
          Seq.length u == n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index w t) ==
               Seq.index (vec_intt #(SZ.v k) (as_zqs vv)) t) /\
          (forall (t: nat). SZ.v vi * n <= t /\ t < SZ.v k * n ==>
             Seq.index w t == Seq.index vv t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    with w0. assert (A.pts_to v w0);
    Seq.lemma_eq_intro (Seq.slice w0 (SZ.v lo) (SZ.v hi))
                       (Seq.slice vv (SZ.v lo) (SZ.v hi));
    assert (pure (Seq.slice w0 (SZ.v lo) (SZ.v hi) ==
                  Seq.slice vv (SZ.v lo) (SZ.v hi)));
    as_zqs_at (SZ.v k) vv (SZ.v vi);
    assert (pure (as_poly (Seq.slice w0 (SZ.v lo) (SZ.v hi)) ==
                  vec_at #(SZ.v k) (as_zqs vv) (SZ.v vi)));
    let blk = Sub.sub v lo hi;
    intt_inplace blk tmp;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub v (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to v w1);
    intt_entry_step (SZ.v k) (SZ.v vi) vv w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to v w);
  intt_entry_done (SZ.v k) vv w;
  assert (pure (as_zqs w == vec_intt #(SZ.v k) (as_zqs vv)));
}

(** {2 The dot product} *)

(** Zero the first [len] coefficients. *)
fn zero_range (dst: A.array zqt) (len: SZ.t) (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 **
         pure (Seq.length v0 == SZ.v len /\ SZ.v len <= 4 * n)
ensures exists* v. A.pts_to dst v **
  pure (Seq.length v == SZ.v len /\
        (forall (t: nat). t < SZ.v len ==> S16.v (Seq.index v t) == 0))
{
  A.pts_to_len dst;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\ SZ.v len <= 4 * n /\
          (forall (t: nat). t < SZ.v vi ==> S16.v (Seq.index v t) == 0))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    A.((dst.(vi) <- S16.classify 0us));
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
}

(** [dst <- sum of u_i * v_i], both vectors in the NTT domain.  [tmp] holds
    one product at a time; the sum is accumulated in [dst]. *)
fn dot_impl (dst u v tmp: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
            (#vd: erased (Seq.seq zqt)) (#pu #pv: perm)
            (#vu #vv #vt: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
         A.pts_to tmp vt **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vd == n /\
               Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
               Seq.length vt == n)
ensures exists* w c. A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
  A.pts_to tmp c **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == n /\ Seq.length c == n /\
        Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
        as_poly w == dot #(SZ.v k) (as_zqs vu) (as_zqs vv))
{
  A.pts_to_len dst;
  A.pts_to_len u;
  A.pts_to_len v;
  A.pts_to_len tmp;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  zero_range dst 256sz;
  with d0. assert (A.pts_to dst d0);
  as_poly_intro d0 poly_zero;
  dot_acc_zero #(SZ.v k) (as_zqs vu) (as_zqs vv);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt) (c: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst w ** A.pts_to u #pu vu ** A.pts_to v #pv vv **
    A.pts_to tmp c **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length w == n /\ Seq.length c == n /\
          Seq.length vu == SZ.v k * n /\ Seq.length vv == SZ.v k * n /\
          as_poly w == dot_acc #(SZ.v k) (as_zqs vu) (as_zqs vv) (SZ.v vi))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    as_zqs_at (SZ.v k) vu (SZ.v vi);
    as_zqs_at (SZ.v k) vv (SZ.v vi);
    let bu = Sub.sub u lo hi;
    let bv = Sub.sub v lo hi;
    multiply tmp bu bv;
    Sub.unsub_id u (SZ.v lo) (SZ.v hi) bu;
    Sub.unsub_id v (SZ.v lo) (SZ.v hi) bv;
    with c. assert (A.pts_to tmp c);
    with d. assert (A.pts_to dst d);
    add_inplace dst tmp 256sz;
    with w1. assert (A.pts_to dst w1);
    dot_step_done #(SZ.v k) (as_zqs vu) (as_zqs vv) (SZ.v vi) d c w1;
    i := SZ.add vi 1sz;
  };
  dot_acc_full #(SZ.v k) (as_zqs vu) (as_zqs vv);
}


(** {2 The matrix-vector product} *)

(** [dst <- m v], with [m] a [k x k] matrix flat and row-major.  One
    {!dot_impl} per row; [tmp] is the dot product's scratch space. *)
fn mat_vec_mul_impl (dst m v tmp: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                    (#vd: erased (Seq.seq zqt)) (#pm #pv: perm)
                    (#vm #vv #vt: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to m #pm vm ** A.pts_to v #pv vv **
         A.pts_to tmp vt **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vd == SZ.v k * n /\
               Seq.length vm == SZ.v k * SZ.v k * n /\
               Seq.length vv == SZ.v k * n /\ Seq.length vt == n)
ensures exists* w c. A.pts_to dst w ** A.pts_to m #pm vm ** A.pts_to v #pv vv **
  A.pts_to tmp c **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length w == SZ.v k * n /\
        Seq.length c == n /\ Seq.length vm == SZ.v k * SZ.v k * n /\
        Seq.length vv == SZ.v k * n /\
        as_zqs w == mat_vec_mul #(SZ.v k) (as_zqs vm) (as_zqs vv))
{
  A.pts_to_len dst;
  A.pts_to_len m;
  A.pts_to_len v;
  A.pts_to_len tmp;
  HSZ.fits32 ();
  assert_norm (4 * 4 * n < pow2 32);
  Math.paren_mul_right (SZ.v k) (SZ.v k) n;
  let kn = SZ.mul k 256sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt) (c: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst w ** A.pts_to m #pm vm ** A.pts_to v #pv vv **
    A.pts_to tmp c **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length w == SZ.v k * n /\ Seq.length c == n /\
          Seq.length vm == SZ.v k * SZ.v k * n /\
          Seq.length vv == SZ.v k * n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index w t) ==
               Seq.index (mat_vec_mul #(SZ.v k) (as_zqs vm) (as_zqs vv)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    Math.lemma_mult_le_right (SZ.v k * n) (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi * (SZ.v k * n) + SZ.v k * n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let rlo = SZ.mul vi kn;
    let rhi = SZ.add rlo kn;
    as_zqs_row (SZ.v k) vm (SZ.v vi);
    with w0. assert (A.pts_to dst w0);
    let row = Sub.sub m rlo rhi;
    let blk = Sub.sub dst lo hi;
    dot_impl blk row v tmp k;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub_id m (SZ.v rlo) (SZ.v rhi) row;
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    mv_entry_step (SZ.v k) (SZ.v vi) vm vv w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with w. assert (A.pts_to dst w);
  mv_entry_done (SZ.v k) vm vv w;
  assert (pure (as_zqs w == mat_vec_mul #(SZ.v k) (as_zqs vm) (as_zqs vv)));
}

#pop-options

#pop-options
