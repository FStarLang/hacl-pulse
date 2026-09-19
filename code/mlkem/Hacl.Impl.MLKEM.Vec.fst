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
fn vec_ntt_impl (v tmp: A.array zqt) (k: SZ.t)
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

#pop-options

#pop-options
