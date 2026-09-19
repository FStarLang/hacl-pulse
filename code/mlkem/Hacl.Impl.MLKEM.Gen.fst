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

(** The matrix and the noise vector.

    Both are loops that fill one polynomial at a time from a seed the loop
    itself builds: [rho] and two indices for the matrix, a secret seed and a
    running public counter for the noise.  The matrix is public -- it is
    derived from a seed that travels in the clear -- so its indices are
    ordinary [size_t]s, while the noise counter is a public byte over a
    secret seed. *)
module Hacl.Impl.MLKEM.Gen

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Sample
open Spec.MLKEM
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.Sampler
open Hacl.Impl.MLKEM.GenLemmas
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub
module HSZ = Hacl.SizeT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Algorithm 13 line 3 and Algorithm 14 line 4: the [k x k] matrix, row
    major, [SampleNTT] of [rho] and the two indices.  [tr] swaps the two
    indices, which is how the standard transposes. *)
fn gen_matrix_impl (dst: A.array zqt) (rho: A.array S8.t) (tr: bool) (k: SZ.t)
                   (#vd: erased (Seq.seq zqt)) (#p: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #p vr **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vd == SZ.v k * SZ.v k * n /\ Seq.length vr == 32)
ensures exists* v. A.pts_to dst v ** A.pts_to rho #p vr **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vr == 32 /\
        Seq.length v == SZ.v k * SZ.v k * n /\
        as_zqs v == gen_matrix (SZ.v k) vr tr)
{
  A.pts_to_len dst;
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (4 * 4 * n < pow2 32);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  let z8 = S8.classify 0uy;
  let mut sd = [| z8; 34sz |];
  A.pts_to_len sd;
  copy_prefix sd rho 32sz;
  let kk = SZ.mul k k;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc kk)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt) (vsd: Seq.seq S8.t).
    pts_to c vc ** A.pts_to dst v ** A.pts_to rho #p vr ** A.pts_to sd vsd **
    pure (SZ.v vc <= SZ.v k * SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length v == SZ.v k * SZ.v k * n /\ Seq.length vr == 32 /\
          Seq.length vsd == 34 /\
          (forall (t: nat). t < 32 ==> Seq.index vsd t == Seq.index vr t) /\
          (forall (t: nat). t < SZ.v vc * n ==>
             S16.v (Seq.index v t) == Seq.index (gen_matrix (SZ.v k) vr tr) t))
  decreases (SZ.v k * SZ.v k - SZ.v (!c))
  {
    let vc = !c;
    Math.lemma_mult_le_right n (SZ.v vc + 1) (SZ.v k * SZ.v k);
    Math.distributivity_add_left (SZ.v vc) 1 n;
    Math.lemma_mult_le_right (SZ.v k) (SZ.v k) 4;
    Math.lemma_mult_le_left 4 (SZ.v k) 4;
    Math.lemma_mult_le_right n (SZ.v k * SZ.v k) 16;
    SZ.fits_u32_implies_fits (SZ.v vc * n + n);
    SZ.fits_u32_implies_fits (SZ.v vc + 1);
    let lo = SZ.mul vc 256sz;
    let hi = SZ.add lo 256sz;
    let ci = SZ.div vc k;
    let cj = SZ.rem vc k;
    div_lt (SZ.v vc) (SZ.v k) (SZ.v k);
    let bi = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 ci);
    let bj = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 cj);
    Math.small_mod (SZ.v ci) 256;
    Math.small_mod (SZ.v cj) 256;
    Math.small_mod (SZ.v ci) 4294967296;
    Math.small_mod (SZ.v cj) 4294967296;
    assert (pure (U8.v bi == SZ.v ci /\ U8.v bj == SZ.v cj));
    let b32 = (if tr then bi else bj);
    let b33 = (if tr then bj else bi);
    A.((sd.(32sz) <- S8.classify b32));
    A.((sd.(33sz) <- S8.classify b33));
    with vsd. assert (A.pts_to sd vsd);
    seed_eq vr (SZ.v ci) (SZ.v cj) tr vsd;
    assert (pure (SZ.v ci == SZ.v vc / SZ.v k /\ SZ.v cj == SZ.v vc % SZ.v k));
    assert (pure (vsd == matrix_seed vr
                    (if tr then SZ.v vc % SZ.v k else SZ.v vc / SZ.v k)
                    (if tr then SZ.v vc / SZ.v k else SZ.v vc % SZ.v k)));
    with w0. assert (A.pts_to dst w0);
    let blk = Sub.sub dst lo hi;
    sample_ntt_impl blk sd 34sz;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    gen_entry_step (SZ.v k) vr tr (SZ.v vc) w0 w1 b1 vsd;
    c := SZ.add vc 1sz;
  };
  with v. assert (A.pts_to dst v);
  gen_entry_done (SZ.v k) vr tr v;
  assert (pure (as_zqs v == gen_matrix (SZ.v k) vr tr));
}

(** Algorithm 13 lines 8-11: [k] consecutive PRF calls with a running
    counter. *)
fn noise_vec_impl (dst: A.array zqt) (s: A.array S8.t) (start: U8.t) (eta k: SZ.t)
                  (#vd: erased (Seq.seq zqt)) (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to s #p vs **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               U8.v start + SZ.v k <= 256 /\
               Seq.length vd == SZ.v k * n /\ Seq.length vs == 32)
ensures exists* v. A.pts_to dst v ** A.pts_to s #p vs **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        U8.v start + SZ.v k <= 256 /\ Seq.length vs == 32 /\
        Seq.length v == SZ.v k * n /\
        as_zqs v == noise_vec (SZ.v k) (SZ.v eta) vs (U8.v start))
{
  A.pts_to_len dst;
  A.pts_to_len s;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to s #p vs **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          1 <= SZ.v eta /\ SZ.v eta <= 3 /\ U8.v start + SZ.v k <= 256 /\
          Seq.length v == SZ.v k * n /\ Seq.length vs == 32 /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index v t) ==
               Seq.index (noise_vec (SZ.v k) (SZ.v eta) vs (U8.v start)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let bi = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 vi);
    let byte = U8.add start bi;
    with w0. assert (A.pts_to dst w0);
    let blk = Sub.sub dst lo hi;
    sample_poly_cbd_impl blk s byte eta;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    noise_entry_step (SZ.v k) (SZ.v eta) vs (U8.v start) (SZ.v vi) w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  noise_entry_done (SZ.v k) (SZ.v eta) vs (U8.v start) v;
  assert (pure (as_zqs v == noise_vec (SZ.v k) (SZ.v eta) vs (U8.v start)));
}

#pop-options
