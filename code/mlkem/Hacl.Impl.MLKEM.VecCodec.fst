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

(** The vector coders.

    Each of the four is the same loop: take entry [i] of the input, run the
    polynomial coder on it, and write the result into block [i] of the
    output.  The block size is [n] coefficients on the coefficient side and
    [32 d] bytes on the byte side, which is why {!Hacl.Impl.MLKEM.VecLemmas.flat_step}
    is stated for an arbitrary block size and an arbitrary view. *)
module Hacl.Impl.MLKEM.VecCodec

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Encode
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.Encode
open Hacl.Impl.MLKEM.VecLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub
module HSZ = Hacl.SizeT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** [out <- ByteEncode_d] of each entry. *)
fn vec_encode_impl (out: A.array S8.t) (src: A.array zqt) (d k: SZ.t)
                   (#p: perm) (#vo: erased (Seq.seq S8.t)) (#vs: erased (Seq.seq zqt))
requires A.pts_to out vo ** A.pts_to src #p vs **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vs == SZ.v k * n /\
               Seq.length vo == SZ.v k * (32 * SZ.v d))
ensures exists* v. A.pts_to out v ** A.pts_to src #p vs **
  pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
        Seq.length vs == SZ.v k * n /\ Seq.length v == SZ.v k * (32 * SZ.v d) /\
        v == vec_encode (SZ.v d) (SZ.v k) (as_ints vs))
{
  A.pts_to_len out;
  A.pts_to_len src;
  HSZ.fits32 ();
  assert_norm (4 * (32 * 12) < pow2 32);
  assert_norm (4 * n < pow2 32);
  let el = SZ.mul 32sz d;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to src #p vs **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v d /\ SZ.v d <= 12 /\
          1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length vs == SZ.v k * n /\
          Seq.length v == SZ.v k * (32 * SZ.v d) /\
          (forall (t: nat). t < SZ.v vi * (32 * SZ.v d) ==>
             Seq.index v t == Seq.index (vec_encode (SZ.v d) (SZ.v k) (as_ints vs)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    Math.lemma_mult_le_right (32 * SZ.v d) (SZ.v vi + 1) (SZ.v k);
    Math.distributivity_add_left (SZ.v vi) 1 (32 * SZ.v d);
    Math.lemma_mult_le_right (32 * SZ.v d) (SZ.v k) 4;
    Math.lemma_mult_le_left 4 (32 * SZ.v d) (32 * 12);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi * (32 * SZ.v d) + 32 * SZ.v d);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let blo = SZ.mul vi el;
    let bhi = SZ.add blo el;
    as_nats_at (SZ.v k) vs (SZ.v vi);
    vec_encode_at (SZ.v d) (SZ.v k) (as_ints vs) (SZ.v vi);
    with w0. assert (A.pts_to out w0);
    let blk = Sub.sub src lo hi;
    let obl = Sub.sub out blo bhi;
    encode_poly obl blk d;
    with b1. assert (A.pts_to obl b1);
    Sub.unsub_id src (SZ.v lo) (SZ.v hi) blk;
    Sub.unsub out (SZ.v blo) (SZ.v bhi) obl;
    with w1. assert (A.pts_to out w1);
    flat_step (SZ.v k) (32 * SZ.v d) (fun (x: S8.t) -> x) (SZ.v vi) w0 w1 b1
              (vec_encode (SZ.v d) (SZ.v k) (as_ints vs));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  Seq.lemma_eq_intro v (vec_encode (SZ.v d) (SZ.v k) (as_ints vs));
  assert (pure (v == vec_encode (SZ.v d) (SZ.v k) (as_ints vs)));
}

(** [dst <- ByteDecode_d] of each block. *)
fn vec_decode_impl (dst: A.array zqt) (b: A.array S8.t) (d k: SZ.t)
                   (#p: perm) (#vd: erased (Seq.seq zqt)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to b #p vb **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vd == SZ.v k * n /\
               Seq.length vb == SZ.v k * (32 * SZ.v d))
ensures exists* v. A.pts_to dst v ** A.pts_to b #p vb **
  pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
        Seq.length v == SZ.v k * n /\
        Seq.length vb == SZ.v k * (32 * SZ.v d) /\
        as_zqs v == vec_decode (SZ.v d) (SZ.v k) vb)
{
  A.pts_to_len dst;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (4 * (32 * 12) < pow2 32);
  assert_norm (4 * n < pow2 32);
  let el = SZ.mul 32sz d;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v d /\ SZ.v d <= 12 /\
          1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length v == SZ.v k * n /\
          Seq.length vb == SZ.v k * (32 * SZ.v d) /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index v t) ==
               Seq.index (vec_decode (SZ.v d) (SZ.v k) vb) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    Math.lemma_mult_le_right (32 * SZ.v d) (SZ.v vi + 1) (SZ.v k);
    Math.distributivity_add_left (SZ.v vi) 1 (32 * SZ.v d);
    Math.lemma_mult_le_right (32 * SZ.v d) (SZ.v k) 4;
    Math.lemma_mult_le_left 4 (32 * SZ.v d) (32 * 12);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi * (32 * SZ.v d) + 32 * SZ.v d);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let blo = SZ.mul vi el;
    let bhi = SZ.add blo el;
    vec_decode_at (SZ.v d) (SZ.v k) vb (SZ.v vi);
    with w0. assert (A.pts_to dst w0);
    let bbl = Sub.sub b blo bhi;
    let blk = Sub.sub dst lo hi;
    decode_poly blk bbl d;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub_id b (SZ.v blo) (SZ.v bhi) bbl;
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    flat_step (SZ.v k) n (fun (x: zqt) -> (S16.v x <: zq)) (SZ.v vi) w0 w1 b1
              (vec_decode (SZ.v d) (SZ.v k) vb);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_zqs_intro v (vec_decode (SZ.v d) (SZ.v k) vb);
  assert (pure (as_zqs v == vec_decode (SZ.v d) (SZ.v k) vb));
}

(** [dst <- Compress_d] of each entry. *)
fn vec_compress_impl (dst src: A.array zqt) (d k: SZ.t)
                     (#p: perm) (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs **
         pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vd == SZ.v k * n /\ Seq.length vs == SZ.v k * n)
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs **
  pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
        Seq.length v == SZ.v k * n /\ Seq.length vs == SZ.v k * n /\
        as_ints v == vec_compress (SZ.v d) #(SZ.v k) (as_zqs vs))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #p vs **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v d /\ SZ.v d <= 11 /\
          1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length v == SZ.v k * n /\ Seq.length vs == SZ.v k * n /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index v t) ==
               Seq.index (vec_compress (SZ.v d) #(SZ.v k) (as_zqs vs)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    as_zqs_at (SZ.v k) vs (SZ.v vi);
    vec_compress_at (SZ.v d) #(SZ.v k) (as_zqs vs) (SZ.v vi);
    with w0. assert (A.pts_to dst w0);
    let sbl = Sub.sub src lo hi;
    let blk = Sub.sub dst lo hi;
    compress_poly blk sbl d;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub_id src (SZ.v lo) (SZ.v hi) sbl;
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    flat_step (SZ.v k) n (fun (x: zqt) -> (S16.v x <: nat)) (SZ.v vi) w0 w1 b1
              (vec_compress (SZ.v d) #(SZ.v k) (as_zqs vs));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_ints_intro v (vec_compress (SZ.v d) #(SZ.v k) (as_zqs vs));
  assert (pure (as_ints v == vec_compress (SZ.v d) #(SZ.v k) (as_zqs vs)));
}

(** [dst <- Decompress_d] of each entry. *)
fn vec_decompress_impl (dst src: A.array zqt) (d k: SZ.t)
                       (#p: perm) (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs **
         pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vd == SZ.v k * n /\ Seq.length vs == SZ.v k * n /\
               (forall (t: nat). t < SZ.v k * n ==>
                  S16.v (Seq.index vs t) < pow2 (SZ.v d)))
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs **
  pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
        Seq.length v == SZ.v k * n /\ Seq.length vs == SZ.v k * n /\
        as_zqs v == vec_decompress (SZ.v d) (SZ.v k) (as_ints vs))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #p vs **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v d /\ SZ.v d <= 11 /\
          1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length v == SZ.v k * n /\ Seq.length vs == SZ.v k * n /\
          (forall (t: nat). t < SZ.v k * n ==>
             S16.v (Seq.index vs t) < pow2 (SZ.v d)) /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index v t) ==
               Seq.index (vec_decompress (SZ.v d) (SZ.v k) (as_ints vs)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    as_nats_at (SZ.v k) vs (SZ.v vi);
    vec_decompress_at (SZ.v d) (SZ.v k) (as_ints vs) (SZ.v vi);
    with w0. assert (A.pts_to dst w0);
    let sbl = Sub.sub src lo hi;
    let blk = Sub.sub dst lo hi;
    decompress_poly blk sbl d;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub_id src (SZ.v lo) (SZ.v hi) sbl;
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    flat_step (SZ.v k) n (fun (x: zqt) -> (S16.v x <: zq)) (SZ.v vi) w0 w1 b1
              (vec_decompress (SZ.v d) (SZ.v k) (as_ints vs));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_zqs_intro v (vec_decompress (SZ.v d) (SZ.v k) (as_ints vs));
  assert (pure (as_zqs v == vec_decompress (SZ.v d) (SZ.v k) (as_ints vs)));
}
