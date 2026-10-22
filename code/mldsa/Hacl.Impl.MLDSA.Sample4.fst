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

(** ExpandA, four entries at a time, over the four-way Keccak.

    [A-hat] is [k * l] independent [RejNTTPoly]s, each reading its own
    SHAKE128 stream.  As in ML-KEM's {!Hacl.Impl.MLKEM.Sample4}, four of
    them run in lock step so that every permutation they need -- the one
    that ends each absorb, and the one before every squeezed block after
    the first -- is one {!Hacl.Hash.SHA3.Core4.permute4} instead of four
    scalar ones.  Each stream is still read block by block with
    {!Hacl.Hash.SHA3.Sponge.squeeze_block_lanes} and fed to the scalar
    {!Hacl.Impl.MLDSA.Sample.block128_impl}; a stream that filled early
    keeps receiving blocks and ignores them, which is
    {!Spec.MLDSA.Sample.ntt_sampled_stable}.

    {!expand_a_impl} takes entries four at a time while at least four are
    left and the machine has AVX2, and one at a time otherwise (the last
    two of ML-DSA-65's thirty). *)
module Hacl.Impl.MLDSA.Sample4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3.Constants
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Sample
open Hacl.Impl.Table
open Hacl.Hash.SHA3
open Hacl.Hash.SHA3.Sponge
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.XOF
open Hacl.Impl.MLDSA.SampleLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module HSZ = Hacl.SizeT
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module SHA3 = Spec.SHA3
module Mem = Hacl.Mem
module V = Hacl.Vec256
module K4 = Hacl.Hash.SHA3.Core4
module KS4 = Hacl.Impl.MLKEM.Sample4
module S = Hacl.Impl.MLDSA.Sample

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 One stream} *)

(** Stream state after [j] blocks were sampled, with [q] permutations
    applied to the absorbed state. *)
[@@"opaque_to_smt"]
let stream_ok (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
              (c: nat) (q: nat) (j: nat) : prop =
  Seq.length vst == 25 /\
  vst == SHA3.squeeze_state q (xof_start 168 vs) /\
  agree v c (ntt_sampled vs (j * 56))

let stream_ok_elim (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                   (c: nat) (q: nat) (j: nat)
  : Lemma (requires stream_ok v vst vs c q j)
          (ensures Seq.length vst == 25 /\ Seq.length v == n /\ c <= n /\
                   vst == SHA3.squeeze_state q (xof_start 168 vs) /\
                   agree v c (ntt_sampled vs (j * 56)))
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c q j)

let stream_ok_intro (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                    (c: nat) (q: nat) (j: nat)
  : Lemma (requires Seq.length vst == 25 /\
                    vst == SHA3.squeeze_state q (xof_start 168 vs) /\
                    agree v c (ntt_sampled vs (j * 56)))
          (ensures stream_ok v vst vs c q j)
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c q j)

let stream_ok_init (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
  : Lemma (requires Seq.length v == n /\ Seq.length vst == 25 /\
                    SHA3.permute vst == xof_start 168 vs)
          (ensures stream_ok v (SHA3.permute vst) vs 0 0 0)
  = squeeze_state_zero (xof_start 168 vs);
    ntt_sampled_zero vs;
    agree_empty v;
    reveal_opaque (`%stream_ok) (stream_ok v (SHA3.permute vst) vs 0 0 0)

(** The permutation (or, for block zero, none) that brings a stream to
    the state its block [j] is read from. *)
let stream_ok_advance (v: Seq.seq zqt) (vst vst': Seq.seq S64.t) (vs: Seq.seq S8.t)
                      (c: nat) (j: nat)
  : Lemma (requires stream_ok v vst vs c (xof_prev j) j /\
                    (j > 0 ==> Seq.length vst == 25 /\ vst' == SHA3.permute vst) /\
                    (j == 0 ==> vst' == vst))
          (ensures stream_ok v vst' vs c j j)
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c (xof_prev j) j);
    if j > 0 then squeeze_state_succ (j - 1) (xof_start 168 vs);
    reveal_opaque (`%stream_ok) (stream_ok v vst' vs c j j)

(** Both ways a stream can end. *)
let stream_ok_done (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                   (c: nat) (q: nat) (j: nat)
  : Lemma (requires stream_ok v vst vs c q j /\ j <= 16 /\ (c >= n \/ j == 16))
          (ensures Seq.length v == n /\
                   (c >= n ==> as_poly v == rej_ntt_poly vs) /\
                   (c < n ==> rej_ntt_poly vs == poly_zero))
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c q j);
    assert (16 * 56 == max_triples);
    ntt_done vs (j * 56) v c

(** The bytes [squeeze_block_lanes] read from block [j]'s state are the
    sampler's triples [j * 56] onwards. *)
let stream_bytes (vk: Seq.seq S8.t) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t) (j: nat)
  : Lemma (requires Seq.length vk == 168 /\ Seq.length vst == 25 /\
                    vst == SHA3.squeeze_state j (xof_start 168 vs) /\
                    (forall (k: nat). 0 <= k /\ k < 0 + 168 ==>
                       Seq.index vk k == SHA3.state_byte vst (k - 0)))
          (ensures forall (u: nat). u < 168 ==>
                     Seq.index vk u == shake128_byte vs (3 * (j * 56) + u))
  = Math.swap_mul 3 (j * 56);
    Math.paren_mul_right j 56 3;
    assert (3 * (j * 56) == j * 168);
    block128_bytes vs j;
    introduce forall (u: nat). u < 168 ==> Seq.index vk u == shake128_byte vs (3 * (j * 56) + u)
    with introduce _ ==> _
    with assert (Seq.index vk u == SHA3.state_byte vst (u - 0))

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** Block [j] of one stream, whose state is already block [j]'s. *)
inline_for_extraction
fn stream_block (dst: A.array zqt) (blk: A.array S8.t) (st: A.array S64.t)
                (c: SZ.t) (j: SZ.t) (vs: erased (Seq.seq S8.t))
                (#v0: erased (Seq.seq zqt)) (#vk0: erased (Seq.seq S8.t))
                (#vst: erased (Seq.seq S64.t))
requires A.pts_to dst v0 ** A.pts_to blk vk0 ** A.pts_to st vst **
         pure (Seq.length vk0 == 168 /\ SZ.v j < 16 /\
               stream_ok v0 vst vs (SZ.v c) (SZ.v j) (SZ.v j))
returns c': SZ.t
ensures exists* (v: Seq.seq zqt) (vk: Seq.seq S8.t).
  A.pts_to dst v ** A.pts_to blk vk ** A.pts_to st vst **
  pure (Seq.length vk == 168 /\ stream_ok v vst vs (SZ.v c') (SZ.v j) (SZ.v j + 1))
{
  stream_ok_elim v0 vst vs (SZ.v c) (SZ.v j) (SZ.v j);
  squeeze_block_lanes blk 0sz 168sz st;
  with vk. assert (A.pts_to blk vk);
  stream_bytes vk vst vs (SZ.v j);
  let x = S.block128_impl dst blk c vs (hide (SZ.v j * 56));
  assert (pure (SZ.v j * 56 + 56 == (SZ.v j + 1) * 56));
  with v. assert (A.pts_to dst v);
  stream_ok_intro v vst vs (SZ.v x) (SZ.v j) (SZ.v j + 1);
  x
}

(** The result of one stream, once the loop is over. *)
inline_for_extraction
fn stream_finish (dst: A.array zqt) (c: SZ.t) (j: SZ.t) (vs: erased (Seq.seq S8.t))
                 (vst: erased (Seq.seq S64.t)) (q: erased nat)
                 (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 **
         pure (stream_ok v0 vst vs (SZ.v c) q (SZ.v j) /\ SZ.v j <= 16 /\
               (SZ.v c >= 256 \/ SZ.v j == 16))
ensures exists* (v: Seq.seq zqt). A.pts_to dst v **
  pure (Seq.length v == n /\ as_poly v == rej_ntt_poly vs)
{
  stream_ok_done v0 vst vs (SZ.v c) q (SZ.v j);
  if (SZ.lt c 256sz) {
    S.zero_poly dst;
  } else {
    assert (pure (as_poly v0 == rej_ntt_poly vs));
  }
}

(** [d_i <- RejNTTPoly s_i] for four seeds of the same length.  Uses
    AVX2: the caller checks {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn rej_ntt_poly4_impl (d0 d1 d2 d3: A.array zqt) (s0 s1 s2 s3: A.array S8.t) (slen: SZ.t)
                      (#vd0 #vd1 #vd2 #vd3: erased (Seq.seq zqt))
                      (#p0 #p1 #p2 #p3: perm)
                      (#vs0 #vs1 #vs2 #vs3: erased (Seq.seq S8.t))
requires A.pts_to d0 vd0 ** A.pts_to d1 vd1 ** A.pts_to d2 vd2 ** A.pts_to d3 vd3 **
         A.pts_to s0 #p0 vs0 ** A.pts_to s1 #p1 vs1 **
         A.pts_to s2 #p2 vs2 ** A.pts_to s3 #p3 vs3 **
         pure (Seq.length vd0 == n /\ Seq.length vd1 == n /\
               Seq.length vd2 == n /\ Seq.length vd3 == n /\
               SZ.v slen == Seq.length vs0 /\ SZ.v slen == Seq.length vs1 /\
               SZ.v slen == Seq.length vs2 /\ SZ.v slen == Seq.length vs3)
ensures exists* (w0 w1 w2 w3: Seq.seq zqt).
  A.pts_to d0 w0 ** A.pts_to d1 w1 ** A.pts_to d2 w2 ** A.pts_to d3 w3 **
  A.pts_to s0 #p0 vs0 ** A.pts_to s1 #p1 vs1 **
  A.pts_to s2 #p2 vs2 ** A.pts_to s3 #p3 vs3 **
  pure (Seq.length w0 == n /\ Seq.length w1 == n /\
        Seq.length w2 == n /\ Seq.length w3 == n /\
        as_poly w0 == rej_ntt_poly vs0 /\ as_poly w1 == rej_ntt_poly vs1 /\
        as_poly w2 == rej_ntt_poly vs2 /\ as_poly w3 == rej_ntt_poly vs3)
{
  A.pts_to_len d0;
  A.pts_to_len d1;
  A.pts_to_len d2;
  A.pts_to_len d3;
  HSZ.fits32 ();
  let z64 = S64.classify 0uL;
  let mut st0 = [| z64; 25sz |];
  Mem.track st0;
  A.pts_to_len st0;
  let mut st1 = [| z64; 25sz |];
  Mem.track st1;
  A.pts_to_len st1;
  let mut st2 = [| z64; 25sz |];
  Mem.track st2;
  A.pts_to_len st2;
  let mut st3 = [| z64; 25sz |];
  Mem.track st3;
  A.pts_to_len st3;
  let mut barr = [| z64; 25sz |];
  Mem.track barr;
  A.pts_to_len barr;
  let z8 = S8.classify 0uy;
  let mut blk = [| z8; 168sz |];
  Mem.track blk;
  A.pts_to_len blk;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  with prc vrc. assert (A.pts_to rc_tbl #prc vrc);
  assert (pure (reveal vrc == (rc <: Seq.seq S64.t)));

  KS4.shake128_absorb_pre st0 barr rc_tbl s0 slen;
  KS4.shake128_absorb_pre st1 barr rc_tbl s1 slen;
  KS4.shake128_absorb_pre st2 barr rc_tbl s2 slen;
  KS4.shake128_absorb_pre st3 barr rc_tbl s3 slen;
  with b0. assert (A.pts_to st0 b0);
  with b1. assert (A.pts_to st1 b1);
  with b2. assert (A.pts_to st2 b2);
  with b3. assert (A.pts_to st3 b3);
  K4.permute4 st0 st1 st2 st3 rc_tbl;
  stream_ok_init vd0 b0 vs0;
  stream_ok_init vd1 b1 vs1;
  stream_ok_init vd2 b2 vs2;
  stream_ok_init vd3 b3 vs3;
  assert (pure (xof_prev 0 == 0));

  let mut c0 = 0sz;
  let mut c1 = 0sz;
  let mut c2 = 0sz;
  let mut c3 = 0sz;
  let mut jj = 0sz;
  while (let vc0 = !c0; let vc1 = !c1; let vc2 = !c2; let vc3 = !c3; let vj = !jj;
         (SZ.lt vc0 256sz || SZ.lt vc1 256sz || SZ.lt vc2 256sz || SZ.lt vc3 256sz) &&
         SZ.lt vj 16sz)
  invariant exists* (vc0 vc1 vc2 vc3 vj: SZ.t)
                    (w0 w1 w2 w3: Seq.seq zqt)
                    (u0 u1 u2 u3: Seq.seq S64.t) (vb: Seq.seq S64.t) (vk: Seq.seq S8.t).
    pts_to c0 vc0 ** pts_to c1 vc1 ** pts_to c2 vc2 ** pts_to c3 vc3 ** pts_to jj vj **
    A.pts_to d0 w0 ** A.pts_to d1 w1 ** A.pts_to d2 w2 ** A.pts_to d3 w3 **
    A.pts_to st0 u0 ** A.pts_to st1 u1 ** A.pts_to st2 u2 ** A.pts_to st3 u3 **
    A.pts_to barr vb ** A.pts_to blk vk ** A.pts_to rc_tbl #prc vrc **
    pure (SZ.v vj <= 16 /\ Seq.length vb == 25 /\ Seq.length vk == 168 /\
          reveal vrc == (rc <: Seq.seq S64.t) /\
          stream_ok w0 u0 vs0 (SZ.v vc0) (xof_prev (SZ.v vj)) (SZ.v vj) /\
          stream_ok w1 u1 vs1 (SZ.v vc1) (xof_prev (SZ.v vj)) (SZ.v vj) /\
          stream_ok w2 u2 vs2 (SZ.v vc2) (xof_prev (SZ.v vj)) (SZ.v vj) /\
          stream_ok w3 u3 vs3 (SZ.v vc3) (xof_prev (SZ.v vj)) (SZ.v vj))
  decreases (16 - SZ.v (!jj))
  {
    let vj = !jj;
    with w0 u0 vc0. assert (A.pts_to d0 w0 ** A.pts_to st0 u0 ** pts_to c0 vc0);
    with w1 u1 vc1. assert (A.pts_to d1 w1 ** A.pts_to st1 u1 ** pts_to c1 vc1);
    with w2 u2 vc2. assert (A.pts_to d2 w2 ** A.pts_to st2 u2 ** pts_to c2 vc2);
    with w3 u3 vc3. assert (A.pts_to d3 w3 ** A.pts_to st3 u3 ** pts_to c3 vc3);
    stream_ok_elim w0 u0 vs0 (SZ.v vc0) (xof_prev (SZ.v vj)) (SZ.v vj);
    stream_ok_elim w1 u1 vs1 (SZ.v vc1) (xof_prev (SZ.v vj)) (SZ.v vj);
    stream_ok_elim w2 u2 vs2 (SZ.v vc2) (xof_prev (SZ.v vj)) (SZ.v vj);
    stream_ok_elim w3 u3 vs3 (SZ.v vc3) (xof_prev (SZ.v vj)) (SZ.v vj);
    KS4.permute4_if (SZ.gt vj 0sz) st0 st1 st2 st3 rc_tbl;
    with x0. assert (A.pts_to st0 x0);
    with x1. assert (A.pts_to st1 x1);
    with x2. assert (A.pts_to st2 x2);
    with x3. assert (A.pts_to st3 x3);
    stream_ok_advance w0 u0 x0 vs0 (SZ.v vc0) (SZ.v vj);
    stream_ok_advance w1 u1 x1 vs1 (SZ.v vc1) (SZ.v vj);
    stream_ok_advance w2 u2 x2 vs2 (SZ.v vc2) (SZ.v vj);
    stream_ok_advance w3 u3 x3 vs3 (SZ.v vc3) (SZ.v vj);
    let vc0 = !c0;
    let y0 = stream_block d0 blk st0 vc0 vj vs0;
    c0 := y0;
    let vc1 = !c1;
    let y1 = stream_block d1 blk st1 vc1 vj vs1;
    c1 := y1;
    let vc2 = !c2;
    let y2 = stream_block d2 blk st2 vc2 vj vs2;
    c2 := y2;
    let vc3 = !c3;
    let y3 = stream_block d3 blk st3 vc3 vj vs3;
    c3 := y3;
    SZ.fits_u32_implies_fits (SZ.v vj + 1);
    jj := SZ.add vj 1sz;
    assert (pure (xof_prev (SZ.v vj + 1) == SZ.v vj));
  };

  drop_table rc_tbl;
  Mem.wipe blk 168sz;
  Mem.wipe barr 25sz;
  let vj = !jj;
  let vc0 = !c0;
  let vc1 = !c1;
  let vc2 = !c2;
  let vc3 = !c3;
  with u0. assert (A.pts_to st0 u0);
  with u1. assert (A.pts_to st1 u1);
  with u2. assert (A.pts_to st2 u2);
  with u3. assert (A.pts_to st3 u3);
  stream_finish d0 vc0 vj vs0 u0 (xof_prev (SZ.v vj));
  stream_finish d1 vc1 vj vs1 u1 (xof_prev (SZ.v vj));
  stream_finish d2 vc2 vj vs2 u2 (xof_prev (SZ.v vj));
  stream_finish d3 vc3 vj vs3 u3 (xof_prev (SZ.v vj));
  Mem.wipe st3 25sz;
  Mem.wipe st2 25sz;
  Mem.wipe st1 25sz;
  Mem.wipe st0 25sz;
}

#pop-options

(** {2 ExpandA} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The seed of entry [t]: [rho], then the column [t % l] and the row
    [t / l]. *)
let seed_ok (p: params) (vr: Seq.seq S8.t) (t: nat) (vsd: Seq.seq S8.t) : prop
  = Seq.length vsd == 34 /\ Seq.length vr == 32 /\
    (forall (i: nat). i < 32 ==> Seq.index vsd i == Seq.index vr i) /\
    S8.v (Seq.index vsd 32) == t % p.l /\
    S8.v (Seq.index vsd 33) == t / p.l

(** Bytes [32] and [33] of [sd] for entry [t], the first thirty-two
    already being [rho]'s. *)
inline_for_extraction
fn set_seed (p: erased params) (sd: A.array S8.t) (l: SZ.t) (t: SZ.t)
            (vr: erased (Seq.seq S8.t)) (#v0: erased (Seq.seq S8.t))
requires A.pts_to sd v0 **
         pure (Seq.length v0 == 34 /\ Seq.length vr == 32 /\
               SZ.v l == p.l /\ SZ.v t < p.k * p.l /\
               (forall (i: nat). i < 32 ==> Seq.index v0 i == Seq.index vr i))
ensures exists* (v: Seq.seq S8.t). A.pts_to sd v **
  pure (seed_ok p vr (SZ.v t) v)
{
  expand_a_bounds p.k p.l (SZ.v t);
  HSZ.fits32 ();
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  let ci = SZ.div t l;
  let cj = SZ.rem t l;
  let bi = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 ci);
  let bj = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 cj);
  Math.small_mod (SZ.v ci) 256;
  Math.small_mod (SZ.v cj) 256;
  Math.small_mod (SZ.v ci) 4294967296;
  Math.small_mod (SZ.v cj) 4294967296;
  assert (pure (U8.v bi == SZ.v t / p.l /\ U8.v bj == SZ.v t % p.l));
  A.((sd.(32sz) <- S8.classify bj));
  A.((sd.(33sz) <- S8.classify bi));
}

(** [dst <- src], one polynomial. *)
inline_for_extraction
fn copy_poly (dst: A.array zqt) (src: A.array zqt)
             (#vd: erased (Seq.seq zqt)) (#vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src vs **
         pure (Seq.length vd == n /\ Seq.length vs == n)
ensures A.pts_to dst vs ** A.pts_to src vs
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src vs **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vs == n /\
          (forall (t: nat). t < SZ.v vi ==> Seq.index v t == Seq.index vs t))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.(dst.(vi) <- x);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  assert (pure (Seq.equal v vs));
  rewrite (A.pts_to dst v) as (A.pts_to dst vs);
}

(** Writes the sampled entry [t] back into [A-hat]. *)
inline_for_extraction
fn put_entry (p: erased params) (dst: A.array zqt) (src: A.array zqt) (t: SZ.t)
             (vr: erased (Seq.seq S8.t)) (vsd: erased (Seq.seq S8.t))
             (#vd: erased (Seq.seq zqt)) (#vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src vs **
         pure (Seq.length vr == 32 /\ SZ.v t < p.k * p.l /\
               Seq.length vd == p.k * p.l * n /\ Seq.length vs == n /\
               prefix_eq vd (expand_a p vr) (SZ.v t * n) /\
               seed_ok p vr (SZ.v t) vsd /\
               as_poly vs == rej_ntt_poly vsd)
ensures exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to src vs **
  pure (Seq.length vr == 32 /\ Seq.length v == p.k * p.l * n /\
        prefix_eq v (expand_a p vr) ((SZ.v t + 1) * n))
{
  A.pts_to_len dst;
  expand_a_bounds p.k p.l (SZ.v t);
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (SZ.v t * n + n);
  let lo = SZ.mul t 256sz;
  let hi = SZ.add lo 256sz;
  let blk = Sub.sub dst lo hi;
  A.pts_to_len blk;
  copy_poly blk src;
  Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
  with w1. assert (A.pts_to dst w1);
  assert (pure (SZ.v lo == SZ.v t * n /\ SZ.v hi == SZ.v t * n + n));
  assert (pure (forall (i: nat). i < p.k * p.l * n ==>
         Seq.index w1 i == (if SZ.v t * n <= i && i < SZ.v t * n + n
                            then Seq.index vs (i - SZ.v t * n) else Seq.index vd i)));
  expand_a_step p vr (SZ.v t) vd w1 vs vsd;
  assert (pure (prefix_eq w1 (expand_a p vr) ((SZ.v t + 1) * n)));
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Entries [t .. t + 4) of [A-hat], sampled together.  Uses AVX2: the
    caller checks {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn expand_a4 (p: erased params) (dst: A.array zqt) (rho: A.array S8.t) (l: SZ.t) (t: SZ.t)
             (#vd: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 32 /\ SZ.v l == p.l /\ SZ.v t + 4 <= p.k * p.l /\
               Seq.length vd == p.k * p.l * n /\
               prefix_eq vd (expand_a p vr) (SZ.v t * n))
ensures exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 32 /\ Seq.length v == p.k * p.l * n /\
        prefix_eq v (expand_a p vr) ((SZ.v t + 4) * n))
{
  A.pts_to_len rho;
  HSZ.fits32 ();
  expand_a_bounds p.k p.l (SZ.v t + 3);
  SZ.fits_u32_implies_fits (SZ.v t + 3);
  let t1 = SZ.add t 1sz;
  let t2 = SZ.add t 2sz;
  let t3 = SZ.add t 3sz;
  let z8 = S8.classify 0uy;
  let mut sd0 = [| z8; 34sz |];
  Mem.track sd0;
  A.pts_to_len sd0;
  let mut sd1 = [| z8; 34sz |];
  Mem.track sd1;
  A.pts_to_len sd1;
  let mut sd2 = [| z8; 34sz |];
  Mem.track sd2;
  A.pts_to_len sd2;
  let mut sd3 = [| z8; 34sz |];
  Mem.track sd3;
  A.pts_to_len sd3;
  Copy.copy_prefix sd0 rho 32sz;
  Copy.copy_prefix sd1 rho 32sz;
  Copy.copy_prefix sd2 rho 32sz;
  Copy.copy_prefix sd3 rho 32sz;
  set_seed p sd0 l t vr;
  set_seed p sd1 l t1 vr;
  set_seed p sd2 l t2 vr;
  set_seed p sd3 l t3 vr;
  with e0. assert (A.pts_to sd0 e0);
  with e1. assert (A.pts_to sd1 e1);
  with e2. assert (A.pts_to sd2 e2);
  with e3. assert (A.pts_to sd3 e3);
  let z32 : zqt = S32.zero;
  let mut p0 = [| z32; 256sz |];
  Mem.track p0;
  A.pts_to_len p0;
  let mut p1 = [| z32; 256sz |];
  Mem.track p1;
  A.pts_to_len p1;
  let mut p2 = [| z32; 256sz |];
  Mem.track p2;
  A.pts_to_len p2;
  let mut p3 = [| z32; 256sz |];
  Mem.track p3;
  A.pts_to_len p3;
  rej_ntt_poly4_impl p0 p1 p2 p3 sd0 sd1 sd2 sd3 34sz;
  put_entry p dst p0 t vr e0;
  put_entry p dst p1 t1 vr e1;
  put_entry p dst p2 t2 vr e2;
  put_entry p dst p3 t3 vr e3;
  Mem.wipe p3 256sz;
  Mem.wipe p2 256sz;
  Mem.wipe p1 256sz;
  Mem.wipe p0 256sz;
  Mem.wipe sd3 34sz;
  Mem.wipe sd2 34sz;
  Mem.wipe sd1 34sz;
  Mem.wipe sd0 34sz;
}

(** Algorithm 32: [A-hat], row major, entry [t = r * l + s] seeded with
    [rho], [s], [r]; four entries at a time where it can. *)
fn expand_a_impl (p: erased params) (dst: A.array zqt) (rho: A.array S8.t)
                 ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                 (#vd: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 32 /\ SZ.v k == p.k /\ SZ.v l == p.l /\
               Seq.length vd == p.k * p.l * n)
ensures exists* v. A.pts_to dst v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 32 /\ Seq.length v == p.k * p.l * n /\
        as_zqs v == expand_a p vr)
{
  A.pts_to_len dst;
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (8 * 7 * n < pow2 32);
  Math.lemma_mult_le_right (SZ.v l) (SZ.v k) 8;
  Math.lemma_mult_le_left 8 (SZ.v l) 7;
  SZ.fits_u32_implies_fits 60;
  let z8 = S8.classify 0uy;
  let mut sd = [| z8; 34sz |];
  Mem.track sd;
  A.pts_to_len sd;
  Copy.copy_prefix sd rho 32sz;
  prefix_zero vd (expand_a p vr);
  let kl = SZ.mul k l;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc kl)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt) (vsd: Seq.seq S8.t).
    pts_to c vc ** A.pts_to dst v ** A.pts_to rho #pr vr ** A.pts_to sd vsd **
    pure (SZ.v vc <= SZ.v kl /\ SZ.v kl == p.k * p.l /\
          SZ.v k == p.k /\ SZ.v l == p.l /\
          Seq.length v == p.k * p.l * n /\ Seq.length vr == 32 /\
          Seq.length vsd == 34 /\
          (forall (t: nat). t < 32 ==> Seq.index vsd t == Seq.index vr t) /\
          prefix_eq v (expand_a p vr) (SZ.v vc * n))
  decreases (SZ.v kl - SZ.v (!c))
  {
    let vc = !c;
    if (SZ.lte (SZ.add vc 4sz) kl && V.supported ()) {
      expand_a4 p dst rho l vc;
      c := SZ.add vc 4sz;
    } else {
      expand_a_bounds p.k p.l (SZ.v vc);
      SZ.fits_u32_implies_fits (SZ.v vc * n + n);
      let lo = SZ.mul vc 256sz;
      let hi = SZ.add lo 256sz;
      set_seed p sd l vc vr;
      with vsd. assert (A.pts_to sd vsd);
      with w0. assert (A.pts_to dst w0);
      let blk = Sub.sub dst lo hi;
      S.rej_ntt_poly_impl blk sd 34sz;
      with b1. assert (A.pts_to blk b1);
      Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
      with w1. assert (A.pts_to dst w1);
      expand_a_step p vr (SZ.v vc) w0 w1 b1 vsd;
      c := SZ.add vc 1sz;
    }
  };
  with v. assert (A.pts_to dst v);
  prefix_done (p.k * p.l) v (expand_a p vr);
  assert (pure (as_zqs v == expand_a p vr));
  Mem.wipe sd 34sz;
}

#pop-options
