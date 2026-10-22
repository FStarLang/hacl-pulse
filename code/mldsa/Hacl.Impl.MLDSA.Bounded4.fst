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

(** ExpandS, four polynomials at a time over the four-way Keccak.

    Each polynomial of [s1] and [s2] is [RejBoundedPoly] of
    [SHAKE256(rho' || u16(r))], usually two or three blocks.
    {!rej_bounded4_impl} runs four of these streams in lock step: the
    absorbs are {!Hacl.Impl.MLDSA.Mask4.seed_absorb_pre} and one
    {!Hacl.Hash.SHA3.Core4.permute4}, each block is read with
    {!Hacl.Hash.SHA3.Sponge.squeeze_block_lanes} and fed to the scalar
    {!Hacl.Impl.MLDSA.Sample.block256_bounded_impl}, and a stream that
    filled early keeps receiving blocks and ignores them.

    {!expand_s_part_impl} takes four polynomials at a time while at least
    two are left and the machine has AVX2, sliding the last window back
    to end at the vector's length, as {!Hacl.Impl.MLDSA.Mask4} does. *)
module Hacl.Impl.MLDSA.Bounded4

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
module S4 = Hacl.Impl.MLDSA.Sample4
module M4 = Hacl.Impl.MLDSA.Mask4
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 One stream} *)

(** Stream state after [j] blocks were sampled, with [q] permutations
    applied to the absorbed state. *)
[@@"opaque_to_smt"]
let bstream_ok (eta: pos) (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
               (c: nat) (q: nat) (j: nat) : prop =
  Seq.length vst == 25 /\
  vst == SHA3.squeeze_state q (xof_start 136 vs) /\
  agree v c (bounded_sampled eta vs (j * 136))

let bstream_ok_elim (eta: pos) (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                    (c: nat) (q: nat) (j: nat)
  : Lemma (requires bstream_ok eta v vst vs c q j)
          (ensures Seq.length vst == 25 /\ Seq.length v == n /\ c <= n /\
                   vst == SHA3.squeeze_state q (xof_start 136 vs) /\
                   agree v c (bounded_sampled eta vs (j * 136)))
  = reveal_opaque (`%bstream_ok) (bstream_ok eta v vst vs c q j)

let bstream_ok_intro (eta: pos) (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                     (c: nat) (q: nat) (j: nat)
  : Lemma (requires Seq.length vst == 25 /\
                    vst == SHA3.squeeze_state q (xof_start 136 vs) /\
                    agree v c (bounded_sampled eta vs (j * 136)))
          (ensures bstream_ok eta v vst vs c q j)
  = reveal_opaque (`%bstream_ok) (bstream_ok eta v vst vs c q j)

let bstream_ok_init (eta: pos) (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
  : Lemma (requires Seq.length v == n /\ Seq.length vst == 25 /\
                    SHA3.permute vst == SHA3.absorb 136 SHA3.shake_suffix vs)
          (ensures bstream_ok eta v (SHA3.permute vst) vs 0 0 0)
  = squeeze_state_zero (xof_start 136 vs);
    bounded_sampled_zero eta vs;
    agree_empty v;
    reveal_opaque (`%bstream_ok) (bstream_ok eta v (SHA3.permute vst) vs 0 0 0)

let bstream_ok_advance (eta: pos) (v: Seq.seq zqt) (vst vst': Seq.seq S64.t) (vs: Seq.seq S8.t)
                       (c: nat) (j: nat)
  : Lemma (requires bstream_ok eta v vst vs c (xof_prev j) j /\
                    (j > 0 ==> Seq.length vst == 25 /\ vst' == SHA3.permute vst) /\
                    (j == 0 ==> vst' == vst))
          (ensures bstream_ok eta v vst' vs c j j)
  = reveal_opaque (`%bstream_ok) (bstream_ok eta v vst vs c (xof_prev j) j);
    if j > 0 then squeeze_state_succ (j - 1) (xof_start 136 vs);
    reveal_opaque (`%bstream_ok) (bstream_ok eta v vst' vs c j j)

let bstream_ok_done (eta: pos) (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                    (c: nat) (q: nat) (j: nat)
  : Lemma (requires bstream_ok eta v vst vs c q j /\ j <= 8 /\ (c >= n \/ j == 8))
          (ensures Seq.length v == n /\
                   (c >= n ==> as_poly v == rej_bounded_poly eta vs) /\
                   (c < n ==> rej_bounded_poly eta vs == poly_zero))
  = reveal_opaque (`%bstream_ok) (bstream_ok eta v vst vs c q j);
    assert (8 * 136 == max_bounded);
    bounded_done eta vs (j * 136) v c

let bstream_bytes (vk: Seq.seq S8.t) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t) (j: nat)
  : Lemma (requires Seq.length vk == 136 /\ Seq.length vst == 25 /\
                    vst == SHA3.squeeze_state j (xof_start 136 vs) /\
                    (forall (k: nat). 0 <= k /\ k < 0 + 136 ==>
                       Seq.index vk k == SHA3.state_byte vst (k - 0)))
          (ensures forall (u: nat). u < 136 ==>
                     Seq.index vk u == shake256_byte vs (j * 136 + u))
  = block256_bytes vs j;
    introduce forall (u: nat). u < 136 ==> Seq.index vk u == shake256_byte vs (j * 136 + u)
    with introduce _ ==> _
    with assert (Seq.index vk u == SHA3.state_byte vst (u - 0))

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** Block [j] of one stream, whose state is already block [j]'s. *)
inline_for_extraction
fn bstream_block (dst: A.array zqt) (blk: A.array S8.t) (st: A.array S64.t)
                 (c: SZ.t) (j: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                 (vs: erased (Seq.seq S8.t))
                 (#v0: erased (Seq.seq zqt)) (#vk0: erased (Seq.seq S8.t))
                 (#vst: erased (Seq.seq S64.t))
requires A.pts_to dst v0 ** A.pts_to blk vk0 ** A.pts_to st vst **
         pure (Seq.length vk0 == 136 /\ SZ.v j < 8 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
               bstream_ok (SZ.v eta) v0 vst vs (SZ.v c) (SZ.v j) (SZ.v j))
returns c': SZ.t
ensures exists* (v: Seq.seq zqt) (vk: Seq.seq S8.t).
  A.pts_to dst v ** A.pts_to blk vk ** A.pts_to st vst **
  pure (Seq.length vk == 136 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
        bstream_ok (SZ.v eta) v vst vs (SZ.v c') (SZ.v j) (SZ.v j + 1))
{
  bstream_ok_elim (SZ.v eta) v0 vst vs (SZ.v c) (SZ.v j) (SZ.v j);
  squeeze_block_lanes blk 0sz 136sz st;
  with vk. assert (A.pts_to blk vk);
  bstream_bytes vk vst vs (SZ.v j);
  let x = S.block256_bounded_impl dst blk c eta vs (hide (SZ.v j * 136));
  assert (pure (SZ.v j * 136 + 136 == (SZ.v j + 1) * 136));
  with v. assert (A.pts_to dst v);
  bstream_ok_intro (SZ.v eta) v vst vs (SZ.v x) (SZ.v j) (SZ.v j + 1);
  x
}

inline_for_extraction
fn bstream_finish (dst: A.array zqt) (c: SZ.t) (j: SZ.t) (eta: erased pos)
                  (vs: erased (Seq.seq S8.t))
                  (vst: erased (Seq.seq S64.t)) (q: erased nat)
                  (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 **
         pure (bstream_ok eta v0 vst vs (SZ.v c) q (SZ.v j) /\ SZ.v j <= 8 /\
               (SZ.v c >= 256 \/ SZ.v j == 8))
ensures exists* (v: Seq.seq zqt). A.pts_to dst v **
  pure (Seq.length v == n /\ as_poly v == rej_bounded_poly eta vs)
{
  bstream_ok_done eta v0 vst vs (SZ.v c) q (SZ.v j);
  if (SZ.lt c 256sz) {
    S.zero_poly dst;
  } else {
    assert (pure (as_poly v0 == rej_bounded_poly eta vs));
  }
}

(** [d_i <- RejBoundedPoly_eta(rho' || u16(x_i))] for [i < 4].  Uses
    AVX2: the caller checks {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn rej_bounded4_impl (d0 d1 d2 d3: A.array zqt) (rho: A.array S8.t)
                     (x0 x1 x2 x3: SZ.t)
                     ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                     (#vd0 #vd1 #vd2 #vd3: erased (Seq.seq zqt))
                     (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to d0 vd0 ** A.pts_to d1 vd1 ** A.pts_to d2 vd2 ** A.pts_to d3 vd3 **
         A.pts_to rho #pr vr **
         pure (Seq.length vd0 == n /\ Seq.length vd1 == n /\
               Seq.length vd2 == n /\ Seq.length vd3 == n /\
               Seq.length vr == 64 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
               SZ.v x0 < pow2 16 /\ SZ.v x1 < pow2 16 /\
               SZ.v x2 < pow2 16 /\ SZ.v x3 < pow2 16)
ensures exists* (w0 w1 w2 w3: Seq.seq zqt).
  A.pts_to d0 w0 ** A.pts_to d1 w1 ** A.pts_to d2 w2 ** A.pts_to d3 w3 **
  A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
        SZ.v x0 < pow2 16 /\ SZ.v x1 < pow2 16 /\
        SZ.v x2 < pow2 16 /\ SZ.v x3 < pow2 16 /\
        Seq.length w0 == n /\ Seq.length w1 == n /\
        Seq.length w2 == n /\ Seq.length w3 == n /\
        as_poly w0 == rej_bounded_poly (SZ.v eta) (M4.lane_msg vr x0) /\
        as_poly w1 == rej_bounded_poly (SZ.v eta) (M4.lane_msg vr x1) /\
        as_poly w2 == rej_bounded_poly (SZ.v eta) (M4.lane_msg vr x2) /\
        as_poly w3 == rej_bounded_poly (SZ.v eta) (M4.lane_msg vr x3))
{
  A.pts_to_len d0;
  A.pts_to_len d1;
  A.pts_to_len d2;
  A.pts_to_len d3;
  HSZ.fits32 ();
  let vs0 : erased (Seq.seq S8.t) = hide (M4.lane_msg vr x0);
  let vs1 : erased (Seq.seq S8.t) = hide (M4.lane_msg vr x1);
  let vs2 : erased (Seq.seq S8.t) = hide (M4.lane_msg vr x2);
  let vs3 : erased (Seq.seq S8.t) = hide (M4.lane_msg vr x3);
  let ve : erased pos = hide (SZ.v eta);
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
  let mut blk = [| z8; 136sz |];
  Mem.track blk;
  A.pts_to_len blk;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  with prc vrc. assert (A.pts_to rc_tbl #prc vrc);
  assert (pure (reveal vrc == (rc <: Seq.seq S64.t)));

  M4.seed_absorb_pre st0 barr rc_tbl rho x0 66sz;
  M4.seed_absorb_pre st1 barr rc_tbl rho x1 66sz;
  M4.seed_absorb_pre st2 barr rc_tbl rho x2 66sz;
  M4.seed_absorb_pre st3 barr rc_tbl rho x3 66sz;
  with b0. assert (A.pts_to st0 b0);
  with b1. assert (A.pts_to st1 b1);
  with b2. assert (A.pts_to st2 b2);
  with b3. assert (A.pts_to st3 b3);
  K4.permute4 st0 st1 st2 st3 rc_tbl;
  bstream_ok_init ve vd0 b0 vs0;
  bstream_ok_init ve vd1 b1 vs1;
  bstream_ok_init ve vd2 b2 vs2;
  bstream_ok_init ve vd3 b3 vs3;
  assert (pure (xof_prev 0 == 0));

  let mut c0 = 0sz;
  let mut c1 = 0sz;
  let mut c2 = 0sz;
  let mut c3 = 0sz;
  let mut jj = 0sz;
  while (let vc0 = !c0; let vc1 = !c1; let vc2 = !c2; let vc3 = !c3; let vj = !jj;
         (SZ.lt vc0 256sz || SZ.lt vc1 256sz || SZ.lt vc2 256sz || SZ.lt vc3 256sz) &&
         SZ.lt vj 8sz)
  invariant exists* (vc0 vc1 vc2 vc3 vj: SZ.t)
                    (w0 w1 w2 w3: Seq.seq zqt)
                    (u0 u1 u2 u3: Seq.seq S64.t) (vb: Seq.seq S64.t) (vk: Seq.seq S8.t).
    pts_to c0 vc0 ** pts_to c1 vc1 ** pts_to c2 vc2 ** pts_to c3 vc3 ** pts_to jj vj **
    A.pts_to d0 w0 ** A.pts_to d1 w1 ** A.pts_to d2 w2 ** A.pts_to d3 w3 **
    A.pts_to st0 u0 ** A.pts_to st1 u1 ** A.pts_to st2 u2 ** A.pts_to st3 u3 **
    A.pts_to barr vb ** A.pts_to blk vk ** A.pts_to rc_tbl #prc vrc **
    pure (SZ.v vj <= 8 /\ Seq.length vb == 25 /\ Seq.length vk == 136 /\
          reveal vrc == (rc <: Seq.seq S64.t) /\
          reveal ve == SZ.v eta /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
          bstream_ok ve w0 u0 vs0 (SZ.v vc0) (xof_prev (SZ.v vj)) (SZ.v vj) /\
          bstream_ok ve w1 u1 vs1 (SZ.v vc1) (xof_prev (SZ.v vj)) (SZ.v vj) /\
          bstream_ok ve w2 u2 vs2 (SZ.v vc2) (xof_prev (SZ.v vj)) (SZ.v vj) /\
          bstream_ok ve w3 u3 vs3 (SZ.v vc3) (xof_prev (SZ.v vj)) (SZ.v vj))
  decreases (8 - SZ.v (!jj))
  {
    let vj = !jj;
    with w0 u0 vc0. assert (A.pts_to d0 w0 ** A.pts_to st0 u0 ** pts_to c0 vc0);
    with w1 u1 vc1. assert (A.pts_to d1 w1 ** A.pts_to st1 u1 ** pts_to c1 vc1);
    with w2 u2 vc2. assert (A.pts_to d2 w2 ** A.pts_to st2 u2 ** pts_to c2 vc2);
    with w3 u3 vc3. assert (A.pts_to d3 w3 ** A.pts_to st3 u3 ** pts_to c3 vc3);
    bstream_ok_elim ve w0 u0 vs0 (SZ.v vc0) (xof_prev (SZ.v vj)) (SZ.v vj);
    bstream_ok_elim ve w1 u1 vs1 (SZ.v vc1) (xof_prev (SZ.v vj)) (SZ.v vj);
    bstream_ok_elim ve w2 u2 vs2 (SZ.v vc2) (xof_prev (SZ.v vj)) (SZ.v vj);
    bstream_ok_elim ve w3 u3 vs3 (SZ.v vc3) (xof_prev (SZ.v vj)) (SZ.v vj);
    KS4.permute4_if (SZ.gt vj 0sz) st0 st1 st2 st3 rc_tbl;
    with x0. assert (A.pts_to st0 x0);
    with x1. assert (A.pts_to st1 x1);
    with x2. assert (A.pts_to st2 x2);
    with x3. assert (A.pts_to st3 x3);
    bstream_ok_advance ve w0 u0 x0 vs0 (SZ.v vc0) (SZ.v vj);
    bstream_ok_advance ve w1 u1 x1 vs1 (SZ.v vc1) (SZ.v vj);
    bstream_ok_advance ve w2 u2 x2 vs2 (SZ.v vc2) (SZ.v vj);
    bstream_ok_advance ve w3 u3 x3 vs3 (SZ.v vc3) (SZ.v vj);
    let vc0 = !c0;
    let y0 = bstream_block d0 blk st0 vc0 vj eta vs0;
    c0 := y0;
    let vc1 = !c1;
    let y1 = bstream_block d1 blk st1 vc1 vj eta vs1;
    c1 := y1;
    let vc2 = !c2;
    let y2 = bstream_block d2 blk st2 vc2 vj eta vs2;
    c2 := y2;
    let vc3 = !c3;
    let y3 = bstream_block d3 blk st3 vc3 vj eta vs3;
    c3 := y3;
    SZ.fits_u32_implies_fits (SZ.v vj + 1);
    jj := SZ.add vj 1sz;
    assert (pure (xof_prev (SZ.v vj + 1) == SZ.v vj));
  };

  drop_table rc_tbl;
  Mem.wipe blk 136sz;
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
  bstream_finish d0 vc0 vj ve vs0 u0 (xof_prev (SZ.v vj));
  bstream_finish d1 vc1 vj ve vs1 u1 (xof_prev (SZ.v vj));
  bstream_finish d2 vc2 vj ve vs2 u2 (xof_prev (SZ.v vj));
  bstream_finish d3 vc3 vj ve vs3 u3 (xof_prev (SZ.v vj));
  Mem.wipe st3 25sz;
  Mem.wipe st2 25sz;
  Mem.wipe st1 25sz;
  Mem.wipe st0 25sz;
}

#pop-options

(** {2 ExpandS} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let s_step (p: params) (rho': Seq.lseq S8.t 64) (second: bool)
           (t: nat { t < s_count p second })
           (w0 w1: Seq.seq zqt) (b: Seq.seq zqt)
  : Lemma (requires
      Seq.length w0 == s_count p second * n /\ Seq.length w1 == s_count p second * n /\
      Seq.length b == n /\
      (forall (i: nat). i < s_count p second * n ==>
         Seq.index w1 i == (if t * n <= i && i < t * n + n
                            then Seq.index b (i - t * n) else Seq.index w0 i)) /\
      prefix_eq w0 (s_target p rho' second) (t * n) /\
      t + s_off p second < 256 /\
      (assert_norm (pow2 16 == 65536);
       as_poly b == rej_bounded_poly p.eta (seed_16 rho' (t + s_off p second))))
    (ensures prefix_eq w1 (s_target p rho' second) ((t + 1) * n))
  = reveal_opaque (`%prefix_eq) (prefix_eq w0 (s_target p rho' second) (t * n));
    reveal_opaque (`%prefix_eq) (prefix_eq w1 (s_target p rho' second) ((t + 1) * n));
    if second then expand_s2_at p rho' t else expand_s1_at p rho' t;
    Math.lemma_mult_le_right n t (s_count p second);
    introduce forall (i: nat). i < t * n ==>
                S32.v (Seq.index w0 i) == Seq.index (s_target p rho' second) i
    with introduce _ ==> _ with assert (i < s_count p second * n);
    flat_step (s_count p second) t w0 w1 b (s_target p rho' second)

let prefix_mono (w: Seq.seq zqt) (r: Seq.seq zq) (m m': nat)
  : Lemma (requires prefix_eq w r m /\ m' <= m) (ensures prefix_eq w r m')
  = reveal_opaque (`%prefix_eq) (prefix_eq w r m);
    reveal_opaque (`%prefix_eq) (prefix_eq w r m')

let s_bounds (p: params) (second: bool)
  : Lemma (s_count p second + s_off p second <= 15 /\ s_count p second <= 8 /\
           (p.eta == 2 \/ p.eta == 4))
  = ()

(** Writes polynomial [t], sampled into [src], back into [dst]. *)
inline_for_extraction
fn put_s (p: erased params) (second: erased bool) (dst: A.array zqt) (src: A.array zqt)
         (t: SZ.t) (vr: erased (Seq.seq S8.t))
         (#vd: erased (Seq.seq zqt)) (#vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src vs **
         pure (Seq.length vr == 64 /\ SZ.v t < s_count p second /\
               Seq.length vd == s_count p second * n /\ Seq.length vs == n /\
               prefix_eq vd (s_target p vr second) (SZ.v t * n) /\
               SZ.v t + s_off p second < 256 /\
               (assert_norm (pow2 16 == 65536);
                as_poly vs == rej_bounded_poly p.eta (seed_16 vr (SZ.v t + s_off p second))))
ensures exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to src vs **
  pure (Seq.length vr == 64 /\ Seq.length v == s_count p second * n /\
        prefix_eq v (s_target p vr second) ((SZ.v t + 1) * n))
{
  A.pts_to_len dst;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  Math.lemma_mult_le_right n (SZ.v t + 1) (s_count p second);
  Math.distributivity_add_left (SZ.v t) 1 n;
  s_bounds p second;
  Math.lemma_mult_le_right n (s_count p second) 8;
  SZ.fits_u32_implies_fits (SZ.v t * n + n);
  let lo = SZ.mul t 256sz;
  let hi = SZ.add lo 256sz;
  let blk = Sub.sub dst lo hi;
  A.pts_to_len blk;
  S4.copy_poly blk src;
  Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
  with w1. assert (A.pts_to dst w1);
  assert (pure (SZ.v lo == SZ.v t * n /\ SZ.v hi == SZ.v t * n + n));
  assert (pure (forall (i: nat). i < s_count p second * n ==>
         Seq.index w1 i == (if SZ.v t * n <= i && i < SZ.v t * n + n
                            then Seq.index vs (i - SZ.v t * n) else Seq.index vd i)));
  s_step p vr second (SZ.v t) vd w1 vs;
  assert (pure (prefix_eq w1 (s_target p vr second) ((SZ.v t + 1) * n)));
}

(** Polynomial [t] of the vector, one stream. *)
fn s_one (p: erased params) (second: erased bool) (dst: A.array zqt) (rho: A.array S8.t)
         (t: SZ.t) (off: SZ.t)
         ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
         (#vd: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 64 /\ SZ.v t < s_count p second /\
               SZ.v off == s_off p second /\ SZ.v eta == p.eta /\
               Seq.length vd == s_count p second * n /\
               prefix_eq vd (s_target p vr second) (SZ.v t * n))
ensures exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length v == s_count p second * n /\
        prefix_eq v (s_target p vr second) ((SZ.v t + 1) * n))
{
  A.pts_to_len dst;
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  s_bounds p second;
  Math.lemma_mult_le_right n (SZ.v t + 1) (s_count p second);
  Math.distributivity_add_left (SZ.v t) 1 n;
  Math.lemma_mult_le_right n (s_count p second) 8;
  SZ.fits_u32_implies_fits (SZ.v t * n + n);
  let z8 = S8.classify 0uy;
  let mut sd = [| z8; 66sz |];
  Mem.track sd;
  A.pts_to_len sd;
  Copy.copy_prefix sd rho 64sz;
  A.((sd.(65sz) <- S8.classify 0uy));
  let x = SZ.add t off;
  let bx = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 x);
  Math.small_mod (SZ.v x) 256;
  Math.small_mod (SZ.v x) 4294967296;
  A.((sd.(64sz) <- S8.classify bx));
  with vsd. assert (A.pts_to sd vsd);
  let lo = SZ.mul t 256sz;
  let hi = SZ.add lo 256sz;
  with w0. assert (A.pts_to dst w0);
  let blk = Sub.sub dst lo hi;
  S.rej_bounded_poly_impl blk sd 66sz eta;
  with b1. assert (A.pts_to blk b1);
  Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
  with w1. assert (A.pts_to dst w1);
  expand_s_step p vr second (SZ.v t) w0 w1 b1 vsd;
  assert (pure (prefix_eq w1 (s_target p vr second) ((SZ.v t + 1) * n)));
  Mem.wipe sd 66sz;
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Polynomials [s .. s + 4) of the vector, sampled together.  Uses
    AVX2: the caller checks {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn s_four (p: erased params) (second: erased bool) (dst: A.array zqt) (rho: A.array S8.t)
          (s: SZ.t) (off: SZ.t)
          ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
          (#vd: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 64 /\ SZ.v s + 4 <= s_count p second /\
               SZ.v off == s_off p second /\ SZ.v eta == p.eta /\
               Seq.length vd == s_count p second * n /\
               prefix_eq vd (s_target p vr second) (SZ.v s * n))
ensures exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length v == s_count p second * n /\
        prefix_eq v (s_target p vr second) ((SZ.v s + 4) * n))
{
  A.pts_to_len rho;
  HSZ.fits32 ();
  s_bounds p second;
  assert_norm (pow2 16 == 65536);
  let s1 = SZ.add s 1sz;
  let s2 = SZ.add s 2sz;
  let s3 = SZ.add s 3sz;
  let x0 = SZ.add s off;
  let x1 = SZ.add s1 off;
  let x2 = SZ.add s2 off;
  let x3 = SZ.add s3 off;
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
  rej_bounded4_impl p0 p1 p2 p3 rho x0 x1 x2 x3 eta;
  put_s p second dst p0 s vr;
  put_s p second dst p1 s1 vr;
  put_s p second dst p2 s2 vr;
  put_s p second dst p3 s3 vr;
  Mem.wipe p3 256sz;
  Mem.wipe p2 256sz;
  Mem.wipe p1 256sz;
  Mem.wipe p0 256sz;
}

(** [s1] ([second = false], [l] polynomials, nonces [0 .. l)) or [s2]
    ([second = true], [k] polynomials, nonces [l .. l + k)), four at a
    time where it can. *)
fn expand_s_part_impl (p: erased params) (second: erased bool)
                      (dst: A.array zqt) (rho: A.array S8.t)
                      ([@@@FStar.Attributes.monomorphize] cnt: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] off: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                      (#vd: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 64 /\ SZ.v cnt == s_count p second /\
               SZ.v off == s_off p second /\ SZ.v eta == p.eta /\
               Seq.length vd == SZ.v cnt * n)
ensures exists* v. A.pts_to dst v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ SZ.v cnt == s_count p second /\
        Seq.length v == SZ.v cnt * n /\
        as_zqs v == s_target p vr second)
{
  A.pts_to_len dst;
  A.pts_to_len rho;
  HSZ.fits32 ();
  prefix_zero vd (s_target p vr second);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc cnt)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt).
    pts_to c vc ** A.pts_to dst v ** A.pts_to rho #pr vr **
    pure (SZ.v vc <= SZ.v cnt /\ SZ.v cnt == s_count p second /\
          SZ.v off == s_off p second /\ SZ.v eta == p.eta /\
          Seq.length v == SZ.v cnt * n /\ Seq.length vr == 64 /\
          prefix_eq v (s_target p vr second) (SZ.v vc * n))
  decreases (SZ.v cnt - SZ.v (!c))
  {
    let vc = !c;
    s_bounds p second;
    if (SZ.lte (SZ.add vc 2sz) cnt && SZ.gte cnt 4sz && V.supported ()) {
      let s = (if SZ.lte (SZ.add vc 4sz) cnt then vc else SZ.sub cnt 4sz);
      with v. assert (A.pts_to dst v);
      Math.lemma_mult_le_right n (SZ.v s) (SZ.v vc);
      prefix_mono v (s_target p vr second) (SZ.v vc * n) (SZ.v s * n);
      s_four p second dst rho s off eta;
      c := SZ.add s 4sz;
    } else {
      s_one p second dst rho vc off eta;
      c := SZ.add vc 1sz;
    }
  };
  with v. assert (A.pts_to dst v);
  prefix_done (s_count p second) v (s_target p vr second);
  assert (pure (as_zqs v == s_target p vr second));
}

(** Algorithm 33: [s1 <- ExpandS_1 rho'] and [s2 <- ExpandS_2 rho']. *)
fn expand_s_impl (p: erased params) (s1: A.array zqt) (s2: A.array zqt) (rho: A.array S8.t)
                 ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                 (#v1: erased (Seq.seq zqt)) (#v2: erased (Seq.seq zqt))
                 (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 64 /\ SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
               Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n)
ensures exists* w1 w2. A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length w1 == p.l * n /\ Seq.length w2 == p.k * n /\
        as_zqs w1 == expand_s1 p vr /\ as_zqs w2 == expand_s2 p vr)
{
  expand_s_part_impl p (hide false) s1 rho l 0sz eta;
  expand_s_part_impl p (hide true) s2 rho k l eta;
}

#pop-options
