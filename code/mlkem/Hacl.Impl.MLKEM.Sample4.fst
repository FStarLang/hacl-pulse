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

(** Four [SampleNTT]s at once, over the four-way Keccak.

    The matrix is [k * k] independent rejection samplers, each reading its
    own SHAKE128 stream.  Run four of them in lock step and every Keccak
    permutation they need -- the one that ends each absorb, and the one
    before every squeezed block after the first -- is one
    {!Hacl.Hash.SHA3.Core4.permute4} instead of four scalar ones.

    Nothing about a single stream changes.  Each is the same state, read
    block by block through {!Hacl.Hash.SHA3.Sponge.squeeze_block} and fed
    to the same {!Hacl.Impl.MLKEM.Sample.block_impl}; only the
    permutations are shared.  The loop runs until all four samplers are
    full (or the sixteen-block bound is reached), so a stream that filled
    early keeps receiving blocks; a full sampler ignores them, which is the
    same {!Spec.MLKEM.Sample.sampled_stable} the scalar sampler's early
    exit relies on.

    Each stream's loop invariant is one opaque {!stream_ok}, so the loop's
    verification condition holds four applications of a symbol rather
    than four copies of the sampler's invariant. *)
module Hacl.Impl.MLKEM.Sample4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Sample
open Spec.SHA3
open Spec.SHA3.Constants
open Hacl.Impl.Table
open Hacl.Hash.SHA3
open Hacl.Hash.SHA3.Sponge
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.XOF

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module S64 = Hacl.Secret.UInt64
module Loops = Hacl.Spec.Loops
module HSZ = Hacl.SizeT
module Mem = Hacl.Mem
module S = Hacl.Impl.MLKEM.Sample
module K4 = Hacl.Hash.SHA3.Core4

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 One stream} *)

(** Stream state after [j] blocks were sampled, with [q] permutations
    applied to the absorbed state: [q] is [xof_prev j] before the
    permutation for block [j], and [j] after it. *)
[@@"opaque_to_smt"]
let stream_ok (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
              (c: nat) (q: nat) (j: nat) : prop =
  Seq.length v == n /\ Seq.length vst == 25 /\
  vst == squeeze_state q (absorb 168 shake_suffix vs) /\
  c == Seq.length (sampled vs (j * 56)) /\
  (forall (k: nat). k < c ==> S16.v (Seq.index v k) == Seq.index (sampled vs (j * 56)) k)

let stream_ok_elim (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                   (c: nat) (q: nat) (j: nat)
  : Lemma (requires stream_ok v vst vs c q j)
          (ensures Seq.length v == n /\ Seq.length vst == 25 /\
                   vst == squeeze_state q (absorb 168 shake_suffix vs) /\
                   c == Seq.length (sampled vs (j * 56)) /\
                   (forall (k: nat). k < c ==>
                      S16.v (Seq.index v k) == Seq.index (sampled vs (j * 56)) k))
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c q j)

let stream_ok_intro (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                    (c: nat) (q: nat) (j: nat)
  : Lemma (requires Seq.length v == n /\ Seq.length vst == 25 /\
                    vst == squeeze_state q (absorb 168 shake_suffix vs) /\
                    c == Seq.length (sampled vs (j * 56)) /\
                    (forall (k: nat). k < c ==>
                       S16.v (Seq.index v k) == Seq.index (sampled vs (j * 56)) k))
          (ensures stream_ok v vst vs c q j)
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c q j)

let stream_ok_init (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
  : Lemma (requires Seq.length v == n /\ Seq.length vst == 25 /\
                    vst == absorb 168 shake_suffix vs)
          (ensures stream_ok v vst vs 0 0 0)
  = squeeze_state_zero (absorb 168 shake_suffix vs);
    Loops.repeati_g_zero (sample_step vs) (Seq.empty #zq);
    reveal_opaque (`%stream_ok) (stream_ok v vst vs 0 0 0)

(** The permutation (or, for block zero, none) that brings a stream to
    the state its block [j] is read from. *)
let stream_ok_advance (v: Seq.seq zqt) (vst vst': Seq.seq S64.t) (vs: Seq.seq S8.t)
                      (c: nat) (j: nat)
  : Lemma (requires stream_ok v vst vs c (xof_prev j) j /\
                    (j > 0 ==> Seq.length vst == 25 /\ vst' == permute vst) /\
                    (j == 0 ==> vst' == vst))
          (ensures stream_ok v vst' vs c j j)
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c (xof_prev j) j);
    if j > 0 then squeeze_state_succ (j - 1) (absorb 168 shake_suffix vs);
    reveal_opaque (`%stream_ok) (stream_ok v vst' vs c j j)

(** A full sampler is the answer. *)
let stream_ok_full (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                   (c: nat) (q: nat) (j: nat)
  : Lemma (requires stream_ok v vst vs c q j /\ c >= n /\ j <= 16)
          (ensures Seq.length v == n /\ as_poly v == sample_ntt vs)
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c q j);
    sampled_stable vs (j * 56) max_triples;
    as_poly_intro v (sample_ntt vs)

(** A sampler still short after sixteen blocks gives up. *)
let stream_ok_short (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                    (c: nat) (q: nat)
  : Lemma (requires stream_ok v vst vs c q 16 /\ c < n)
          (ensures Seq.length v == n /\ sample_ntt vs == poly_zero)
  = reveal_opaque (`%stream_ok) (stream_ok v vst vs c q 16)

(** Both ways a stream can end. *)
let stream_ok_done (v: Seq.seq zqt) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t)
                   (c: nat) (q: nat) (j: nat)
  : Lemma (requires stream_ok v vst vs c q j /\ j <= 16 /\ (c >= n \/ j == 16))
          (ensures Seq.length v == n /\
                   (c >= n ==> as_poly v == sample_ntt vs) /\
                   (c < n ==> sample_ntt vs == poly_zero))
  = if c >= n then stream_ok_full v vst vs c q j
    else stream_ok_short v vst vs c q

(** The bytes [squeeze_block] read from block [j]'s state are the
    sampler's triples [j * 56] onwards. *)
let stream_bytes (vk: Seq.seq S8.t) (vst: Seq.seq S64.t) (vs: Seq.seq S8.t) (j: nat)
  : Lemma (requires Seq.length vk == 168 /\ Seq.length vst == 25 /\
                    vst == squeeze_state j (absorb 168 shake_suffix vs) /\
                    (forall (k: nat). 0 <= k /\ k < 0 + 168 ==>
                       Seq.index vk k == state_byte vst (k - 0)))
          (ensures forall (u: nat). u < 168 ==>
                     Seq.index vk u == xof_byte vs (3 * (j * 56) + u))
  = assert (3 * (j * 56) == j * 168);
    introduce forall (u: nat). u < 168 ==> Seq.index vk u == xof_byte vs (3 * (j * 56) + u)
    with introduce _ ==> _
    with (xof_block_byte vs j u;
          assert (Seq.index vk u == state_byte vst (u - 0)))

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
  let x = S.block_impl dst blk c vs (hide (SZ.v j * 56));
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
  pure (Seq.length v == n /\ as_poly v == sample_ntt vs)
{
  stream_ok_done v0 vst vs (SZ.v c) q (SZ.v j);
  if (SZ.lt c 256sz) {
    S.zero_poly dst;
  } else {
    assert (pure (as_poly v0 == sample_ntt vs));
  }
}

#pop-options

(** {2 Four streams} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** All but the absorb's last permutation, for SHAKE128; not inlined, so
    that the four calls below share one copy. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn shake128_absorb_pre (st: A.array S64.t) (b: A.array S64.t) (rc_tbl: A.array S64.t)
                       (seed: A.array S8.t) (slen: SZ.t)
                       (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
                       (#prc: perm) (#vrc: erased (Seq.seq S64.t))
                       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         A.pts_to seed #ps vs **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ SZ.v slen == Seq.length vs)
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  A.pts_to seed #ps vs **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\
        permute vst == absorb 168 shake_suffix vs)
{
  absorb_pre st b rc_tbl seed slen 168sz shake_suffix;
}

(** [st_i <- permute st_i] for all four when [c]. *)
inline_for_extraction
fn permute4_if (c: bool) (st0 st1 st2 st3: A.array S64.t) (rc_tbl: A.array S64.t)
               (#v0 #v1 #v2 #v3: erased (Seq.seq S64.t))
               (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to st0 v0 ** A.pts_to st1 v1 ** A.pts_to st2 v2 ** A.pts_to st3 v3 **
         A.pts_to rc_tbl #prc vrc **
         pure (Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
               Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
               reveal vrc == (rc <: Seq.seq S64.t))
ensures exists* (w0 w1 w2 w3: Seq.seq S64.t).
  A.pts_to st0 w0 ** A.pts_to st1 w1 ** A.pts_to st2 w2 ** A.pts_to st3 w3 **
  A.pts_to rc_tbl #prc vrc **
  pure (Seq.length v0 == 25 /\ Seq.length v1 == 25 /\
        Seq.length v2 == 25 /\ Seq.length v3 == 25 /\
        (c ==> w0 == permute v0 /\ w1 == permute v1 /\ w2 == permute v2 /\ w3 == permute v3) /\
        (not c ==> w0 == reveal v0 /\ w1 == reveal v1 /\ w2 == reveal v2 /\ w3 == reveal v3))
{
  if c {
    K4.permute4 st0 st1 st2 st3 rc_tbl;
  } else {
    ()
  }
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** [d_i <- SampleNTT s_i] for four seeds of the same length.  Uses AVX2:
    the caller checks {!Hacl.Vec256.supported}. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn sample_ntt4_impl (d0 d1 d2 d3: A.array zqt) (s0 s1 s2 s3: A.array S8.t) (slen: SZ.t)
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
        as_poly w0 == sample_ntt vs0 /\ as_poly w1 == sample_ntt vs1 /\
        as_poly w2 == sample_ntt vs2 /\ as_poly w3 == sample_ntt vs3)
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

  shake128_absorb_pre st0 barr rc_tbl s0 slen;
  shake128_absorb_pre st1 barr rc_tbl s1 slen;
  shake128_absorb_pre st2 barr rc_tbl s2 slen;
  shake128_absorb_pre st3 barr rc_tbl s3 slen;
  K4.permute4 st0 st1 st2 st3 rc_tbl;
  with a0. assert (A.pts_to st0 a0);
  with a1. assert (A.pts_to st1 a1);
  with a2. assert (A.pts_to st2 a2);
  with a3. assert (A.pts_to st3 a3);
  stream_ok_init vd0 a0 vs0;
  stream_ok_init vd1 a1 vs1;
  stream_ok_init vd2 a2 vs2;
  stream_ok_init vd3 a3 vs3;
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
    permute4_if (SZ.gt vj 0sz) st0 st1 st2 st3 rc_tbl;
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
