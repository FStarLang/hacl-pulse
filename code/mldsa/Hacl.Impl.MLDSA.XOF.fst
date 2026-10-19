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


(** SHAKE128 and SHAKE256 as streams, for ML-DSA's rejection samplers.

    The same opening of the sponge as {!Hacl.Impl.MLKEM.XOF}, with the rate
    an argument: [RejNTTPoly] squeezes SHAKE128 (rate 168) and
    [RejBoundedPoly] and [SampleInBall] squeeze SHAKE256 (rate 136), one
    block at a time and only as many blocks as they need.

    {!xof_absorb} runs the absorb; {!xof_block} hands back block [j],
    permuting first unless [j] is zero, so that the block a sampler stops
    at is never followed by a permutation.
    {!block128_bytes} and {!block256_bytes} connect a block to the
    specification's streams {!Spec.MLDSA.Sample.shake128_byte} and
    {!Spec.MLDSA.Sample.shake256_byte}: byte [u] of block [j] is byte
    [r j + u] of the stream. *)
module Hacl.Impl.MLDSA.XOF

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants
open Spec.MLDSA.Sample
open Hacl.Impl.Table
open Hacl.Hash.SHA3.Core
open Hacl.Hash.SHA3.Sponge

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The two rates ML-DSA squeezes at. *)
let xof_rate (r: nat) : prop = r == 168 \/ r == 136

(** The state the squeeze starts from. *)
let xof_start (r: nat { xof_rate r }) (seed: Seq.seq S8.t) : state
  = absorb r shake_suffix seed

(** Byte [u] of block [j] of SHAKE128 is byte [168 j + u] of the stream. *)
let block128_byte (seed: Seq.seq S8.t) (j: nat) (u: nat { u < 168 })
  : Lemma (state_byte (squeeze_state j (xof_start 168 seed)) u ==
           shake128_byte seed (j * 168 + u))
  = squeeze_byte_eq 168 (absorb 168 shake_suffix seed) (j * 168 + u + 1) j u

let block128_bytes (seed: Seq.seq S8.t) (j: nat)
  : Lemma (forall (u: nat). u < 168 ==>
             state_byte (squeeze_state j (xof_start 168 seed)) u ==
             shake128_byte seed (j * 168 + u))
  = FStar.Classical.forall_intro (block128_byte seed j)

(** Byte [u] of block [j] of SHAKE256 is byte [136 j + u] of the stream. *)
let block256_byte (seed: Seq.seq S8.t) (j: nat) (u: nat { u < 136 })
  : Lemma (state_byte (squeeze_state j (xof_start 136 seed)) u ==
           shake256_byte seed (j * 136 + u))
  = squeeze_byte_eq 136 (absorb 136 shake_suffix seed) (j * 136 + u + 1) j u

let block256_bytes (seed: Seq.seq S8.t) (j: nat)
  : Lemma (forall (u: nat). u < 136 ==>
             state_byte (squeeze_state j (xof_start 136 seed)) u ==
             shake256_byte seed (j * 136 + u))
  = FStar.Classical.forall_intro (block256_byte seed j)

(** No block taken yet is the state the absorb left. *)
let squeeze_state_zero (s: state)
  : Lemma (squeeze_state 0 s == s)
  = Loops.repeati_zero (fun _ st -> permute st) s

(** Taking a block advances the state by one permutation. *)
let squeeze_state_succ (j: nat) (s: state)
  : Lemma (squeeze_state (j + 1) s == permute (squeeze_state j s))
  = Loops.unfold_repeati j (fun _ st -> permute st) s

(** The state {!xof_block} expects when asked for block [j]: block [0]'s
    own, and from then on the previous block's.  Permuting on the way in
    rather than on the way out means the last block a sampler takes is not
    followed by a permutation whose result nobody reads. *)
let xof_prev (j: nat) : nat = if j = 0 then 0 else j - 1

(** [st <- absorb r 0x1f seed]: the state block [0] is read from. *)
fn xof_absorb (st: A.array S64.t) (b: A.array S64.t) (rc_tbl: A.array S64.t)
              (seed: A.array S8.t) (slen: SZ.t) (r: SZ.t)
              (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
              (#prc: perm) (#vrc: erased (Seq.seq S64.t))
              (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
         A.pts_to seed #ps vs **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\ xof_rate (SZ.v r) /\
               reveal vrc == (rc <: Seq.seq S64.t) /\ SZ.v slen == Seq.length vs)
ensures exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
  A.pts_to seed #ps vs **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\ xof_rate (SZ.v r) /\
        vst == squeeze_state 0 (xof_start (SZ.v r) vs))
{
  absorb_impl st b rc_tbl seed slen r shake_suffix;
  squeeze_state_zero (xof_start (SZ.v r) vs);
  ()
}

(** [blk <- block j]; the state is block [j - 1]'s on the way in and block
    [j]'s on the way out. *)
fn xof_block (blk: A.array S8.t) (st: A.array S64.t) (b: A.array S64.t)
             (rc_tbl: A.array S64.t) (r: SZ.t)
             (j: SZ.t) (vsq: erased (Seq.seq S64.t))
             (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
             (#vblk0: erased (Seq.seq S8.t))
             (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to blk vblk0 ** A.pts_to st vst0 ** A.pts_to b vb0 **
         A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               xof_rate (SZ.v r) /\ Seq.length vblk0 == SZ.v r /\
               reveal vrc == (rc <: Seq.seq S64.t) /\
               Seq.length vsq == 25 /\
               reveal vst0 == squeeze_state (xof_prev (SZ.v j)) vsq)
ensures exists* (v: Seq.seq S8.t) (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to blk v ** A.pts_to st vst ** A.pts_to b vb **
  A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length v == SZ.v r /\
        xof_rate (SZ.v r) /\ Seq.length vsq == 25 /\
        reveal vst == squeeze_state (SZ.v j) vsq /\
        (forall (u: nat). u < SZ.v r ==>
           Seq.index v u == state_byte (squeeze_state (SZ.v j) vsq) u))
{
  A.pts_to_len blk;
  A.pts_to_len st;
  permute_if (SZ.gt j 0sz) st b rc_tbl;
  squeeze_state_succ (xof_prev (SZ.v j)) vsq;
  squeeze_block blk 0sz r st;
}

#pop-options
