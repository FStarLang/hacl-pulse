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

(** SHAKE128 as a stream.

    [Hacl.Hash.SHA3.shake128] wants to know how many bytes it is going to
    produce.  Rejection sampling does not know: it wants a block, and then
    another one only if the first was not enough.  Asking for the worst
    case -- sixteen blocks, the bound {!Spec.MLKEM.Sample.max_triples}
    fixes -- would mean sixteen Keccak permutations for every entry of the
    matrix, where three or four almost always suffice.  For ML-KEM-768
    that is 144 permutations per matrix instead of about 36.

    So the squeeze phase is opened up.  {!xof_absorb} runs the absorb, and
    {!xof_block} hands back one block and advances the state, with the
    number of blocks already taken carried as a ghost.  The specification
    side of the connection is {!xof_block_byte}: byte [u] of block [j] of
    the squeeze is byte [168 j + u] of the infinite stream that
    {!Spec.MLKEM.Sample.xof_byte} names. *)
module Hacl.Impl.MLKEM.XOF

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants
open Spec.MLKEM.Sample
open Hacl.Impl.Table
open Hacl.Hash.SHA3.Core
open Hacl.Hash.SHA3.Sponge

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module SHA3 = Spec.SHA3

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The rate, once. *)
inline_for_extraction
let xof_rate : SZ.t = 168sz

(** Byte [u] of the [j]th squeezed block is byte [168 j + u] of the
    stream.  Both sides are the same [state_byte]; the work is in lining up
    [squeeze]'s division by the rate. *)
let xof_block_byte (seed: Seq.seq S8.t) (j: nat) (u: nat { u < 168 })
  : Lemma (state_byte (squeeze_state j (absorb 168 shake_suffix seed)) u ==
           xof_byte seed (j * 168 + u))
  = let s = absorb 168 shake_suffix seed in
    squeeze_byte_eq 168 s (j * 168 + u + 1) j u

(** Every byte of a block at once, which is the shape the sampler's loop
    invariant has. *)
let xof_block_bytes (seed: Seq.seq S8.t) (j: nat)
  : Lemma (forall (u: nat). u < 168 ==>
             state_byte (squeeze_state j (absorb 168 shake_suffix seed)) u ==
             xof_byte seed (j * 168 + u))
  = FStar.Classical.forall_intro (xof_block_byte seed j)

(** No block taken yet is the state the absorb left. *)
let squeeze_state_zero (s: state)
  : Lemma (squeeze_state 0 s == s)
  = Loops.repeati_zero (fun _ st -> permute st) s

(** Taking a block advances the state by one permutation. *)
let squeeze_state_succ (j: nat) (s: state)
  : Lemma (squeeze_state (j + 1) s == permute (squeeze_state j s))
  = Loops.unfold_repeati j (fun _ st -> permute st) s

(** {2 The two halves of the sponge, separately} *)

(** [st <- absorb 168 0x1f seed]: the state the squeeze starts from. *)
fn xof_absorb (st: A.array S64.t) (b: A.array S64.t) (rc_tbl: A.array S64.t)
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
        vst == absorb 168 shake_suffix vs)
{
  absorb_impl st b rc_tbl seed slen 168sz shake_suffix;
}

(** [blk <- block j], and the state moves on to block [j + 1]. *)
fn xof_block (blk: A.array S8.t) (st: A.array S64.t) (b: A.array S64.t)
             (rc_tbl: A.array S64.t)
             (j: erased nat) (vsq: erased (Seq.seq S64.t))
             (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
             (#vblk0: erased (Seq.seq S8.t))
             (#prc: perm) (#vrc: erased (Seq.seq S64.t))
requires A.pts_to blk vblk0 ** A.pts_to st vst0 ** A.pts_to b vb0 **
         A.pts_to rc_tbl #prc vrc **
         pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
               Seq.length vblk0 == 168 /\
               reveal vrc == (rc <: Seq.seq S64.t) /\
               Seq.length vsq == 25 /\
               reveal vst0 == squeeze_state j vsq)
ensures exists* (v: Seq.seq S8.t) (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
  A.pts_to blk v ** A.pts_to st vst ** A.pts_to b vb **
  A.pts_to rc_tbl #prc vrc **
  pure (Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length v == 168 /\
        Seq.length vsq == 25 /\
        reveal vst == squeeze_state (j + 1) vsq /\
        (forall (u: nat). u < 168 ==>
           Seq.index v u == state_byte (squeeze_state j vsq) u))
{
  A.pts_to_len blk;
  A.pts_to_len st;
  squeeze_block blk 0sz 168sz st;
  permute_impl st b rc_tbl;
  squeeze_state_succ j vsq;
  assert (pure (squeeze_state (j + 1) vsq == permute (squeeze_state j vsq)));
}

#pop-options
