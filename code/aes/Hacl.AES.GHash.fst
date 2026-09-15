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

(** GHASH over a buffer, folded into an accumulator.

    GCM hashes three pieces in a row -- padded associated data, padded
    ciphertext, a block of lengths -- and the padding is not stored anywhere.
    So the driver here does not take "the input"; it takes an accumulator and
    one piece, and the caller runs it three times.  [Spec.GF128.ghash_upd] is
    the fold this refines and [Spec.GF128.ghash_upd_append] is what makes
    running it three times equal to hashing the concatenation.

    The padding never exists in memory either: a partial final block is
    assembled in sixteen bytes of stack that start at zero. *)
module Hacl.AES.GHash

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Spec.GCM
open Hacl.AES.GF128

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = Spec.GF128
module Copy = Hacl.Impl.Copy

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The pure side} *)

(** The offset of a whole block is a block index. *)
let block_index (d: Seq.seq elem) (i: nat)
  : Lemma (requires i % blocklen == 0 /\ i + blocklen <= Seq.length d)
          (ensures (i / blocklen) * blocklen == i /\
                   (i + blocklen) / blocklen == i / blocklen + 1)
  = Math.euclidean_division_definition i blocklen;
    Math.division_addition_lemma i blocklen 1

(** One turn of the loop: multiply the accumulator, after adding the block at
    offset [i], by the hash key. *)
let ghash_body (h acc0: G.block) (d: Seq.seq elem) (i: nat)
  : Lemma (requires i % blocklen == 0 /\ i + blocklen <= Seq.length d)
          (ensures (let k = i / blocklen in
                    k + 1 <= G.nblocks (whole d) /\
                    (i + blocklen) / blocklen == k + 1 /\
                    G.ghash_from h acc0 (whole d) (k + 1) ==
                      G.gmul (G.gadd (G.ghash_from h acc0 (whole d) k)
                                     (Seq.slice d i (i + blocklen))) h))
  = block_index d i;
    let k = i / blocklen in
    Math.distributivity_add_left k 1 blocklen;
    blk_whole d k;
    nblocks_whole d;
    G.ghash_from_step h acc0 (whole d) k

(** Leaving the loop: no whole block is left, so the count reached is the
    number of blocks of the input. *)
let ghash_loop_done (d: Seq.seq elem) (i: nat)
  : Lemma (requires i % blocklen == 0 /\ i <= Seq.length d /\
                    Seq.length d < i + blocklen)
          (ensures i / blocklen == G.nblocks (whole d) /\
                   i == G.nblocks d * blocklen /\
                   Seq.length d - i == Seq.length d % blocklen)
  = Math.euclidean_division_definition i blocklen;
    Math.euclidean_division_definition (Seq.length d) blocklen;
    Math.lemma_div_le i (Seq.length d) blocklen;
    Math.small_div (Seq.length d - i) blocklen;
    Math.lemma_div_plus (Seq.length d - i) (i / blocklen) blocklen;
    nblocks_whole d

(** The scratch block, once the tail has been copied over the zeroes, holds
    exactly the padded final block of the spec. *)
let tail_eq (vd vb: Seq.seq S8.t) (i: nat)
  : Lemma (requires Seq.length vb == blocklen /\ i <= Seq.length vd /\
                    i % blocklen == 0 /\ Seq.length vd < i + blocklen /\
                    Seq.length vd % blocklen <> 0 /\
                    (forall (k: nat). k < Seq.length vd - i ==>
                       Seq.index (vals vb) k == Seq.index (vals vd) (i + k)) /\
                    (forall (k: nat). Seq.length vd - i <= k /\ k < blocklen ==>
                       Seq.index (vals vb) k == 0))
          (ensures vals vb == tail_block (vals vd))
  = ghash_loop_done (vals vd) i;
    Seq.lemma_eq_intro (vals vb) (tail_block (vals vd))

#push-options "--fuel 2"
(** Folding a single block is one multiply-add. *)
let ghash_one (h acc: G.block) (b: Seq.seq elem)
  : Lemma (requires Seq.length b == blocklen)
          (ensures Seq.length b % blocklen == 0 /\
                   G.ghash_upd h acc b == G.gmul (G.gadd acc b) h)
  = Math.multiple_modulo_lemma 1 G.blocklen;
    Math.multiple_division_lemma 1 G.blocklen;
    assert (G.nblocks b == 1);
    Seq.lemma_eq_elim (G.blk b 0) b;
    assert (G.ghash_upd h acc b == G.ghash_from h acc b 1)

(** Entering the loop. *)
let ghash_start (h acc: G.block)
                (d: Seq.seq elem { Seq.length d % G.blocklen == 0 })
  : Lemma (G.ghash_from h acc d 0 == acc) = ()
#pop-options

(** {2 The driver} *)

(** [acc := ghash_upd h acc (pad data)]: fold the whole blocks of [data] into
    the accumulator, then its zero-padded remainder if it has one. *)

fn ghash_upd_impl (acc: A.array S8.t) (h: A.array S8.t) (data: A.array S8.t) (n: SZ.t)
                  (#va0 #vh: erased (Seq.seq S8.t))
                  (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to acc va0 ** A.pts_to h vh ** A.pts_to data #pd vd ** pure (
  Seq.length va0 == blocklen /\ Seq.length vh == blocklen /\
  SZ.fits (Seq.length vd + blocklen))
         ** pure (SZ.v n == Seq.length vd)
ensures exists* (va1: Seq.seq S8.t).
  A.pts_to acc va1 ** A.pts_to h vh ** A.pts_to data #pd vd ** pure (
  Seq.length va0 == blocklen /\ Seq.length vh == blocklen /\
  Seq.length va1 == blocklen /\
  vals va1 == G.ghash_upd (vals vh) (vals va0) (pad (vals vd)))
{
  A.pts_to_len acc;
  A.pts_to_len h;
  A.pts_to_len data;

  ghash_start (vals vh) (vals va0) (whole (vals vd));
  let mut i = 0sz;
  while (let vi = !i; SZ.lte (SZ.add vi 16sz) n)
  invariant exists* (vi: SZ.t) (va: Seq.seq S8.t).
    pts_to i vi ** A.pts_to acc va ** A.pts_to h vh ** A.pts_to data #pd vd **
    pure (SZ.v vi <= SZ.v n /\ SZ.v vi % blocklen == 0 /\
          Seq.length va == blocklen /\ Seq.length va0 == blocklen /\
          Seq.length vh == blocklen /\ Seq.length vd == SZ.v n /\
          SZ.fits (SZ.v n + blocklen) /\
          SZ.v vi / blocklen <= G.nblocks (whole (vals vd)) /\
          vals va == G.ghash_from (vals vh) (vals va0) (whole (vals vd))
                                  (SZ.v vi / blocklen))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with va. assert A.pts_to acc va;
    ghash_body (vals vh) (vals va0) (vals vd) (SZ.v vi);
    gadd_at_impl acc data vi;
    Hacl.AES.GMul.gmul_impl acc h;
    i := SZ.add vi 16sz;
  };

  let vi = !i;
  let rem = SZ.sub n vi;
  ghash_loop_done (vals vd) (SZ.v vi);
  ghash_pad (vals vh) (vals va0) (vals vd);

  let z = S8.zero;
  let mut tb = [| z; 16sz |];
  A.pts_to_len tb;
  A.pts_to_len tb;

  if (SZ.gt rem 0sz) {
    Copy.copy_range tb 0sz data vi rem;
    with vb. assert A.pts_to tb vb;
    tail_eq vd vb (SZ.v vi);
    Seq.lemma_eq_intro (Seq.slice (vals vb) 0 blocklen) (vals vb);
    with va. assert A.pts_to acc va;
    ghash_one (vals vh) (vals va) (tail_block (vals vd));
    gadd_at_impl acc tb 0sz;
    Hacl.AES.GMul.gmul_impl acc h;
    } else {
    }
}

#pop-options
