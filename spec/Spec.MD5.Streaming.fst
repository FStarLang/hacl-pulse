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

(** What an incremental MD5 remembers.

    The same three facts as [Spec.SHA2.Streaming], for the same reason: an
    incremental hash keeps an accumulator that has absorbed some whole number
    of blocks, a partial block, and a count, and everything the implementation
    must prove reduces to "the fold over [n] blocks depends only on those [n]
    blocks".  [agree_upto] is shared with SHA-2 -- it says nothing about any
    algorithm -- but the folds are MD5's, so they are stated here. *)
module Spec.MD5.Streaming

open Spec.MD5
open Hacl.Spec.Loops

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module G = FStar.Ghost

(** The accumulator after absorbing [n] blocks of [m].  Total: [update_step]
    is the identity past the end of [m], so no bound is needed here. *)
let absorb (m: Seq.seq S8.t) (n: nat) : GTot (Seq.lseq S32.t state_words)
  = repeati_g n (update_step m) iv

let absorb_zero (m: Seq.seq S8.t) : Lemma (absorb m 0 == iv) = ()

unfold let agree_upto (m1: Seq.seq S8.t) (m2: Seq.seq S8.t) (n: nat) =
  n <= Seq.length m1 /\ n <= Seq.length m2 /\
  (forall (k: nat). k < n ==> Seq.index m1 k == Seq.index m2 k)

(** The fold over [n] blocks depends only on those [n] blocks. *)
let rec absorb_congr (m1: Seq.seq S8.t) (m2: Seq.seq S8.t) (n: nat)
  : Lemma (requires agree_upto m1 m2 (n * block_len))
          (ensures absorb m1 n == absorb m2 n)
          (decreases n)
  = if n = 0
    then ()
    else begin
      Math.lemma_mult_le_right block_len (n - 1) n;
      absorb_congr m1 m2 (n - 1);
      Math.distributivity_add_left (n - 1) 1 block_len;
      Seq.lemma_eq_intro (block_at m1 ((n - 1) * block_len))
                         (block_at m2 ((n - 1) * block_len))
    end

(** {2 The two shapes the implementation needs}

    Both are [absorb_congr] with the pointwise hypothesis discharged. *)

(** Padding does not disturb the blocks already absorbed. *)
let absorb_padded (m: Seq.seq S8.t { Seq.length m < max_input }) (n: nat)
  : Lemma (requires n * block_len <= Seq.length m)
          (ensures absorb (padded m) n == absorb m n)
  = let mp = padded m in
    let aux (k: nat { k < n * block_len }) : Lemma (Seq.index mp k == Seq.index m k)
      = Seq.lemma_index_app1 m (padding (Seq.length m)) k
    in
    FStar.Classical.forall_intro aux;
    absorb_congr mp m n

(** Nor does whatever is appended after them. *)
let absorb_append (pre: Seq.seq S8.t) (rest: Seq.seq S8.t) (m: Seq.seq S8.t) (n: nat)
  : Lemma (requires n * block_len <= Seq.length pre /\ agree_upto pre m (n * block_len))
          (ensures absorb (Seq.append pre rest) n == absorb m n)
  = let a = Seq.append pre rest in
    let aux (k: nat { k < n * block_len }) : Lemma (Seq.index a k == Seq.index m k)
      = Seq.lemma_index_app1 pre rest k
    in
    FStar.Classical.forall_intro aux;
    absorb_congr a m n

(** {2 The state relation}

    [state_ok seen nb acc] says [acc] is the accumulator of an incremental
    hash that has been fed [seen] and has absorbed [nb] of its blocks. *)

unfold let state_ok (seen: Seq.seq S8.t) (nb: nat) (acc: Seq.lseq S32.t state_words) =
  nb == Seq.length seen / block_len /\ acc == absorb seen nb

(** A digest is the one-shot hash of everything seen. *)
let digest_correct (seen: Seq.seq S8.t { Seq.length seen < max_input })
  : Lemma (hash seen ==
             finish (absorb (padded seen) (Seq.length (padded seen) / block_len)))
  = ()
