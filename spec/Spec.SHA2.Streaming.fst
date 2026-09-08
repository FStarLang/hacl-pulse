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

(** What an incremental hash remembers.

    [Spec.SHA2.hash] folds over the *padded* message, and the padding depends
    on the total length -- which an incremental hash does not know until it is
    asked for a digest.  The way out is that a fold over the first [n] blocks
    cannot see anything past byte [n * block_len]:

      [absorb_congr]:  if [m1] and [m2] agree on their first [n] blocks then
                       [absorb p m1 n == absorb p m2 n].

    So the accumulator after [n] blocks of the message seen so far is equally
    the accumulator after [n] blocks of the eventual padded message, whatever
    that turns out to be.  That single lemma is the whole justification for
    the streaming state, and it is what lets [Hacl.Hash.SHA2.Streaming] reuse
    [hash_blocks] and [tail_and_finish] unchanged. *)
module Spec.SHA2.Streaming

open Hacl.Secret.Word
open Hacl.Spec.Loops
open Spec.SHA2

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost

(** The accumulator after absorbing [n] blocks of [m].  Total: [update_step]
    is the identity past the end of [m], so no bound is needed here. *)
let absorb (#t: Type0) {| word t |} (p: params t) (m: Seq.seq S8.t) (n: nat)
  : GTot (Seq.lseq t 8)
  = repeati_g n (update_step p m) (G.reveal p.iv)

let absorb_zero (#t: Type0) {| word t |} (p: params t) (m: Seq.seq S8.t)
  : Lemma (absorb p m 0 == G.reveal p.iv)
  = ()

unfold let agree_upto (m1: Seq.seq S8.t) (m2: Seq.seq S8.t) (n: nat) =
  n <= Seq.length m1 /\ n <= Seq.length m2 /\
  (forall (k: nat). k < n ==> Seq.index m1 k == Seq.index m2 k)

(** The fold over [n] blocks depends only on those [n] blocks. *)
let rec absorb_congr (#t: Type0) {| word t |} (p: params t)
                     (m1: Seq.seq S8.t) (m2: Seq.seq S8.t) (n: nat)
  : Lemma (requires agree_upto m1 m2 (n * block_len #t))
          (ensures absorb p m1 n == absorb p m2 n)
          (decreases n)
  = if n = 0
    then ()
    else begin
      Math.lemma_mult_le_right (block_len #t) (n - 1) n;
      absorb_congr p m1 m2 (n - 1);
      Math.distributivity_add_left (n - 1) 1 (block_len #t);
      Seq.lemma_eq_intro (block_at #t m1 ((n - 1) * block_len #t))
                         (block_at #t m2 ((n - 1) * block_len #t))
    end

(** {2 The two shapes the implementation needs}

    Both are [absorb_congr] with the pointwise hypothesis discharged. *)

(** Padding does not disturb the blocks already absorbed. *)
let absorb_padded (#t: Type0) {| word t |} (p: params t)
                  (m: Seq.seq S8.t { Seq.length m < max_input #t }) (n: nat)
  : Lemma (requires n * block_len #t <= Seq.length m)
          (ensures absorb p (padded #t m) n == absorb p m n)
  = let mp = padded #t m in
    let aux (k: nat { k < n * block_len #t }) : Lemma (Seq.index mp k == Seq.index m k)
      = Seq.lemma_index_app1 m (padding #t (Seq.length m)) k
    in
    FStar.Classical.forall_intro aux;
    absorb_congr p mp m n

(** Nor does whatever is appended after them. *)
let absorb_append (#t: Type0) {| word t |} (p: params t)
                  (pre: Seq.seq S8.t) (rest: Seq.seq S8.t) (m: Seq.seq S8.t) (n: nat)
  : Lemma (requires n * block_len #t <= Seq.length pre /\
                    agree_upto pre m (n * block_len #t))
          (ensures absorb p (Seq.append pre rest) n == absorb p m n)
  = let a = Seq.append pre rest in
    let aux (k: nat { k < n * block_len #t }) : Lemma (Seq.index a k == Seq.index m k)
      = Seq.lemma_index_app1 pre rest k
    in
    FStar.Classical.forall_intro aux;
    absorb_congr p a m n

(** {2 The state relation}

    [state_ok p seen nb acc] says [acc] is the accumulator of an incremental
    hash that has been fed [seen] and has absorbed [nb] of its blocks. *)

unfold let state_ok (#t: Type0) {| word t |} (p: params t)
                    (seen: Seq.seq S8.t) (nb: nat) (acc: Seq.lseq t 8) =
  nb == Seq.length seen / block_len #t /\ acc == absorb p seen nb

(** A digest is the one-shot hash of everything seen. *)
let digest_correct (#t: Type0) {| word t |} (p: params t)
                   (seen: Seq.seq S8.t { Seq.length seen < max_input #t })
  : Lemma (hash p seen ==
             finish p (absorb p (padded #t seen)
                         (Seq.length (padded #t seen) / block_len #t)))
  = ()
