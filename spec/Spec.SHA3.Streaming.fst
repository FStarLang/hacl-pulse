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

(** What an incremental sponge remembers.

    The argument is the same as for SHA-2 ([Spec.SHA2.Streaming]): absorbing
    [n] blocks cannot look past byte [n * r], so the state after [n] blocks of
    the message seen so far is equally the state after [n] blocks of the
    eventual padded message, whatever the padding turns out to be.

    Two lemmas do all the work.  [sabsorb_congr] is that observation.
    [absorb_from_state] says the one-shot [absorb] is the incremental state
    after the whole message, with one more [absorb_block] for the padded last
    block -- which is exactly what a [digest] does on a copy of the state. *)
module Spec.SHA3.Streaming

open Spec.SHA3

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module Classical = FStar.Classical

(** The state after absorbing [n] blocks of [m], unpadded.  Total: [block_at]
    is zero past the end of [m], so no bound on [n] is needed. *)
let sabsorb (r: rate_t) (m: Seq.seq S8.t) (n: nat) : state =
  Loops.repeati n (absorb_step r m) zero_state

let sabsorb_zero (r: rate_t) (m: Seq.seq S8.t)
  : Lemma (sabsorb r m 0 == zero_state)
  = ()

let sabsorb_unfold (r: rate_t) (m: Seq.seq S8.t) (n: nat)
  : Lemma (sabsorb r m (n + 1) == absorb_block r (block_at r m n) (sabsorb r m n))
  = Loops.unfold_repeati n (absorb_step r m) zero_state

unfold let agree_upto (m1: Seq.seq S8.t) (m2: Seq.seq S8.t) (n: nat) =
  n <= Seq.length m1 /\ n <= Seq.length m2 /\
  (forall (k: nat). k < n ==> Seq.index m1 k == Seq.index m2 k)

(** {2 Absorbing looks only at the blocks it absorbs} *)

let block_at_congr (r: rate_t) (m1: Seq.seq S8.t) (m2: Seq.seq S8.t) (i: nat)
  : Lemma (requires agree_upto m1 m2 (i * r + r))
          (ensures block_at r m1 i == block_at r m2 i)
  = let aux (k: nat { k < r })
      : Lemma (Seq.index (block_at r m1 i) k == Seq.index (block_at r m2 i) k)
      = block_at_index r m1 i k;
        block_at_index r m2 i k
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (block_at r m1 i) (block_at r m2 i)

(** Block [j] of the message is the slice of the buffer the implementation is
    about to absorb.  Stated over an absolute offset because that is what the
    caller has: block indices would put a product under a trigger. *)
let block_eq_slice (r: rate_t) (s: Seq.seq S8.t) (j: nat)
                   (vin: Seq.seq S8.t) (base: nat)
  : Lemma (requires j * r + r <= Seq.length s /\ base + r <= Seq.length vin /\
                    (forall (k: nat). k < r ==>
                       Seq.index vin (base + k) == Seq.index s (j * r + k)))
          (ensures block_at r s j == Seq.slice vin base (base + r))
  = let aux (k: nat { k < r })
      : Lemma (Seq.index (block_at r s j) k ==
               Seq.index (Seq.slice vin base (base + r)) k)
      = block_at_index r s j k
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (block_at r s j) (Seq.slice vin base (base + r))

(** The same, for the [j]th of a run of [nfull] blocks the implementation is
    absorbing out of one buffer.  The whole run is what the caller has a
    hypothesis about, so the run is what this lemma takes: instantiating that
    hypothesis at [j * r + k] is arithmetic Z3 will not do under a trigger in a
    Pulse-sized context, and does do here. *)
let block_eq_slice_at (r: rate_t) (s: Seq.seq S8.t) (nb: nat) (j: nat)
                      (vin: Seq.seq S8.t) (base: nat) (nfull: nat)
  : Lemma (requires j < nfull /\ base + nfull * r <= Seq.length vin /\
                    (nb + nfull) * r <= Seq.length s /\
                    (forall (k: nat). k < nfull * r ==>
                       Seq.index vin (base + k) == Seq.index s (nb * r + k)))
          (ensures block_at r s (nb + j) ==
                   Seq.slice vin (base + j * r) (base + j * r + r))
  = Math.lemma_mult_le_right r (j + 1) nfull;
    Math.distributivity_add_left j 1 r;
    Math.distributivity_add_left nb j r;
    Math.distributivity_add_left (nb + j) 1 r;
    Math.lemma_mult_le_right r (nb + j + 1) (nb + nfull);
    let aux (k: nat { k < r })
      : Lemma (Seq.index vin (base + j * r + k) == Seq.index s ((nb + j) * r + k))
      = assert (j * r + k < nfull * r);
        assert (Seq.index vin (base + (j * r + k)) == Seq.index s (nb * r + (j * r + k)))
    in
    Classical.forall_intro aux;
    block_eq_slice r s (nb + j) vin (base + j * r)

let rec sabsorb_congr (r: rate_t) (m1: Seq.seq S8.t) (m2: Seq.seq S8.t) (n: nat)  : Lemma (requires agree_upto m1 m2 (n * r))
          (ensures sabsorb r m1 n == sabsorb r m2 n)
          (decreases n)
  = if n = 0
    then ()
    else begin
      Math.lemma_mult_le_right r (n - 1) n;
      sabsorb_congr r m1 m2 (n - 1);
      Math.distributivity_add_left (n - 1) 1 r;
      block_at_congr r m1 m2 (n - 1);
      sabsorb_unfold r m1 (n - 1);
      sabsorb_unfold r m2 (n - 1)
    end

(** Padding does not disturb the blocks already absorbed. *)let sabsorb_padded (r: rate_t) (suffix: U8.t) (m: Seq.seq S8.t) (n: nat)
  : Lemma (requires n * r <= Seq.length m)
          (ensures sabsorb r (padded r suffix m) n == sabsorb r m n)
  = padded_len r suffix m;
    let mp = padded r suffix m in
    let aux (k: nat { k < n * r }) : Lemma (Seq.index mp k == Seq.index m k)
      = Seq.lemma_index_app1 m (padding r suffix (Seq.length m)) k
    in
    Classical.forall_intro aux;
    sabsorb_congr r mp m n

(** {2 The one-shot hash, restarted from the incremental state} *)

(** [absorb] is the incremental state after every whole block of the message,
    plus the padded last block. *)
let absorb_from_state (r: rate_t) (suffix: U8.t) (m: Seq.seq S8.t)
  : Lemma (absorb r suffix m ==
           absorb_block r (block_at r (padded r suffix m) (Seq.length m / r))
                          (sabsorb r m (Seq.length m / r)))
  = nblocks_eq r m;
    sabsorb_unfold r (padded r suffix m) (Seq.length m / r);
    Math.multiply_fractions (Seq.length m) r;
    sabsorb_padded r suffix m (Seq.length m / r)

(** The last block built from the buffered tail alone is the last block of the
    padded message: the padding depends on the length only through [n % r], and
    that is the length of the tail. *)
let last_block_eq (r: rate_t) (suffix: U8.t) (seen: Seq.seq S8.t) (tail: Seq.seq S8.t)
  : Lemma (requires Seq.length tail == Seq.length seen % r /\
                    (forall (k: nat). k < Seq.length tail ==>
                       Seq.index tail k == Seq.index seen (Seq.length seen / r * r + k)))
          (ensures block_at r (padded r suffix seen) (Seq.length seen / r) ==
                   block_at r (padded r suffix tail) 0)
  = let n = Seq.length seen in
    let m = Seq.length tail in
    Math.euclidean_division_definition n r;
    Math.small_div m r;
    Math.small_mod m r;
    padded_len r suffix tail;
    let blk = block_at r (padded r suffix tail) 0 in
    let aux (k: nat { k < r }) : Lemma
      (Seq.index blk k ==
         (if k < m then Seq.index seen (n - n % r + k)
          else pad_byte suffix (r - n % r) (k - n % r)))
      = block_at_index r (padded r suffix tail) 0 k;
        padded_index r suffix tail k
    in
    Classical.forall_intro aux;
    block_at_last r suffix seen blk

(** {2 The state relation}

    [stream_ok r seen st buf tot] is the whole invariant of an incremental
    sponge: the state has absorbed every whole block of [seen], the buffer
    holds the bytes past them, and [tot] is the length of [seen]. *)

unfold let state_ok (r: rate_t) (seen: Seq.seq S8.t)
                    (vst: Seq.seq S64.t) (vbuf: Seq.seq S8.t) =
  Seq.length vst == 25 /\ Seq.length vbuf == r /\
  vst == sabsorb r seen (Seq.length seen / r) /\
  (forall (k: nat). k < Seq.length seen % r ==>
     Seq.index vbuf k == Seq.index seen (Seq.length seen / r * r + k))
