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

(** What an incremental Poly1305 remembers.

    Poly1305 is easier to stream than a hash: a full block is absorbed the
    same way whether or not it is the last, and only a short final block is
    special.  So an incremental MAC can absorb every whole block the moment
    it has one, and keeps back only the fewer than sixteen bytes past the last
    of them.  Its accumulator is [Spec.Poly1305.blocks_acc] over the whole
    blocks of what it has been fed, which is exactly what the one-shot MAC's
    loop computes before its short block, so [digest] is the one-shot MAC's
    tail.

    The one fact needed is that this fold can be continued in pieces: the
    first [n] blocks of the message, then [k] more that live somewhere else
    -- in the state's buffer, or in the caller's next chunk. *)
module Spec.Poly1305.Streaming

open Hacl.Spec.Loops
open Spec.Poly1305

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"

(** Sixteen bytes that agree pointwise are the same block. *)
let block16_agree (m: Seq.seq S8.t) (sub: Seq.seq S8.t) (off soff: nat)
  : Lemma (requires off + 16 <= Seq.length m /\ soff + 16 <= Seq.length sub /\
                    (forall (j: nat). j < 16 ==>
                       Seq.index sub (soff + j) == Seq.index m (off + j)))
          (ensures block16 m off == block16 sub soff)
  = Seq.lemma_eq_intro (Seq.slice m off (off + 16)) (Seq.slice sub soff (soff + 16))

(** The fold over the first [n + k] blocks of [m] is the fold over the first
    [n], continued over [k] blocks of [sub], provided those [k] blocks are
    blocks [n .. n + k) of [m]. *)
let blocks_acc_extend (m: Seq.seq S8.t) (sub: Seq.seq S8.t) (n k: nat) (r: nat) (acc: nat)
  : Lemma (requires 16 * (n + k) <= Seq.length m /\ 16 * k <= Seq.length sub /\
                    (forall (j: nat). j < 16 * k ==>
                       Seq.index sub j == Seq.index m (n * 16 + j)))
          (ensures blocks_acc m 0 (n + k) r acc ==
                   blocks_acc sub 0 k r (blocks_acc m 0 n r acc))
  = repeati_g_split n (n + k) (bstep m 0 r) acc;
    let aux (i: nat)
      : Lemma (i < k ==>
               (forall (a: nat). shift_g n (bstep m 0 r) i a == bstep sub 0 r i a))
      = if i < k then begin
          Math.lemma_mult_le_left 16 (i + 1) k;
          Math.distributivity_add_right 16 n i;
          Math.distributivity_add_right 16 (n + i) 1;
          block16_agree m sub (16 * (n + i)) (16 * i)
        end
    in
    FStar.Classical.forall_intro aux;
    repeati_g_ext k (shift_g n (bstep m 0 r)) (bstep sub 0 r) (blocks_acc m 0 n r acc)

#pop-options

(** Nothing has been absorbed from nothing. *)
let blocks_acc_zero (m: Seq.seq S8.t) (r: nat) (acc: nat)
  : Lemma (blocks_acc m 0 0 r acc == acc)
  = repeati_g_zero (bstep m 0 r) acc
