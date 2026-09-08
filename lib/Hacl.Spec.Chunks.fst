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

(** Sequence facts an incremental hash needs.

    Every streaming construction here keeps the same three pieces of state --
    an accumulator, a partial block of buffered bytes, and a length -- and
    every one of them has to relate the buffer and the caller's data to the
    ghost message seen so far.  Those relations are pure sequence facts, they
    do not mention the algorithm, and they are stated here once.

    They are stated *outside* Pulse deliberately: the E-matching needed for
    [Seq.append] and for a multiplication by the block length does not survive
    the size of a Pulse verification condition, so each one is proved in
    isolation and then used as a single instantiated fact. *)
module Hacl.Spec.Chunks

module Seq = FStar.Seq
module Classical = FStar.Classical

(** Splitting a sequence in three and re-appending is the identity. *)
let split3 (#a: Type) (s: Seq.seq a) (i: nat) (j: nat)
  : Lemma (requires i <= j /\ j <= Seq.length s)
          (ensures Seq.append (Seq.slice s 0 i)
                     (Seq.append (Seq.slice s i j) (Seq.slice s j (Seq.length s))) == s)
  = Seq.lemma_eq_elim (Seq.append (Seq.slice s 0 i)
                        (Seq.append (Seq.slice s i j) (Seq.slice s j (Seq.length s)))) s

let index_append_agrees (#a: Type) (s1 s2: Seq.seq a) (i: nat)
  : Lemma (requires i < Seq.length s1 + Seq.length s2)
          (ensures Seq.index (Seq.append s1 s2) i ==
                   (if i < Seq.length s1 then Seq.index s1 i
                    else Seq.index s2 (i - Seq.length s1)))
  = if i < Seq.length s1 then Seq.lemma_index_app1 s1 s2 i
    else Seq.lemma_index_app2 s1 s2 i

(** After copying [fill] bytes of [vdata] into [vbuf] at offset [blen], the
    first [blen + fill] bytes of the buffer are block [nb0] of [seen ++ vdata]. *)
let buf_agrees (#a: Type) (bl: pos) (seen vdata vbuf vbuf': Seq.seq a)
               (nb0 blen fill: nat)
  : Lemma (requires
      Seq.length seen == nb0 * bl + blen /\
      blen + fill <= Seq.length vbuf' /\ blen <= Seq.length vbuf /\ fill <= Seq.length vdata /\
      (forall (k: nat). k < blen ==> Seq.index vbuf' k == Seq.index vbuf k) /\
      (forall (k: nat). k < fill ==> Seq.index vbuf' (blen + k) == Seq.index vdata k) /\
      (forall (k: nat). k < blen ==> Seq.index vbuf k == Seq.index seen (nb0 * bl + k)))
    (ensures forall (k: nat). k < blen + fill ==>
       Seq.index vbuf' k == Seq.index (Seq.append seen vdata) (nb0 * bl + k))
  = let aux (k: nat{k < blen + fill})
      : Lemma (Seq.index vbuf' k == Seq.index (Seq.append seen vdata) (nb0 * bl + k))
      = index_append_agrees seen vdata (nb0 * bl + k)
    in Classical.forall_intro aux

(** The buffer holds exactly the bytes of [seen] past its last whole block. *)
let buf_is_tail (#a: Type) (bl: pos) (seen vbuf: Seq.seq a) (nb0 blen: nat)
  : Lemma (requires Seq.length seen == nb0 * bl + blen /\ blen <= Seq.length vbuf /\
                    (forall (k: nat). k < blen ==>
                       Seq.index vbuf k == Seq.index seen (nb0 * bl + k)))
          (ensures Seq.append (Seq.slice seen 0 (nb0 * bl)) (Seq.slice vbuf 0 blen) == seen)
  = Seq.lemma_eq_elim
      (Seq.append (Seq.slice seen 0 (nb0 * bl)) (Seq.slice vbuf 0 blen)) seen

(** Block [nb1] of [seen ++ vdata] onwards lives at offset [off] of [vdata],
    provided the first [nb1] blocks are exactly [seen] followed by [off] bytes. *)
let tail_agrees (#a: Type) (bl: pos) (seen vdata: Seq.seq a) (nb1 off n: nat)
  : Lemma (requires nb1 * bl == Seq.length seen + off /\ off + n <= Seq.length vdata)
          (ensures forall (k: nat). k < n ==>
             Seq.index vdata (off + k) ==
             Seq.index (Seq.append seen vdata) (nb1 * bl + k))
  = let aux (k: nat{k < n})
      : Lemma (Seq.index vdata (off + k) ==
               Seq.index (Seq.append seen vdata) (nb1 * bl + k))
      = index_append_agrees seen vdata (nb1 * bl + k)
    in Classical.forall_intro aux
