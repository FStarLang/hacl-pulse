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

(** HKDF, RFC 5869: extract-then-expand key derivation over HMAC.

    [extract salt ikm] is just [HMAC(salt, ikm)].  [expand prk info len] is the
    first [len] bytes of [T(1) || T(2) || ...], where

      [T(0) = <>]  and  [T(i) = HMAC(prk, T(i-1) || info || i)].

    The counter [i] is a single byte, which is what bounds the output to
    [255 * hash_bytes] and is why [expand_t] is indexed by an [i < 256]. *)
module Spec.HKDF

open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC

module Seq = FStar.Seq
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

(** {2 Extract} *)

let extract (#t: Type0) {| word t |} (p: params t)
            (salt: Seq.seq S8.t { Seq.length salt < max_input #t })
            (ikm: Seq.seq S8.t { block_len #t + Seq.length ikm < max_input #t })
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = hmac p salt ikm

(** {2 Expand} *)

(** The message hashed at each round is one digest, the info string, and one
    counter byte; this says it is short enough to hash. *)
unfold let info_ok (#t: Type0) {| word t |} (p: params t) (info: Seq.seq S8.t) =
  block_len #t + (hash_bytes p) + Seq.length info + 1 < max_input #t

unfold let prk_ok (#t: Type0) {| word t |} (p: params t) (prk: Seq.seq S8.t) =
  Seq.length prk < max_input #t

let counter (i: nat { 0 < i /\ i < 256 }) : Seq.lseq S8.t 1 =
  Seq.create 1 (S8.classify (U8.uint_to_t i))

let rec expand_t (#t: Type0) {| word t |} (p: params t)
                 (prk: Seq.seq S8.t { prk_ok p prk })
                 (info: Seq.seq S8.t { info_ok p info })
                 (i: nat { i < 256 })
  : GTot (r: Seq.seq S8.t { Seq.length r == (if i = 0 then 0 else hash_bytes p) })
        (decreases i)
  = if i = 0
    then Seq.empty
    else
      let prev = expand_t p prk info (i - 1) in
      hmac p prk (Seq.append (Seq.append prev info) (counter i))

(** [T(1) || ... || T(n)]. *)
let rec expand_all (#t: Type0) {| word t |} (p: params t)
                   (prk: Seq.seq S8.t { prk_ok p prk })
                   (info: Seq.seq S8.t { info_ok p info })
                   (n: nat { n < 256 })
  : GTot (r: Seq.seq S8.t { Seq.length r == n * (hash_bytes p) }) (decreases n)
  = if n = 0
    then Seq.empty
    else begin
      Math.distributivity_add_left (n - 1) 1 (hash_bytes p);
      Seq.append (expand_all p prk info (n - 1)) (expand_t p prk info n)
    end

(** How many rounds [len] bytes of output take, and the fact that they suffice. *)
let nrounds (#t: Type0) {| word t |} (p: params t)
            (len: nat { len <= 255 * (hash_bytes p) })
  : n: nat { n < 256 /\ len <= n * (hash_bytes p) } =
  let hb = hash_bytes p in
  let n = (len + hb - 1) / hb in
  Math.lemma_div_le (len + hb - 1) (255 * hb + hb - 1) hb;
  Math.division_addition_lemma (hb - 1) hb 255;
  Math.euclidean_division_definition (len + hb - 1) hb;
  Math.lemma_mod_lt (len + hb - 1) hb;
  n

let expand (#t: Type0) {| word t |} (p: params t)
           (prk: Seq.seq S8.t { prk_ok p prk })
           (info: Seq.seq S8.t { info_ok p info })
           (len: nat { len <= 255 * (hash_bytes p) })
  : GTot (Seq.lseq S8.t len)
  = Seq.slice (expand_all p prk info (nrounds p len)) 0 len

(** {2 Lemmas for the implementation}

    The implementation writes [T(i)] into the output one round at a time and
    never materializes [expand_all]; these are the two facts that let its loop
    invariant be stated pointwise against the specification. *)

let expand_all_index_prev (#t: Type0) {| word t |} (p: params t)
                          (prk: Seq.seq S8.t { prk_ok p prk })
                          (info: Seq.seq S8.t { info_ok p info })
                          (n: nat { 0 < n /\ n < 256 })
  : Lemma (forall (k: nat). k < (n - 1) * (hash_bytes p) ==>
             Seq.index (expand_all p prk info n) k ==
             Seq.index (expand_all p prk info (n - 1)) k)
  = let prev = expand_all p prk info (n - 1) in
    let last = expand_t p prk info n in
    let aux (k: nat { k < (n - 1) * (hash_bytes p) })
      : Lemma (Seq.index (expand_all p prk info n) k == Seq.index prev k)
      = Seq.lemma_index_app1 prev last k
    in
    FStar.Classical.forall_intro aux

let expand_all_index_last (#t: Type0) {| word t |} (p: params t)
                          (prk: Seq.seq S8.t { prk_ok p prk })
                          (info: Seq.seq S8.t { info_ok p info })
                          (n: nat { 0 < n /\ n < 256 })
  : Lemma (forall (k: nat). k < (hash_bytes p) ==>
             Seq.index (expand_all p prk info n) ((n - 1) * (hash_bytes p) + k) ==
             Seq.index (expand_t p prk info n) k)
  = let prev = expand_all p prk info (n - 1) in
    let last = expand_t p prk info n in
    let aux (k: nat { k < (hash_bytes p) })
      : Lemma (Seq.index (expand_all p prk info n) ((n - 1) * (hash_bytes p) + k) ==
               Seq.index last k)
      = Seq.lemma_index_app2 prev last ((n - 1) * (hash_bytes p) + k)
    in
    FStar.Classical.forall_intro aux

(** The message of round [i], as the implementation lays it out in memory: one
    digest, the info string, and the counter byte. *)
let round_msg_pointwise (#t: Type0) {| word t |}
                        (m: Seq.seq S8.t) (prev: Seq.seq S8.t) (info: Seq.seq S8.t)
                        (i: nat { 0 < i /\ i < 256 })
  : Lemma (requires
             Seq.length m == Seq.length prev + Seq.length info + 1 /\
             (forall (k: nat). k < Seq.length prev ==> Seq.index m k == Seq.index prev k) /\
             (forall (k: nat). k < Seq.length info ==>
                Seq.index m (Seq.length prev + k) == Seq.index info k) /\
             Seq.index m (Seq.length prev + Seq.length info) ==
               S8.classify (U8.uint_to_t i))
          (ensures m == Seq.append (Seq.append prev info) (counter i))
  = let l = Seq.append prev info in
    let r = Seq.append l (counter i) in
    let aux (k: nat { k < Seq.length m }) : Lemma (Seq.index m k == Seq.index r k)
      = if k < Seq.length l
        then begin
          Seq.lemma_index_app1 l (counter i) k;
          if k < Seq.length prev
          then Seq.lemma_index_app1 prev info k
          else Seq.lemma_index_app2 prev info k
        end
        else Seq.lemma_index_app2 l (counter i) k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro m r
