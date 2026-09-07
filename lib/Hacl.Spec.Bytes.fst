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

(** Big-endian conversion between secret bytes and secret machine words.

    Specifications here are arithmetic on [nat]: the number a byte string
    denotes, and the byte string a number denotes.  Nothing is phrased with
    shifts or masks, so the SMT solver sees ordinary division and
    multiplication and the correspondence with the machine code is one lemma
    per loop step rather than a bit-level argument.
    [Hacl.Secret.Word.of_v] is what makes this possible: a word is determined
    by, and determines, its value.

    [be_nat] recurses on the *last* byte, matching the shape of a loop that
    scans left to right accumulating [acc * 256 + b]. *)
module Hacl.Spec.Bytes

open Hacl.Secret.Word

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module UInt = FStar.UInt
module S8 = Hacl.Secret.UInt8

(** {2 Bytes as numbers} *)

let rec be_nat (s: Seq.seq S8.t) : GTot nat (decreases Seq.length s) =
  let n = Seq.length s in
  if n = 0 then 0
  else be_nat (Seq.slice s 0 (n - 1)) * 256 + S8.v (Seq.index s (n - 1))

let rec be_nat_bound (s: Seq.seq S8.t)
  : Lemma (ensures be_nat s < pow2 (8 * Seq.length s)) (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      be_nat_bound (Seq.slice s 0 (n - 1));
      Math.pow2_plus (8 * (n - 1)) 8
    end

(** Extending a byte string on the right shifts its value up by one byte.
    This is the equation a left-to-right accumulation loop needs. *)
let be_nat_snoc (s: Seq.seq S8.t) (j: nat { j < Seq.length s })
  : Lemma (be_nat (Seq.slice s 0 (j + 1)) == be_nat (Seq.slice s 0 j) * 256 + S8.v (Seq.index s j))
  = Seq.lemma_eq_intro (Seq.slice (Seq.slice s 0 (j + 1)) 0 j) (Seq.slice s 0 j)

(** {2 Numbers as bytes} *)

let byte_of_nat (n: nat) (x: nat) (i: nat { i < n }) : S8.t =
  S8.classify (U8.uint_to_t ((x / pow2 (8 * (n - 1 - i))) % 256))

let nat_to_be (n: nat) (x: nat) : Seq.lseq S8.t n =
  Seq.init n (byte_of_nat n x)

let nat_to_be_index (n: nat) (x: nat) (i: nat { i < n })
  : Lemma (S8.v (Seq.index (nat_to_be n x) i) == (x / pow2 (8 * (n - 1 - i))) % 256)
  = ()

(** {2 Words} *)

let word_from_be (#t: Type0) {| word t |} (s: Seq.lseq S8.t (bytes #t)) : GTot t =
  be_nat_bound s;
  of_v (be_nat s)

let word_to_be (#t: Type0) {| word t |} (x: t) : GTot (Seq.lseq S8.t (bytes #t)) =
  nat_to_be (bytes #t) (v x)

(** {2 Blocks of words} *)

let sub_block (#t: Type0) {| word t |} (n: nat) (s: Seq.lseq S8.t (n * bytes #t)) (i: nat { i < n })
  : Seq.lseq S8.t (bytes #t)
  = Math.lemma_mult_le_right (bytes #t) (i + 1) n;
    Seq.slice s (i * bytes #t) (i * bytes #t + bytes #t)

let words_from_be (#t: Type0) {| word t |} (n: nat) (s: Seq.lseq S8.t (n * bytes #t))
  : GTot (Seq.lseq t n)
  = Seq.init_ghost n (fun i -> word_from_be (sub_block n s i))

let words_to_be (#t: Type0) {| word t |} (n: nat) (ws: Seq.lseq t n)
  : GTot (Seq.lseq S8.t (n * bytes #t))
  = Seq.init_ghost (n * bytes #t)
      (fun i -> Seq.index (word_to_be (Seq.index ws (i / bytes #t))) (i % bytes #t))

(** {2 The two step lemmas the machine loops need}

    Loading shifts the accumulator up by a byte and drops the new byte in; the
    two do not overlap, so the [logor] is an addition.  Storing peels the low
    byte off and divides. *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"

let load_step (#t: Type0) {| w: word t |} (a: t) (b: S8.t)
  : Lemma (requires v a * 256 < pow2 (bits #t))
          (ensures v (logor #t (shift_left a 8ul) (of_byte b)) == v a * 256 + S8.v b)
  = let h : t = w.shift_left a 8ul in
    Math.small_mod (v a * pow2 8) (pow2 (bits #t));
    assert (v h == v a * 256);
    Math.multiple_modulo_lemma (v a) (pow2 8);
    Math.pow2_le_compat (bits #t) 8;
    UInt.logor_disjoint #(bits #t) (v h) (S8.v b) 8

let store_step (#t: Type0) {| w: word t |} (x: t) (c: t) (k: nat)
  : Lemma (requires v c == v x / pow2 (8 * k))
          (ensures v (shift_right #t c 8ul) == v x / pow2 (8 * (k + 1)))
  = Math.pow2_plus (8 * k) 8;
    Math.division_multiplication_lemma (v x) (pow2 (8 * k)) (pow2 8)

#pop-options

(** {2 Writing a state out word by word}

    One step of the loop that serializes [n] words: the bytes below [j * bytes]
    are already final and [store_be] has just filled the [bytes] that follow. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let digest_step (#t: Type0) {| w: word t |} (n: nat) (ws: Seq.lseq t n) (j: nat { j < n })
                (o: nat) (vd: Seq.seq S8.t)
  : Lemma
      (requires
        o == j * bytes #t /\ Seq.length vd == n * bytes #t /\
        o + bytes #t <= Seq.length vd /\
        (forall (i: nat). i < o ==> Seq.index vd i == Seq.index (words_to_be n ws) i) /\
        (forall (k: nat). k < bytes #t ==>
           S8.v (Seq.index vd (o + k)) ==
             (v (Seq.index ws j) / pow2 (8 * (bytes #t - 1 - k))) % 256))
      (ensures
        (forall (i: nat). i < o + bytes #t ==> Seq.index vd i == Seq.index (words_to_be n ws) i))
  = let nb = bytes #t in
    let aux (i: nat { i < o + nb })
      : Lemma (Seq.index vd i == Seq.index (words_to_be n ws) i)
      = if i < o then ()
        else begin
          let k : nat = i - o in
          Math.lemma_div_plus k j nb;
          Math.small_div k nb;
          Math.lemma_mod_plus k j nb;
          Math.small_mod k nb;
          assert (i / nb == j);
          assert (i % nb == k);
          nat_to_be_index nb (v (Seq.index ws j)) k;
          assert (S8.v (Seq.index vd (o + k)) ==
                  (v (Seq.index ws j) / pow2 (8 * (nb - 1 - k))) % 256)
        end
    in
    FStar.Classical.forall_intro aux

#pop-options
