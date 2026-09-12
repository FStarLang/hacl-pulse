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
module Classical = FStar.Classical
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

(** Decoding undoes encoding.  ECDSA needs it: the x-coordinate leaves the
    field as bytes and comes back as a scalar, and without this the two
    numbers are unrelated. *)
let rec be_nat_to_be (n: nat) (x: nat)
  : Lemma (requires x < pow2 (8 * n))
          (ensures be_nat (nat_to_be n x) == x)
          (decreases n)
  = if n = 0 then assert_norm (pow2 0 == 1)
    else begin
      assert_norm (pow2 8 == 256);
      Math.pow2_plus (8 * (n - 1)) 8;
      let s = nat_to_be n x in
      let t = nat_to_be (n - 1) (x / 256) in
      let aux (i: nat { i < n - 1 })
        : Lemma (Seq.index (Seq.slice s 0 (n - 1)) i == Seq.index t i)
        = Math.pow2_plus (8 * (n - 2 - i)) 8;
          Math.division_multiplication_lemma x 256 (pow2 (8 * (n - 2 - i)))
      in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro (Seq.slice s 0 (n - 1)) t;
      be_nat_to_be (n - 1) (x / 256);
      nat_to_be_index n x (n - 1);
      assert_norm (pow2 0 == 1);
      Math.euclidean_division_definition x 256
    end

(** The parity of a big-endian number is the parity of its last byte.  The
    SEC1 compressed forms are a bit of [y], and this is what connects that
    bit to the byte a program actually reads. *)
let be_nat_parity (s: Seq.seq S8.t { 0 < Seq.length s })
  : Lemma (be_nat s % 2 == S8.v (Seq.index s (Seq.length s - 1)) % 2)
  = let n = Seq.length s in
    be_nat_snoc s (n - 1);
    Seq.lemma_eq_intro (Seq.slice s 0 n) s;
    Math.lemma_mod_plus (S8.v (Seq.index s (n - 1))) (be_nat (Seq.slice s 0 (n - 1)) * 128) 2

let nat_to_be_parity (n: pos) (x: nat)
  : Lemma (S8.v (Seq.index (nat_to_be n x) (n - 1)) % 2 == x % 2)
  = nat_to_be_index n x (n - 1);
    assert_norm (pow2 0 == 1);
    Math.modulo_modulo_lemma x 2 128

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

(** {2 The same, little end first}

    BLAKE2 reads and writes its words little-endian.  Rather than reuse the
    big-endian machinery over a reversed sequence -- which would put a
    reversal in every trigger -- the four definitions are repeated with the
    byte order flipped.  They are short, and keeping them separate means a
    goal about one never wakes up a lemma about the other.

    The recursion peels the *first* byte, because that is the step a machine
    loop takes: it reads the bytes from the top down, so after reading indices
    [n-1] down to [j] the accumulator holds [le_nat (Seq.slice s j n)], and one
    more iteration multiplies by 256 and adds byte [j-1]. *)

let rec le_nat (s: Seq.seq S8.t) : GTot nat (decreases Seq.length s) =
  let n = Seq.length s in
  if n = 0 then 0
  else S8.v (Seq.index s 0) + 256 * le_nat (Seq.slice s 1 n)

let rec le_nat_bound (s: Seq.seq S8.t)
  : Lemma (ensures le_nat s < pow2 (8 * Seq.length s)) (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      le_nat_bound (Seq.slice s 1 n);
      Math.pow2_plus 8 (8 * (n - 1))
    end

(** One step of a top-down accumulation: the suffix from [j] is the byte at
    [j] plus 256 times the suffix from [j + 1]. *)
let le_nat_cons (s: Seq.seq S8.t) (j: nat { j < Seq.length s })
  : Lemma (le_nat (Seq.slice s j (Seq.length s)) ==
           S8.v (Seq.index s j) + 256 * le_nat (Seq.slice s (j + 1) (Seq.length s)))
  = let n = Seq.length s in
    Seq.lemma_eq_intro (Seq.slice (Seq.slice s j n) 1 (n - j)) (Seq.slice s (j + 1) n)

(** Cutting a little-endian number in two.  The low [k] bytes are the low
    [8k] bits, so the value is the prefix plus [2^(8k)] times the suffix.
    This is what turns two sixty-four-bit loads into one hundred-and-twenty-
    eight-bit number, and what says a zero-padded block with a one byte
    appended is worth [le_nat] of the block plus [2^(8*len)]. *)
let rec le_nat_split (s: Seq.seq S8.t) (k: nat { k <= Seq.length s })
  : Lemma (ensures le_nat s == le_nat (Seq.slice s 0 k) +
                               pow2 (8 * k) * le_nat (Seq.slice s k (Seq.length s)))
          (decreases k)
  = let n = Seq.length s in
    if k = 0 then Seq.lemma_eq_intro (Seq.slice s 0 n) s
    else begin
      let t = Seq.slice s 1 n in
      let p = Seq.slice s 0 k in
      le_nat_split t (k - 1);
      Seq.lemma_eq_intro (Seq.slice t 0 (k - 1)) (Seq.slice p 1 k);
      Seq.lemma_eq_intro (Seq.slice t (k - 1) (n - 1)) (Seq.slice s k n);
      assert (le_nat p == S8.v (Seq.index s 0) + 256 * le_nat (Seq.slice t 0 (k - 1)));
      assert (le_nat s == S8.v (Seq.index s 0) + 256 * le_nat t);
      Math.pow2_plus 8 (8 * (k - 1));
      Math.paren_mul_right 256 (pow2 (8 * (k - 1))) (le_nat (Seq.slice s k n))
    end

(** An all-zero sequence is zero. *)
let rec le_nat_zeros (s: Seq.seq S8.t)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> S8.v (Seq.index s i) == 0)
          (ensures le_nat s == 0)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      assert (forall (i: nat). i < n - 1 ==> Seq.index (Seq.slice s 1 n) i == Seq.index s (i + 1));
      le_nat_zeros (Seq.slice s 1 n)
    end

(** A one followed by zeros is one: the pad byte a short Poly1305 block gets. *)
let le_nat_one_zeros (s: Seq.seq S8.t)
  : Lemma (requires 0 < Seq.length s /\ S8.v (Seq.index s 0) == 1 /\
                    (forall (i: nat). 0 < i /\ i < Seq.length s ==>
                       S8.v (Seq.index s i) == 0))
          (ensures le_nat s == 1)
  = let n = Seq.length s in
    assert (forall (i: nat). i < n - 1 ==> Seq.index (Seq.slice s 1 n) i == Seq.index s (i + 1));
    le_nat_zeros (Seq.slice s 1 n)

let byte_of_nat_le (n: nat) (x: nat) (i: nat { i < n }) : S8.t =
  S8.classify (U8.uint_to_t ((x / pow2 (8 * i)) % 256))

let nat_to_le (n: nat) (x: nat) : Seq.lseq S8.t n =
  Seq.init n (byte_of_nat_le n x)

let nat_to_le_index (n: nat) (x: nat) (i: nat { i < n })
  : Lemma (S8.v (Seq.index (nat_to_le n x) i) == (x / pow2 (8 * i)) % 256)
  = ()

let word_from_le (#t: Type0) {| word t |} (s: Seq.lseq S8.t (bytes #t)) : GTot t =
  le_nat_bound s;
  of_v (le_nat s)

let word_to_le (#t: Type0) {| word t |} (x: t) : GTot (Seq.lseq S8.t (bytes #t)) =
  nat_to_le (bytes #t) (v x)

let words_from_le (#t: Type0) {| word t |} (n: nat) (s: Seq.lseq S8.t (n * bytes #t))
  : GTot (Seq.lseq t n)
  = Seq.init_ghost n (fun i -> word_from_le (sub_block n s i))

let words_to_le (#t: Type0) {| word t |} (n: nat) (ws: Seq.lseq t n)
  : GTot (Seq.lseq S8.t (n * bytes #t))
  = Seq.init_ghost (n * bytes #t)
      (fun i -> Seq.index (word_to_le (Seq.index ws (i / bytes #t))) (i % bytes #t))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let digest_step_le (#t: Type0) {| w: word t |} (n: nat) (ws: Seq.lseq t n) (j: nat { j < n })
                   (o: nat) (vd: Seq.seq S8.t)
  : Lemma
      (requires
        o == j * bytes #t /\ Seq.length vd == n * bytes #t /\
        o + bytes #t <= Seq.length vd /\
        (forall (i: nat). i < o ==> Seq.index vd i == Seq.index (words_to_le n ws) i) /\
        (forall (k: nat). k < bytes #t ==>
           S8.v (Seq.index vd (o + k)) == (v (Seq.index ws j) / pow2 (8 * k)) % 256))
      (ensures
        (forall (i: nat). i < o + bytes #t ==> Seq.index vd i == Seq.index (words_to_le n ws) i))
  = let nb = bytes #t in
    let aux (i: nat { i < o + nb })
      : Lemma (Seq.index vd i == Seq.index (words_to_le n ws) i)
      = if i < o then ()
        else begin
          let k : nat = i - o in
          Math.lemma_div_plus k j nb;
          Math.small_div k nb;
          Math.lemma_mod_plus k j nb;
          Math.small_mod k nb;
          assert (i / nb == j);
          assert (i % nb == k);
          nat_to_le_index nb (v (Seq.index ws j)) k
        end
    in
    FStar.Classical.forall_intro aux

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** Which of two sixty-four-bit words a byte of the hundred-and-twenty-eight
    bit number comes from.  This is what lets a sixteen-byte little-endian
    store be two [store_le]s: below eight the byte is a byte of the low word,
    at eight and above it is a byte of the high one. *)
let le_bytes_split (lo hi: nat) (k: nat)
  : Lemma (requires lo < pow2 64 /\ hi < pow2 64 /\ k < 16)
          (ensures (let n = lo + pow2 64 * hi in
                    ((n / pow2 (8 * k)) % 256 ==
                       (if k < 8 then (lo / pow2 (8 * k)) % 256
                                 else (hi / pow2 (8 * (k - 8))) % 256))))
  = let n = lo + pow2 64 * hi in
    if k < 8 then begin
      Math.pow2_plus (8 * k) (64 - 8 * k);
      Math.paren_mul_right (pow2 (8 * k)) (pow2 (64 - 8 * k)) hi;
      Math.lemma_div_plus lo (pow2 (64 - 8 * k) * hi) (pow2 (8 * k));
      Math.pow2_plus 8 (56 - 8 * k);
      Math.paren_mul_right (pow2 8) (pow2 (56 - 8 * k)) hi;
      assert_norm (pow2 8 == 256);
      Math.lemma_mod_plus (lo / pow2 (8 * k)) (pow2 (56 - 8 * k) * hi) 256
    end else begin
      Math.pow2_plus 64 (8 * (k - 8));
      Math.division_multiplication_lemma n (pow2 64) (pow2 (8 * (k - 8)));
      Math.lemma_div_plus lo hi (pow2 64);
      Math.small_division_lemma_1 lo (pow2 64)
    end

#pop-options
