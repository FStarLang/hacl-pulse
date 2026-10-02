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

(** [ByteEncode_d] and [ByteDecode_d] as one number.

    {!Spec.MLKEM.Encode} states both coders bit by bit, because that is how
    FIPS 203 states them: {!Spec.MLKEM.Encode.coeff_bit} reads bit
    [b mod d] of coefficient [b / d] and {!Spec.MLKEM.Encode.stream_bit}
    reads bit [pos mod 8] of byte [pos / 8].  An implementation that
    follows that shape divides by [d] twice per bit, and [d] is a
    parameter, so the divisions are real ones.  At twelve bits a key is
    three thousand divisions.

    The way out is to say what the bit string {i is}.  Packing 256
    [d]-bit values least significant first is exactly writing down the
    integer

      [ sum_j f_j 2^(d j) ]

    and a byte string read least significant first is exactly
    {!Hacl.Spec.Bytes.le_nat}.  So both coders are the identity on one
    [256 d]-bit number, and an implementation may move bits in and out of
    it in whatever chunks it likes -- in particular a byte at a time
    through a shift register, which is what {!Hacl.Impl.MLKEM.Encode}
    does, with no division anywhere.

    This module is the bridge.  {!enc_num} is the number; {!enc_bit} says
    its bits are [coeff_bit]'s, {!byte_val_num} lifts that to bytes, and
    {!byte_encode_prefix} says each byte of [byte_encode] is fixed by the
    coefficients already read.
    {!bits_val_num} is the other direction and is shorter, because
    [stream_bit] is already stated over bytes.

    Nothing here mentions [q], the NTT or any parameter set: it is
    arithmetic about radix-[2^d] and radix-256 representations of the same
    natural number. *)
module Spec.MLKEM.Pack

open Spec.MLKEM.Zq
open Spec.MLKEM.Encode
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Arithmetic}

    Four facts about division by powers of two, each stated with its
    hypotheses as parameters so that no caller has to put a [pow2] of a
    symbolic exponent and a quotient in the same query. *)

(** Adding a multiple of [2^m] does not disturb bit [p] below it. *)
let high_add_bit (x: nat) (c: nat) (p: nat) (m: nat { p < m })
  : Lemma ((x + c * pow2 m) / pow2 p % 2 == x / pow2 p % 2)
  = Math.pow2_plus p (m - p);
    Math.paren_mul_right c (pow2 p) (pow2 (m - p));
    assert (c * pow2 m == c * pow2 (m - p) * pow2 p);
    Math.lemma_div_plus x (c * pow2 (m - p)) (pow2 p);
    assert ((x + c * pow2 m) / pow2 p == x / pow2 p + c * pow2 (m - p));
    Math.pow2_double_mult (m - p - 1);
    Math.lemma_mod_plus (x / pow2 p) (c * pow2 (m - p - 1)) 2

(** Adding a multiple of [2^m] does not disturb the byte at [p] when the
    byte ends at or below [m]. *)
let high_add_byte (x: nat) (c: nat) (p: nat) (m: nat { p + 8 <= m })
  : Lemma ((x + c * pow2 m) / pow2 p % 256 == x / pow2 p % 256)
  = Math.pow2_plus p (m - p);
    Math.paren_mul_right c (pow2 p) (pow2 (m - p));
    Math.lemma_div_plus x (c * pow2 (m - p)) (pow2 p);
    Math.pow2_plus 8 (m - p - 8);
    Math.paren_mul_right c (pow2 (m - p - 8)) (pow2 8);
    Math.lemma_mod_plus (x / pow2 p) (c * pow2 (m - p - 8)) 256

(** Dropping a remainder below [2^m] and reading at or above [m]. *)
let low_drop (a: nat) (v: nat) (m: nat) (r: nat)
  : Lemma (requires a < pow2 m)
          (ensures (a + v * pow2 m) / pow2 (m + r) == v / pow2 r)
  = Math.pow2_plus m r;
    Math.division_multiplication_lemma (a + v * pow2 m) (pow2 m) (pow2 r);
    Math.lemma_div_plus a v (pow2 m);
    Math.small_div a (pow2 m)

(** The bit a masked value shows is the bit the value shows, below the
    mask. *)
let mask_bit (x: nat) (d: pos) (r: nat { r < d })
  : Lemma ((x % pow2 d) / pow2 r % 2 == x / pow2 r % 2)
  = Math.pow2_modulo_division_lemma_1 x r d;
    assert ((x % pow2 d) / pow2 r == (x / pow2 r) % pow2 (d - r));
    Math.pow2_modulo_modulo_lemma_1 (x / pow2 r) 1 (d - r)

#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"

(** {2 The number}

    [enc_num d f i] is the first [i] coefficients packed, least
    significant first, each contributing its low [d] bits.  The mask is
    not a restriction on the caller: [coeff_bit] reads only bits below
    [d] as well, so the two agree on anything, and carrying no
    precondition is what lets the implementation mask instead of
    assuming. *)
let rec enc_num (d: pos) (f: Seq.seq nat) (i: nat { i <= Seq.length f })
  : GTot nat (decreases i)
  = if i = 0 then 0
    else enc_num d f (i - 1) + (Seq.index f (i - 1) % pow2 d) * pow2 (d * (i - 1))

(** The empty packing is zero.  Stated because the implementation runs at
    [--fuel 0] and this is the one place it needs the definition. *)
let enc_num_zero (d: pos) (f: Seq.seq nat) : Lemma (enc_num d f 0 == 0) = ()

(** [i] coefficients of [d] bits occupy [d i] bits. *)
let rec enc_num_bound (d: pos) (f: Seq.seq nat) (i: nat { i <= Seq.length f })
  : Lemma (ensures enc_num d f i < pow2 (d * i)) (decreases i)
  = if i = 0 then ()
    else begin
      enc_num_bound d f (i - 1);
      let c = Seq.index f (i - 1) % pow2 d in
      Math.lemma_mult_le_right (pow2 (d * (i - 1))) c (pow2 d - 1);
      Math.distributivity_sub_left (pow2 d) 1 (pow2 (d * (i - 1)));
      Math.pow2_plus d (d * (i - 1));
      assert (d * i == d + d * (i - 1))
    end

(** What the coefficients from [a] on contribute, with [a] shifted to
    zero: [enc_num] of the whole is [enc_num] of the prefix plus
    [2^(d a)] times this. *)
let rec enc_tail (d: pos) (f: Seq.seq nat) (a: nat) (b: nat { a <= b /\ b <= Seq.length f })
  : GTot nat (decreases (b - a))
  = if b = a then 0
    else enc_tail d f a (b - 1) + (Seq.index f (b - 1) % pow2 d) * pow2 (d * (b - 1 - a))

let rec enc_num_split (d: pos) (f: Seq.seq nat) (a: nat) (b: nat { a <= b /\ b <= Seq.length f })
  : Lemma (ensures enc_num d f b == enc_num d f a + pow2 (d * a) * enc_tail d f a b)
          (decreases (b - a))
  = if b = a then ()
    else begin
      enc_num_split d f a (b - 1);
      let c = Seq.index f (b - 1) % pow2 d in
      Math.pow2_plus (d * a) (d * (b - 1 - a));
      assert (d * (b - 1) == d * a + d * (b - 1 - a));
      Math.paren_mul_right c (pow2 (d * a)) (pow2 (d * (b - 1 - a)));
      Math.distributivity_add_right (pow2 (d * a))
        (enc_tail d f a (b - 1)) (c * pow2 (d * (b - 1 - a)))
    end

#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"

(** Bit [p] of the number is {!Spec.MLKEM.Encode.coeff_bit} at [p]: the
    coefficient it falls in is [p / d] and the bit within it [p mod d].
    This is the whole content of the encoder. *)
let enc_bit (d: pos) (f: Seq.seq nat) (i: nat { i <= Seq.length f }) (p: nat { p < d * i })
  : Lemma (enc_num d f i / pow2 p % 2 ==
           (div_lt p i d; Seq.index f (p / d) / pow2 (p % d) % 2))
  = div_lt p i d;
    let i0 = p / d in
    let r = p % d in
    Math.euclidean_division_definition p d;
    assert (p == d * i0 + r);
    (* Everything from coefficient i0 + 1 on sits above bit p. *)
    enc_num_split d f (i0 + 1) i;
    Math.lemma_mult_le_right d (i0 + 1) i;
    high_add_bit (enc_num d f (i0 + 1)) (enc_tail d f (i0 + 1) i) p (d * (i0 + 1));
    (* And coefficient i0 is the one the bit is in. *)
    enc_num_bound d f i0;
    let c = Seq.index f i0 % pow2 d in
    assert (enc_num d f (i0 + 1) == enc_num d f i0 + c * pow2 (d * i0));
    low_drop (enc_num d f i0) c (d * i0) r;
    mask_bit (Seq.index f i0) d r

#pop-options

#push-options "--fuel 9 --ifuel 0 --z3rlimit 60"

(** A byte is its eight bits.  Written as a fold so that the induction is
    on the width; [byte_val] is the same sum written out, and the two meet
    at [m = 8]. *)
let rec bit_sum (x: nat) (m: nat) : GTot nat (decreases m)
  = if m = 0 then 0
    else bit_sum x (m - 1) + (x / pow2 (m - 1) % 2) * pow2 (m - 1)

let rec bit_sum_ok (x: nat) (m: nat)
  : Lemma (ensures x % pow2 m == bit_sum x m) (decreases m)
  = if m = 0 then ()
    else begin
      bit_sum_ok x (m - 1);
      Math.pow2_modulo_modulo_lemma_1 x (m - 1) m;
      Math.pow2_modulo_division_lemma_1 x (m - 1) m;
      Math.pow2_double_mult (m - 1);
      Math.euclidean_division_definition (x % pow2 m) (pow2 (m - 1));
      Math.small_div (x % pow2 m) (pow2 m)
    end

let byte_of_bits (x: nat)
  : Lemma (x % 256 == (x / 1 % 2) * 1 + (x / 2 % 2) * 2
                    + (x / 4 % 2) * 4 + (x / 8 % 2) * 8
                    + (x / 16 % 2) * 16 + (x / 32 % 2) * 32
                    + (x / 64 % 2) * 64 + (x / 128 % 2) * 128)
  = bit_sum_ok x 8;
    assert_norm (pow2 0 == 1); assert_norm (pow2 1 == 2);
    assert_norm (pow2 2 == 4); assert_norm (pow2 3 == 8);
    assert_norm (pow2 4 == 16); assert_norm (pow2 5 == 32);
    assert_norm (pow2 6 == 64); assert_norm (pow2 7 == 128);
    assert_norm (pow2 8 == 256)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Byte [i] of the packed form is byte [i] of the number. *)
let byte_val_num (d: pos { d <= 12 }) (f: Seq.lseq nat n) (i: nat { i < 32 * d })
  : Lemma (byte_val d f i == enc_num d f n / pow2 (8 * i) % 256)
  = let nm = enc_num d f n in
    let bit (p: nat { p < d * n }) : Lemma (nm / pow2 p % 2 == coeff_bit d f p)
      = enc_bit d f n p in
    assert (8 * i + 7 < d * n);
    bit (8 * i); bit (8 * i + 1); bit (8 * i + 2); bit (8 * i + 3);
    bit (8 * i + 4); bit (8 * i + 5); bit (8 * i + 6); bit (8 * i + 7);
    byte_of_bits (nm / pow2 (8 * i));
    let e (j: nat { j <= 7 })
      : Lemma (nm / pow2 (8 * i) / pow2 j == nm / pow2 (8 * i + j))
      = Math.pow2_plus (8 * i) j;
        Math.division_multiplication_lemma nm (pow2 (8 * i)) (pow2 j) in
    e 0; e 1; e 2; e 3; e 4; e 5; e 6; e 7;
    assert_norm (pow2 0 == 1); assert_norm (pow2 1 == 2);
    assert_norm (pow2 2 == 4); assert_norm (pow2 3 == 8);
    assert_norm (pow2 4 == 16); assert_norm (pow2 5 == 32);
    assert_norm (pow2 6 == 64); assert_norm (pow2 7 == 128)

(** Byte [i] of the encoding, once enough coefficients have been packed to
    reach past it.  This is the form the loop needs: it does not have the
    whole number, only the prefix it has read. *)
let byte_encode_prefix (d: pos { d <= 12 }) (f: Seq.lseq nat n)
                       (i: nat { i <= n }) (o: nat { o < 32 * d /\ 8 * o + 8 <= d * i })
  : Lemma (Seq.index (byte_encode d f) o ==
           S8.classify (U8.uint_to_t (enc_num d f i / pow2 (8 * o) % 256)))
  = byte_encode_index d f o;
    byte_val_num d f o;
    enc_num_split d f i n;
    high_add_byte (enc_num d f i) (enc_tail d f i n) (8 * o) (d * i)

#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"

(** {2 The encoder's three steps}

    The shift register holds [enc_num d f i / 2^(8 o)]: everything packed
    so far, less the bytes already written out.  [nb = d i - 8 o] bits of
    it are live.  Pushing a coefficient adds it at [nb]; flushing a byte
    divides by 256.  Nothing else happens. *)

let enc_acc_bound (d: pos) (f: Seq.seq nat) (i: nat { i <= Seq.length f })
                  (o: nat) (nb: nat { d * i == 8 * o + nb })
  : Lemma (enc_num d f i / pow2 (8 * o) < pow2 nb)
  = enc_num_bound d f i;
    Math.pow2_plus (8 * o) nb;
    Math.lemma_div_lt_nat (enc_num d f i) (d * i) (8 * o)

let enc_push (d: pos) (f: Seq.seq nat) (i: nat { i < Seq.length f })
             (o: nat) (nb: nat { d * i == 8 * o + nb })
  : Lemma (enc_num d f (i + 1) / pow2 (8 * o) ==
           enc_num d f i / pow2 (8 * o) + (Seq.index f i % pow2 d) * pow2 nb)
  = let c = Seq.index f i % pow2 d in
    Math.pow2_plus (8 * o) nb;
    Math.paren_mul_right c (pow2 nb) (pow2 (8 * o));
    Math.lemma_div_plus (enc_num d f i) (c * pow2 nb) (pow2 (8 * o))

(** There is room for the byte about to be written.  Hoisted for the same
    reason as {!enc_done}: [d * (i + 1) <= 256 d] is nonlinear, and asking
    for it inside the loop body, where [enc_num] and a quantified frame
    condition are also in scope, burns the whole rlimit. *)
let enc_room (d: pos) (i: nat { i < 256 }) (o: nat) (nb: nat)
  : Lemma (requires d * (i + 1) == 8 * o + nb /\ 8 <= nb)
          (ensures 8 * o + 8 <= 256 * d /\ o < 32 * d)
  = Math.lemma_mult_le_left d (i + 1) 256;
    Math.swap_mul d 256

(** The encoder has written every byte once it has pushed every
    coefficient.  Hoisted because the loop exits knowing only [i >= 256]
    and [i <= 256], and substituting [256] for [i] underneath [d * i] is
    the one propagation from arithmetic into congruence that Z3 will not
    make inside a Pulse body. *)
let enc_done (d: pos) (i: nat) (o: nat) (nb: nat)
  : Lemma (requires i == 256 /\ d * i == 8 * o + nb /\ nb < 8)
          (ensures o == 32 * d /\ nb == 0)
  = ()

let enc_flush (d: pos) (f: Seq.seq nat) (i: nat { i <= Seq.length f }) (o: nat)
  : Lemma (enc_num d f i / pow2 (8 * o) / 256 == enc_num d f i / pow2 (8 * (o + 1)))
  = Math.pow2_plus (8 * o) 8;
    assert_norm (pow2 8 == 256);
    Math.division_multiplication_lemma (enc_num d f i) (pow2 (8 * o)) 256

(** {2 Decoding}

    The other direction needs no new number: a byte string {i is} its
    [le_nat], so all that has to be said is that [stream_bit] and
    [bits_val] read it. *)

let stream_bit_num (b: Seq.seq S8.t) (p: nat)
  : Lemma (stream_bit b p == le_nat b / pow2 p % 2)
  = let k = p / 8 in
    let r = p % 8 in
    Math.euclidean_division_definition p 8;
    if k < Seq.length b then begin
      le_nat_byte b k;
      Math.pow2_plus (8 * k) r;
      Math.division_multiplication_lemma (le_nat b) (pow2 (8 * k)) (pow2 r);
      Math.pow2_modulo_division_lemma_1 (le_nat b / pow2 (8 * k)) r 8;
      assert_norm (pow2 8 == 256);
      Math.pow2_modulo_modulo_lemma_1 (le_nat b / pow2 (8 * k) / pow2 r) 1 (8 - r)
    end else begin
      le_nat_bound b;
      Math.pow2_le_compat p (8 * Seq.length b);
      Math.small_div (le_nat b) (pow2 p)
    end

let rec bits_val_num (b: Seq.seq S8.t) (off: nat) (m: nat)
  : Lemma (ensures bits_val b off m == le_nat b / pow2 off % pow2 m) (decreases m)
  = if m = 0 then ()
    else begin
      bits_val_num b (off + 1) (m - 1);
      stream_bit_num b off;
      let x = le_nat b / pow2 off in
      Math.pow2_plus off 1;
      Math.division_multiplication_lemma (le_nat b) (pow2 off) (pow2 1);
      assert_norm (pow2 1 == 2);
      assert (le_nat b / pow2 (off + 1) == x / 2);
      Math.pow2_modulo_modulo_lemma_1 x 1 m;
      Math.pow2_modulo_division_lemma_1 x 1 m;
      Math.euclidean_division_definition (x % pow2 m) 2;
      Math.small_div (x % pow2 m) (pow2 m)
    end

(** {2 The decoder's two steps}

    Here the register holds a window on the one number the bytes already
    are: bits [d i] up to [8 p] of [le_nat b].  Reading a byte widens the
    window at the top, taking a coefficient narrows it at the bottom. *)

let dec_read (b: Seq.seq S8.t) (off: nat) (nb: nat) (p: nat { off + nb == 8 * p })
  : Lemma (requires p < Seq.length b)
          (ensures le_nat b / pow2 off % pow2 (nb + 8) ==
                   le_nat b / pow2 off % pow2 nb +
                   S8.v (Seq.index b p) * pow2 nb)
  = let x = le_nat b / pow2 off in
    Math.pow2_modulo_modulo_lemma_1 x nb (nb + 8);
    Math.pow2_modulo_division_lemma_1 x nb (nb + 8);
    Math.euclidean_division_definition (x % pow2 (nb + 8)) (pow2 nb);
    Math.pow2_plus off nb;
    Math.division_multiplication_lemma (le_nat b) (pow2 off) (pow2 nb);
    le_nat_byte b p;
    assert_norm (pow2 8 == 256)

let dec_take (b: Seq.seq S8.t) (off: nat) (nb: nat) (d: pos { d <= nb })
  : Lemma (le_nat b / pow2 off % pow2 nb / pow2 d ==
           le_nat b / pow2 (off + d) % pow2 (nb - d))
  = let x = le_nat b / pow2 off in
    Math.pow2_modulo_division_lemma_1 x d nb;
    Math.pow2_plus off d;
    Math.division_multiplication_lemma (le_nat b) (pow2 off) (pow2 d)

let dec_val (b: Seq.seq S8.t) (off: nat) (nb: nat) (d: pos { d <= nb })
  : Lemma (le_nat b / pow2 off % pow2 nb % pow2 d == bits_val b off d)
  = Math.pow2_modulo_modulo_lemma_1 (le_nat b / pow2 off) d nb;
    bits_val_num b off d

#pop-options

(** The decoder's read pointer is in range.  Hoisted for the same reason as
    {!enc_room}. *)
let dec_room (d: pos) (i: nat { i < 256 }) (p: nat) (nb: nat)
  : Lemma (requires 8 * p == d * i + nb /\ nb < d)
          (ensures p < 32 * d)
  = Math.lemma_mult_le_left d (i + 1) 256;
    Math.swap_mul d 256
