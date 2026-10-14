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

(** The arithmetic behind the radix-2^64 X25519 field.

    An element is four words, any value below [2^256], and stands for its
    residue mod [p = 2^255 - 19].  Nothing is kept reduced between
    operations: every result is merely below [2^256], and the one fact that
    makes that enough is [2^256 = 2 p + 38], so a carry out of the top word
    is worth thirty-eight at the bottom ({!fold38}).

    The powers of the radix are numerals, not [pow2 (64 * k)].  With
    numerals a carry chain -- [s_i + 2^64 c_(i+1) = a_i + b_i + c_i], four
    times -- is linear arithmetic, and Z3 sums it without help.  So the
    lemmas here are only the nonlinear steps: a row of a schoolbook product
    ({!row}), adding a row into the accumulator ({!acc}), the square's
    identity ({!sq_identity}), and the bounds that say a top word does not
    overflow. *)
module Spec.Curve25519.Field64

open FStar.Tactics.V2
open FStar.Tactics.CanonCommSemiring

module Math = FStar.Math.Lemmas
module C = Spec.Curve25519

unfold let w  : pos = 18446744073709551616
unfold let w2 : pos = 340282366920938463463374607431768211456
unfold let w3 : pos = 6277101735386680763835789423207666416102355444464034512896
unfold let w4 : pos = 115792089237316195423570985008687907853269984665640564039457584007913129639936
unfold let w5 : pos = 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576
unfold let w6 : pos = 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816
unfold let w7 : pos = 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656

unfold let w8 : pos = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096

(** [(2^64 - 1) * (2^256 - 1)], the largest one row can be. *)
unfold let rowmax : pos = 2135987035920910082279229616932235919179133537347964862093771623156579161741164519270975247745025

unfold let ev4 (a0 a1 a2 a3: int) : int = a0 + w * a1 + w2 * a2 + w3 * a3

let consts (_: unit)
  : Lemma (pow2 64 == w /\ Spec.Bignum.base == w /\
           C.prime == 57896044618658097711785492504343953926634992332820282019728792003956564819949 /\
           pow2 255 == 57896044618658097711785492504343953926634992332820282019728792003956564819968 /\
           pow2 63 == 9223372036854775808)
  = assert_norm (pow2 64 == w);
    assert_norm (pow2 63 == 9223372036854775808);
    assert_norm (pow2 255 == 57896044618658097711785492504343953926634992332820282019728792003956564819968);
    assert_norm (C.prime == 57896044618658097711785492504343953926634992332820282019728792003956564819949)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** [2^256 = 2 p + 38]. *)
let fold38 (x k: int) : Lemma ((x + w4 * k) % C.prime == (x + 38 * k) % C.prime)
  = consts ();
    Math.lemma_mod_plus (x + 38 * k) (2 * k) C.prime

let prod_lt (x y: nat) (xm ym: pos)
  : Lemma (requires x < xm /\ y < ym) (ensures x * y < xm * ym)
  = Math.lemma_mult_le_right y x xm;
    Math.lemma_mult_lt_left xm y ym

(** The field operations' specifications, restated on representatives. *)
let fadd_ok (x y: int)
  : Lemma (C.fadd (x % C.prime) (y % C.prime) == (x + y) % C.prime)
  = Math.lemma_mod_plus_distr_l x (y % C.prime) C.prime;
    Math.lemma_mod_plus_distr_r x y C.prime

let fsub_ok (x y: int)
  : Lemma (C.fsub (x % C.prime) (y % C.prime) == (x - y) % C.prime)
  = Math.lemma_mod_plus_distr_l x (C.prime - y % C.prime) C.prime;
    Math.lemma_mod_sub_distr (x + C.prime) y C.prime;
    Math.lemma_mod_plus (x - y) 1 C.prime

let fmul_ok (x y: int)
  : Lemma (C.fmul (x % C.prime) (y % C.prime) == (x * y) % C.prime)
  = Math.lemma_mod_mul_distr_l x (y % C.prime) C.prime;
    Math.lemma_mod_mul_distr_r x y C.prime

(** {2 Products} *)

let distr4 (x b0 b1 b2 b3: int)
  : Lemma (x * ev4 b0 b1 b2 b3 == x * b0 + w * (x * b1) + w2 * (x * b2) + w3 * (x * b3))
  = Math.distributivity_add_right x b0 (w * b1 + w2 * b2 + w3 * b3);
    Math.distributivity_add_right x (w * b1) (w2 * b2 + w3 * b3);
    Math.distributivity_add_right x (w2 * b2) (w3 * b3);
    Math.paren_mul_right x w b1;
    Math.paren_mul_right x w2 b2;
    Math.paren_mul_right x w3 b3;
    Math.swap_mul x w;
    Math.swap_mul x w2;
    Math.swap_mul x w3;
    Math.paren_mul_right w x b1;
    Math.paren_mul_right w2 x b2;
    Math.paren_mul_right w3 x b3

(** One row of the schoolbook product: [x] times the four words of [b], the
    sixteen half-products chained into five words.  The fifth, [h3 + c3],
    is at most [x]: the row is below [x * 2^256]. *)
let row (x b0 b1 b2 b3 l0 h0 l1 h1 l2 h2 l3 h3 r1 r2 r3 c1 c2 c3: nat)
  : Lemma (requires x < w /\ b0 < w /\ b1 < w /\ b2 < w /\ b3 < w /\
                    l0 + w * h0 == x * b0 /\ l1 + w * h1 == x * b1 /\
                    l2 + w * h2 == x * b2 /\ l3 + w * h3 == x * b3 /\
                    r1 + w * c1 == l1 + h0 /\
                    r2 + w * c2 == l2 + h1 + c1 /\
                    r3 + w * c3 == l3 + h2 + c2)
          (ensures h3 + c3 <= x /\ h3 + c3 < w /\ x * ev4 b0 b1 b2 b3 <= rowmax /\
                   ev4 l0 r1 r2 r3 + w4 * (h3 + c3) == x * ev4 b0 b1 b2 b3)
  = distr4 x b0 b1 b2 b3;
    Math.lemma_mult_le_left x (ev4 b0 b1 b2 b3) (w4 - 1);
    Math.lemma_mult_le_right (w4 - 1) x (w - 1)

(** The four rows of a product, each added into the accumulator at its
    offset, make the product.  Row [k] reads the four words the rows before
    it left at [k .. k+3] and leaves five at [k .. k+4]. *)
let mul_combine (a0 a1 a2 a3 bb: nat)
                (u0 u1 u2 u3 u4 v1 v2 v3 v4 v5 x2 x3 x4 x5 x6 y3 y4 y5 y6 y7: int)
  : Lemma (requires ev4 u0 u1 u2 u3 + w4 * u4 == a0 * bb /\
                    ev4 v1 v2 v3 v4 + w4 * v5 == ev4 u1 u2 u3 u4 + a1 * bb /\
                    ev4 x2 x3 x4 x5 + w4 * x6 == ev4 v2 v3 v4 v5 + a2 * bb /\
                    ev4 y3 y4 y5 y6 + w4 * y7 == ev4 x3 x4 x5 x6 + a3 * bb)
          (ensures ev4 u0 v1 x2 y3 + w4 * ev4 y4 y5 y6 y7 == ev4 a0 a1 a2 a3 * bb)
  = Math.distributivity_add_left a0 (w * a1 + w2 * a2 + w3 * a3) bb;
    Math.distributivity_add_left (w * a1) (w2 * a2 + w3 * a3) bb;
    Math.distributivity_add_left (w2 * a2) (w3 * a3) bb;
    Math.paren_mul_right w a1 bb;
    Math.paren_mul_right w2 a2 bb;
    Math.paren_mul_right w3 a3 bb

(** Adding row [k] into the accumulator.  Before, the accumulator is [L]
    below [wk] and the four words [x] above it, and is [pre * B]; the row is
    [ak * B].  After, the four words are [s] and the carry is [top], and the
    accumulator is [(pre + wk * ak) * B] -- which is below [wk * 2^320],
    so [top] is a word. *)
let acc (wk: pos) (lo pre ak bb x0 x1 x2 x3 y0 y1 y2 y3 y4 s0 s1 s2 s3 c1 c2 c3 c4: nat)
  : Lemma (requires lo + wk * ev4 x0 x1 x2 x3 == pre * bb /\
                    ev4 y0 y1 y2 y3 + w4 * y4 == ak * bb /\
                    pre + wk * ak < wk * w /\ bb < w4 /\
                    s0 + w * c1 == x0 + y0 /\
                    s1 + w * c2 == x1 + y1 + c1 /\
                    s2 + w * c3 == x2 + y2 + c2 /\
                    s3 + w * c4 == x3 + y3 + c3)
          (ensures y4 + c4 < w /\
                   lo + wk * (ev4 s0 s1 s2 s3 + w4 * (y4 + c4)) == (pre + wk * ak) * bb)
  = let e = ev4 s0 s1 s2 s3 + w4 * (y4 + c4) in
    assert (e == ev4 x0 x1 x2 x3 + (ev4 y0 y1 y2 y3 + w4 * y4));
    Math.distributivity_add_right wk (ev4 x0 x1 x2 x3) (ev4 y0 y1 y2 y3 + w4 * y4);
    Math.paren_mul_right wk ak bb;
    Math.distributivity_add_left pre (wk * ak) bb;
    prod_lt (pre + wk * ak) bb (wk * w) w4;
    Math.paren_mul_right wk w w4;
    if e >= w5 then Math.lemma_mult_le_left wk w5 e

(** {2 Squares} *)

let ring () : Tac unit =
  norm [delta_only [`%ev4]];
  canon_semiring int_cr

(** [A^2] is the four squares on the even positions plus twice the six cross
    products. *)
let sq_identity (a0 a1 a2 a3: int)
  : Lemma (ev4 a0 a1 a2 a3 * ev4 a0 a1 a2 a3 ==
           (a0 * a0 + w2 * (a1 * a1) + w4 * (a2 * a2) + w6 * (a3 * a3)) +
           2 * (w * (a0 * a1) + w2 * (a0 * a2) + w3 * (a0 * a3 + a1 * a2) +
                w4 * (a1 * a3) + w5 * (a2 * a3)))
  = assert (ev4 a0 a1 a2 a3 * ev4 a0 a1 a2 a3 ==
            (a0 * a0 + w2 * (a1 * a1) + w4 * (a2 * a2) + w6 * (a3 * a3)) +
            2 * (w * (a0 * a1) + w2 * (a0 * a2) + w3 * (a0 * a3 + a1 * a2) +
                 w4 * (a1 * a3) + w5 * (a2 * a3)))
        by (ring ())

(** The cross products fit in seven words. *)
let cross_lt (a0 a1 a2 a3: nat)
  : Lemma (requires a0 < w /\ a1 < w /\ a2 < w /\ a3 < w)
          (ensures w * (a0 * a1) + w2 * (a0 * a2) + w3 * (a0 * a3 + a1 * a2) +
                   w4 * (a1 * a3) + w5 * (a2 * a3) < w7)
  = let m = (w - 1) * (w - 1) in
    Math.lemma_mult_le_left a0 a1 (w - 1);
    Math.lemma_mult_le_right (w - 1) a0 (w - 1);
    Math.lemma_mult_le_left a0 a2 (w - 1);
    Math.lemma_mult_le_right (w - 1) a0 (w - 1);
    Math.lemma_mult_le_left a0 a3 (w - 1);
    Math.lemma_mult_le_left a1 a2 (w - 1);
    Math.lemma_mult_le_right (w - 1) a1 (w - 1);
    Math.lemma_mult_le_left a1 a3 (w - 1);
    Math.lemma_mult_le_left a2 a3 (w - 1);
    Math.lemma_mult_le_right (w - 1) a2 (w - 1);
    assert (a0 * a1 <= m /\ a0 * a2 <= m /\ a0 * a3 <= m /\ a1 * a2 <= m /\
            a1 * a3 <= m /\ a2 * a3 <= m)

(** The whole square fits in eight words. *)
let sq_lt (a0 a1 a2 a3: nat)
  : Lemma (requires a0 < w /\ a1 < w /\ a2 < w /\ a3 < w)
          (ensures ev4 a0 a1 a2 a3 * ev4 a0 a1 a2 a3 < w8)
  = prod_lt (ev4 a0 a1 a2 a3) (ev4 a0 a1 a2 a3) w4 w4

#pop-options

(** {2 Bytes} *)

open Hacl.Spec.Bytes
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {!Hacl.Spec.Bytes.le_bytes_split} for a low part of any whole number of
    bytes, and no bound on the high part. *)
let byte_split (lo hi: nat) (m: pos) (k: nat)
  : Lemma (requires lo < pow2 (8 * m))
          (ensures (let n = lo + pow2 (8 * m) * hi in
                    ((n / pow2 (8 * k)) % 256 ==
                       (if k < m then (lo / pow2 (8 * k)) % 256
                                 else (hi / pow2 (8 * (k - m))) % 256))))
  = let n = lo + pow2 (8 * m) * hi in
    if k < m then begin
      Math.pow2_plus (8 * k) (8 * m - 8 * k);
      Math.paren_mul_right (pow2 (8 * k)) (pow2 (8 * m - 8 * k)) hi;
      Math.lemma_div_plus lo (pow2 (8 * m - 8 * k) * hi) (pow2 (8 * k));
      Math.pow2_plus 8 (8 * m - 8 * k - 8);
      Math.paren_mul_right (pow2 8) (pow2 (8 * m - 8 * k - 8)) hi;
      assert_norm (pow2 8 == 256);
      Math.lemma_mod_plus (lo / pow2 (8 * k)) (pow2 (8 * m - 8 * k - 8) * hi) 256
    end else begin
      Math.pow2_plus (8 * m) (8 * (k - m));
      Math.division_multiplication_lemma n (pow2 (8 * m)) (pow2 (8 * (k - m)));
      Math.lemma_div_plus lo hi (pow2 (8 * m));
      Math.small_division_lemma_1 lo (pow2 (8 * m))
    end

let sel4 (l0 l1 l2 l3: nat) (j: nat { j < 4 }) : nat =
  if j = 0 then l0 else if j = 1 then l1 else if j = 2 then l2 else l3

(** Byte [8 j + k] of a four-word number is byte [k] of word [j]. *)
let store_byte (l0 l1 l2 l3: nat) (j: nat { j < 4 }) (k: nat { k < 8 })
  : Lemma (requires l0 < w /\ l1 < w /\ l2 < w /\ l3 < w)
          (ensures (ev4 l0 l1 l2 l3 / pow2 (8 * (8 * j + k))) % 256 ==
                   (sel4 l0 l1 l2 l3 j / pow2 (8 * k)) % 256)
  = consts ();
    assert_norm (pow2 128 == w2);
    assert_norm (pow2 (8 * 8) == w);
    assert_norm (pow2 (8 * 16) == w2);
    let lo = l0 + w * l1 in
    let hi = l2 + w * l3 in
    assert (ev4 l0 l1 l2 l3 == lo + pow2 (8 * 16) * hi);
    byte_split lo hi 16 (8 * j + k);
    if j < 2 then byte_split l0 l1 8 (8 * j + k)
    else byte_split l2 l3 8 (8 * j + k - 16)

(** Thirty-two bytes are four little-endian words. *)
let load_split (u: Seq.seq S8.t { Seq.length u == 32 })
  : Lemma (le_nat u == ev4 (le_nat (Seq.slice u 0 8)) (le_nat (Seq.slice u 8 16))
                           (le_nat (Seq.slice u 16 24)) (le_nat (Seq.slice u 24 32)))
  = consts ();
    assert_norm (pow2 (8 * 8) == w);
    assert_norm (pow2 (8 * 16) == w2);
    let lo = Seq.slice u 0 16 in
    let hi = Seq.slice u 16 32 in
    le_nat_split u 16;
    le_nat_split lo 8;
    le_nat_split hi 8;
    Seq.lemma_eq_intro (Seq.slice lo 0 8) (Seq.slice u 0 8);
    Seq.lemma_eq_intro (Seq.slice lo 8 16) (Seq.slice u 8 16);
    Seq.lemma_eq_intro (Seq.slice hi 0 8) (Seq.slice u 16 24);
    Seq.lemma_eq_intro (Seq.slice hi 8 16) (Seq.slice u 24 32);
    Seq.lemma_eq_intro (Seq.slice u 0 16) lo;
    Seq.lemma_eq_intro (Seq.slice u 16 32) hi

(** Clearing the top bit of the top word is reducing mod [2^255]. *)
let mask_top (l0 l1 l2 l3: nat)
  : Lemma (requires l0 < w /\ l1 < w /\ l2 < w /\ l3 < w)
          (ensures ev4 l0 l1 l2 (l3 % pow2 63) == ev4 l0 l1 l2 l3 % pow2 255)
  = consts ();
    let r = l3 % pow2 63 in
    let q = l3 / pow2 63 in
    Math.euclidean_division_definition l3 (pow2 63);
    assert (ev4 l0 l1 l2 l3 == ev4 l0 l1 l2 r + pow2 255 * q);
    Math.lemma_mod_plus (ev4 l0 l1 l2 r) q (pow2 255);
    Math.small_mod (ev4 l0 l1 l2 r) (pow2 255)

let stored (vb: Seq.seq S8.t) (l0 l1 l2 l3: nat) : prop =
  Seq.length vb == 32 /\
  (forall (k: nat). k < 8 ==> S8.v (Seq.index vb k) == (l0 / pow2 (8 * k)) % 256) /\
  (forall (k: nat). k < 8 ==> S8.v (Seq.index vb (8 + k)) == (l1 / pow2 (8 * k)) % 256) /\
  (forall (k: nat). k < 8 ==> S8.v (Seq.index vb (16 + k)) == (l2 / pow2 (8 * k)) % 256) /\
  (forall (k: nat). k < 8 ==> S8.v (Seq.index vb (24 + k)) == (l3 / pow2 (8 * k)) % 256)

(** Stored word by word, a four-word number is its thirty-two bytes. *)
let store_ok (vb: Seq.seq S8.t) (l0 l1 l2 l3: nat)
  : Lemma (requires l0 < w /\ l1 < w /\ l2 < w /\ l3 < w /\ stored vb l0 l1 l2 l3)
          (ensures vb == nat_to_le 32 (ev4 l0 l1 l2 l3))
  = let x = ev4 l0 l1 l2 l3 in
    let aux (i: nat { i < 32 }) : Lemma (Seq.index vb i == Seq.index (nat_to_le 32 x) i) =
      if i < 8 then begin
        store_byte l0 l1 l2 l3 0 i;
        assert (S8.v (Seq.index vb i) == (l0 / pow2 (8 * i)) % 256)
      end else if i < 16 then begin
        let k = i - 8 in
        store_byte l0 l1 l2 l3 1 k;
        assert (S8.v (Seq.index vb (8 + k)) == (l1 / pow2 (8 * k)) % 256)
      end else if i < 24 then begin
        let k = i - 16 in
        store_byte l0 l1 l2 l3 2 k;
        assert (S8.v (Seq.index vb (16 + k)) == (l2 / pow2 (8 * k)) % 256)
      end else begin
        let k = i - 24 in
        store_byte l0 l1 l2 l3 3 k;
        assert (S8.v (Seq.index vb (24 + k)) == (l3 / pow2 (8 * k)) % 256)
      end;
      nat_to_le_index 32 x i;
      S8.v_extensional (Seq.index vb i) (Seq.index (nat_to_le 32 x) i)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro vb (nat_to_le 32 x)

(** The top bit of the top word is the number's bit 255. *)
let split255 (l0 l1 l2 l3: nat)
  : Lemma (requires l0 < w /\ l1 < w /\ l2 < w /\ l3 < w)
          (ensures ev4 l0 l1 l2 l3 == ev4 l0 l1 l2 (l3 % pow2 63) + pow2 255 * (l3 / pow2 63) /\
                   ev4 l0 l1 l2 (l3 % pow2 63) < pow2 255 /\ l3 / pow2 63 <= 1)
  = consts ();
    Math.euclidean_division_definition l3 (pow2 63)

(** [2^255 = 19]: the bit above two hundred and fifty-five, folded. *)
let fold255_ok (lo t: nat)
  : Lemma (requires lo < pow2 255 /\ t <= 1)
          (ensures (lo + 19 * t) % C.prime == (lo + pow2 255 * t) % C.prime /\
                   lo + 19 * t < pow2 255 + 19 /\
                   (lo + pow2 255 * t < pow2 255 + 19 ==> lo + 19 * t < pow2 255))
  = consts ();
    Math.lemma_mod_plus (lo + 19 * t) t C.prime

(** Below [2^255], at most one [p] comes off, and adding nineteen says
    whether it does. *)
let final_ok (x t lo: nat)
  : Lemma (requires x < pow2 255 /\ t <= 1 /\ lo < pow2 255 /\ x + 19 == lo + pow2 255 * t)
          (ensures (if t = 1 then lo else x) == x % C.prime)
  = consts ();
    if t = 1 then begin
      Math.lemma_mod_sub x C.prime 1;
      Math.small_mod lo C.prime
    end else Math.small_mod x C.prime

#pop-options
