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

(** Unpacking undoes packing, up to the reduction modulo [2^d]:

    [S16.v (Seq.index (unpack d len (pack d len m)) j) == S16.v (Seq.index m j) % pow2 d]

    ([unpack_pack]), and so for the two instances FrodoKEM uses,
    [unpack_n (pack_n m)] and [unpack_8 (pack_8 m)].

    Both directions are stated bit by bit, so the proof is too.  Bit [r] of
    byte [i] of the packed string, read most significant first, is
    [pack_bit d m (8 i + r)] ([stream_bit_pack]): the byte is a sum of eight
    weighted bits and dividing by [2^(7 - r)] isolates one of them.  Then
    [unpack_val] reads [d] consecutive bits most significant first, which is
    Horner's rule, and Horner's rule over the top [k] of the [d] bits of [x]
    gives [(x / 2^(d - k)) % 2^k] ([unpack_val_bits]); at [k = d] that is
    [x % 2^d]. *)
module Spec.Frodo.Pack.Lemmas

open Spec.Frodo.Params
open Spec.Frodo

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module Math = FStar.Math.Lemmas
module M = Spec.Frodo.Matrix

#push-options "--fuel 0 --ifuel 0"

(** {2 One bit of a byte} *)

let bit_of (hi: nat) (b: nat { b < 2 }) (lo: nat) (k: nat)
  : Lemma (requires lo < pow2 k) (ensures (((hi * 2 + b) * pow2 k + lo) / pow2 k) % 2 == b)
  = Math.lemma_div_plus lo (hi * 2 + b) (pow2 k);
    Math.small_div lo (pow2 k);
    Math.lemma_mod_plus b hi 2;
    Math.small_mod b 2

let byte_bit (b0 b1 b2 b3 b4 b5 b6 b7: (n: nat { n < 2 })) (r: nat { r < 8 })
  : Lemma (let x = b0 * 128 + b1 * 64 + b2 * 32 + b3 * 16 + b4 * 8 + b5 * 4 + b6 * 2 + b7 in
           (x / pow2 (7 - r)) % 2 ==
           (if r = 0 then b0 else if r = 1 then b1 else if r = 2 then b2
            else if r = 3 then b3 else if r = 4 then b4 else if r = 5 then b5
            else if r = 6 then b6 else b7))
  = assert_norm (pow2 0 == 1 /\ pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\
                 pow2 4 == 16 /\ pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128);
    if r = 0 then bit_of 0 b0 (b1 * 64 + b2 * 32 + b3 * 16 + b4 * 8 + b5 * 4 + b6 * 2 + b7) 7
    else if r = 1 then bit_of b0 b1 (b2 * 32 + b3 * 16 + b4 * 8 + b5 * 4 + b6 * 2 + b7) 6
    else if r = 2 then bit_of (b0 * 2 + b1) b2 (b3 * 16 + b4 * 8 + b5 * 4 + b6 * 2 + b7) 5
    else if r = 3 then bit_of (b0 * 4 + b1 * 2 + b2) b3 (b4 * 8 + b5 * 4 + b6 * 2 + b7) 4
    else if r = 4 then bit_of (b0 * 8 + b1 * 4 + b2 * 2 + b3) b4 (b5 * 4 + b6 * 2 + b7) 3
    else if r = 5 then bit_of (b0 * 16 + b1 * 8 + b2 * 4 + b3 * 2 + b4) b5 (b6 * 2 + b7) 2
    else if r = 6 then bit_of (b0 * 32 + b1 * 16 + b2 * 8 + b3 * 4 + b4 * 2 + b5) b6 b7 1
    else bit_of (b0 * 64 + b1 * 32 + b2 * 16 + b3 * 8 + b4 * 4 + b5 * 2 + b6) b7 0 0

let byte_val_bit (d: pos) (m: Seq.seq S16.t) (i: nat) (r: nat { r < 8 })
  : Lemma ((byte_val d m i / pow2 (7 - r)) % 2 == pack_bit d m (8 * i + r))
  = let b0 = pack_bit d m (8 * i) in
    let b1 = pack_bit d m (8 * i + 1) in
    let b2 = pack_bit d m (8 * i + 2) in
    let b3 = pack_bit d m (8 * i + 3) in
    let b4 = pack_bit d m (8 * i + 4) in
    let b5 = pack_bit d m (8 * i + 5) in
    let b6 = pack_bit d m (8 * i + 6) in
    let b7 = pack_bit d m (8 * i + 7) in
    assert (byte_val d m i ==
            b0 * 128 + b1 * 64 + b2 * 32 + b3 * 16 + b4 * 8 + b5 * 4 + b6 * 2 + b7);
    byte_bit b0 b1 b2 b3 b4 b5 b6 b7 r;
    if r = 0 then assert (8 * i + r == 8 * i)
    else if r = 1 then () else if r = 2 then () else if r = 3 then ()
    else if r = 4 then () else if r = 5 then () else if r = 6 then ()
    else assert (r == 7)

(** {2 The packed bit stream} *)

let stream_bit_pack (d: pos { d <= 16 }) (len: nat { len % 8 == 0 }) (m: Seq.lseq S16.t len)
                    (pos: nat { pos < d * len })
  : Lemma (stream_bit (pack d len m) pos == pack_bit d m pos)
  = Math.euclidean_division_definition len 8;
    Math.paren_mul_right d (len / 8) 8;
    M.div_lt pos (d * (len / 8)) 8;
    Math.euclidean_division_definition pos 8;
    byte_val_bit d m (pos / 8) (pos % 8)

(** {2 Horner's rule} *)

let horner_step (y: nat) (k: pos)
  : Lemma (2 * ((y / 2) % pow2 (k - 1)) + y % 2 == y % pow2 k)
  = Math.pow2_plus 1 (k - 1);
    assert_norm (pow2 1 == 2);
    Math.modulo_division_lemma y 2 (pow2 (k - 1));
    Math.modulo_modulo_lemma y 2 (pow2 (k - 1));
    Math.euclidean_division_definition (y % pow2 k) 2

#push-options "--fuel 1"

let rec unpack_val_bits (b: Seq.seq S8.t) (off: nat) (d: nat) (x: nat) (k: nat { k <= d })
  : Lemma (requires forall (t: nat). t < d ==> stream_bit b (off + t) == (x / pow2 (d - 1 - t)) % 2)
          (ensures unpack_val b off k == (x / pow2 (d - k)) % pow2 k)
          (decreases k)
  = if k = 0 then assert_norm (pow2 0 == 1)
    else begin
      unpack_val_bits b off d x (k - 1);
      Math.pow2_plus (d - k) 1;
      assert_norm (pow2 1 == 2);
      Math.division_multiplication_lemma x (pow2 (d - k)) 2;
      Math.lemma_div_le 0 x (pow2 (d - k));
      horner_step (x / pow2 (d - k)) k
    end

#pop-options

(** {2 The round trip} *)

let pack_bit_at (d: pos) (m: Seq.seq S16.t) (j: nat { j < Seq.length m }) (t: nat { t < d })
  : Lemma (pack_bit d m (j * d + t) == (S16.v (Seq.index m j) / pow2 (d - 1 - t)) % 2)
  = Math.lemma_mult_le_right d (j + 1) (Seq.length m);
    Math.lemma_div_plus t j d;
    Math.small_div t d;
    Math.lemma_mod_plus t j d;
    Math.small_mod t d

let unpack_val_all (b: Seq.seq S8.t) (off: nat) (d: nat) (x: nat)
  : Lemma (requires forall (t: nat). t < d ==> stream_bit b (off + t) == (x / pow2 (d - 1 - t)) % 2)
          (ensures unpack_val b off d == x % pow2 d)
  = unpack_val_bits b off d x d;
    assert_norm (pow2 0 == 1);
    Math.cancel_mul_div x 1

let stream_bits_pack (d: pos { d <= 16 }) (len: nat { len % 8 == 0 }) (m: Seq.lseq S16.t len)
                     (j: nat { j < len })
  : Lemma (forall (t: nat). t < d ==>
             stream_bit (pack d len m) (j * d + t) ==
             (S16.v (Seq.index m j) / pow2 (d - 1 - t)) % 2)
  = introduce forall (t: nat). t < d ==>
                stream_bit (pack d len m) (j * d + t) ==
                (S16.v (Seq.index m j) / pow2 (d - 1 - t)) % 2
    with introduce _ ==> _ with begin
      Math.lemma_mult_le_right d (j + 1) len;
      stream_bit_pack d len m (j * d + t);
      pack_bit_at d m j t
    end

let unpack_pack (d: pos { d <= 16 }) (len: nat { len % 8 == 0 }) (m: Seq.lseq S16.t len)
                (j: nat { j < len })
  : Lemma (S16.v (Seq.index (unpack d len (pack d len m)) j) == S16.v (Seq.index m j) % pow2 d)
  = stream_bits_pack d len m j;
    unpack_val_all (pack d len m) (j * d) d (S16.v (Seq.index m j));
    Math.pow2_le_compat 16 d

let unpack_pack_n (p: params) (m: Seq.seq S16.t { Seq.length m == n p * nbar })
                  (j: nat { j < n p * nbar })
  : Lemma (S16.v (Seq.index (unpack_n p (pack_n p m)) j) == S16.v (Seq.index m j) % pow2 (logq p))
  = Math.multiple_division_lemma (n p) nbar;
    Math.multiple_modulo_lemma (n p) nbar;
    unpack_pack (logq p) (n p * nbar) m j

let unpack_pack_8 (p: params) (m: M.matrix nbar nbar) (j: nat { j < nbar * nbar })
  : Lemma (S16.v (Seq.index (unpack_8 p (pack_8 p m)) j) == S16.v (Seq.index m j) % pow2 (logq p))
  = unpack_pack (logq p) (nbar * nbar) m j

#pop-options
