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

(** The serialisers of {!Spec.MLKEM.Encode} are inverse to each other where
    FIPS 203 says they are (section 4.2.1):

    - [byte_decode_encode]: [ByteDecode_d (ByteEncode_d f) == f] for every
      [f] whose coefficients fit in [d] bits and are below [q] -- the
      direction keys and ciphertexts travel in;
    - [byte_encode_decode]: [ByteEncode_d (ByteDecode_d b) == b] for every
      byte string [b] and [d < 12] -- the direction the message travels in,
      and the reason the decrypted message comes back byte for byte;
    - the same for the [k]-fold vector coders, and [vec_decode_encode_12]
      for the twelve-bit key encoding of canonical coefficients.

    Both directions are one fact about little-endian bit strings, proved
    once for an arbitrary bit function ([lev]): bit [j] of the number a
    bit string spells is bit [j] of the string ([lev_bit]), and a number
    below [2^m] is spelled by its own bits ([lev_of_nat]).  Encoding and
    decoding then only ever compare one bit of the byte stream with one bit
    of a coefficient, and the index arithmetic between the two is the
    division of a bit position by [8] or by [d]. *)
module Spec.MLKEM.Encode.Lemmas

open Spec.MLKEM.Zq
open Spec.MLKEM.Encode

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0"

(** {2 Little-endian bit strings} *)

(** The number spelled by [m] bits starting at [off], least significant
    first: the common shape of [bits_val] and [byte_val]. *)
let rec lev (bit: nat -> GTot (x: nat { x < 2 })) (off: nat) (m: nat) : GTot nat (decreases m)
  = if m = 0 then 0 else bit off + 2 * lev bit (off + 1) (m - 1)

let half (b: nat { b < 2 }) (y: nat) : Lemma ((b + 2 * y) / 2 == y /\ (b + 2 * y) % 2 == b)
  = Math.lemma_div_plus b y 2;
    Math.lemma_mod_plus b y 2

#push-options "--fuel 1"
let rec lev_bit (bit: nat -> GTot (x: nat { x < 2 })) (off: nat) (m: nat) (j: nat { j < m })
  : Lemma (ensures (lev bit off m / pow2 j) % 2 == bit (off + j)) (decreases j)
  = half (bit off) (lev bit (off + 1) (m - 1));
    if j > 0 then begin
      lev_bit bit (off + 1) (m - 1) (j - 1);
      Math.pow2_double_mult (j - 1);
      Math.division_multiplication_lemma (lev bit off m) 2 (pow2 (j - 1))
    end

let rec lev_ext (b1 b2: nat -> GTot (x: nat { x < 2 })) (off: nat) (m: nat)
  : Lemma (requires forall (j: nat). j < m ==> b1 (off + j) == b2 (off + j))
          (ensures lev b1 off m == lev b2 off m) (decreases m)
  = if m > 0 then begin
      assert (b1 (off + 0) == b2 (off + 0));
      introduce forall (j: nat). j < m - 1 ==> b1 (off + 1 + j) == b2 (off + 1 + j)
      with introduce _ ==> _ with assert (b1 (off + (j + 1)) == b2 (off + (j + 1)));
      lev_ext b1 b2 (off + 1) (m - 1)
    end

let rec lev_of_nat (bit: nat -> GTot (x: nat { x < 2 })) (off: nat) (m: nat) (x: nat)
  : Lemma (requires x < pow2 m /\ (forall (j: nat). j < m ==> bit (off + j) == (x / pow2 j) % 2))
          (ensures lev bit off m == x) (decreases m)
  = if m = 0 then assert_norm (pow2 0 == 1)
    else begin
      assert (bit (off + 0) == (x / pow2 0) % 2);
      assert_norm (pow2 0 == 1);
      assert (bit off == x % 2);
      Math.pow2_double_mult (m - 1);
      introduce forall (j: nat). j < m - 1 ==> bit (off + 1 + j) == ((x / 2) / pow2 j) % 2
      with introduce _ ==> _ with begin
        let j' : nat = j + 1 in
        assert (bit (off + j') == (x / pow2 j') % 2);
        assert (off + j' == off + 1 + j);
        Math.pow2_double_mult j;
        assert (pow2 j' == 2 * pow2 j);
        Math.division_multiplication_lemma x 2 (pow2 j)
      end;
      lev_of_nat bit (off + 1) (m - 1) (x / 2);
      assert (lev bit off m == bit off + 2 * lev bit (off + 1) (m - 1));
      Math.euclidean_division_definition x 2
    end

let rec bits_val_lev (b: Seq.seq S8.t) (off: nat) (m: nat)
  : Lemma (ensures bits_val b off m == lev (stream_bit b) off m) (decreases m)
  = if m > 0 then bits_val_lev b (off + 1) (m - 1)
let lev_step (bit: nat -> GTot (x: nat { x < 2 })) (off: nat) (m: nat)
  : Lemma (lev bit off (m + 1) == bit off + 2 * lev bit (off + 1) m)
  = ()

let lev_zero (bit: nat -> GTot (x: nat { x < 2 })) (off: nat) : Lemma (lev bit off 0 == 0) = ()
#pop-options

let byte_val_lev (d: pos) (f: Seq.seq nat) (i: nat)
  : Lemma (byte_val d f i == lev (coeff_bit d f) (8 * i) 8)
  = let b = coeff_bit d f in
    let o = 8 * i in
    lev_step b o 7; lev_step b (o + 1) 6; lev_step b (o + 2) 5; lev_step b (o + 3) 4;
    lev_step b (o + 4) 3; lev_step b (o + 5) 2; lev_step b (o + 6) 1; lev_step b (o + 7) 0;
    lev_zero b (o + 8)

(** Position [j * d + i] of a coefficient stream is bit [i] of coefficient
    [j]. *)
let coeff_pos (d: pos) (j: nat) (i: nat { i < d })
  : Lemma ((j * d + i) / d == j /\ (j * d + i) % d == i)
  = Math.lemma_div_plus i j d;
    Math.small_div i d;
    Math.lemma_mod_plus i j d;
    Math.small_mod i d

(** {2 Encode, then decode} *)

let stream_bit_encode (d: pos { d <= 12 }) (f: Seq.lseq nat n) (p: nat)
  : Lemma (stream_bit (byte_encode d f) p == coeff_bit d f p)
  = if p / 8 < 32 * d then begin
      byte_encode_index d f (p / 8);
      byte_val_lev d f (p / 8);
      Math.euclidean_division_definition p 8;
      lev_bit (coeff_bit d f) (8 * (p / 8)) 8 (p % 8)
    end else begin
      Math.lemma_div_le (d * n) p 8;
      assert (d * n == (32 * d) * 8);
      Math.cancel_mul_div (32 * d) 8
    end

let byte_decode_encode_at (d: pos { d <= 12 }) (f: Seq.lseq nat n) (j: nat { j < n })
  : Lemma (requires Seq.index f j < pow2 d /\ Seq.index f j < q)
          (ensures Seq.index (byte_decode d (byte_encode d f)) j == Seq.index f j)
  = let enc = byte_encode d f in
    let x = Seq.index f j in
    byte_decode_index d enc j;
    bits_val_lev enc (j * d) d;
    introduce forall (i: nat). i < d ==> stream_bit enc (j * d + i) == coeff_bit d f (j * d + i)
    with introduce _ ==> _ with stream_bit_encode d f (j * d + i);
    lev_ext (stream_bit enc) (coeff_bit d f) (j * d) d;
    introduce forall (i: nat). i < d ==> coeff_bit d f (j * d + i) == (x / pow2 i) % 2
    with introduce _ ==> _ with begin
      coeff_pos d j i;
      Math.lemma_mult_le_right d (j + 1) n
    end;
    lev_of_nat (coeff_bit d f) (j * d) d x;
    Math.small_mod x q

let byte_decode_encode (d: pos { d <= 12 }) (f: Seq.lseq nat n)
  : Lemma (requires forall (j: nat). j < n ==> Seq.index f j < pow2 d /\ Seq.index f j < q)
          (ensures widen (byte_decode d (byte_encode d f)) == f)
  = introduce forall (j: nat { j < n }).
      Seq.index (widen (byte_decode d (byte_encode d f))) j == Seq.index f j
    with byte_decode_encode_at d f j;
    Seq.lemma_eq_intro (widen (byte_decode d (byte_encode d f))) f

(** {2 Decode, then encode} *)

let stream_bit_byte (b: Seq.seq S8.t) (i: nat { i < Seq.length b }) (j: nat { j < 8 })
  : Lemma (stream_bit b (8 * i + j) == (S8.v (Seq.index b i) / pow2 j) % 2)
  = coeff_pos 8 i j

let byte_encode_decode_at (d: pos { d < 12 }) (b: Seq.lseq S8.t (32 * d)) (i: nat { i < 32 * d })
  : Lemma (Seq.index (byte_encode d (widen (byte_decode d b))) i == Seq.index b i)
  = let f = widen (byte_decode d b) in
    let x = S8.v (Seq.index b i) in
    byte_encode_index d f i;
    byte_val_lev d f i;
    introduce forall (j: nat). j < 8 ==> coeff_bit d f (8 * i + j) == stream_bit b (8 * i + j)
    with introduce _ ==> _ with begin
      let p = 8 * i + j in
      assert (p < d * n);
      div_lt p n d;
      Math.euclidean_division_definition p d;
      byte_decode_index d b (p / d);
      Math.pow2_le_compat 11 d;
      assert_norm (pow2 11 < q);
      Math.small_mod (bits_val b ((p / d) * d) d) q;
      bits_val_lev b ((p / d) * d) d;
      lev_bit (stream_bit b) ((p / d) * d) d (p % d)
    end;
    lev_ext (coeff_bit d f) (stream_bit b) (8 * i) 8;
    introduce forall (j: nat). j < 8 ==> stream_bit b (8 * i + j) == (x / pow2 j) % 2
    with introduce _ ==> _ with stream_bit_byte b i j;
    assert_norm (pow2 8 == 256);
    lev_of_nat (stream_bit b) (8 * i) 8 x;
    S8.v_extensional (Seq.index (byte_encode d f) i) (Seq.index b i)

let byte_encode_decode (d: pos { d < 12 }) (b: Seq.lseq S8.t (32 * d))
  : Lemma (byte_encode d (widen (byte_decode d b)) == b)
  = introduce forall (i: nat { i < 32 * d }).
      Seq.index (byte_encode d (widen (byte_decode d b))) i == Seq.index b i
    with byte_encode_decode_at d b i;
    Seq.lemma_eq_intro (byte_encode d (widen (byte_decode d b))) b

(** {2 Vectors} *)

(** Two flat sequences are equal if all their blocks are. *)
let flat_ext (#a: Type) (k: pos) (m: pos) (u v: Seq.lseq a (k * m))
  : Lemma (requires forall (i: nat { i < k }). flat_at k m u i == flat_at k m v i)
          (ensures u == v)
  = introduce forall (t: nat { t < k * m }). Seq.index u t == Seq.index v t
    with begin
      div_lt t k m;
      let i = t / m in
      Math.euclidean_division_definition t m;
      Math.lemma_mult_le_right m (i + 1) k;
      assert (Seq.index (flat_at k m u i) (t % m) == Seq.index (flat_at k m v i) (t % m))
    end;
    Seq.lemma_eq_intro u v

let flat_at_widen (k: pos) (v: Seq.lseq zq (k * n)) (i: nat { i < k })
  : Lemma (flat_at k n (widen v) i == widen (flat_at k n v i))
  = Math.lemma_mult_le_right n (i + 1) k;
    Seq.lemma_eq_intro (flat_at k n (widen v) i) (widen (flat_at k n v i))

let vec_decode_encode (d: pos { d <= 12 }) (k: pos) (v: Seq.lseq nat (k * n))
  : Lemma (requires forall (t: nat). t < k * n ==> Seq.index v t < pow2 d /\ Seq.index v t < q)
          (ensures widen (vec_decode d k (vec_encode d k v)) == v)
  = let enc = vec_encode d k v in
    introduce forall (i: nat { i < k }).
      flat_at k n (widen (vec_decode d k enc)) i == flat_at k n v i
    with begin
      flat_at_widen k (vec_decode d k enc) i;
      vec_decode_at d k enc i;
      vec_encode_at d k v i;
      Math.lemma_mult_le_right n (i + 1) k;
      byte_decode_encode d (flat_at k n v i)
    end;
    flat_ext k n (widen (vec_decode d k enc)) v

let widen_injective (#m: nat) (f g: Seq.lseq zq m)
  : Lemma (requires widen f == widen g) (ensures f == g)
  = introduce forall (i: nat { i < m }). Seq.index f i == Seq.index g i
    with assert (Seq.index (widen f) i == Seq.index (widen g) i);
    Seq.lemma_eq_intro f g

(** Keys: twelve bits hold every canonical coefficient, so the twelve-bit
    encoding of a vector over [Z_q] decodes back to it. *)
let vec_decode_encode_12 (#k: pos) (v: pvec k)
  : Lemma (vec_decode 12 k (vec_encode_12 v) == v)
  = q_bound ();
    vec_decode_encode 12 k (widen v);
    widen_injective (vec_decode 12 k (vec_encode_12 v)) v

#pop-options
