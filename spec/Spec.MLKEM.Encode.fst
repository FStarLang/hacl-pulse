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

(** Serialisation and lossy compression, FIPS 203 algorithms 4 through 6
    and section 4.2.1.

    Two independent things happen between a polynomial and the bytes on the
    wire.  [Compress_d] throws away all but the top [d] bits of information
    in each coefficient -- that is what makes ML-KEM ciphertexts small, and
    it is why decapsulation has to tolerate noise.  [ByteEncode_d] then
    packs 256 [d]-bit values into [32 d] bytes losslessly.  The standard
    keeps them separate and so does this.

    Bits run least significant first, both within a coefficient and within
    a byte.  That is the opposite of Frodo, which packs most significant
    first; the two libraries' packers therefore cannot be shared even
    though they are the same idea, and mixing the conventions up is the
    easiest possible way to produce something that verifies against the
    wrong standard. *)
module Spec.MLKEM.Encode

open Spec.MLKEM.Zq

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 1 --ifuel 0"

(** {2 Bit access}

    [ByteEncode] is specified in the standard as a composition through a
    sequence of bits.  Materialising that sequence would mean a 3072-entry
    intermediate; instead each side reads the bit it wants directly out of
    the other representation, which is also what the implementation does. *)

(** Bit [b] of the coefficient sequence [f], least significant first within
    each coefficient.  Out of range reads give zero so that the byte-valued
    function below needs no case analysis -- exactly the trick
    {!Spec.Frodo.pack_bit} uses. *)
let coeff_bit (d: pos) (f: Seq.seq nat) (b: nat) : GTot (x: nat { x < 2 })
  = if b < d * Seq.length f then begin
      div_lt b (Seq.length f) d;
      (Seq.index f (b / d) / pow2 (b % d)) % 2
    end else 0

(** Byte [i] of the packed form, least significant bit first. *)
let byte_val (d: pos) (f: Seq.seq nat) (i: nat) : GTot (x: nat { x < 256 })
  =   coeff_bit d f (8 * i)     * 1   + coeff_bit d f (8 * i + 1) * 2
    + coeff_bit d f (8 * i + 2) * 4   + coeff_bit d f (8 * i + 3) * 8
    + coeff_bit d f (8 * i + 4) * 16  + coeff_bit d f (8 * i + 5) * 32
    + coeff_bit d f (8 * i + 6) * 64  + coeff_bit d f (8 * i + 7) * 128

(** Bit [b] of a byte string, least significant first. *)
let stream_bit (b: Seq.seq S8.t) (pos: nat) : GTot (x: nat { x < 2 })
  = if pos / 8 < Seq.length b
    then (S8.v (Seq.index b (pos / 8)) / pow2 (pos % 8)) % 2
    else 0

(** [m] bits starting at [off], read as a little-endian integer.  The bound
    is part of the type because every caller needs it and because it is the
    reason [byte_decode] lands in [zq] without a reduction for [d < 12]. *)
let rec bits_val (b: Seq.seq S8.t) (off: nat) (m: nat)
  : GTot (x: nat { x < pow2 m }) (decreases m)
  = if m = 0 then 0
    else begin
      Math.pow2_double_mult (m - 1);
      stream_bit b off + 2 * bits_val b (off + 1) (m - 1)
    end

(** The top bit peeled off instead of the bottom one, which is the shape a
    loop that accumulates from the least significant end needs. *)
let rec bits_val_snoc (b: Seq.seq S8.t) (off: nat) (m: pos)
  : Lemma (ensures bits_val b off m ==
                   bits_val b off (m - 1) + pow2 (m - 1) * stream_bit b (off + m - 1))
          (decreases m)
  = if m = 1 then ()
    else begin
      bits_val_snoc b (off + 1) (m - 1);
      Math.pow2_double_mult (m - 2)
    end

(** {2 Encoding}

    Algorithms 5 and 6.  [d] ranges over 1, 4, 5, 10, 11 and 12 across the
    three parameter sets: one for the message, [dv] for the second
    ciphertext component, [du] for the first, and 12 for keys, which are
    stored uncompressed. *)

let byte_encode (d: pos { d <= 12 }) (f: Seq.lseq nat n) : GTot (Seq.lseq S8.t (32 * d))
  = Seq.init_ghost (32 * d) (fun i -> S8.classify (U8.uint_to_t (byte_val d f i)))

(** [ByteDecode_d].  For [d < 12] the result is below [2^d <= 2048 < q] and
    is therefore already canonical; only [d = 12] can overflow, and the
    standard reduces it.  Both cases land in [zq], so the caller never has
    to ask which one it is in. *)
let byte_decode (d: pos { d <= 12 }) (b: Seq.lseq S8.t (32 * d)) : GTot poly
  = Seq.init_ghost n (fun i ->
      let v = bits_val b (i * d) d in
      let r: zq =
        if d = 12 then v % q
        else begin
          Math.pow2_le_compat 11 d;
          assert_norm (pow2 11 < q);
          v
        end in
      r)

(** {2 Compression}

    [Compress_d x = round(2^d x / q) mod 2^d], with ties away from zero.
    Written with the standard implementation trick: [q] is odd and [2^d x]
    is even, so [2 * 2^d * x + q] is odd and can never be a multiple of
    [2 q].  There is thus no tie to break, and the cheap
    [(2^d x + floor(q/2)) / q] agrees with the rounding the standard
    describes.  That is worth spelling out because it is the one place in
    ML-KEM where an off-by-one in rounding would still decapsulate
    correctly almost always. *)

let compress (d: pos { d <= 11 }) (x: zq) : r: nat { r < pow2 d }
  = ((x * pow2 d + q / 2) / q) % pow2 d

(** [Decompress_d y = round(q y / 2^d)], again with ties away from zero;
    here [2^d] is even so the tie is real, and [+ 2^(d-1)] breaks it
    upwards as the standard says. *)
let decompress (d: pos { d <= 11 }) (y: nat { y < pow2 d }) : zq
  = let p = pow2 d in
    Math.pow2_le_compat 10 (d - 1);
    assert_norm (pow2 10 < q);
    Math.lemma_mult_le_right q y (p - 1);
    Math.distributivity_sub_left p 1 q;
    div_lt (y * q + pow2 (d - 1)) q p;
    (y * q + pow2 (d - 1)) / p

(** The two lifted to polynomials.  Compression does not land in [poly],
    since its results are [d]-bit and not [q]-bounded, so it produces the
    plain sequence of naturals [byte_encode] consumes. *)

let poly_compress (d: pos { d <= 11 }) (f: poly) : Seq.lseq nat n
  = Seq.init n (fun i -> (compress d (Seq.index f i) <: nat))

(** The guard is vacuous on anything [poly_compress] or [byte_decode]
    produced -- both are [d]-bit by construction -- but carrying the
    refinement through the flat vector types costs more than it saves,
    since [FStar.Seq] is invariant in its element type. *)
let poly_decompress (d: pos { d <= 11 }) (f: Seq.lseq nat n) : GTot poly
  = Seq.init_ghost n (fun i ->
      let v = Seq.index f i in
      let r: zq = if v < pow2 d then decompress d v else 0 in
      r)

(** {2 Vectors}

    A compressed vector is [k] compressed polynomials laid end to end; a
    key is [k] uncompressed ones.  Both are just [k]-fold concatenations,
    but writing them out here keeps the length arithmetic in one place. *)

let vec_encode (d: pos { d <= 12 }) (k: pos) (v: Seq.lseq nat (k * n))
  : GTot (Seq.lseq S8.t (k * (32 * d)))
  = flat_of_fun_g k (32 * d) (fun i -> byte_encode d (flat_at k n v i))

let vec_decode (d: pos { d <= 12 }) (k: pos) (b: Seq.lseq S8.t (k * (32 * d))) : GTot (pvec k)
  = vec_of_fun_g k (fun i -> byte_decode d (flat_at k (32 * d) b i))

let vec_compress (d: pos { d <= 11 }) (#k: pos) (v: pvec k) : Seq.lseq nat (k * n)
  = flat_of_fun k n (fun i -> poly_compress d (vec_at v i))

(** The uncompressed twelve-bit encoding keys use. *)
let vec_encode_12 (#k: pos) (v: pvec k) : GTot (Seq.lseq S8.t (k * (32 * 12)))
  = vec_encode 12 k (widen v)

let vec_decompress (d: pos { d <= 11 }) (k: pos) (v: Seq.lseq nat (k * n)) : GTot (pvec k)
  = vec_of_fun_g k (fun i -> poly_decompress d (flat_at k n v i))

#pop-options

(** {2 Pointwise views}

    Every one of the four coders above is a [Seq.init], so an
    implementation that fills an output one index at a time needs to know
    what that index holds; none of these carry an SMT pattern, because
    letting the solver unfold a coder at a symbolic index inside a loop
    invariant is exactly what makes such a proof unaffordable. *)

let byte_encode_index (d: pos { d <= 12 }) (f: Seq.lseq nat n) (i: nat { i < 32 * d })
  : Lemma (Seq.index (byte_encode d f) i == S8.classify (U8.uint_to_t (byte_val d f i)))
  = Seq.init_ghost_index_ (32 * d) (fun j -> S8.classify (U8.uint_to_t (byte_val d f j))) i

let byte_decode_index (d: pos { d <= 12 }) (b: Seq.lseq S8.t (32 * d)) (i: nat { i < n })
  : Lemma (Seq.index (byte_decode d b) i == bits_val b (i * d) d % q)
  = Seq.init_ghost_index_ n
      (fun j ->
        let v = bits_val b (j * d) d in
        let r: zq =
          if d = 12 then v % q
          else begin
            Math.pow2_le_compat 11 d;
            assert_norm (pow2 11 < q);
            v
          end in
        r) i;
    if d < 12 then begin
      Math.pow2_le_compat 11 d;
      assert_norm (pow2 11 < q);
      Math.small_mod (bits_val b (i * d) d) q
    end

let poly_compress_index (d: pos { d <= 11 }) (f: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_compress d f) i == compress d (Seq.index f i))
  = Seq.init_index_ n (fun j -> (compress d (Seq.index f j) <: nat)) i

let poly_decompress_index (d: pos { d <= 11 }) (f: Seq.lseq nat n) (i: nat { i < n })
  : Lemma (requires Seq.index f i < pow2 d)
          (ensures Seq.index (poly_decompress d f) i == decompress d (Seq.index f i))
  = Seq.init_ghost_index_ n
      (fun j ->
        let v = Seq.index f j in
        let r: zq = if v < pow2 d then decompress d v else 0 in
        r) i
