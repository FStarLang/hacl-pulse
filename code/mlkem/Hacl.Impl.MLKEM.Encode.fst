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

(** Serialisation and compression.

    [ByteEncode_d] and [ByteDecode_d] are bit-serial coders, the same shape
    as FrodoKEM's packer and written the same way, one bit at a time with
    out-of-range reads giving zero so that neither end needs a case
    analysis.  The one difference is the bit order --- ML-KEM is
    least-significant-first where FrodoKEM is most-significant-first ---
    and it is enough to stop the two sharing any code.

    [Compress_d] divides by [q], and a division instruction on a secret is
    not something to emit, so {!Hacl.Impl.MLKEM.Zq.div_q} replaces it with
    a multiply and a shift.  [Decompress_d] divides by [2^d], which is a
    shift already. *)
module Hacl.Impl.MLKEM.Encode

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Encode
open Hacl.Impl.MLKEM.Zq

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module HSZ = Hacl.SizeT
module U32 = FStar.UInt32

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 Encoding} *)

(** Bit [pos] of the coefficient sequence: bit [pos mod d] of coefficient
    [pos / d], counting from the least significant. *)
inline_for_extraction
fn coeff_bit_impl (f: A.array zqt) (d: SZ.t) (pos: SZ.t)
                  (#p: perm) (#vf: erased (Seq.seq zqt))
requires A.pts_to f #p vf **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n)
returns b: S16.t
ensures A.pts_to f #p vf **
        pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n /\
              S16.v b == coeff_bit (SZ.v d) (as_nats vf) (SZ.v pos))
{
  A.pts_to_len f;
  HSZ.fits32 ();
  assert_norm (12 * 256 < pow2 32);
  SZ.fits_u32_implies_fits (SZ.v d * n);
  if (SZ.lt pos (SZ.mul d 256sz)) {
    div_lt (SZ.v pos) n (SZ.v d);
    let i = SZ.div pos d;
    let r = SZ.rem pos d;
    let x = A.(f.(i));
    let y = S16.shift_right x (SZ.sizet_to_uint32 r);
    S16.logand_mask_low y 1ul;
    assert_norm (pow2 1 == 2);
    S16.logand y (S16.mask_low 1ul)
  } else {
    S16.zero
  }
}

(** Eight of them, least significant first.  Written out rather than
    folded because the specification is written out. *)
inline_for_extraction
fn encode_byte (f: A.array zqt) (d: SZ.t) (i: SZ.t)
               (#p: perm) (#vf: erased (Seq.seq zqt))
requires A.pts_to f #p vf **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n /\ SZ.v i < 32 * SZ.v d)
returns b: S8.t
ensures A.pts_to f #p vf **
        pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n /\
              S8.v b == byte_val (SZ.v d) (as_nats vf) (SZ.v i))
{
  HSZ.fits32 ();
  assert_norm (12 * 256 < pow2 32);
  SZ.fits_u32_implies_fits (8 * SZ.v i + 8);
  assert_norm (pow2 1 == 2);
  assert_norm (pow2 2 == 4);
  assert_norm (pow2 3 == 8);
  assert_norm (pow2 4 == 16);
  assert_norm (pow2 5 == 32);
  assert_norm (pow2 6 == 64);
  assert_norm (pow2 7 == 128);
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  let base = SZ.mul 8sz i;
  let b0 = coeff_bit_impl f d base;
  let b1 = coeff_bit_impl f d (SZ.add base 1sz);
  let b2 = coeff_bit_impl f d (SZ.add base 2sz);
  let b3 = coeff_bit_impl f d (SZ.add base 3sz);
  let b4 = coeff_bit_impl f d (SZ.add base 4sz);
  let b5 = coeff_bit_impl f d (SZ.add base 5sz);
  let b6 = coeff_bit_impl f d (SZ.add base 6sz);
  let b7 = coeff_bit_impl f d (SZ.add base 7sz);
  assert (pure (S16.v b0 < 2 /\ S16.v b1 < 2 /\ S16.v b2 < 2 /\ S16.v b3 < 2 /\
                S16.v b4 < 2 /\ S16.v b5 < 2 /\ S16.v b6 < 2 /\ S16.v b7 < 2));
  let a1 = S16.add_mod b0 (S16.shift_left b1 1ul);
  assert (pure (S16.v a1 == S16.v b0 + 2 * S16.v b1 /\ S16.v a1 <= 3));
  let a2 = S16.add_mod a1 (S16.shift_left b2 2ul);
  assert (pure (S16.v a2 == S16.v a1 + 4 * S16.v b2 /\ S16.v a2 <= 7));
  let a3 = S16.add_mod a2 (S16.shift_left b3 3ul);
  assert (pure (S16.v a3 == S16.v a2 + 8 * S16.v b3 /\ S16.v a3 <= 15));
  let a4 = S16.add_mod a3 (S16.shift_left b4 4ul);
  assert (pure (S16.v a4 == S16.v a3 + 16 * S16.v b4 /\ S16.v a4 <= 31));
  let a5 = S16.add_mod a4 (S16.shift_left b5 5ul);
  assert (pure (S16.v a5 == S16.v a4 + 32 * S16.v b5 /\ S16.v a5 <= 63));
  let a6 = S16.add_mod a5 (S16.shift_left b6 6ul);
  assert (pure (S16.v a6 == S16.v a5 + 64 * S16.v b6 /\ S16.v a6 <= 127));
  let a7 = S16.add_mod a6 (S16.shift_left b7 7ul);
  assert (pure (S16.v a7 == S16.v a6 + 128 * S16.v b7 /\ S16.v a7 < 256));
  S16.lo a7
}

(** [out <- ByteEncode_d f], [32 d] bytes of it. *)
fn encode_poly (out: A.array S8.t) (f: A.array zqt) (d: SZ.t)
               (#p: perm) (#vo: erased (Seq.seq S8.t)) (#vf: erased (Seq.seq zqt))
requires A.pts_to out vo ** A.pts_to f #p vf **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\
               Seq.length vf == n /\ Seq.length vo == 32 * SZ.v d)
ensures exists* v. A.pts_to out v ** A.pts_to f #p vf **
        pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n /\
              v == byte_encode (SZ.v d) (as_nats vf))
{
  A.pts_to_len out;
  A.pts_to_len f;
  HSZ.fits32 ();
  assert_norm (32 * 12 < pow2 32);
  SZ.fits_u32_implies_fits (32 * SZ.v d);
  let len = SZ.mul 32sz d;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to f #p vf **
    pure (SZ.v vi <= 32 * SZ.v d /\ Seq.length v == 32 * SZ.v d /\
          1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v k == Seq.index (byte_encode (SZ.v d) (as_nats vf)) k))
  decreases (32 * SZ.v d - SZ.v (!i))
  {
    let vi = !i;
    let b = encode_byte f d vi;
    byte_encode_index (SZ.v d) (as_nats vf) (SZ.v vi);
    A.((out.(vi) <- b));
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  Seq.lemma_eq_intro v (byte_encode (SZ.v d) (as_nats vf));
  assert (pure (v == byte_encode (SZ.v d) (as_nats vf)));
}

(** {2 Decoding} *)

(** Bit [pos] of a byte string, least significant first. *)
inline_for_extraction
fn stream_bit_impl (b: A.array S8.t) (blen: SZ.t) (pos: SZ.t)
                   (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (Seq.length vb == SZ.v blen)
returns x: S16.t
ensures A.pts_to b #p vb **
        pure (Seq.length vb == SZ.v blen /\ S16.v x == stream_bit vb (SZ.v pos))
{
  A.pts_to_len b;
  let j = SZ.div pos 8sz;
  if (SZ.lt j blen) {
    let r = SZ.rem pos 8sz;
    let y = A.(b.(j));
    let z = S8.shift_right y (SZ.sizet_to_uint32 r);
    Math.pow2_le_compat 16 8;
    let e = S16.of_bytes_le z (S8.classify 0uy);
    S16.logand_mask_low e 1ul;
    assert_norm (pow2 1 == 2);
    S16.logand e (S16.mask_low 1ul)
  } else {
    S16.zero
  }
}

(** [d] bits starting at [off], read as a little-endian integer.  The loop
    runs from the least significant bit up, which is why the specification
    needs {!Spec.MLKEM.Encode.bits_val_snoc}: it is written the other way
    round. *)
inline_for_extraction
fn bits_val_impl (b: A.array S8.t) (blen: SZ.t) (off: SZ.t) (d: SZ.t)
                 (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vb == SZ.v blen /\
               SZ.v off <= 12 * n)
returns x: S16.t
ensures A.pts_to b #p vb **
        pure (Seq.length vb == SZ.v blen /\ 1 <= SZ.v d /\ SZ.v d <= 12 /\
              S16.v x == bits_val vb (SZ.v off) (SZ.v d))
{
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (pow2 12 == 4096);
  assert_norm (4096 < pow2 16);
  assert_norm (12 * n + 12 < pow2 32);
  let mut acc = S16.zero;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj d)
  invariant exists* (vj: SZ.t) (a: S16.t).
    pts_to j vj ** pts_to acc a ** A.pts_to b #p vb **
    pure (SZ.v vj <= SZ.v d /\ Seq.length vb == SZ.v blen /\
          1 <= SZ.v d /\ SZ.v d <= 12 /\ SZ.v off <= 12 * n /\
          S16.v a == bits_val vb (SZ.v off) (SZ.v vj))
  decreases (SZ.v d - SZ.v (!j))
  {
    let vj = !j;
    let a = !acc;
    SZ.fits_u32_implies_fits (SZ.v off + SZ.v vj);
    SZ.fits_u32_implies_fits (SZ.v vj + 1);
    let bit = stream_bit_impl b blen (SZ.add off vj);
    bits_val_snoc vb (SZ.v off) (SZ.v vj + 1);
    Math.pow2_le_compat 12 (SZ.v vj + 1);
    Math.pow2_lt_compat 12 (SZ.v vj);
    Math.small_mod (S16.v a + pow2 (SZ.v vj) * S16.v bit) (pow2 16);
    acc := S16.add_mod a (S16.shift_left bit (SZ.sizet_to_uint32 vj));
    j := SZ.add vj 1sz;
  };
  !acc
}

(** [dst <- ByteDecode_d b].  For [d < 12] the result is below [2^d] and
    already canonical; only [d = 12] can exceed [q], and it cannot exceed
    [2q], so the same conditional subtraction serves both and the
    implementation never has to ask which case it is in. *)
fn decode_poly (dst: A.array zqt) (b: A.array S8.t) (d: SZ.t)
               (#p: perm) (#vd: erased (Seq.seq zqt)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to b #p vb **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\
               Seq.length vd == n /\ Seq.length vb == 32 * SZ.v d)
ensures exists* v. A.pts_to dst v ** A.pts_to b #p vb **
        pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length v == n /\
              Seq.length vb == 32 * SZ.v d /\
              as_poly v == byte_decode (SZ.v d) vb)
{
  A.pts_to_len dst;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (32 * 12 < pow2 32);
  assert_norm (pow2 12 < 2 * q);
  SZ.fits_u32_implies_fits (32 * SZ.v d);
  let blen = SZ.mul 32sz d;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to b #p vb **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vb == 32 * SZ.v d /\
          1 <= SZ.v d /\ SZ.v d <= 12 /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) == Seq.index (byte_decode (SZ.v d) vb) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (SZ.v d) (SZ.v vi) n;
    Math.lemma_mult_le_left n (SZ.v d) 12;
    assert_norm (12 * n < pow2 32);
    SZ.fits_u32_implies_fits (SZ.v vi * SZ.v d);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let x = bits_val_impl b blen (SZ.mul vi d) d;
    Math.pow2_le_compat 12 (SZ.v d);
    byte_decode_index (SZ.v d) vb (SZ.v vi);
    A.((dst.(vi) <- csub x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_poly_intro v (byte_decode (SZ.v d) vb);
  assert (pure (as_poly v == byte_decode (SZ.v d) vb));
}

(** {2 Compression} *)

(** [Compress_d x], as a multiply and two shifts. *)
inline_for_extraction
let compress_impl (d: SZ.t { 1 <= SZ.v d /\ SZ.v d <= 11 }) (x: zqt)
  : r: zqt { S16.v r == compress (SZ.v d) (S16.v x) }
= let dd = SZ.sizet_to_uint32 d in
  Math.pow2_le_compat 11 (SZ.v d);
  assert_norm (pow2 11 == 2048);
  assert_norm ((q - 1) * 2048 + q / 2 < pow2 23);
  assert_norm (pow2 23 * 2580335 < pow2 64);
  assert_norm (pow2 23 < pow2 64);
  Math.lemma_mult_le_right (pow2 (SZ.v d)) (S16.v x) (q - 1);
  Math.lemma_mult_le_right (q - 1) (pow2 (SZ.v d)) 2048;
  let y = S64.add_mod (S64.shift_left (Cast.u16_to_u64 x) dd) (S64.classify 1664uL) in
  Math.small_mod (S16.v x * pow2 (SZ.v d)) (pow2 64);
  Math.small_mod (S16.v x * pow2 (SZ.v d) + 1664) (pow2 64);
  assert (S64.v y == S16.v x * pow2 (SZ.v d) + q / 2);
  div_q (S64.v y);
  Math.small_mod (S64.v y * 2580335) (pow2 64);
  let t = S64.shift_right (S64.mul_mod y (S64.classify 2580335uL)) 33ul in
  assert (S64.v t == (S16.v x * pow2 (SZ.v d) + q / 2) / q);
  S64.logand_mask_low t dd;
  let m = S64.logand t (S64.mask_low dd) in
  Math.pow2_le_compat 16 (SZ.v d);
  Math.small_mod (S64.v m) (pow2 16);
  let r = Cast.u64_to_u16 m in
  assert (S16.v r == compress (SZ.v d) (S16.v x));
  r

(** [Decompress_d y]: [y] is [d] bits, so this is a multiply, an add and a
    shift, with no division to avoid. *)
inline_for_extraction
let decompress_impl (d: SZ.t { 1 <= SZ.v d /\ SZ.v d <= 11 })
                    (y: zqt { S16.v y < pow2 (SZ.v d) })
  : r: zqt { S16.v r == decompress (SZ.v d) (S16.v y) }
= let dd = SZ.sizet_to_uint32 d in
  Math.pow2_le_compat 11 (SZ.v d);
  assert_norm (pow2 11 == 2048);
  assert_norm (2048 * q + 1024 < pow2 23);
  assert_norm (pow2 23 < pow2 64);
  Math.lemma_mult_le_right q (S16.v y) 2048;
  Math.pow2_le_compat (SZ.v d) (SZ.v d - 1);
  Math.pow2_le_compat 11 (SZ.v d - 1);
  let h = S64.shift_left (S64.classify 1uL) (U32.sub dd 1ul) in
  Math.small_mod (pow2 (SZ.v d - 1)) (pow2 64);
  let z = S64.add_mod (S64.mul_mod (Cast.u16_to_u64 y) (S64.classify 3329uL)) h in
  Math.small_mod (S16.v y * q) (pow2 64);
  Math.small_mod (S16.v y * q + pow2 (SZ.v d - 1)) (pow2 64);
  let t = S64.shift_right z dd in
  Math.pow2_le_compat 16 (SZ.v d);
  Math.small_mod (S64.v t) (pow2 16);
  let r = Cast.u64_to_u16 t in
  r

(** The two lifted to polynomials. *)

fn compress_poly (dst src: A.array zqt) (d: SZ.t)
                 (#p: perm) (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs **
         pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ Seq.length vd == n /\ Seq.length vs == n)
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs **
        pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ Seq.length v == n /\ Seq.length vs == n /\
              as_nats v == poly_compress (SZ.v d) (as_poly vs))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #p vs **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vs == n /\
          1 <= SZ.v d /\ SZ.v d <= 11 /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) == Seq.index (poly_compress (SZ.v d) (as_poly vs)) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    poly_compress_index (SZ.v d) (as_poly vs) (SZ.v vi);
    A.((dst.(vi) <- compress_impl d x));
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_nats_intro v (poly_compress (SZ.v d) (as_poly vs));
  assert (pure (as_nats v == poly_compress (SZ.v d) (as_poly vs)));
}

fn decompress_poly (dst src: A.array zqt) (d: SZ.t)
                   (#p: perm) (#vd #vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #p vs **
         pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ Seq.length vd == n /\ Seq.length vs == n /\
               (forall (k: nat). k < n ==> S16.v (Seq.index vs k) < pow2 (SZ.v d)))
ensures exists* v. A.pts_to dst v ** A.pts_to src #p vs **
        pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ Seq.length v == n /\ Seq.length vs == n /\
              as_poly v == poly_decompress (SZ.v d) (as_nats vs))
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #p vs **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vs == n /\
          1 <= SZ.v d /\ SZ.v d <= 11 /\
          (forall (k: nat). k < n ==> S16.v (Seq.index vs k) < pow2 (SZ.v d)) /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) == Seq.index (poly_decompress (SZ.v d) (as_nats vs)) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    poly_decompress_index (SZ.v d) (as_nats vs) (SZ.v vi);
    A.((dst.(vi) <- decompress_impl d x));
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_poly_intro v (poly_decompress (SZ.v d) (as_nats vs));
  assert (pure (as_poly v == poly_decompress (SZ.v d) (as_nats vs)));
}

#pop-options
