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
open Spec.MLKEM.Pack
open Hacl.Spec.Bytes
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

(** {2 Encoding}

    Both coders run a shift register.  FIPS 203 states them bit by bit and
    {!Spec.MLKEM.Encode} follows it, but a bit-serial implementation
    divides by [d] twice for every bit it moves, and [d] is a parameter,
    so those are real divisions: twelve bits of key is three thousand of
    them.  {!Spec.MLKEM.Pack} says instead what the bit string is --- the
    integer [sum_j f_j 2^(d j)], whose little-endian bytes are the
    encoding --- and that one number can be filled and emptied in whatever
    chunks suit the machine.

    So [encode_poly] holds a sixty-four bit register containing the bits
    packed so far and not yet written out, pushes each coefficient in at
    the top with a shift and an add, and writes a byte off the bottom
    whenever eight have accumulated.  [decode_poly] runs the same register
    the other way.  Neither divides by anything, and the register is never
    wider than [8 + d <= 20] bits, so the shifts and adds are exact and
    the arithmetic is plain. *)

#push-options "--z3rlimit 150"

(** [out <- ByteEncode_d f], [32 d] bytes of it. *)
fn encode_poly (out: A.array S8.t) (f: A.array zqt) (d: SZ.t)
               (#p: perm) (#vout: erased (Seq.seq S8.t)) (#vf: erased (Seq.seq zqt))
requires A.pts_to out vout ** A.pts_to f #p vf **
         pure (1 <= SZ.v d /\ SZ.v d <= 12 /\
               Seq.length vf == n /\ Seq.length vout == 32 * SZ.v d)
ensures exists* v. A.pts_to out v ** A.pts_to f #p vf **
        pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n /\
              v == byte_encode (SZ.v d) (as_nats vf))
{
  A.pts_to_len out;
  A.pts_to_len f;
  HSZ.fits32 ();
  assert_norm (32 * 12 < pow2 32);
  assert_norm (pow2 12 == 4096);
  assert_norm (pow2 20 < pow2 64);
  SZ.fits_u32_implies_fits (32 * SZ.v d);
  let dd = SZ.sizet_to_uint32 d;
  enc_num_zero (SZ.v d) (as_nats vf);
  assert_norm (pow2 0 == 1);
  let mut acc = S64.zero;
  let mut nb = 0sz;
  let mut o = 0sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi vn vo: SZ.t) (va: S64.t) (v: Seq.seq S8.t).
    pts_to i vi ** pts_to nb vn ** pts_to o vo ** pts_to acc va **
    A.pts_to out v ** A.pts_to f #p vf **
    pure (SZ.v vi <= n /\ SZ.v vn < 8 /\
          SZ.v d * SZ.v vi == 8 * SZ.v vo + SZ.v vn /\
          SZ.v vo <= 32 * SZ.v d /\
          1 <= SZ.v d /\ SZ.v d <= 12 /\
          Seq.length vf == n /\ Seq.length v == 32 * SZ.v d /\
          S64.v va == enc_num (SZ.v d) (as_nats vf) (SZ.v vi) / pow2 (8 * SZ.v vo) /\
          (forall (k: nat). k < SZ.v vo ==>
             Seq.index v k == Seq.index (byte_encode (SZ.v d) (as_nats vf)) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let vn = !nb;
    let vo = !o;
    let va = !acc;
    let x = A.(f.(vi));
    S16.logand_mask_low x dd;
    let c = S16.logand x (S16.mask_low dd);
    assert (pure (S16.v c == S16.v x % pow2 (SZ.v d)));
    Math.pow2_le_compat 12 (SZ.v d);
    Math.lemma_mult_le_right (pow2 (SZ.v vn)) (S16.v c) 4096;
    Math.pow2_le_compat 8 (SZ.v vn);
    Math.pow2_plus 12 8;
    Math.small_mod (S16.v c * pow2 (SZ.v vn)) (pow2 64);
    let y = S64.shift_left (Cast.u16_to_u64 c) (SZ.sizet_to_uint32 vn);
    assert (pure (S64.v y == S16.v c * pow2 (SZ.v vn)));
    enc_acc_bound (SZ.v d) (as_nats vf) (SZ.v vi) (SZ.v vo) (SZ.v vn);
    enc_push (SZ.v d) (as_nats vf) (SZ.v vi) (SZ.v vo) (SZ.v vn);
    Math.small_mod (S64.v va + S64.v y) (pow2 64);
    acc := S64.add_mod va y;
    nb := SZ.add vn d;
    i := SZ.add vi 1sz;
    Math.lemma_mult_le_left (SZ.v d) (SZ.v vi + 1) 256;
    Math.distributivity_add_right (SZ.v d) (SZ.v vi) 1;
    while (let vn' = !nb; SZ.gte vn' 8sz)
    invariant exists* (vn vo: SZ.t) (va: S64.t) (v: Seq.seq S8.t).
      pts_to i (SZ.add vi 1sz) ** pts_to nb vn ** pts_to o vo ** pts_to acc va **
      A.pts_to out v ** A.pts_to f #p vf **
      pure (SZ.v vn < 8 + SZ.v d /\
            SZ.v d * (SZ.v vi + 1) == 8 * SZ.v vo + SZ.v vn /\
            SZ.v vo <= 32 * SZ.v d /\
            1 <= SZ.v d /\ SZ.v d <= 12 /\ SZ.v vi < n /\
            Seq.length vf == n /\ Seq.length v == 32 * SZ.v d /\
            S64.v va == enc_num (SZ.v d) (as_nats vf) (SZ.v vi + 1) / pow2 (8 * SZ.v vo) /\
            (forall (k: nat). k < SZ.v vo ==>
               Seq.index v k == Seq.index (byte_encode (SZ.v d) (as_nats vf)) k))
    decreases (SZ.v (!nb))
    {
      let vn = !nb;
      let vo = !o;
      let va = !acc;
      enc_room (SZ.v d) (SZ.v vi) (SZ.v vo) (SZ.v vn);
      byte_encode_prefix (SZ.v d) (as_nats vf) (SZ.v vi + 1) (SZ.v vo);
      assert_norm (pow2 8 == 256);
      A.((out.(vo) <- Cast.u64_to_u8 va));
      enc_flush (SZ.v d) (as_nats vf) (SZ.v vi + 1) (SZ.v vo);
      acc := S64.shift_right va 8ul;
      nb := SZ.sub vn 8sz;
      o := SZ.add vo 1sz;
    }
  };
  with vie vne voe. assert (pts_to i vie ** pts_to nb vne ** pts_to o voe);
  assert (pure (256 <= SZ.v vie));
  assert (pure (SZ.v vie <= 256));
  assert (pure (SZ.v vie == 256));
  enc_done (SZ.v d) (SZ.v vie) (SZ.v voe) (SZ.v vne);
  with v. assert (A.pts_to out v);
  Seq.lemma_eq_intro v (byte_encode (SZ.v d) (as_nats vf));
  assert (pure (v == byte_encode (SZ.v d) (as_nats vf)));
}

#pop-options

(** {2 Decoding} *)

(** Bit [pos] of a byte string, least significant first.  The accumulator
    loops below do not need this, but centred binomial sampling still reads
    one bit at a time, and it reads only [2 eta] of them per coefficient. *)
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

#push-options "--z3rlimit 600"

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
  assert_norm (pow2 12 == 4096);
  assert_norm (pow2 12 < 2 * q);
  assert_norm (pow2 20 < pow2 64);
  SZ.fits_u32_implies_fits (32 * SZ.v d);
  let dd = SZ.sizet_to_uint32 d;
  let mut acc = S64.zero;
  let mut nb = 0sz;
  let mut pos = 0sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi vn vp: SZ.t) (va: S64.t) (v: Seq.seq zqt).
    pts_to i vi ** pts_to nb vn ** pts_to pos vp ** pts_to acc va **
    A.pts_to dst v ** A.pts_to b #p vb **
    pure (SZ.v vi <= n /\ SZ.v vn < 8 /\
          8 * SZ.v vp == SZ.v d * SZ.v vi + SZ.v vn /\
          1 <= SZ.v d /\ SZ.v d <= 12 /\
          Seq.length v == n /\ Seq.length vb == 32 * SZ.v d /\
          S64.v va == le_nat vb / pow2 (SZ.v d * SZ.v vi) % pow2 (SZ.v vn) /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) == Seq.index (byte_decode (SZ.v d) vb) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    while (let vn' = !nb; SZ.lt vn' d)
    invariant exists* (vn vp: SZ.t) (va: S64.t) (v: Seq.seq zqt).
      pts_to i vi ** pts_to nb vn ** pts_to pos vp ** pts_to acc va **
      A.pts_to dst v ** A.pts_to b #p vb **
      pure (SZ.v vi < n /\ SZ.v vn < SZ.v d + 8 /\
            8 * SZ.v vp == SZ.v d * SZ.v vi + SZ.v vn /\
            1 <= SZ.v d /\ SZ.v d <= 12 /\
            Seq.length v == n /\ Seq.length vb == 32 * SZ.v d /\
            S64.v va == le_nat vb / pow2 (SZ.v d * SZ.v vi) % pow2 (SZ.v vn) /\
            (forall (k: nat). k < SZ.v vi ==>
               S16.v (Seq.index v k) == Seq.index (byte_decode (SZ.v d) vb) k))
    decreases (SZ.v d + 8 - SZ.v (!nb))
    {
      let vn = !nb;
      let vp = !pos;
      let va = !acc;
      dec_room (SZ.v d) (SZ.v vi) (SZ.v vp) (SZ.v vn);
      let bk = A.(b.(vp));
      Math.pow2_le_compat 12 (SZ.v vn);
      Math.lemma_mult_le_right (pow2 (SZ.v vn)) (S8.v bk) 256;
      Math.pow2_plus 8 12;
      Math.small_mod (S8.v bk * pow2 (SZ.v vn)) (pow2 64);
      let y = S64.shift_left (Cast.u8_to_u64 bk) (SZ.sizet_to_uint32 vn);
      assert (pure (S64.v y == S8.v bk * pow2 (SZ.v vn)));
      dec_read vb (SZ.v d * SZ.v vi) (SZ.v vn) (SZ.v vp);
      Math.pow2_le_compat 20 (SZ.v vn + 8);
      Math.small_mod (S64.v va + S64.v y) (pow2 64);
      Math.lemma_mod_lt (le_nat vb / pow2 (SZ.v d * SZ.v vi)) (pow2 (SZ.v vn + 8));
      acc := S64.add_mod va y;
      nb := SZ.add vn 8sz;
      SZ.fits_u32_implies_fits (SZ.v vp + 1);
      pos := SZ.add vp 1sz;
    };
    let vn = !nb;
    let va = !acc;
    S64.logand_mask_low va dd;
    let m = S64.logand va (S64.mask_low dd);
    dec_val vb (SZ.v d * SZ.v vi) (SZ.v vn) (SZ.v d);
    assert (pure (S64.v m == bits_val vb (SZ.v d * SZ.v vi) (SZ.v d)));
    Math.pow2_le_compat 12 (SZ.v d);
    Math.pow2_le_compat 16 (SZ.v d);
    Math.small_mod (S64.v m) (pow2 16);
    let x = Cast.u64_to_u16 m;
    byte_decode_index (SZ.v d) vb (SZ.v vi);
    Math.swap_mul (SZ.v vi) (SZ.v d);
    A.((dst.(vi) <- csub x));
    dec_take vb (SZ.v d * SZ.v vi) (SZ.v vn) (SZ.v d);
    Math.distributivity_add_right (SZ.v d) (SZ.v vi) 1;
    acc := S64.shift_right va dd;
    nb := SZ.sub vn d;
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  with vie vne vpe vae v.
    assert (pts_to i vie ** pts_to nb vne ** pts_to pos vpe **
            pts_to acc vae ** A.pts_to dst v);
  assert (pure (256 <= SZ.v vie));
  assert (pure (SZ.v vie <= 256));
  assert (pure (SZ.v vie == 256));
  as_poly_intro v (byte_decode (SZ.v d) vb);
  assert (pure (as_poly v == byte_decode (SZ.v d) vb));
}

#pop-options

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
