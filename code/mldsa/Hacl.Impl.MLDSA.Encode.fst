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


(** [SimpleBitPack], [BitPack] and their inverses on one polynomial.

    The coders are ML-KEM's shift registers ({!Hacl.Impl.MLKEM.Encode}),
    widened to twenty bits a coefficient: the register never holds more
    than [7 + 20] live bits, so sixty-four are plenty.  One packer serves
    both [SimpleBitPack] and [BitPack]: in the signed form each
    coefficient [c] is first replaced by [b - c] in [Z_q], which for every
    [c] in [[-a, b]] is the natural number the standard packs.  Likewise
    the unpacker optionally maps each field [x] to [b - x]. *)
module Hacl.Impl.MLDSA.Encode

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Spec.Bytes
open Spec.MLDSA.Zq
open Spec.MLDSA.Encode
open Hacl.Impl.MLDSA.Zq

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module Cast = Hacl.Secret.Cast
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module HSZ = Hacl.SizeT
module KE = Spec.MLKEM.Encode
module KP = Spec.MLKEM.Pack

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 What is packed} *)

let src (signed: bool) (b: zq) (vf: Seq.seq zqt { Seq.length vf == n }) : GTot (Seq.lseq nat n)
  = if signed then Seq.init_ghost n (fun i -> (sub b (S32.v (Seq.index vf i)) <: nat))
    else as_ints vf

let src_index (signed: bool) (b: zq) (vf: Seq.seq zqt { Seq.length vf == n }) (i: nat { i < n })
  : Lemma (Seq.index (src signed b vf) i ==
           (if signed then sub b (S32.v (Seq.index vf i)) else S32.v (Seq.index vf i)))
  = if signed then Seq.init_ghost_index_ n (fun i -> (sub b (S32.v (Seq.index vf i)) <: nat)) i

let src_signed (b: zq) (vf: Seq.seq zqt { Seq.length vf == n }) (d: pos { d <= 20 })
  : Lemma (simple_bit_pack d (src true b vf) == bit_pack b d (as_poly vf))
  = let f = as_poly vf in
    let g = Seq.init n (fun i -> (sub b (Seq.index f i) <: nat)) in
    let aux (i: nat { i < n }) : Lemma (Seq.index (src true b vf) i == Seq.index g i)
      = src_index true b vf i in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (src true b vf) g

(** {2 Pack lemmas at up to twenty bits}

    {!Spec.MLKEM.Pack} states the byte-level facts against ML-KEM's
    [byte_encode], whose width stops at twelve; the proofs do not use the
    bound, and these are the same facts against {!simple_bit_pack}. *)

let sbp_index (d: pos { d <= 20 }) (f: Seq.lseq nat n) (i: nat { i < 32 * d })
  : Lemma (Seq.index (simple_bit_pack d f) i == S8.classify (U8.uint_to_t (KE.byte_val d f i)))
  = Seq.init_ghost_index_ (32 * d) (fun j -> S8.classify (U8.uint_to_t (KE.byte_val d f j))) i

let byte_val_num (d: pos { d <= 20 }) (f: Seq.lseq nat n) (i: nat { i < 32 * d })
  : Lemma (KE.byte_val d f i == KP.enc_num d f n / pow2 (8 * i) % 256)
  = let nm = KP.enc_num d f n in
    let bit (p: nat { p < d * n }) : Lemma (nm / pow2 p % 2 == KE.coeff_bit d f p)
      = KP.enc_bit d f n p in
    assert (8 * i + 7 < d * n);
    bit (8 * i); bit (8 * i + 1); bit (8 * i + 2); bit (8 * i + 3);
    bit (8 * i + 4); bit (8 * i + 5); bit (8 * i + 6); bit (8 * i + 7);
    KP.byte_of_bits (nm / pow2 (8 * i));
    let e (j: nat { j <= 7 })
      : Lemma (nm / pow2 (8 * i) / pow2 j == nm / pow2 (8 * i + j))
      = Math.pow2_plus (8 * i) j;
        Math.division_multiplication_lemma nm (pow2 (8 * i)) (pow2 j) in
    e 0; e 1; e 2; e 3; e 4; e 5; e 6; e 7;
    assert_norm (pow2 0 == 1); assert_norm (pow2 1 == 2);
    assert_norm (pow2 2 == 4); assert_norm (pow2 3 == 8);
    assert_norm (pow2 4 == 16); assert_norm (pow2 5 == 32);
    assert_norm (pow2 6 == 64); assert_norm (pow2 7 == 128)

let sbp_prefix (d: pos { d <= 20 }) (f: Seq.lseq nat n)
               (i: nat { i <= n }) (o: nat { o < 32 * d /\ 8 * o + 8 <= d * i })
  : Lemma (Seq.index (simple_bit_pack d f) o ==
           S8.classify (U8.uint_to_t (KP.enc_num d f i / pow2 (8 * o) % 256)))
  = sbp_index d f o;
    byte_val_num d f o;
    KP.enc_num_split d f i n;
    KP.high_add_byte (KP.enc_num d f i) (KP.enc_tail d f i n) (8 * o) (d * i)

let sbu_index (d: pos { d <= 20 }) (b: Seq.lseq S8.t (32 * d)) (i: nat { i < n })
  : Lemma (Seq.index (simple_bit_unpack d b) i == KE.bits_val b (i * d) d)
  = Seq.init_ghost_index_ n (fun j -> (KE.bits_val b (j * d) d <: nat)) i

let bu_index (b0: zq) (d: pos { d <= 20 }) (b: Seq.lseq S8.t (32 * d)) (i: nat { i < n })
  : Lemma (KE.bits_val b (i * d) d < q /\
           Seq.index (bit_unpack b0 d b) i == sub b0 (KE.bits_val b (i * d) d))
  = unpack_bound d (KE.bits_val b (i * d) d);
    Seq.init_ghost_index_ n (fun j ->
      let x = KE.bits_val b (j * d) d in
      unpack_bound d x;
      sub b0 x) i

(** {2 Packing} *)

let pack_ok (d: SZ.t) : prop = 1 <= SZ.v d /\ SZ.v d <= 20

let shl_small (cm: S64.t) (vn: SZ.t { SZ.v vn < 8 })
  : Lemma (requires S64.v cm < pow2 20)
          (ensures FStar.UInt32.v (SZ.sizet_to_uint32 vn) == SZ.v vn /\
                   S64.v (S64.shift_left cm (SZ.sizet_to_uint32 vn)) == S64.v cm * pow2 (SZ.v vn))
  = let k = SZ.v vn in
    Math.pow2_lt_compat 32 3;
    assert_norm (pow2 3 == 8);
    Math.small_mod k (pow2 32);
    Math.lemma_mult_le_right (pow2 k) (S64.v cm) (pow2 20);
    Math.pow2_le_compat 8 k;
    Math.lemma_mult_le_left (pow2 20) (pow2 k) (pow2 8);
    Math.pow2_plus 20 8;
    Math.pow2_lt_compat 64 28;
    Math.small_mod (S64.v cm * pow2 k) (pow2 64)

#push-options "--z3rlimit 200"

(** [out <- SimpleBitPack_d (src signed b f)]: [32 d] bytes. *)
fn pack_poly (out: A.array S8.t) (f: A.array zqt) (d: SZ.t) (signed: bool) (b: zqt)
             (#p: perm) (#vout: erased (Seq.seq S8.t)) (#vf: erased (Seq.seq zqt))
requires A.pts_to out vout ** A.pts_to f #p vf **
         pure (pack_ok d /\ Seq.length vf == n /\ Seq.length vout == 32 * SZ.v d)
ensures exists* v. A.pts_to out v ** A.pts_to f #p vf **
        pure (pack_ok d /\ Seq.length vf == n /\
              v == simple_bit_pack (SZ.v d) (src signed (S32.v b) vf))
{
  A.pts_to_len out;
  A.pts_to_len f;
  HSZ.fits32 ();
  assert_norm (32 * 20 < pow2 32);
  assert_norm (pow2 28 < pow2 64);
  SZ.fits_u32_implies_fits (32 * SZ.v d);
  let dd = SZ.sizet_to_uint32 d;
  KP.enc_num_zero (SZ.v d) (src signed (S32.v b) vf);
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
          SZ.v vo <= 32 * SZ.v d /\ pack_ok d /\
          Seq.length vf == n /\ Seq.length v == 32 * SZ.v d /\
          S64.v va == KP.enc_num (SZ.v d) (src signed (S32.v b) vf) (SZ.v vi) / pow2 (8 * SZ.v vo) /\
          (forall (k: nat). k < SZ.v vo ==>
             Seq.index v k == Seq.index (simple_bit_pack (SZ.v d) (src signed (S32.v b) vf)) k))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let vn = !nb;
    let vo = !o;
    let va = !acc;
    let x = A.(f.(vi));
    let c = if signed then zq_sub b x else x;
    src_index signed (S32.v b) vf (SZ.v vi);
    S64.logand_mask_low (Cast.u32_to_u64 c) dd;
    let cm = S64.logand (Cast.u32_to_u64 c) (S64.mask_low dd);
    assert (pure (S64.v cm == Seq.index (src signed (S32.v b) vf) (SZ.v vi) % pow2 (SZ.v d)));
    Math.pow2_le_compat 20 (SZ.v d);
    Math.lemma_mod_lt (Seq.index (src signed (S32.v b) vf) (SZ.v vi)) (pow2 (SZ.v d));
    Math.lemma_mult_le_right (pow2 (SZ.v vn)) (S64.v cm) (pow2 20);
    Math.pow2_le_compat 8 (SZ.v vn);
    Math.pow2_plus 20 8;
    Math.small_mod (S64.v cm * pow2 (SZ.v vn)) (pow2 64);
    assert (pure (S64.v cm < pow2 20));
    shl_small cm vn;
    let y = S64.shift_left cm (SZ.sizet_to_uint32 vn);
    assert (pure (S64.v y == S64.v cm * pow2 (SZ.v vn)));
    KP.enc_acc_bound (SZ.v d) (src signed (S32.v b) vf) (SZ.v vi) (SZ.v vo) (SZ.v vn);
    KP.enc_push (SZ.v d) (src signed (S32.v b) vf) (SZ.v vi) (SZ.v vo) (SZ.v vn);
    Math.pow2_le_compat 28 (SZ.v vn);
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
            SZ.v vo <= 32 * SZ.v d /\ pack_ok d /\ SZ.v vi < n /\
            Seq.length vf == n /\ Seq.length v == 32 * SZ.v d /\
            S64.v va == KP.enc_num (SZ.v d) (src signed (S32.v b) vf) (SZ.v vi + 1) / pow2 (8 * SZ.v vo) /\
            (forall (k: nat). k < SZ.v vo ==>
               Seq.index v k == Seq.index (simple_bit_pack (SZ.v d) (src signed (S32.v b) vf)) k))
    decreases (SZ.v (!nb))
    {
      let vn = !nb;
      let vo = !o;
      let va = !acc;
      KP.enc_room (SZ.v d) (SZ.v vi) (SZ.v vo) (SZ.v vn);
      sbp_prefix (SZ.v d) (src signed (S32.v b) vf) (SZ.v vi + 1) (SZ.v vo);
      assert_norm (pow2 8 == 256);
      A.((out.(vo) <- Cast.u64_to_u8 va));
      KP.enc_flush (SZ.v d) (src signed (S32.v b) vf) (SZ.v vi + 1) (SZ.v vo);
      acc := S64.shift_right va 8ul;
      nb := SZ.sub vn 8sz;
      o := SZ.add vo 1sz;
    }
  };
  with vie vne voe. assert (pts_to i vie ** pts_to nb vne ** pts_to o voe);
  assert (pure (256 <= SZ.v vie));
  assert (pure (SZ.v vie <= 256));
  assert (pure (SZ.v vie == 256));
  KP.enc_done (SZ.v d) (SZ.v vie) (SZ.v voe) (SZ.v vne);
  with v. assert (A.pts_to out v);
  Seq.lemma_eq_intro v (simple_bit_pack (SZ.v d) (src signed (S32.v b) vf));
  ()
}

#pop-options

(** {2 Unpacking} *)

let unpacked (signed: bool) (b: zq) (d: pos { d <= 20 }) (vb: Seq.lseq S8.t (32 * d))
             (v: Seq.seq zqt { Seq.length v == n }) : prop
  = (signed ==> as_poly v == bit_unpack b d vb) /\
    (not signed ==> as_ints v == simple_bit_unpack d vb)

let field (signed: bool) (b: zq) (d: pos { d <= 20 }) (vb: Seq.lseq S8.t (32 * d)) (k: nat)
  : GTot nat
  = let x = KE.bits_val vb (k * d) d in
    unpack_bound d x;
    if signed then sub b x else x

let unpacked_intro (signed: bool) (b: zq) (d: pos { d <= 20 }) (vb: Seq.lseq S8.t (32 * d))
                   (v: Seq.seq zqt { Seq.length v == n })
  : Lemma (requires forall (k: nat). k < n ==>
             S32.v (Seq.index v k) == field signed b d vb k)
          (ensures unpacked signed b d vb v)
  = if signed then begin
      let aux (k: nat { k < n }) : Lemma (Seq.index (as_poly v) k == Seq.index (bit_unpack b d vb) k)
        = bu_index b d vb k in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro (as_poly v) (bit_unpack b d vb)
    end else begin
      let aux (k: nat { k < n })
        : Lemma (Seq.index (as_ints v) k == Seq.index (simple_bit_unpack d vb) k)
        = sbu_index d vb k in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro (as_ints v) (simple_bit_unpack d vb)
    end

let field_ok (signed: bool) (b: zq) (d: pos { d <= 20 }) (vb: Seq.lseq S8.t (32 * d))
             (k: nat) (x: zqt) : prop
  = S32.v x == field signed b d vb k

#push-options "--z3rlimit 400"

(** [dst <- b - BitUnpack_d vb] (signed) or [SimpleBitUnpack_d vb]. *)
fn unpack_poly (dst: A.array zqt) (bs: A.array S8.t) (d: SZ.t) (signed: bool) (b: zqt)
               (#p: perm) (#vd: erased (Seq.seq zqt)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to bs #p vb **
         pure (pack_ok d /\ Seq.length vd == n /\ Seq.length vb == 32 * SZ.v d)
ensures exists* v. A.pts_to dst v ** A.pts_to bs #p vb **
        pure (pack_ok d /\ Seq.length v == n /\ Seq.length vb == 32 * SZ.v d /\
              unpacked signed (S32.v b) (SZ.v d) vb v /\
              (forall (k: nat). k < n ==> field_ok signed (S32.v b) (SZ.v d) vb k (Seq.index v k)))
{
  A.pts_to_len dst;
  A.pts_to_len bs;
  HSZ.fits32 ();
  assert_norm (32 * 20 < pow2 32);
  assert_norm (pow2 28 < pow2 64);
  SZ.fits_u32_implies_fits (32 * SZ.v d);
  let dd = SZ.sizet_to_uint32 d;
  let mut acc = S64.zero;
  let mut nb = 0sz;
  let mut pos = 0sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi vn vp: SZ.t) (va: S64.t) (v: Seq.seq zqt).
    pts_to i vi ** pts_to nb vn ** pts_to pos vp ** pts_to acc va **
    A.pts_to dst v ** A.pts_to bs #p vb **
    pure (SZ.v vi <= n /\ SZ.v vn < 8 /\
          8 * SZ.v vp == SZ.v d * SZ.v vi + SZ.v vn /\ pack_ok d /\
          Seq.length v == n /\ Seq.length vb == 32 * SZ.v d /\
          S64.v va == le_nat vb / pow2 (SZ.v d * SZ.v vi) % pow2 (SZ.v vn) /\
          (forall (k: nat). k < SZ.v vi ==>
             field_ok signed (S32.v b) (SZ.v d) vb k (Seq.index v k)))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    while (let vn' = !nb; SZ.lt vn' d)
    invariant exists* (vn vp: SZ.t) (va: S64.t) (v: Seq.seq zqt).
      pts_to i vi ** pts_to nb vn ** pts_to pos vp ** pts_to acc va **
      A.pts_to dst v ** A.pts_to bs #p vb **
      pure (SZ.v vi < n /\ SZ.v vn < SZ.v d + 8 /\
            8 * SZ.v vp == SZ.v d * SZ.v vi + SZ.v vn /\ pack_ok d /\
            Seq.length v == n /\ Seq.length vb == 32 * SZ.v d /\
            S64.v va == le_nat vb / pow2 (SZ.v d * SZ.v vi) % pow2 (SZ.v vn) /\
            (forall (k: nat). k < SZ.v vi ==>
               field_ok signed (S32.v b) (SZ.v d) vb k (Seq.index v k)))
    decreases (SZ.v d + 8 - SZ.v (!nb))
    {
      let vn = !nb;
      let vp = !pos;
      let va = !acc;
      KP.dec_room (SZ.v d) (SZ.v vi) (SZ.v vp) (SZ.v vn);
      let bk = A.(bs.(vp));
      Math.pow2_le_compat 20 (SZ.v vn);
      Math.lemma_mult_le_right (pow2 (SZ.v vn)) (S8.v bk) 256;
      Math.pow2_plus 8 20;
      Math.small_mod (S8.v bk * pow2 (SZ.v vn)) (pow2 64);
      let y = S64.shift_left (Cast.u8_to_u64 bk) (SZ.sizet_to_uint32 vn);
      assert (pure (S64.v y == S8.v bk * pow2 (SZ.v vn)));
      KP.dec_read vb (SZ.v d * SZ.v vi) (SZ.v vn) (SZ.v vp);
      Math.pow2_le_compat 28 (SZ.v vn + 8);
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
    KP.dec_val vb (SZ.v d * SZ.v vi) (SZ.v vn) (SZ.v d);
    assert (pure (S64.v m == KE.bits_val vb (SZ.v d * SZ.v vi) (SZ.v d)));
    Math.pow2_le_compat 20 (SZ.v d);
    assert_norm (pow2 20 < q);
    Math.small_mod (S64.v m) (pow2 32);
    let x : zqt = Cast.u64_to_u32 m;
    let r = if signed then zq_sub b x else x;
    Math.swap_mul (SZ.v vi) (SZ.v d);
    assert (pure (field_ok signed (S32.v b) (SZ.v d) vb (SZ.v vi) r));
    A.((dst.(vi) <- r));
    KP.dec_take vb (SZ.v d * SZ.v vi) (SZ.v vn) (SZ.v d);
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
  unpacked_intro signed (S32.v b) (SZ.v d) vb v;
  ()
}

#pop-options
#pop-options
