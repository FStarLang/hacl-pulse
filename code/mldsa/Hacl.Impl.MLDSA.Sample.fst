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


(** The samplers of FIPS 204, algorithms 29 to 33.

    [RejNTTPoly] (ExpandA), [RejBoundedPoly] (ExpandS) and [SampleInBall]
    are rejection samplers over a SHAKE stream.  Each squeezes one block
    at a time ({!Hacl.Impl.MLDSA.XOF}) and stops as soon as it is done,
    which the specification's stability lemmas say is the same answer as
    running to its bounds; reaching a bound yields the zero polynomial,
    exactly as specified.

    Constant time.  The rejection decisions are declassified and branched
    on, as in the reference implementation and in ML-KEM's [SampleNTT]:
    - for [RejNTTPoly] the seed is [rho] and two public indices, and the
      matrix is public;
    - for [RejBoundedPoly] only the one-bit accept/reject outcome of each
      nibble is declassified; the coefficient itself is computed without a
      branch;
    - for [SampleInBall] the challenge is public once the signature is,
      so the positions and the sign bits are declassified. *)
module Hacl.Impl.MLDSA.Sample

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3.Constants
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Sample
open Hacl.Impl.Table
open Hacl.Hash.SHA3
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.XOF
open Hacl.Impl.MLDSA.SampleLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module SCast = Hacl.Secret.Cast
module Declassify = Hacl.Secret.Declassify
module Math = FStar.Math.Lemmas
module HSZ = Hacl.SizeT
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module KZ = Spec.MLKEM.Zq
module SHA3 = Spec.SHA3
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Common pieces} *)

(** The zero polynomial, which is what an exhausted rejection loop
    returns. *)
inline_for_extraction
fn zero_poly (dst: A.array zqt) (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 ** pure (Seq.length v0 == n)
ensures exists* v. A.pts_to dst v **
  pure (Seq.length v == n /\ as_poly v == poly_zero)
{
  A.pts_to_len dst;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v **
    pure (SZ.v vi <= n /\ Seq.length v == n /\
          (forall (k: nat). k < SZ.v vi ==> S32.v (Seq.index v k) == 0))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    A.((dst.(vi) <- S32.classify 0ul));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_poly_intro v poly_zero;
  assert (pure (as_poly v == poly_zero));
}

(** Write [x] at [c] and count it if there is room and it was accepted. *)
inline_for_extraction
fn push_impl (dst: A.array zqt) (c: SZ.t) (ok: bool) (x: zqt) (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 ** pure (Seq.length v0 == n /\ SZ.v c <= n)
returns c': SZ.t
ensures exists* v. A.pts_to dst v ** pure (push_post v0 v (SZ.v c) (SZ.v c') ok (S32.v x))
{
  A.pts_to_len dst;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 257;
  if (SZ.lt c 256sz && ok) {
    A.((dst.(c) <- x));
    SZ.add c 1sz
  } else {
    c
  }
}

(** {2 Uniform sampling: RejNTTPoly} *)

inline_for_extraction
let ntt_candidate (b0 b1 b2: U8.t)
  : r: U32.t { U32.v r == U8.v b0 + 256 * U8.v b1 + 65536 * (U8.v b2 % 128) }
  = let x0 = Cast.uint8_to_uint32 b0 in
    let x1 = Cast.uint8_to_uint32 b1 in
    let x2 = Cast.uint8_to_uint32 b2 in
    U32.add x0 (U32.add (U32.mul 256ul x1) (U32.mul 65536ul (U32.rem x2 128ul)))

inline_for_extraction
let cand_val (d: U32.t) (ok: bool { ok <==> U32.v d < q })
  : r: zqt { ok ==> S32.v r == U32.v d }
  = if ok then S32.classify d else S32.zero

(** One three-byte candidate: {!Spec.MLDSA.Sample.ntt_step}. *)
inline_for_extraction
fn triple_impl (dst: A.array zqt) (blk: A.array S8.t) (c: SZ.t) (u: SZ.t)
               (sd: erased (Seq.seq S8.t)) (t: erased nat)
               (#v0: erased (Seq.seq zqt)) (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to blk #pb vk **
         pure (Seq.length vk == 168 /\ SZ.v u < 56 /\
               agree v0 (SZ.v c) (ntt_sampled sd t) /\
               Seq.index vk (3 * SZ.v u) == shake128_byte sd (3 * reveal t) /\
               Seq.index vk (3 * SZ.v u + 1) == shake128_byte sd (3 * reveal t + 1) /\
               Seq.index vk (3 * SZ.v u + 2) == shake128_byte sd (3 * reveal t + 2))
returns c': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to blk #pb vk **
  pure (agree v (SZ.v c') (ntt_sampled sd (reveal t + 1)))
{
  A.pts_to_len dst;
  A.pts_to_len blk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 168;
  let base = SZ.mul 3sz u;
  let y0 = A.(blk.(base));
  let y1 = A.(blk.(SZ.add base 1sz));
  let y2 = A.(blk.(SZ.add base 2sz));
  let b0 = Declassify.u8 y0;
  let b1 = Declassify.u8 y1;
  let b2 = Declassify.u8 y2;
  let d = ntt_candidate b0 b1 b2;
  assert (pure (U32.v d == ntt_cand sd t));
  let ok = U32.lt d 8380417ul;
  let c' = push_impl dst c ok (cand_val d ok);
  with v. assert (A.pts_to dst v);
  ntt_push sd t v0 v (SZ.v c) (SZ.v c') ok (U32.v d);
  c'
}

(** One SHAKE128 block: the fifty-six candidates it holds exactly. *)
inline_for_extraction
fn block128_impl (dst: A.array zqt) (blk: A.array S8.t) (c: SZ.t)
                 (sd: erased (Seq.seq S8.t)) (t0: erased nat)
                 (#v0: erased (Seq.seq zqt)) (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to blk #pb vk **
         pure (Seq.length vk == 168 /\
               agree v0 (SZ.v c) (ntt_sampled sd t0) /\
               (forall (u: nat). u < 168 ==>
                  Seq.index vk u == shake128_byte sd (3 * reveal t0 + u)))
returns c': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to blk #pb vk **
  pure (agree v (SZ.v c') (ntt_sampled sd (reveal t0 + 56)))
{
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 56;
  let mut cnt = c;
  let mut uu = 0sz;
  while (let vu = !uu; SZ.lt vu 56sz)
  invariant exists* (vu: SZ.t) (vc: SZ.t) (v: Seq.seq zqt).
    pts_to uu vu ** pts_to cnt vc ** A.pts_to dst v ** A.pts_to blk #pb vk **
    pure (SZ.v vu <= 56 /\ Seq.length vk == 168 /\
          (forall (u: nat). u < 168 ==>
             Seq.index vk u == shake128_byte sd (3 * reveal t0 + u)) /\
          agree v (SZ.v vc) (ntt_sampled sd (reveal t0 + SZ.v vu)))
  decreases (56 - SZ.v (!uu))
  {
    let vu = !uu;
    let vc = !cnt;
    let x = triple_impl dst blk vc vu sd (hide (reveal t0 + SZ.v vu));
    cnt := x;
    uu := SZ.add vu 1sz;
  };
  let vf = !uu;
  assert (pure (SZ.v vf == 56));
  !cnt
}

#push-options "--z3rlimit 200"

(** [dst <- RejNTTPoly seed]. *)
fn rej_ntt_poly_impl (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                     (#vd: erased (Seq.seq zqt))
                     (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to seed #ps vs **
         pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs)
ensures exists* v. A.pts_to dst v ** A.pts_to seed #ps vs **
  pure (Seq.length v == n /\ as_poly v == rej_ntt_poly vs)
{
  A.pts_to_len dst;
  A.pts_to_len seed;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let z64 = S64.classify 0uL;
  let mut starr = [| z64; 25sz |];
  Mem.track starr;
  A.pts_to_len starr;
  let mut barr = [| z64; 25sz |];
  Mem.track barr;
  A.pts_to_len barr;
  let z8 = S8.classify 0uy;
  let mut blk = [| z8; 168sz |];
  Mem.track blk;
  A.pts_to_len blk;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  with prc vrc. assert (A.pts_to rc_tbl #prc vrc);
  assert (pure (reveal vrc == (rc <: Seq.seq S64.t)));

  xof_absorb starr barr rc_tbl seed slen 168sz;

  ntt_sampled_zero vs;
  with v0. assert (A.pts_to dst v0);
  agree_empty v0;

  let mut cnt = 0sz;
  let mut jj = 0sz;
  while (let vc = !cnt; let vj = !jj; SZ.lt vc 256sz && SZ.lt vj 16sz)
  invariant exists* (vc: SZ.t) (vj: SZ.t) (v: Seq.seq zqt)
                    (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vk: Seq.seq S8.t).
    pts_to cnt vc ** pts_to jj vj ** A.pts_to dst v **
    A.pts_to starr vst ** A.pts_to barr vb ** A.pts_to blk vk **
    A.pts_to rc_tbl #prc vrc **
    pure (SZ.v vj <= 16 /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length vk == 168 /\
          reveal vrc == (rc <: Seq.seq S64.t) /\
          reveal vst == SHA3.squeeze_state (xof_prev (SZ.v vj)) (xof_start 168 vs) /\
          agree v (SZ.v vc) (ntt_sampled vs (SZ.v vj * 56)))
  decreases (16 - SZ.v (!jj))
  {
    let vj = !jj;
    let vc = !cnt;
    xof_block blk starr barr rc_tbl 168sz vj (hide (xof_start 168 vs));
    block128_bytes vs (SZ.v vj);
    assert (pure (3 * (SZ.v vj * 56) == SZ.v vj * 168));
    let x = block128_impl dst blk vc vs (hide (SZ.v vj * 56));
    assert (pure (SZ.v vj * 56 + 56 == (SZ.v vj + 1) * 56));
    cnt := x;
    jj := SZ.add vj 1sz;
  };

  drop_table rc_tbl;
  Mem.wipe blk 168sz;
  Mem.wipe barr 25sz;
  Mem.wipe starr 25sz;
  let vc = !cnt;
  let vj = !jj;
  with v. assert (A.pts_to dst v);
  ntt_done vs (SZ.v vj * 56) v (SZ.v vc);
  if (SZ.lt vc 256sz) {
    zero_poly dst;
  }
}

#pop-options

(** {2 Bounded sampling: RejBoundedPoly} *)

(** [CoeffFromHalfByte]'s value, without a branch on the nibble. *)
inline_for_extraction
let coeff_impl (eta: SZ.t { SZ.v eta == 2 \/ SZ.v eta == 4 }) (z: S32.t { S32.v z < 16 })
  : r: zqt { S32.v r == coeff_of (SZ.v eta) (S32.v z) }
  = assert_norm (pow2 32 == 4294967296);
    if SZ.eq eta 2sz then begin
      let ten = S32.classify 10ul in
      let five = S32.classify 5ul in
      let m1 = S32.select (S32.gte_mask z ten) (S32.sub_mod z ten) z in
      assert (S32.v m1 == (if S32.v z >= 10 then S32.v z - 10 else S32.v z));
      let m2 = S32.select (S32.gte_mask m1 five) (S32.sub_mod m1 five) m1 in
      assert (S32.v m2 == (if S32.v m1 >= 5 then S32.v m1 - 5 else S32.v m1));
      mod5 (S32.v z);
      sub_of_int 2 (S32.v m2);
      zq_sub (S32.classify 2ul) m2
    end else begin
      sub_of_int 4 (S32.v z);
      zq_sub (S32.classify 4ul) z
    end

(** One nibble: accepted if it is in range, which is the one bit that is
    declassified. *)
inline_for_extraction
fn half_impl (dst: A.array zqt) (c: SZ.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
             (z: S32.t) (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 **
         pure (Seq.length v0 == n /\ SZ.v c <= n /\ S32.v z < 16 /\
               (SZ.v eta == 2 \/ SZ.v eta == 4))
returns c': SZ.t
ensures exists* v. A.pts_to dst v **
  pure ((SZ.v eta == 2 \/ SZ.v eta == 4) /\
        push_post v0 v (SZ.v c) (SZ.v c') (coeff_ok (SZ.v eta) (S32.v z))
                  (coeff_of (SZ.v eta) (S32.v z)))
{
  let bound = (if SZ.eq eta 2sz then 15ul else 9ul);
  let m = S32.lt_mask z (S32.classify bound);
  let ok = not (U32.eq (Declassify.u32 m) 0ul);
  assert (pure (ok == coeff_ok (SZ.v eta) (S32.v z)));
  let x = coeff_impl eta z;
  push_impl dst c ok x
}

let nibbles (z: nat { z < 256 })
  : Lemma (z / 16 < 16 /\ (z - (z / 16) * 16) == z % 16)
  = Math.lemma_div_mod z 16

(** One byte: two nibbles, low first, {!Spec.MLDSA.Sample.bounded_step}. *)
inline_for_extraction
fn byte_impl (dst: A.array zqt) (blk: A.array S8.t) (c: SZ.t) (u: SZ.t)
             ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
             (sd: erased (Seq.seq S8.t)) (t: erased nat)
             (#v0: erased (Seq.seq zqt)) (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to blk #pb vk **
         pure (Seq.length vk == 136 /\ SZ.v u < 136 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
               agree v0 (SZ.v c) (bounded_sampled (SZ.v eta) sd t) /\
               Seq.index vk (SZ.v u) == shake256_byte sd t)
returns c': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to blk #pb vk **
  pure ((SZ.v eta == 2 \/ SZ.v eta == 4) /\
        agree v (SZ.v c') (bounded_sampled (SZ.v eta) sd (reveal t + 1)))
{
  A.pts_to_len blk;
  let y = A.(blk.(u));
  let z = SCast.u8_to_u32 y;
  let hi = S32.shift_right z 4ul;
  assert_norm (pow2 4 == 16);
  assert_norm (pow2 32 == 4294967296);
  nibbles (S8.v y);
  Math.small_mod (S32.v hi * 16) (pow2 32);
  let lo = S32.sub_mod z (S32.shift_left hi 4ul);
  Math.small_mod (S32.v z - S32.v hi * 16) (pow2 32);
  assert (pure (S32.v lo == S8.v y % 16 /\ S32.v hi == S8.v y / 16));
  let c1 = half_impl dst c eta lo;
  with v1. assert (A.pts_to dst v1);
  half_push (SZ.v eta) (bounded_sampled (SZ.v eta) sd t) (S32.v lo) v0 v1 (SZ.v c) (SZ.v c1)
            (coeff_ok (SZ.v eta) (S32.v lo)) (coeff_of (SZ.v eta) (S32.v lo));
  let c2 = half_impl dst c1 eta hi;
  with v2. assert (A.pts_to dst v2);
  half_push (SZ.v eta) (push_half (SZ.v eta) (bounded_sampled (SZ.v eta) sd t) (S32.v lo))
            (S32.v hi) v1 v2 (SZ.v c1) (SZ.v c2)
            (coeff_ok (SZ.v eta) (S32.v hi)) (coeff_of (SZ.v eta) (S32.v hi));
  bounded_succ (SZ.v eta) sd t;
  c2
}

(** One SHAKE256 block of 136 bytes. *)
inline_for_extraction
fn block256_bounded_impl (dst: A.array zqt) (blk: A.array S8.t) (c: SZ.t)
                         ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                         (sd: erased (Seq.seq S8.t)) (t0: erased nat)
                         (#v0: erased (Seq.seq zqt)) (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to blk #pb vk **
         pure (Seq.length vk == 136 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
               agree v0 (SZ.v c) (bounded_sampled (SZ.v eta) sd t0) /\
               (forall (u: nat). u < 136 ==>
                  Seq.index vk u == shake256_byte sd (reveal t0 + u)))
returns c': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to blk #pb vk **
  pure ((SZ.v eta == 2 \/ SZ.v eta == 4) /\
        agree v (SZ.v c') (bounded_sampled (SZ.v eta) sd (reveal t0 + 136)))
{
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 136;
  let mut cnt = c;
  let mut uu = 0sz;
  while (let vu = !uu; SZ.lt vu 136sz)
  invariant exists* (vu: SZ.t) (vc: SZ.t) (v: Seq.seq zqt).
    pts_to uu vu ** pts_to cnt vc ** A.pts_to dst v ** A.pts_to blk #pb vk **
    pure (SZ.v vu <= 136 /\ Seq.length vk == 136 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
          (forall (u: nat). u < 136 ==>
             Seq.index vk u == shake256_byte sd (reveal t0 + u)) /\
          agree v (SZ.v vc) (bounded_sampled (SZ.v eta) sd (reveal t0 + SZ.v vu)))
  decreases (136 - SZ.v (!uu))
  {
    let vu = !uu;
    let vc = !cnt;
    let x = byte_impl dst blk vc vu eta sd (hide (reveal t0 + SZ.v vu));
    cnt := x;
    uu := SZ.add vu 1sz;
  };
  let vf = !uu;
  assert (pure (SZ.v vf == 136));
  !cnt
}

#push-options "--z3rlimit 200"

(** [dst <- RejBoundedPoly_eta seed]. *)
fn rej_bounded_poly_impl (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                         ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                         (#vd: erased (Seq.seq zqt))
                         (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to seed #ps vs **
         pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs /\
               (SZ.v eta == 2 \/ SZ.v eta == 4))
ensures exists* v. A.pts_to dst v ** A.pts_to seed #ps vs **
  pure (Seq.length v == n /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
        as_poly v == rej_bounded_poly (SZ.v eta) vs)
{
  A.pts_to_len dst;
  A.pts_to_len seed;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  let z64 = S64.classify 0uL;
  let mut starr = [| z64; 25sz |];
  Mem.track starr;
  A.pts_to_len starr;
  let mut barr = [| z64; 25sz |];
  Mem.track barr;
  A.pts_to_len barr;
  let z8 = S8.classify 0uy;
  let mut blk = [| z8; 136sz |];
  Mem.track blk;
  A.pts_to_len blk;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  with prc vrc. assert (A.pts_to rc_tbl #prc vrc);
  assert (pure (reveal vrc == (rc <: Seq.seq S64.t)));

  xof_absorb starr barr rc_tbl seed slen 136sz;

  bounded_sampled_zero (SZ.v eta) vs;
  with v0. assert (A.pts_to dst v0);
  agree_empty v0;

  let mut cnt = 0sz;
  let mut jj = 0sz;
  while (let vc = !cnt; let vj = !jj; SZ.lt vc 256sz && SZ.lt vj 8sz)
  invariant exists* (vc: SZ.t) (vj: SZ.t) (v: Seq.seq zqt)
                    (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vk: Seq.seq S8.t).
    pts_to cnt vc ** pts_to jj vj ** A.pts_to dst v **
    A.pts_to starr vst ** A.pts_to barr vb ** A.pts_to blk vk **
    A.pts_to rc_tbl #prc vrc **
    pure (SZ.v vj <= 8 /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length vk == 136 /\
          reveal vrc == (rc <: Seq.seq S64.t) /\
          reveal vst == SHA3.squeeze_state (xof_prev (SZ.v vj)) (xof_start 136 vs) /\
          agree v (SZ.v vc) (bounded_sampled (SZ.v eta) vs (SZ.v vj * 136)))
  decreases (8 - SZ.v (!jj))
  {
    let vj = !jj;
    let vc = !cnt;
    xof_block blk starr barr rc_tbl 136sz vj (hide (xof_start 136 vs));
    block256_bytes vs (SZ.v vj);
    let x = block256_bounded_impl dst blk vc eta vs (hide (SZ.v vj * 136));
    assert (pure (SZ.v vj * 136 + 136 == (SZ.v vj + 1) * 136));
    cnt := x;
    jj := SZ.add vj 1sz;
  };

  drop_table rc_tbl;
  Mem.wipe blk 136sz;
  Mem.wipe barr 25sz;
  Mem.wipe starr 25sz;
  let vc = !cnt;
  let vj = !jj;
  with v. assert (A.pts_to dst v);
  bounded_done (SZ.v eta) vs (SZ.v vj * 136) v (SZ.v vc);
  if (SZ.lt vc 256sz) {
    zero_poly dst;
  }
}

#pop-options

(** {2 The challenge: SampleInBall} *)

(** Bit [s] of a public byte. *)
inline_for_extraction
let bit_of (b: U8.t) (s: SZ.t { SZ.v s < 8 })
  : r: bool { r == ((U8.v b / pow2 (SZ.v s)) % 2 = 1) }
  = assert_norm (pow2 32 == 4294967296);
    Math.small_mod (SZ.v s) (pow2 32);
    U8.rem (U8.shift_right b (SZ.sizet_to_uint32 s)) 2uy = 1uy

(** One stream byte, {!Spec.MLDSA.Sample.ball_step}.  [sgn] holds the
    eight sign bytes. *)
inline_for_extraction
fn ball_byte_impl (dst: A.array zqt) (sgn: A.array S8.t) (blk: A.array S8.t) (i: SZ.t) (u: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                  (sd: erased (Seq.seq S8.t)) (t: erased nat)
                  (#v0: erased (Seq.seq zqt)) (#pg: perm) (#vg: erased (Seq.seq S8.t))
                  (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to sgn #pg vg ** A.pts_to blk #pb vk **
         pure (Seq.length vk == 136 /\ SZ.v u < 136 /\ 0 < SZ.v tau /\ SZ.v tau <= 60 /\
               Seq.length vg == 8 /\
               (forall (k: nat). k < 8 ==> Seq.index vg k == shake256_byte sd k) /\
               ball_agree v0 (SZ.v i) (ball_sampled (SZ.v tau) sd t) /\
               ball_ok (SZ.v tau) (ball_sampled (SZ.v tau) sd t) /\
               Seq.index vk (SZ.v u) == shake256_byte sd (8 + t))
returns i': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to sgn #pg vg ** A.pts_to blk #pb vk **
  pure (0 < SZ.v tau /\ SZ.v tau <= 60 /\
        ball_agree v (SZ.v i') (ball_sampled (SZ.v tau) sd (reveal t + 1)) /\
        ball_ok (SZ.v tau) (ball_sampled (SZ.v tau) sd (reveal t + 1)))
{
  A.pts_to_len dst;
  A.pts_to_len sgn;
  A.pts_to_len blk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 512;
  let y = A.(blk.(u));
  let jb = Declassify.u8 y;
  let j = SZ.uint16_to_sizet (Cast.uint8_to_uint16 jb);
  if (SZ.lt i 256sz && SZ.lte j i) {
    let cj = A.(dst.(j));
    A.((dst.(i) <- cj));
    let kk = SZ.sub (SZ.add i tau) 256sz;
    let sb = A.(sgn.(SZ.div kk 8sz));
    let bit = bit_of (Declassify.u8 sb) (SZ.rem kk 8sz);
    assert (pure (bit == sign_bit sd (SZ.v kk)));
    let sv = (if bit then S32.classify 8380416ul else S32.classify 1ul);
    A.((dst.(j) <- sv));
    with v. assert (A.pts_to dst v);
    ball_push (SZ.v tau) sd t v0 v (SZ.v i) (SZ.v i + 1) (SZ.v j) sv;
    SZ.add i 1sz
  } else {
    ball_push (SZ.v tau) sd t v0 v0 (SZ.v i) (SZ.v i) (SZ.v j) (S32.classify 1ul);
    i
  }
}

(** The bytes [u0 .. 136) of a SHAKE256 block that starts at stream
    offset [tb]. *)
inline_for_extraction
fn ball_block_impl (dst: A.array zqt) (sgn: A.array S8.t) (blk: A.array S8.t) (i: SZ.t)
                   (u0: SZ.t) ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                   (sd: erased (Seq.seq S8.t)) (tb: erased nat)
                   (#v0: erased (Seq.seq zqt)) (#pg: perm) (#vg: erased (Seq.seq S8.t))
                   (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to sgn #pg vg ** A.pts_to blk #pb vk **
         pure (Seq.length vk == 136 /\ SZ.v u0 <= 136 /\ 8 <= reveal tb + SZ.v u0 /\
               0 < SZ.v tau /\ SZ.v tau <= 60 /\ Seq.length vg == 8 /\
               (forall (k: nat). k < 8 ==> Seq.index vg k == shake256_byte sd k) /\
               (forall (u: nat). u < 136 ==> Seq.index vk u == shake256_byte sd (reveal tb + u)) /\
               ball_agree v0 (SZ.v i) (ball_sampled (SZ.v tau) sd (reveal tb + SZ.v u0 - 8)) /\
               ball_ok (SZ.v tau) (ball_sampled (SZ.v tau) sd (reveal tb + SZ.v u0 - 8)))
returns i': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to sgn #pg vg ** A.pts_to blk #pb vk **
  pure (0 < SZ.v tau /\ SZ.v tau <= 60 /\ 8 <= reveal tb + 136 /\
        ball_agree v (SZ.v i') (ball_sampled (SZ.v tau) sd (reveal tb + 136 - 8)) /\
        ball_ok (SZ.v tau) (ball_sampled (SZ.v tau) sd (reveal tb + 136 - 8)))
{
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 136;
  let mut ii = i;
  let mut uu = u0;
  while (let vu = !uu; SZ.lt vu 136sz)
  invariant exists* (vu: SZ.t) (vi: SZ.t) (v: Seq.seq zqt).
    pts_to uu vu ** pts_to ii vi ** A.pts_to dst v **
    A.pts_to sgn #pg vg ** A.pts_to blk #pb vk **
    pure (SZ.v u0 <= SZ.v vu /\ SZ.v vu <= 136 /\ Seq.length vk == 136 /\
          8 <= reveal tb + SZ.v u0 /\
          0 < SZ.v tau /\ SZ.v tau <= 60 /\ Seq.length vg == 8 /\
          (forall (k: nat). k < 8 ==> Seq.index vg k == shake256_byte sd k) /\
          (forall (u: nat). u < 136 ==> Seq.index vk u == shake256_byte sd (reveal tb + u)) /\
          ball_agree v (SZ.v vi) (ball_sampled (SZ.v tau) sd (reveal tb + SZ.v vu - 8)) /\
          ball_ok (SZ.v tau) (ball_sampled (SZ.v tau) sd (reveal tb + SZ.v vu - 8)))
  decreases (136 - SZ.v (!uu))
  {
    let vu = !uu;
    let vi = !ii;
    let x = ball_byte_impl dst sgn blk vi vu tau sd (hide (reveal tb + SZ.v vu - 8));
    ii := x;
    uu := SZ.add vu 1sz;
  };
  let vf = !uu;
  assert (pure (SZ.v vf == 136));
  !ii
}

let ball_exit (vi vj: SZ.t)
  : Lemma (requires false == (SZ.lt vi 256sz && SZ.lt vj 8sz) /\
                    SZ.v vi <= n /\ SZ.v vj <= 8)
          (ensures SZ.v vi == n \/ SZ.v vj == 8)
  = ()

#push-options "--z3rlimit 200"

(** [dst <- SampleInBall seed] for the parameter set's [tau]. *)
fn sample_in_ball_impl (p: erased params) (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                       ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                       (#vd: erased (Seq.seq zqt))
                       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to seed #ps vs **
         pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs /\ SZ.v tau == p.tau)
ensures exists* v. A.pts_to dst v ** A.pts_to seed #ps vs **
  pure (Seq.length v == n /\ as_poly v == sample_in_ball p vs)
{
  A.pts_to_len dst;
  A.pts_to_len seed;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits 256;
  zero_poly dst;
  let z64 = S64.classify 0uL;
  let mut starr = [| z64; 25sz |];
  Mem.track starr;
  A.pts_to_len starr;
  let mut barr = [| z64; 25sz |];
  Mem.track barr;
  A.pts_to_len barr;
  let z8 = S8.classify 0uy;
  let mut blk = [| z8; 136sz |];
  Mem.track blk;
  A.pts_to_len blk;
  let mut sgn = [| z8; 8sz |];
  Mem.track sgn;
  A.pts_to_len sgn;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  with prc vrc. assert (A.pts_to rc_tbl #prc vrc);
  assert (pure (reveal vrc == (rc <: Seq.seq S64.t)));

  xof_absorb starr barr rc_tbl seed slen 136sz;
  xof_block blk starr barr rc_tbl 136sz 0sz (hide (xof_start 136 vs));
  block256_bytes vs 0;
  Copy.copy_prefix sgn blk 8sz;

  with v0. assert (A.pts_to dst v0);
  ball_start (SZ.v tau) vs v0;
  ball_sampled_ok (SZ.v tau) vs 0;
  let i0 = ball_block_impl dst sgn blk (SZ.sub 256sz tau) 8sz tau vs (hide 0);

  let mut ii = i0;
  let mut jj = 1sz;
  while (let vi = !ii; let vj = !jj; SZ.lt vi 256sz && SZ.lt vj 8sz)
  invariant exists* (vi: SZ.t) (vj: SZ.t) (v: Seq.seq zqt)
                    (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vk: Seq.seq S8.t)
                    (vg: Seq.seq S8.t).
    pts_to ii vi ** pts_to jj vj ** A.pts_to dst v **
    A.pts_to starr vst ** A.pts_to barr vb ** A.pts_to blk vk ** A.pts_to sgn vg **
    A.pts_to rc_tbl #prc vrc **
    pure (1 <= SZ.v vj /\ SZ.v vj <= 8 /\ 0 < SZ.v tau /\ SZ.v tau <= 60 /\
          SZ.v tau == p.tau /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length vk == 136 /\
          Seq.length vg == 8 /\
          (forall (k: nat). k < 8 ==> Seq.index vg k == shake256_byte vs k) /\
          reveal vrc == (rc <: Seq.seq S64.t) /\
          reveal vst == SHA3.squeeze_state (xof_prev (SZ.v vj)) (xof_start 136 vs) /\
          ball_agree v (SZ.v vi) (ball_sampled (SZ.v tau) vs (SZ.v vj * 136 - 8)) /\
          ball_ok (SZ.v tau) (ball_sampled (SZ.v tau) vs (SZ.v vj * 136 - 8)))
  decreases (8 - SZ.v (!jj))
  {
    let vj = !jj;
    let vi = !ii;
    xof_block blk starr barr rc_tbl 136sz vj (hide (xof_start 136 vs));
    block256_bytes vs (SZ.v vj);
    ball_idx (SZ.v vj);
    let x = ball_block_impl dst sgn blk vi 0sz tau vs (hide (SZ.v vj * 136));
    ii := x;
    jj := SZ.add vj 1sz;
  };

  drop_table rc_tbl;
  Mem.wipe sgn 8sz;
  Mem.wipe blk 136sz;
  Mem.wipe barr 25sz;
  Mem.wipe starr 25sz;
  with (vi: SZ.t) (vj: SZ.t) (v: Seq.seq zqt).
    assert (pts_to ii vi ** pts_to jj vj ** A.pts_to dst v);
  ball_exit vi vj;
  ball_idx (SZ.v vj);
  ball_done (SZ.v tau) vs (SZ.v vj * 136 - 8) v (SZ.v vi);
  let fi = !ii;
  if (SZ.lt fi 256sz) {
    zero_poly dst;
  }
}

(** {2 Expansion: ExpandS}

    ExpandA, which samples four entries at a time, is in
    {!Hacl.Impl.MLDSA.Sample4}. *)

(** [s1] ([second = false], [l] polynomials, nonces [0 .. l)) or [s2]
    ([second = true], [k] polynomials, nonces [l .. l + k)). *)
fn expand_s_part_impl (p: erased params) (second: erased bool)
                      (dst: A.array zqt) (rho: A.array S8.t)
                      ([@@@FStar.Attributes.monomorphize] cnt: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] off: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                      (#vd: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 64 /\ SZ.v cnt == s_count p second /\
               SZ.v off == s_off p second /\ SZ.v eta == p.eta /\
               Seq.length vd == SZ.v cnt * n)
ensures exists* v. A.pts_to dst v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ SZ.v cnt == s_count p second /\
        Seq.length v == SZ.v cnt * n /\
        as_zqs v == s_target p vr second)
{
  A.pts_to_len dst;
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  let z8 = S8.classify 0uy;
  let mut sd = [| z8; 66sz |];
  Mem.track sd;
  A.pts_to_len sd;
  Copy.copy_prefix sd rho 64sz;
  A.((sd.(65sz) <- S8.classify 0uy));
  prefix_zero vd (s_target p vr second);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc cnt)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt) (vsd: Seq.seq S8.t).
    pts_to c vc ** A.pts_to dst v ** A.pts_to rho #pr vr ** A.pts_to sd vsd **
    pure (SZ.v vc <= SZ.v cnt /\ SZ.v cnt == s_count p second /\
          SZ.v off == s_off p second /\ SZ.v eta == p.eta /\
          Seq.length v == SZ.v cnt * n /\ Seq.length vr == 64 /\
          Seq.length vsd == 66 /\
          (forall (t: nat). t < 64 ==> Seq.index vsd t == Seq.index vr t) /\
          S8.v (Seq.index vsd 65) == 0 /\
          prefix_eq v (s_target p vr second) (SZ.v vc * n))
  decreases (SZ.v cnt - SZ.v (!c))
  {
    let vc = !c;
    Math.lemma_mult_le_right n (SZ.v vc + 1) (SZ.v cnt);
    Math.distributivity_add_left (SZ.v vc) 1 n;
    Math.lemma_mult_le_right n (SZ.v cnt) 8;
    SZ.fits_u32_implies_fits (SZ.v vc * n + n);
    SZ.fits_u32_implies_fits (SZ.v vc + 1);
    let lo = SZ.mul vc 256sz;
    let hi = SZ.add lo 256sz;
    let x = SZ.add vc off;
    let bx = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 x);
    Math.small_mod (SZ.v x) 256;
    Math.small_mod (SZ.v x) 4294967296;
    A.((sd.(64sz) <- S8.classify bx));
    with vsd. assert (A.pts_to sd vsd);
    with w0. assert (A.pts_to dst w0);
    let blk = Sub.sub dst lo hi;
    rej_bounded_poly_impl blk sd 66sz eta;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    expand_s_step p vr second (SZ.v vc) w0 w1 b1 vsd;
    c := SZ.add vc 1sz;
  };
  with v. assert (A.pts_to dst v);
  prefix_done (s_count p second) v (s_target p vr second);
  assert (pure (as_zqs v == s_target p vr second));
  Mem.wipe sd 66sz;
}

(** Algorithm 33: [s1 <- ExpandS_1 rho'] and [s2 <- ExpandS_2 rho']. *)
fn expand_s_impl (p: erased params) (s1: A.array zqt) (s2: A.array zqt) (rho: A.array S8.t)
                 ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                 (#v1: erased (Seq.seq zqt)) (#v2: erased (Seq.seq zqt))
                 (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to rho #pr vr **
         pure (Seq.length vr == 64 /\ SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
               Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n)
ensures exists* w1 w2. A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length w1 == p.l * n /\ Seq.length w2 == p.k * n /\
        as_zqs w1 == expand_s1 p vr /\ as_zqs w2 == expand_s2 p vr)
{
  expand_s_part_impl p (hide false) s1 rho l 0sz eta;
  expand_s_part_impl p (hide true) s2 rho k l eta;
}

#pop-options

#pop-options
