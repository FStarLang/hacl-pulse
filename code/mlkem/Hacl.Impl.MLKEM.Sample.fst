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

(** The two samplers, FIPS 203 algorithms 7 and 8.

    [SampleNTT] is the only place in ML-KEM where control flow depends on
    data, and it is the one place where that is not a leak: the seed is
    [rho] and a pair of public indices, and the matrix it produces travels
    in the clear as part of the encapsulation key.  So the three bytes of
    each candidate are declassified -- {!Hacl.Secret.Declassify} is where
    that claim is written down -- and the rejection test is an ordinary
    branch.

    The loop is the specification's, restructured in two ways.  It runs
    over blocks and then over the fifty-six triples a 168-byte SHAKE128
    block holds exactly, so no candidate ever straddles a block and no
    buffering is needed.  And it stops as soon as 256 coefficients have
    been accepted, which {!Spec.MLKEM.Sample.sampled_stable} says is the
    same answer as running to the specification's bound.  Three or four
    blocks is the overwhelmingly likely cost; sixteen is the bound, and
    reaching it yields the zero polynomial, exactly as specified.

    [SamplePolyCBD] has no such drama: it is a fixed number of bit
    look-ups, all of them secret, with no branch anywhere. *)
module Hacl.Impl.MLKEM.Sample

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Encode
open Spec.MLKEM.Sample
open Spec.SHA3
open Spec.SHA3.Constants
open Hacl.Impl.Table
open Hacl.Hash.SHA3
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.XOF

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Declassify = Hacl.Secret.Declassify
module Math = FStar.Math.Lemmas
module HSZ = Hacl.SizeT

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 Uniform sampling} *)

(** The whole polynomial set to zero, which is what an exhausted
    rejection loop returns. *)
inline_for_extraction
fn zero_poly (dst: A.array zqt) (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 ** pure (Seq.length v0 == n)
ensures exists* v. A.pts_to dst v **
  pure (Seq.length v == n /\ as_poly v == poly_zero)
{
  A.pts_to_len dst;
  HSZ.fits32 ();
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v **
    pure (SZ.v vi <= n /\ Seq.length v == n /\
          (forall (k: nat). k < SZ.v vi ==> S16.v (Seq.index v k) == 0))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    A.((dst.(vi) <- S16.classify 0us));
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_poly_intro v poly_zero;
  assert (pure (as_poly v == poly_zero));
}

(** One candidate: accepted if there is room and it is below [q].  The
    specification side of this is {!Spec.MLKEM.Sample.push}, but the two
    are deliberately kept apart: stating it operationally, as a count and
    an array update, keeps the sampler's ghost accumulator out of this
    function's arguments, and a ghost argument mentioning
    {!Spec.MLKEM.Sample.cand1} costs minutes of normalisation. *)
inline_for_extraction
fn push_impl (dst: A.array zqt) (c: SZ.t) (d: U32.t) (#v0: erased (Seq.seq zqt))
requires A.pts_to dst v0 **
         pure (Seq.length v0 == n /\ U32.v d < 4096 /\ SZ.v c <= n)
returns c': SZ.t
ensures exists* v. A.pts_to dst v **
  pure (Seq.length v == n /\ Seq.length v0 == n /\ SZ.v c <= n /\ SZ.v c' <= n /\
        (forall (k: nat). k < SZ.v c ==> Seq.index v k == Seq.index v0 k) /\
        ((SZ.v c < n /\ U32.v d < q) ==>
           (SZ.v c' == SZ.v c + 1 /\ S16.v (Seq.index v (SZ.v c)) == U32.v d)) /\
        ((SZ.v c == n \/ U32.v d >= q) ==> SZ.v c' == SZ.v c))
{
  A.pts_to_len dst;
  HSZ.fits32 ();
  assert_norm (pow2 16 == 65536);
  if (SZ.lt c 256sz && U32.lt d 3329ul) {
    Math.small_mod (U32.v d) (pow2 16);
    A.((dst.(c) <- S16.classify (Cast.uint32_to_uint16 d)));
    SZ.fits_u32_implies_fits (SZ.v c + 1);
    SZ.add c 1sz
  } else {
    c
  }
}

(** The two twelve-bit candidates a three-byte group carries, taken apart
    exactly as {!Spec.MLKEM.Sample.cand1} and {!Spec.MLKEM.Sample.cand2}
    say. *)
inline_for_extraction
let candidates (b0 b1 b2: U8.t)
  : r: (U32.t & U32.t) { U32.v (fst r) == U8.v b0 + 256 * (U8.v b1 % 16) /\
                         U32.v (snd r) == U8.v b1 / 16 + 16 * U8.v b2 /\
                         U32.v (fst r) < 4096 /\ U32.v (snd r) < 4096 }
= let x0 = Cast.uint8_to_uint32 b0 in
  let x1 = Cast.uint8_to_uint32 b1 in
  let x2 = Cast.uint8_to_uint32 b2 in
  let d1 = U32.add x0 (U32.mul 256ul (U32.rem x1 16ul)) in
  let d2 = U32.add (U32.div x1 16ul) (U32.mul 16ul x2) in
  (d1, d2)

(** One three-byte group: two candidates, each pushed.  This is
    {!Spec.MLKEM.Sample.sample_step}, and it is a separate function so that
    the step's arithmetic -- unfolding the fold by one -- is proved once
    here rather than inside the sampler's loop. *)
inline_for_extraction
fn triple_impl (dst: A.array zqt) (blk: A.array S8.t) (c: SZ.t) (u: SZ.t)
               (sd: erased (Seq.seq S8.t)) (t: erased nat)
               (#v0: erased (Seq.seq zqt)) (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to blk #pb vk **
         pure (Seq.length v0 == n /\ Seq.length vk == 168 /\ SZ.v u < 56 /\
               SZ.v c == Seq.length (sampled sd t) /\
               (forall (k: nat). k < SZ.v c ==>
                  S16.v (Seq.index v0 k) == Seq.index (sampled sd t) k) /\
               Seq.index vk (3 * SZ.v u) == xof_byte sd (3 * reveal t) /\
               Seq.index vk (3 * SZ.v u + 1) == xof_byte sd (3 * reveal t + 1) /\
               Seq.index vk (3 * SZ.v u + 2) == xof_byte sd (3 * reveal t + 2))
returns c': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to blk #pb vk **
  pure (Seq.length v == n /\ SZ.v c' == Seq.length (sampled sd (reveal t + 1)) /\
        (forall (k: nat). k < SZ.v c' ==>
           S16.v (Seq.index v k) == Seq.index (sampled sd (reveal t + 1)) k))
{
  A.pts_to_len dst;
  A.pts_to_len blk;
  HSZ.fits32 ();
  assert_norm (168 < pow2 32);
  SZ.fits_u32_implies_fits (3 * SZ.v u + 2);
  let base = SZ.mul 3sz u;
  let y0 = A.(blk.(base));
  let y1 = A.(blk.(SZ.add base 1sz));
  let y2 = A.(blk.(SZ.add base 2sz));
  let b0 = Declassify.u8 y0;
  let b1 = Declassify.u8 y1;
  let b2 = Declassify.u8 y2;
  let ds = candidates b0 b1 b2;
  assert (pure (U32.v (fst ds) == cand1 sd t /\ U32.v (snd ds) == cand2 sd t));
  Hacl.Spec.Loops.unfold_repeati_g (reveal t) (sample_step sd) Seq.empty;
  sample_step_push sd t (sampled sd t);
  assert (pure (sampled sd (reveal t + 1) ==
                push (push (sampled sd t) (cand1 sd t)) (cand2 sd t)));
  push_len (sampled sd t) (cand1 sd t);
  push_index (sampled sd t) (cand1 sd t);
  push_len (push (sampled sd t) (cand1 sd t)) (cand2 sd t);
  push_index (push (sampled sd t) (cand1 sd t)) (cand2 sd t);
  push_index_new_opt (sampled sd t) (cand1 sd t);
  push_index_new_opt (push (sampled sd t) (cand1 sd t)) (cand2 sd t);
  let c1 = push_impl dst c (fst ds);
  push_impl dst c1 (snd ds)
}

(** One SHAKE128 block: the fifty-six triples it holds exactly, in order.
    Keeping this out of the sampler means neither loop's verification
    condition has to mention the other's. *)
#push-options "--z3rlimit 400"

inline_for_extraction
fn block_impl (dst: A.array zqt) (blk: A.array S8.t) (c: SZ.t)
              (sd: erased (Seq.seq S8.t)) (t0: erased nat)
              (#v0: erased (Seq.seq zqt)) (#pb: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to dst v0 ** A.pts_to blk #pb vk **
         pure (Seq.length v0 == n /\ Seq.length vk == 168 /\
               SZ.v c == Seq.length (sampled sd t0) /\
               (forall (k: nat). k < SZ.v c ==>
                  S16.v (Seq.index v0 k) == Seq.index (sampled sd t0) k) /\
               (forall (u: nat). u < 168 ==>
                  Seq.index vk u == xof_byte sd (3 * reveal t0 + u)))
returns c': SZ.t
ensures exists* v. A.pts_to dst v ** A.pts_to blk #pb vk **
  pure (Seq.length v == n /\ SZ.v c' == Seq.length (sampled sd (reveal t0 + 56)) /\
        (forall (k: nat). k < SZ.v c' ==>
           S16.v (Seq.index v k) == Seq.index (sampled sd (reveal t0 + 56)) k))
{
  A.pts_to_len dst;
  A.pts_to_len blk;
  HSZ.fits32 ();
  assert_norm (168 < pow2 32);
  let mut cnt = c;
  let mut uu = 0sz;
  while (let vu = !uu; SZ.lt vu 56sz)
  invariant exists* (vu: SZ.t) (vc: SZ.t) (v: Seq.seq zqt).
    pts_to uu vu ** pts_to cnt vc ** A.pts_to dst v ** A.pts_to blk #pb vk **
    pure (SZ.v vu <= 56 /\ Seq.length v == n /\ Seq.length vk == 168 /\
          (forall (u: nat). u < 168 ==>
             Seq.index vk u == xof_byte sd (3 * reveal t0 + u)) /\
          SZ.v vc == Seq.length (sampled sd (reveal t0 + SZ.v vu)) /\
          (forall (k: nat). k < SZ.v vc ==>
             S16.v (Seq.index v k) == Seq.index (sampled sd (reveal t0 + SZ.v vu)) k))
  decreases (56 - SZ.v (!uu))
  {
    let vu = !uu;
    let vc = !cnt;
    let x = triple_impl dst blk vc vu sd (hide (reveal t0 + SZ.v vu));
    cnt := x;
    SZ.fits_u32_implies_fits (SZ.v vu + 1);
    uu := SZ.add vu 1sz;
  };
  let vf = !uu;
  assert (pure (SZ.v vf == 56));
  !cnt
}

#pop-options

#push-options "--z3rlimit 400"

(** [dst <- SampleNTT seed]. *)
fn sample_ntt_impl (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                   (#vd: erased (Seq.seq zqt))
                   (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to seed #ps vs **
         pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs)
ensures exists* v. A.pts_to dst v ** A.pts_to seed #ps vs **
  pure (Seq.length v == n /\ as_poly v == sample_ntt vs)
{
  A.pts_to_len dst;
  A.pts_to_len seed;
  HSZ.fits32 ();
  let z64 = S64.classify 0uL;
  let mut starr = [| z64; 25sz |];
  A.pts_to_len starr;
  let mut barr = [| z64; 25sz |];
  A.pts_to_len barr;
  let z8 = S8.classify 0uy;
  let mut blk = [| z8; 168sz |];
  A.pts_to_len blk;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;
  with prc vrc. assert (A.pts_to rc_tbl #prc vrc);
  assert (pure (reveal vrc == (rc <: Seq.seq S64.t)));

  xof_absorb starr barr rc_tbl seed slen;

  squeeze_state_zero (absorb 168 shake_suffix vs);
  Hacl.Spec.Loops.repeati_g_zero (sample_step vs) (Seq.empty #zq);
  assert (pure (sampled vs 0 == Seq.empty #zq));

  let mut cnt = 0sz;
  let mut jj = 0sz;
  while (let vc = !cnt; let vj = !jj; SZ.lt vc 256sz && SZ.lt vj 16sz)
  invariant exists* (vc: SZ.t) (vj: SZ.t) (v: Seq.seq zqt)
                    (vst: Seq.seq S64.t) (vb: Seq.seq S64.t) (vk: Seq.seq S8.t).
    pts_to cnt vc ** pts_to jj vj ** A.pts_to dst v **
    A.pts_to starr vst ** A.pts_to barr vb ** A.pts_to blk vk **
    A.pts_to rc_tbl #prc vrc **
    pure (SZ.v vj <= 16 /\ Seq.length v == n /\
          Seq.length vst == 25 /\ Seq.length vb == 25 /\ Seq.length vk == 168 /\
          reveal vrc == (rc <: Seq.seq S64.t) /\
          reveal vst == squeeze_state (SZ.v vj) (absorb 168 shake_suffix vs) /\
          SZ.v vc == Seq.length (sampled vs (SZ.v vj * 56)) /\
          (forall (k: nat). k < SZ.v vc ==>
             S16.v (Seq.index v k) == Seq.index (sampled vs (SZ.v vj * 56)) k))
  decreases (16 - SZ.v (!jj))
  {
    let vj = !jj;
    let vc = !cnt;
    xof_block blk starr barr rc_tbl (hide (SZ.v vj)) (hide (absorb 168 shake_suffix vs));
    xof_block_bytes vs (SZ.v vj);
    assert (pure (3 * (SZ.v vj * 56) == SZ.v vj * 168));
    let x = block_impl dst blk vc vs (hide (SZ.v vj * 56));
    assert (pure (SZ.v vj * 56 + 56 == (SZ.v vj + 1) * 56));
    cnt := x;
    SZ.fits_u32_implies_fits (SZ.v vj + 1);
    jj := SZ.add vj 1sz;
  };

  drop_table rc_tbl;
  let vc = !cnt;
  let vj = !jj;
  with v. assert (A.pts_to dst v);
  if (SZ.lt vc 256sz) {
    assert (pure (SZ.v vj == 16 /\ SZ.v vj * 56 == max_triples));
    zero_poly dst;
  } else {
    sampled_stable vs (SZ.v vj * 56) max_triples;
    assert (pure (sampled vs max_triples == sampled vs (SZ.v vj * 56)));
    as_poly_intro v (sample_ntt vs);
    assert (pure (as_poly v == sample_ntt vs));
  }
}

#pop-options

#pop-options
