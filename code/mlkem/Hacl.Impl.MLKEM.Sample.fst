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
    that claim is written down -- and the loop stops at an ordinary
    branch once the polynomial is full.  The rejection test itself is
    branch-free anyway ({!push_impl}), for speed rather than secrecy.

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
open Hacl.Impl.MLKEM.Encode
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
module Copy = Hacl.Impl.Copy
module Sub = Hacl.Impl.Sub
module Mem = Hacl.Mem
module V = Hacl.Vec256

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

(** [(d - q) >> 31] in thirty-two bits is the borrow of [d - q]: one
    exactly when [d] is accepted. *)
let accept_bit (d: U32.t { U32.v d < 4096 })
  : Lemma (U32.v (U32.shift_right (U32.sub_mod d 3329ul) 31ul) == (if U32.v d < q then 1 else 0))
  = assert_norm (pow2 31 == 2147483648);
    assert_norm (pow2 32 == 4294967296);
    if U32.v d >= q then begin
      Math.small_mod (U32.v d - q) (pow2 32);
      Math.small_div (U32.v d - q) (pow2 31)
    end else begin
      Math.lemma_mod_plus (U32.v d - q) 1 (pow2 32);
      Math.small_mod (U32.v d - q + pow2 32) (pow2 32)
    end

let accepted_mod (d: U32.t)
  : Lemma (U32.v d < q ==> U32.v d % q == U32.v d)
  = if U32.v d < q then Math.small_mod (U32.v d) q

(** One candidate: accepted if there is room and it is below [q].  The
    specification side of this is {!Spec.MLKEM.Sample.push}, but the two
    are deliberately kept apart: stating it operationally, as a count and
    an array update, keeps the sampler's ghost accumulator out of this
    function's arguments, and a ghost argument mentioning
    {!Spec.MLKEM.Sample.cand1} costs minutes of normalisation.

    The acceptance test is not a branch.  Whenever there is room the
    candidate is stored at [dst[c]] -- reduced by {!Hacl.Impl.MLKEM.Zq.csub},
    which leaves an accepted candidate unchanged and keeps a rejected one
    a valid coefficient -- and the count moves on by {!accept_bit}.  A
    rejected candidate is overwritten by the next store, or lies past the
    count, which the postcondition says nothing about.  About one candidate
    in five is rejected, at random, so as a branch the test is
    mispredicted every few candidates, and the sampler spent about a third
    of its time on it.  Only the [c < n] test, which fails once, remains a
    branch. *)
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
  if (SZ.lt c 256sz) {
    Math.small_mod (U32.v d) (pow2 16);
    let x = csub (S16.classify (Cast.uint32_to_uint16 d));
    accepted_mod d;
    A.((dst.(c) <- x));
    let inc = U32.shift_right (U32.sub_mod d 3329ul) 31ul;
    accept_bit d;
    SZ.fits_u32_implies_fits (SZ.v c + 1);
    SZ.add c (SZ.uint32_to_sizet inc)
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
#push-options "--z3rlimit 400 --using_facts_from '* -Spec.SHA3 -Spec.MLKEM.Sample.xof_byte'"

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
          reveal vst == squeeze_state (xof_prev (SZ.v vj)) (absorb 168 shake_suffix vs) /\
          SZ.v vc == Seq.length (sampled vs (SZ.v vj * 56)) /\
          (forall (k: nat). k < SZ.v vc ==>
             S16.v (Seq.index v k) == Seq.index (sampled vs (SZ.v vj * 56)) k))
  decreases (16 - SZ.v (!jj))
  {
    let vj = !jj;
    let vc = !cnt;
    xof_block blk starr barr rc_tbl vj (hide (absorb 168 shake_suffix vs));
    xof_block_bytes vs (SZ.v vj);
    assert (pure (3 * (SZ.v vj * 56) == SZ.v vj * 168));
    let x = block_impl dst blk vc vs (hide (SZ.v vj * 56));
    assert (pure (SZ.v vj * 56 + 56 == (SZ.v vj + 1) * 56));
    cnt := x;
    SZ.fits_u32_implies_fits (SZ.v vj + 1);
    jj := SZ.add vj 1sz;
  };

  drop_table rc_tbl;
  Mem.wipe blk 168sz;
  Mem.wipe barr 25sz;
  Mem.wipe starr 25sz;
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
  };
}

#pop-options

(** {2 Centred binomial sampling}

    No branch and no early exit: [SamplePolyCBD] reads a fixed number of
    bits and counts them. *)

#push-options "--z3rlimit 200"

(** The bits come out of the PRF output a group at a time: [eta] bytes
    are [8 eta] bits, exactly four coefficients' worth, so a group's bytes
    are loaded once and every bit position inside it is a constant. *)

let stream_bit_byte (b: Seq.seq S8.t) (i k: nat)
  : Lemma (requires i < Seq.length b /\ k < 8)
          (ensures stream_bit b (8 * i + k) == (S8.v (Seq.index b i) / pow2 k) % 2)
  = Math.lemma_div_plus k i 8;
    Math.small_div k 8;
    Math.lemma_mod_plus k i 8;
    Math.small_mod k 8

#push-options "--fuel 3"
let bit_sum_unfold (b: Seq.seq S8.t) (off: nat) (m: nat { 1 <= m /\ m <= 3 })
  : Lemma (bit_sum b off m ==
             stream_bit b off +
             (if m >= 2 then stream_bit b (off + 1) else 0) +
             (if m = 3 then stream_bit b (off + 2) else 0))
  = ()
#pop-options

(** The first [nb] of [y0], [y1], [y2] are bytes [base], [base + 1], ... *)
let grp_ok (vb: Seq.seq S8.t) (base nb: nat) (y0 y1 y2: S8.t) : prop
  = base + nb <= Seq.length vb /\ nb <= 3 /\
    (nb > 0 ==> y0 == Seq.index vb base) /\
    (nb > 1 ==> y1 == Seq.index vb (base + 1)) /\
    (nb > 2 ==> y2 == Seq.index vb (base + 2))

(** Bit [k] of a byte, as a sixteen-bit word. *)
inline_for_extraction
let bit8 (y: S8.t) (k: U32.t { U32.v k < 8 })
  : r: S16.t { S16.v r == (S8.v y / pow2 (U32.v k)) % 2 }
  = let z = S8.shift_right y k in
    Math.pow2_le_compat 16 8;
    let e = S16.of_bytes_le z (S8.classify 0uy) in
    S16.logand_mask_low e 1ul;
    assert_norm (pow2 1 == 2);
    S16.logand e (S16.mask_low 1ul)

(** Bit [p] of a group. *)
inline_for_extraction
let sbit (vb: erased (Seq.seq S8.t)) (base nb: erased nat) (y0 y1 y2: S8.t)
         (p: U32.t { U32.v p < 8 * reveal nb })
  : Pure S16.t (requires grp_ok vb base nb y0 y1 y2)
               (ensures fun r -> S16.v r == stream_bit vb (8 * base + U32.v p))
  = if U32.lt p 8ul then begin
      stream_bit_byte vb base (U32.v p);
      bit8 y0 p
    end else if U32.lt p 16ul then begin
      stream_bit_byte vb (base + 1) (U32.v p - 8);
      bit8 y1 (U32.sub p 8ul)
    end else begin
      stream_bit_byte vb (base + 2) (U32.v p - 16);
      bit8 y2 (U32.sub p 16ul)
    end

(** [bit_sum] of [m] bits of a group, from bit [p]. *)
inline_for_extraction
let gsum (vb: erased (Seq.seq S8.t)) (base nb: erased nat) (y0 y1 y2: S8.t)
         (p: U32.t) (m: U32.t { 1 <= U32.v m /\ U32.v m <= 3 /\ U32.v p + U32.v m <= 8 * reveal nb })
  : Pure S16.t (requires grp_ok vb base nb y0 y1 y2)
               (ensures fun r -> S16.v r == bit_sum vb (8 * base + U32.v p) (U32.v m))
  = bit_sum_unfold vb (8 * base + U32.v p) (U32.v m);
    assert_norm (pow2 16 == 65536);
    let s0 = sbit vb base nb y0 y1 y2 p in
    let s1 =
      if U32.gte m 2ul then begin
        let t = sbit vb base nb y0 y1 y2 (U32.add p 1ul) in
        Math.small_mod (S16.v s0 + S16.v t) (pow2 16);
        S16.add_mod s0 t
      end else s0 in
    if U32.eq m 3ul then begin
      let t = sbit vb base nb y0 y1 y2 (U32.add p 2ul) in
      Math.small_mod (S16.v s1 + S16.v t) (pow2 16);
      S16.add_mod s1 t
    end else s1

(** The first [c] coefficients are done. *)
let cbd_prefix (eta: pos { eta <= 3 }) (vb: Seq.lseq S8.t (64 * eta)) (v: Seq.seq zqt) (c: nat)
  : prop
  = Seq.length v == n /\
    (forall (k: nat). k < c /\ k < n ==> S16.v (Seq.index v k) == Seq.index (sample_cbd eta vb) k)

let cbd_prefix_step (eta: pos { eta <= 3 }) (vb: Seq.lseq S8.t (64 * eta)) (v: Seq.seq zqt)
                    (c: nat { c < n }) (x: zqt)
  : Lemma (requires cbd_prefix eta vb v c /\ S16.v x == Seq.index (sample_cbd eta vb) c)
          (ensures cbd_prefix eta vb (Seq.upd v c x) (c + 1))
  = ()

(** Coefficient [c], whose [2 eta] bits start at bit [p] of the group. *)
inline_for_extraction
fn cbd_coef (dst: A.array zqt) (c: SZ.t) (y0 y1 y2: S8.t) (p: U32.t)
            ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
            (#vb: erased (Seq.seq S8.t)) (#base #nb: erased nat) (#v: erased (Seq.seq zqt))
requires A.pts_to dst v **
         pure (1 <= SZ.v eta /\ SZ.v eta <= 3 /\ Seq.length vb == 64 * SZ.v eta /\
               SZ.v c < n /\ U32.v p + 2 * SZ.v eta <= 8 * reveal nb /\
               2 * SZ.v c * SZ.v eta == 8 * reveal base + U32.v p /\
               grp_ok vb base nb y0 y1 y2 /\ cbd_prefix (SZ.v eta) vb v (SZ.v c))
ensures exists* v'. A.pts_to dst v' **
        pure (1 <= SZ.v eta /\ SZ.v eta <= 3 /\ Seq.length vb == 64 * SZ.v eta /\
              cbd_prefix (SZ.v eta) vb v' (SZ.v c + 1))
{
  A.pts_to_len dst;
  let m = SZ.sizet_to_uint32 eta;
  let x = gsum vb base nb y0 y1 y2 p m;
  let y = gsum vb base nb y0 y1 y2 (U32.add p m) m;
  sample_cbd_index (SZ.v eta) vb (SZ.v c);
  let r = zq_sub x y;
  cbd_prefix_step (SZ.v eta) vb v (SZ.v c) r;
  A.(dst.(c) <- r);
}

(** Coefficient [4 i + t] starts at bit [2 eta t] of group [i]. *)
let grp_pos (eta i t: nat)
  : Lemma (2 * (4 * i + t) * eta == 8 * (eta * i) + t * (2 * eta))
  = ()

(** [dst <- SamplePolyCBD_eta b]. *)
inline_for_extraction
fn cbd_impl_ (dst: A.array zqt) (b: A.array S8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
            (#vd: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to b #p vb **
         pure (Seq.length vd == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               Seq.length vb == 64 * SZ.v eta)
ensures exists* v. A.pts_to dst v ** A.pts_to b #p vb **
  pure (Seq.length v == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        Seq.length vb == 64 * SZ.v eta /\
        as_poly v == sample_cbd (SZ.v eta) vb)
{
  A.pts_to_len dst;
  A.pts_to_len b;
  HSZ.fits32 ();
  assert_norm (64 * 3 < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 64sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to b #p vb **
    pure (SZ.v vi <= 64 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
          Seq.length vb == 64 * SZ.v eta /\
          cbd_prefix (SZ.v eta) vb v (4 * SZ.v vi))
  decreases (64 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_left (SZ.v eta) (SZ.v vi + 1) 64;
    Math.distributivity_add_right (SZ.v eta) (SZ.v vi) 1;
    assert (pure (SZ.v eta * SZ.v vi + SZ.v eta <= 64 * SZ.v eta));
    SZ.fits_u32_implies_fits (SZ.v eta * SZ.v vi + SZ.v eta);
    SZ.fits_u32_implies_fits (4 * SZ.v vi + 4);
    let base = SZ.mul eta vi;
    let y0 = A.(b.(base));
    let y1 = (if SZ.gte eta 2sz then A.(b.(SZ.add base 1sz)) else y0);
    let y2 = (if SZ.eq eta 3sz then A.(b.(SZ.add base 2sz)) else y0);
    assert (pure (grp_ok vb (SZ.v base) (SZ.v eta) y0 y1 y2));
    let c = SZ.mul 4sz vi;
    let pe = SZ.sizet_to_uint32 (SZ.add eta eta);
    let c1 = SZ.add c 1sz;
    let c2 = SZ.add c 2sz;
    let c3 = SZ.add c 3sz;
    let p2 = U32.add pe pe;
    let p3 = U32.add pe p2;
    assert (pure (SZ.v base == SZ.v eta * SZ.v vi /\ SZ.v c == 4 * SZ.v vi /\
                  SZ.v c1 == 4 * SZ.v vi + 1 /\ SZ.v c2 == 4 * SZ.v vi + 2 /\
                  SZ.v c3 == 4 * SZ.v vi + 3 /\ U32.v pe == 1 * (2 * SZ.v eta) /\
                  U32.v p2 == 2 * (2 * SZ.v eta) /\ U32.v p3 == 3 * (2 * SZ.v eta)));
    grp_pos (SZ.v eta) (SZ.v vi) 0;
    grp_pos (SZ.v eta) (SZ.v vi) 1;
    grp_pos (SZ.v eta) (SZ.v vi) 2;
    grp_pos (SZ.v eta) (SZ.v vi) 3;
    cbd_coef dst c y0 y1 y2 0ul eta #vb #(SZ.v base) #(SZ.v eta);
    cbd_coef dst c1 y0 y1 y2 pe eta #vb #(SZ.v base) #(SZ.v eta);
    cbd_coef dst c2 y0 y1 y2 p2 eta #vb #(SZ.v base) #(SZ.v eta);
    cbd_coef dst c3 y0 y1 y2 p3 eta #vb #(SZ.v base) #(SZ.v eta);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  as_poly_intro v (sample_cbd (SZ.v eta) vb);
  assert (pure (as_poly v == sample_cbd (SZ.v eta) vb));
}

(** The same, extracted a second time with [target("avx2")] so that the C
    compiler can vectorise it with wider vectors; chosen at run time. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn cbd_impl_avx2 (dst: A.array zqt) (b: A.array S8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
            (#vd: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to b #p vb **
         pure (Seq.length vd == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               Seq.length vb == 64 * SZ.v eta)
ensures exists* v. A.pts_to dst v ** A.pts_to b #p vb **
  pure (Seq.length v == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        Seq.length vb == 64 * SZ.v eta /\
        as_poly v == sample_cbd (SZ.v eta) vb)
{
  cbd_impl_ dst b eta
}

fn cbd_impl (dst: A.array zqt) (b: A.array S8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
            (#vd: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to b #p vb **
         pure (Seq.length vd == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               Seq.length vb == 64 * SZ.v eta)
ensures exists* v. A.pts_to dst v ** A.pts_to b #p vb **
  pure (Seq.length v == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        Seq.length vb == 64 * SZ.v eta /\
        as_poly v == sample_cbd (SZ.v eta) vb)
{
  if (Hacl.X64.x86_64) {
    if (V.supported ()) { cbd_impl_avx2 dst b eta } else { cbd_impl_ dst b eta }
  } else { cbd_impl_ dst b eta }
}

(** {2 The pseudorandom function}

    [PRF_eta(s, b) = SHAKE256(s || b, 64 eta)].  The counter byte is
    public -- it is a loop index -- so it is classified on the way in. *)
fn prf_impl (out: A.array S8.t) (s: A.array S8.t) (byte: U8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
            (#vo: erased (Seq.seq S8.t)) (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to s #p vs **
         pure (Seq.length vs == 32 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               Seq.length vo == 64 * SZ.v eta)
ensures exists* v. A.pts_to out v ** A.pts_to s #p vs **
  pure (Seq.length vs == 32 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        Seq.length v == 64 * SZ.v eta /\
        v == prf (SZ.v eta) vs byte)
{
  A.pts_to_len out;
  A.pts_to_len s;
  HSZ.fits32 ();
  assert_norm (64 * 3 < pow2 32);
  SZ.fits_u32_implies_fits (64 * SZ.v eta);
  let z8 = S8.classify 0uy;
  let mut msg = [| z8; 33sz |];
  Mem.track msg;
  A.pts_to_len msg;
  Copy.copy_prefix msg s 32sz;
  A.((msg.(32sz) <- S8.classify byte));
  with vm. assert (A.pts_to msg vm);
  Seq.lemma_eq_intro (reveal vm) (Seq.snoc vs (S8.classify byte));
  assert (pure (reveal vm == Seq.snoc vs (S8.classify byte)));
  shake256 out (SZ.mul 64sz eta) msg 33sz;
  Mem.wipe msg 33sz;
}

(** [SamplePolyCBD] driven by the PRF, which is how every caller uses it. *)
fn sample_poly_cbd_impl (dst: A.array zqt) (s: A.array S8.t) (byte: U8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                        (#vd: erased (Seq.seq zqt)) (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to s #p vs **
         pure (Seq.length vd == n /\ Seq.length vs == 32 /\
               1 <= SZ.v eta /\ SZ.v eta <= 3)
ensures exists* v. A.pts_to dst v ** A.pts_to s #p vs **
  pure (Seq.length v == n /\ Seq.length vs == 32 /\
        1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        as_poly v == sample_poly_cbd (SZ.v eta) vs byte)
{
  A.pts_to_len dst;
  A.pts_to_len s;
  HSZ.fits32 ();
  assert_norm (64 * 3 < pow2 32);
  SZ.fits_u32_implies_fits (64 * SZ.v eta);
  let z8 = S8.classify 0uy;
  let mut buf = [| z8; 192sz |];
  Mem.track buf;
  A.pts_to_len buf;
  let el = SZ.mul 64sz eta;
  let bs = Sub.sub buf 0sz el;
  prf_impl bs s byte eta;
  cbd_impl dst bs eta;
  Sub.unsub buf 0 (SZ.v el) bs;
  Mem.wipe buf 192sz;
  ()
}

#pop-options

#pop-options
