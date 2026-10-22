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

(** The incremental BLAKE2.

    The state is the same three pieces of memory as SHA-2's -- an eight-word
    accumulator, one block of buffered bytes and a [size_t] -- but the
    invariant differs in one place, and it is the place where BLAKE2 differs
    from every Merkle-Damgard hash: the buffer holds one to [block_len] bytes,
    not zero to [block_len - 1].  A block that has just been filled is *not*
    compressed, because a compression has to know whether it is the last one,
    and the caller has not said yet.  It is compressed on the next call, which
    is the proof that it was not the last.

    The [size_t] holds the length of the *combined stream* -- the key block,
    if any, followed by the message -- rather than of the message.  That one
    choice makes a keyed hash a special case of an unkeyed one whose buffer
    starts full, and it makes the final compression's counter be exactly the
    stored length, keyed or not.  See [Spec.Blake2.Streaming].

    [digest] does not disturb the state: it copies the accumulator and pads a
    copy of the buffer, so a caller may interleave digests and updates. *)
module Hacl.Hash.Blake2.Streaming

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Loops
open Hacl.Spec.Bytes
open Hacl.Spec.Chunks
open Spec.Blake2
open Spec.Blake2.Streaming
open Hacl.Hash.Blake2.Core
open Hacl.Hash.Blake2
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost
module Classical = FStar.Classical
module Mem = Hacl.Mem

(** {2 The two derived lengths}

    Where the last whole block starts, and how much is in the buffer.  Both
    are pure functions of the stored length. *)

let nlast_sz (#t: Type0) {| w: word t |} (tlen: SZ.t)
  : (n: SZ.t { SZ.v n == nlast_of #t (SZ.v tlen) })
  = if SZ.eq tlen 0sz then 0sz
    else SZ.div (SZ.sub tlen 1sz) (block_len_sz #t #w)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** Eight words: the accumulator, copied so that [digest] can compress
    without destroying the state. *)
fn copy_state (#t: Type0) (dst: A.array t) (src: A.array t)
              (#vd: erased (Seq.seq t)) (#ps: perm) (#vs: erased (Seq.seq t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
         pure (Seq.length vd == 8 /\ Seq.length vs == 8)
ensures exists* vd'. A.pts_to dst vd' ** A.pts_to src #ps vs **
        pure (Seq.length vd' == 8 /\ vd' == reveal vs)
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (vd': Seq.seq t).
    pts_to i vi ** A.pts_to dst vd' ** A.pts_to src #ps vs **
    pure (SZ.v vi <= 8 /\ Seq.length vd' == 8 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' k == Seq.index vs k))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vd'. assert (A.pts_to dst vd');
  assert (pure (reveal vd' `Seq.equal` reveal vs));
}

#pop-options

(** {2 Absorbing whole blocks}

    [nblk] consecutive blocks of the stream, read straight out of [input] at
    [base].  Every one of them is compressed unflagged, at the counter
    "bytes absorbed including this block". *)

(** One iteration of [absorb_blocks], stated over pure values: compressing
    the [j]th block of the run, read out of [vin], at the counter of the
    blocks absorbed so far, is one more step of the fold over [s]. *)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let absorb_step (#t: Type0) {| word t |} (p: params t) (h0: Seq.lseq t 8)
                (vin s: Seq.seq S8.t) (base n0 j nblk: nat)
  : Lemma (requires j < nblk /\
                    base + nblk * block_len #t <= Seq.length vin /\
                    (n0 + nblk) * block_len #t <= Seq.length s /\
                    (forall (k: nat). k < nblk * block_len #t ==>
                       Seq.index vin (base + k) ==
                         Seq.index s (n0 * block_len #t + k)))
          (ensures compress p (sabsorb p h0 s (n0 + j))
                     (words_from_le block_words (pad_block #t vin (base + j * block_len #t)))
                     (n0 * block_len #t + (j + 1) * block_len #t) false
                   == sabsorb p h0 s (n0 + j + 1))
  = pad_block_run #t vin s base n0 j nblk;
    unfold_repeati_g (n0 + j) (sstep p s) h0;
    Math.distributivity_add_left n0 (j + 1) (block_len #t)
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn absorb_blocks (#t: Type0) {| w: word t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (acc: A.array t) (mw: A.array t) (blk: A.array S8.t)
                 (ivs: A.array t)
                 (input: A.array S8.t) (inlen: SZ.t) (base: SZ.t) (nblk: SZ.t) (n0: SZ.t) (ctr0: SZ.t)
                 (h0: erased (Seq.lseq t 8)) (s: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq t))
                 (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to mw vm0 **
         A.pts_to blk vblk0 ** A.pts_to ivs #pi vi **
         A.pts_to input #pin vin **
         pure (Seq.length vacc == 8 /\ Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\
               SZ.v base + SZ.v nblk * block_len #t <= Seq.length vin /\
               (SZ.v n0 + SZ.v nblk) * block_len #t <= Seq.length s /\
               SZ.v n0 * block_len #t + SZ.v nblk * block_len #t <= Seq.length s /\
               Seq.length s < pow2 64 /\ SZ.fits (Seq.length s) /\
               SZ.v ctr0 == SZ.v n0 * block_len #t /\
               reveal vacc == sabsorb p h0 s (SZ.v n0) /\
               (forall (k: nat). k < SZ.v nblk * block_len #t ==>
                  Seq.index vin (SZ.v base + k) ==
                    Seq.index s (SZ.v n0 * block_len #t + k)))
         ** pure (SZ.v inlen == Seq.length vin)
ensures exists* (vacc': Seq.seq t) (vm1: Seq.seq t)
                (vblk1: Seq.seq S8.t).
  A.pts_to acc vacc' ** A.pts_to mw vm1 **
  A.pts_to blk vblk1 ** A.pts_to ivs #pi vi **
  A.pts_to input #pin vin **
  pure (Seq.length vacc' == 8 /\ Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\
        vacc' == sabsorb p h0 s (SZ.v n0 + SZ.v nblk))
{
  A.pts_to_len acc;
  A.pts_to_len input;
  let bl = block_len_sz #t #w;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj nblk)
  invariant exists* (vj: SZ.t) (vacc': Seq.seq t) (vm1: Seq.seq t)
                    (vblk1: Seq.seq S8.t).
    pts_to j vj ** A.pts_to acc vacc' ** A.pts_to mw vm1 **
    A.pts_to blk vblk1 ** A.pts_to ivs #pi vi **
    A.pts_to input #pin vin **
    pure (SZ.v vj <= SZ.v nblk /\ Seq.length vacc' == 8 /\
          Seq.length vm1 == 16 /\
          Seq.length vblk1 == block_len #t /\ Seq.length vi == 8 /\
          reveal vi == G.reveal p.iv /\
          SZ.v base + SZ.v nblk * block_len #t <= Seq.length vin /\
          (SZ.v n0 + SZ.v nblk) * block_len #t <= Seq.length s /\
          Seq.length s < pow2 64 /\ SZ.fits (Seq.length s) /\
          SZ.v ctr0 == SZ.v n0 * block_len #t /\
          (forall (k: nat). k < SZ.v nblk * block_len #t ==>
             Seq.index vin (SZ.v base + k) ==
               Seq.index s (SZ.v n0 * block_len #t + k)) /\
          vacc' == sabsorb p h0 s (SZ.v n0 + SZ.v vj))
  decreases (SZ.v nblk - SZ.v (!j))
  {
    let vj = !j;
    Math.distributivity_add_left (SZ.v vj) 1 (block_len #t);
    Math.distributivity_add_left (SZ.v n0) (SZ.v vj) (block_len #t);
    Math.distributivity_add_left (SZ.v n0 + SZ.v vj) 1 (block_len #t);
    Math.lemma_mult_le_right (block_len #t) (SZ.v vj + 1) (SZ.v nblk);
    Math.lemma_mult_le_right (block_len #t) (SZ.v n0 + SZ.v vj + 1) (SZ.v n0 + SZ.v nblk);
    Math.lemma_mult_le_right (block_len #t) (SZ.v nblk) (SZ.v n0 + SZ.v nblk);
    SZ.fits_lte (SZ.v base + SZ.v vj * block_len #t) (Seq.length vin);
    SZ.fits_lte ((SZ.v vj + 1) * block_len #t) (Seq.length s);
    SZ.fits_lte ((SZ.v n0 + SZ.v vj + 1) * block_len #t) (Seq.length s);

    let off = SZ.add base (SZ.mul vj bl);
    assert (pure (SZ.v off == SZ.v base + SZ.v vj * block_len #t));
    absorb_step p (reveal h0) (reveal vin) (reveal s)
                (SZ.v base) (SZ.v n0) (SZ.v vj) (SZ.v nblk);

    read_block #t blk input inlen off;
    load_block #t mw blk;
    let ctr = SZ.add ctr0 (SZ.mul (SZ.add vj 1sz) bl);
    assert (pure (SZ.v ctr == SZ.v n0 * block_len #t + (SZ.v vj + 1) * block_len #t));
    compress_impl p acc mw ivs ctr false;

    j := SZ.add vj 1sz;
  }
}

#pop-options

(** {2 Initialization} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** Reset to the empty message under [key].  A nonempty key goes straight into
    the buffer as a full block and the stored length starts at one block; an
    empty key leaves both at zero. *)
fn init_impl (#t: Type0) {| w: word t |}
             ([@@@FStar.Attributes.monomorphize] p: params t)
             (acc: A.array t) (buf: A.array S8.t) (tot: A.array SZ.t)
             (ivs: A.array t) (key: A.array S8.t) (klen: SZ.t)
             (#vacc: erased (Seq.seq t)) (#vbuf: erased (Seq.seq S8.t))
             (#vtot: erased (Seq.seq SZ.t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to ivs #pi vi ** A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
               Seq.length vtot == 1 /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\
               Seq.length vkey <= max_key_len #t /\
               3 * block_len #t < pow2 64)
         ** pure (SZ.v klen == Seq.length vkey)
ensures exists* (vacc': Seq.seq t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to ivs #pi vi ** A.pts_to key #pk vkey **
  pure (Seq.length vkey <= max_key_len #t /\
        stream_ok p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.pts_to_len key;
  let bl = block_len_sz #t #w;
  init_state p acc ivs klen;
  with vacc1. assert (A.pts_to acc vacc1);

  if SZ.gt klen 0sz
  ensures exists* (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
    A.pts_to acc vacc1 ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
    A.pts_to ivs #pi vi ** A.pts_to key #pk vkey **
    pure (Seq.length vbuf' == block_len #t /\ Seq.length vtot' == 1 /\
          Seq.length vkey <= max_key_len #t /\
          SZ.v (Seq.index vtot' 0) == Seq.length (stream #t vkey (Seq.empty #S8.t)) /\
          (forall (k: nat). k < brem_of #t (Seq.length (stream #t vkey (Seq.empty #S8.t))) ==>
             Seq.index vbuf' k ==
               Seq.index (stream #t vkey (Seq.empty #S8.t))
                 (nlast_of #t (Seq.length (stream #t vkey (Seq.empty #S8.t)))
                  * block_len #t + k)))
  {
    read_block #t buf key klen 0sz;
    A.((tot.(0sz) <- bl));
    stream_len #t (reveal vkey) (Seq.empty #S8.t);
    Seq.lemma_eq_intro (stream #t (reveal vkey) (Seq.empty #S8.t)) (pad_block #t (reveal vkey) 0);
    Seq.lemma_eq_elim (stream #t (reveal vkey) (Seq.empty #S8.t)) (pad_block #t (reveal vkey) 0);
    nlast_of_step #t 0 (block_len #t);
  }
  else
  {
    A.((tot.(0sz) <- 0sz));
    Seq.lemma_eq_intro (stream #t (reveal vkey) (Seq.empty #S8.t)) (Seq.empty #S8.t);
    Seq.lemma_eq_elim (stream #t (reveal vkey) (Seq.empty #S8.t)) (Seq.empty #S8.t);
  };

  stream_len #t (reveal vkey) (Seq.empty #S8.t);
  brem_bounds #t (Seq.length (stream #t (reveal vkey) (Seq.empty #S8.t)));
  sabsorb_zero p (init p (Seq.length vkey)) (stream #t (reveal vkey) (Seq.empty #S8.t));
}

#pop-options

(** {2 Update}

    The interesting branch is the one where the buffer overflows.  It fills
    the buffer, compresses it -- now known not to be the last block --
    compresses [(rest - 1) / block_len] more blocks straight out of the
    caller's data, and keeps between one and [block_len] bytes.  The [- 1] is
    the whole difference from SHA-2: the last full block is kept, not
    absorbed. *)

#push-options "--z3rlimit 800 --fuel 0 --ifuel 0"

fn update_full (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (acc: A.array t) (mw: A.array t) (blk: A.array S8.t)
               (ivs: A.array t)
               (buf: A.array S8.t) (data: A.array S8.t) (dlen: SZ.t)
               (nlast: SZ.t) (blen: SZ.t)
               (h0: erased (Seq.lseq t 8))
               (s: erased (Seq.seq S8.t)) (s1: erased (Seq.seq S8.t))
               (#vacc: erased (Seq.seq t))
               (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#vbuf: erased (Seq.seq S8.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to mw vm0 **
         A.pts_to blk vblk0 ** A.pts_to ivs #pi vi **
         A.pts_to buf vbuf ** A.pts_to data #pd vdata **
         pure (Seq.length vacc == 8 /\ Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\
               Seq.length vbuf == block_len #t /\
               reveal s1 == Seq.append (reveal s) (reveal vdata) /\
               Seq.length s == SZ.v nlast * block_len #t + SZ.v blen /\
               SZ.v blen <= block_len #t /\
               block_len #t < SZ.v blen + Seq.length vdata /\
               Seq.length s1 < pow2 64 /\ SZ.fits (Seq.length s1) /\
               reveal vacc == sabsorb p h0 s (SZ.v nlast) /\
               (forall (k: nat). k < SZ.v blen ==>
                  Seq.index vbuf k == Seq.index s (SZ.v nlast * block_len #t + k)))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vacc': Seq.seq t) (vm1: Seq.seq t)
                (vblk1: Seq.seq S8.t) (vbuf': Seq.seq S8.t).
  A.pts_to acc vacc' ** A.pts_to mw vm1 **
  A.pts_to blk vblk1 ** A.pts_to ivs #pi vi **
  A.pts_to buf vbuf' ** A.pts_to data #pd vdata **
  pure (Seq.length vacc' == 8 /\ Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\ Seq.length vbuf' == block_len #t /\
        vacc' == sabsorb p h0 s1 (nlast_of #t (Seq.length s1)) /\
        (forall (k: nat). k < brem_of #t (Seq.length s1) ==>
           Seq.index vbuf' k ==
             Seq.index s1 (nlast_of #t (Seq.length s1) * block_len #t + k)))
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len data;
  let bl = block_len_sz #t #w;
  Seq.lemma_len_append (reveal s) (reveal vdata);

  (* Fill the buffer.  It now holds block [nlast] of [s1] in full. *)
  let fill = SZ.sub bl blen;
  copy_range buf blen data 0sz fill;
  with vbuf1. assert (A.pts_to buf vbuf1);
  buf_agrees (block_len #t) (reveal s) (reveal vdata) (reveal vbuf) (reveal vbuf1)
             (SZ.v nlast) (SZ.v blen) (SZ.v fill);

  Math.distributivity_add_left (SZ.v nlast) 1 (block_len #t);
  Math.lemma_mult_le_right (block_len #t) (SZ.v nlast) (SZ.v nlast + 1);
  SZ.fits_lte (SZ.v nlast * block_len #t) (Seq.length s1);
  let ctr0 = SZ.mul nlast bl;
  sabsorb_prefix p h0 (reveal s) (reveal vdata) (SZ.v nlast);
  absorb_blocks p acc mw blk ivs buf bl 0sz 1sz nlast ctr0 h0 s1;

  (* Whole blocks out of the caller's data, all but the last. *)
  let rest = SZ.sub dlen fill;
  let nblk = SZ.div (SZ.sub rest 1sz) bl;
  let tl = SZ.sub rest (SZ.mul nblk bl);
  update_split #t (SZ.v nlast) (SZ.v blen) (SZ.v dlen);
  assert (pure (SZ.v fill == block_len #t - SZ.v blen));
  assert (pure (SZ.v rest == SZ.v dlen - SZ.v fill));
  assert (pure (SZ.v nblk == (SZ.v rest - 1) / block_len #t));
  assert (pure (SZ.v tl == SZ.v rest - SZ.v nblk * block_len #t));
  assert (pure (SZ.v tl <= SZ.v dlen /\ SZ.v dlen - SZ.v tl == SZ.v fill + SZ.v nblk * block_len #t));
  Math.distributivity_add_left (SZ.v nlast + 1) (SZ.v nblk) (block_len #t);
  tail_agrees (block_len #t) (reveal s) (reveal vdata)
              (SZ.v nlast + 1) (SZ.v fill) (SZ.v nblk * block_len #t);
  Math.lemma_mult_le_right (block_len #t) 1 (SZ.v nlast + 1);
  SZ.fits_lte (SZ.v nlast + 1) (Seq.length s1);
  SZ.fits_lte ((SZ.v nlast + 1) * block_len #t) (Seq.length s1);
  absorb_blocks p acc mw blk ivs data dlen fill nblk (SZ.add nlast 1sz)
                (SZ.add ctr0 bl) h0 s1;

  (* Keep the tail: between one and [block_len] bytes. *)
  nlast_of_step #t (SZ.v nlast + 1 + SZ.v nblk) (SZ.v tl);
  tail_agrees (block_len #t) (reveal s) (reveal vdata)
              (SZ.v nlast + 1 + SZ.v nblk) (SZ.v dlen - SZ.v tl) (SZ.v tl);
  copy_range buf 0sz data (SZ.sub dlen tl) tl;
}

#pop-options

#push-options "--z3rlimit 800 --fuel 0 --ifuel 0"

fn update_impl (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (acc: A.array t) (mw: A.array t) (blk: A.array S8.t)
               (ivs: A.array t)
               (buf: A.array S8.t) (tot: A.array SZ.t) (data: A.array S8.t) (dlen: SZ.t)
               (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
               (#vacc: erased (Seq.seq t))
               (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to mw vm0 **
         A.pts_to blk vblk0 ** A.pts_to ivs #pi vi **
         A.pts_to buf vbuf ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
         pure (Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\
               stream_ok p key seen vacc vbuf vtot /\
               Seq.length (stream #t key seen) + Seq.length vdata + 2 * block_len #t < pow2 64 /\
               SZ.fits (Seq.length (stream #t key seen) + Seq.length vdata))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vacc': Seq.seq t) (vm1: Seq.seq t)
                (vblk1: Seq.seq S8.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to mw vm1 **
  A.pts_to blk vblk1 ** A.pts_to ivs #pi vi **
  A.pts_to buf vbuf' ** A.pts_to tot vtot' ** A.pts_to data #pd vdata **
  pure (Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\
        stream_ok p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.pts_to_len data;
  let bl = block_len_sz #t #w;
  let tlen = A.(tot.(0sz));
  let nlast = nlast_sz #t #w tlen;
  let blen = SZ.sub tlen (SZ.mul nlast bl);

  let s = G.hide (stream #t (reveal key) (reveal seen));
  let s1 = G.hide (stream #t (reveal key) (Seq.append (reveal seen) (reveal vdata)));
  stream_append #t (reveal key) (reveal seen) (reveal vdata);
  Seq.lemma_len_append (reveal s) (reveal vdata);
  brem_bounds #t (Seq.length s);
  assert (pure (SZ.v tlen == Seq.length s));
  assert (pure (SZ.v nlast == nlast_of #t (Seq.length s)));
  assert (pure (SZ.v blen == brem_of #t (Seq.length s)));
  assert (pure (SZ.v blen <= block_len #t));
  brem_bounds #t (Seq.length s1);

  if SZ.gt (SZ.add blen dlen) bl
  ensures exists* (vacc': Seq.seq t) (vm1: Seq.seq t)
                  (vblk1: Seq.seq S8.t) (vbuf': Seq.seq S8.t).
    A.pts_to acc vacc' ** A.pts_to mw vm1 **
    A.pts_to blk vblk1 ** A.pts_to ivs #pi vi **
    A.pts_to buf vbuf' ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
    pure (Seq.length vacc' == 8 /\ Seq.length vm1 == 16 /\
          Seq.length vblk1 == block_len #t /\ Seq.length vbuf' == block_len #t /\
          brem_of #t (Seq.length s1) <= block_len #t /\
          Seq.length key <= max_key_len #t /\
          vacc' == sabsorb p (init p (Seq.length key)) s1 (nlast_of #t (Seq.length s1)) /\
          (forall (k: nat). k < brem_of #t (Seq.length s1) ==>
             Seq.index vbuf' k ==
               Seq.index s1 (nlast_of #t (Seq.length s1) * block_len #t + k)))
  {
    update_full p acc mw blk ivs buf data dlen nlast blen
                (G.hide (init p (Seq.length key))) s s1;
  }
  else
  {
    (* Everything fits in the buffer, and the buffer is still the last block. *)
    copy_range buf blen data 0sz dlen;
    with vbuf1. assert (A.pts_to buf vbuf1);
    buf_agrees (block_len #t) (reveal s) (reveal vdata) (reveal vbuf) (reveal vbuf1)
               (SZ.v nlast) (SZ.v blen) (SZ.v dlen);
    nlast_of_step0 #t (SZ.v nlast) (SZ.v blen + SZ.v dlen);
    update_small p (init p (Seq.length key)) (reveal s) (reveal vdata)
                 (reveal vbuf1) (SZ.v nlast) (SZ.v blen);
    ()
  };

  A.((tot.(0sz) <- SZ.add tlen dlen));
  Seq.lemma_len_append (reveal seen) (reveal vdata);
}

#pop-options

(** {2 Digest}

    One flagged compression of the buffered tail, zero-padded, at the counter
    the state already holds.  The accumulator is copied first, so the state is
    left usable. *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn digest_impl (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (acc: A.array t) (mw: A.array t) (blk: A.array S8.t)
               (ivs: A.array t)
               (buf: A.array S8.t) (tot: A.array SZ.t) (out: A.array S8.t)
               (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
               (#pa: perm) (#vacc: erased (Seq.seq t))
               (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
               (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
               (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to mw vm0 **
         A.pts_to blk vblk0 ** A.pts_to ivs #pi vi **
         A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot ** A.pts_to out vout **
         pure (Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\
               Seq.length vout == hash_bytes p /\
               stream_ok p key seen vacc vbuf vtot)
ensures exists* (vm1: Seq.seq t) (vblk1: Seq.seq S8.t)
                (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to mw vm1 **
  A.pts_to blk vblk1 ** A.pts_to ivs #pi vi **
  A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot ** A.pts_to out vout' **
  pure (Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\
        Seq.length key <= max_key_len #t /\
        vout' == blake2 p key seen)
{
  A.pts_to_len acc;
  A.pts_to_len buf;
  A.pts_to_len tot;
  A.pts_to_len out;
  let bl = block_len_sz #t #w;
  let tlen = A.(tot.(0sz));
  let nlast = nlast_sz #t #w tlen;
  let blen = SZ.sub tlen (SZ.mul nlast bl);
  let s = G.hide (stream #t (reveal key) (reveal seen));
  brem_bounds #t (Seq.length s);
  assert (pure (SZ.v tlen == Seq.length s));
  assert (pure (SZ.v nlast == nlast_of #t (Seq.length s)));
  assert (pure (SZ.v blen == brem_of #t (Seq.length s)));
  assert (pure (SZ.v blen <= block_len #t));

  let z0: t = zero #t #w;
  let mut starr = [| z0; 8sz |];
  Mem.track starr;
  A.pts_to_len starr;
  A.pts_to_len starr;
  copy_state starr acc;

  split3 (reveal vbuf) 0 (SZ.v blen);
  let sub = Sub.sub buf 0sz blen;
  with vsub. assert (A.pts_to sub #pb vsub);
  read_block #t blk sub blen 0sz;
  last_block_is_buf #t (reveal s) (reveal vsub) (SZ.v nlast) (SZ.v blen);
  load_block #t mw blk;
  compress_impl p starr mw ivs tlen true;
  blake2_stream p (reveal key) (reveal seen);
  write_digest_le p out starr;

  Sub.unsub_id buf 0 (SZ.v blen) sub;
  Mem.wipe starr 8sz;
}

#pop-options
