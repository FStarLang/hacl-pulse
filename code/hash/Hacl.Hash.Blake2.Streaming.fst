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

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost
module Classical = FStar.Classical

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
fn copy_state (#t: Type0) (dst: S.slice t) (src: S.slice t)
              (#vd: erased (Seq.seq t)) (#ps: perm) (#vs: erased (Seq.seq t))
requires S.pts_to dst vd ** S.pts_to src #ps vs **
         pure (Seq.length vd == 8 /\ Seq.length vs == 8)
ensures exists* vd'. S.pts_to dst vd' ** S.pts_to src #ps vs **
        pure (Seq.length vd' == 8 /\ vd' == reveal vs)
{
  S.pts_to_len dst;
  S.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (vd': Seq.seq t).
    pts_to i vi ** S.pts_to dst vd' ** S.pts_to src #ps vs **
    pure (SZ.v vi <= 8 /\ Seq.length vd' == 8 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' k == Seq.index vs k))
  decreases (8 - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(src.(vi));
    S.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vd'. assert (S.pts_to dst vd');
  assert (pure (reveal vd' `Seq.equal` reveal vs));
}

#pop-options

(** {2 Absorbing whole blocks}

    [nblk] consecutive blocks of the stream, read straight out of [input] at
    [base].  Every one of them is compressed unflagged, at the counter
    "bytes absorbed including this block". *)

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

fn absorb_blocks (#t: Type0) {| w: word t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (acc: S.slice t) (vv: S.slice t) (mw: S.slice t) (blk: S.slice S8.t)
                 (ivs: S.slice t) (sg: S.slice SZ.t)
                 (input: S.slice S8.t) (base: SZ.t) (nblk: SZ.t) (n0: SZ.t) (ctr0: SZ.t)
                 (h0: erased (Seq.lseq t 8)) (s: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq t)) (#vv0: erased (Seq.seq t))
                 (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#psg: perm) (#vsg: erased (Seq.seq SZ.t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to vv vv0 ** S.pts_to mw vm0 **
         S.pts_to blk vblk0 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
         S.pts_to input #pin vin **
         pure (Seq.length vacc == 8 /\ Seq.length vv0 == 16 /\ Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\ sigma_ok vsg /\
               SZ.v base + SZ.v nblk * block_len #t <= Seq.length vin /\
               (SZ.v n0 + SZ.v nblk) * block_len #t <= Seq.length s /\
               Seq.length s < pow2 64 /\ SZ.fits (Seq.length s) /\
               SZ.v ctr0 == SZ.v n0 * block_len #t /\
               reveal vacc == sabsorb p h0 s (SZ.v n0) /\
               (forall (k: nat). k < SZ.v nblk * block_len #t ==>
                  Seq.index vin (SZ.v base + k) ==
                    Seq.index s (SZ.v n0 * block_len #t + k)))
ensures exists* (vacc': Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t)
                (vblk1: Seq.seq S8.t).
  S.pts_to acc vacc' ** S.pts_to vv vv1 ** S.pts_to mw vm1 **
  S.pts_to blk vblk1 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
  S.pts_to input #pin vin **
  pure (Seq.length vacc' == 8 /\ Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\
        vacc' == sabsorb p h0 s (SZ.v n0 + SZ.v nblk))
{
  S.pts_to_len acc;
  S.pts_to_len input;
  let bl = block_len_sz #t #w;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj nblk)
  invariant exists* (vj: SZ.t) (vacc': Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t)
                    (vblk1: Seq.seq S8.t).
    pts_to j vj ** S.pts_to acc vacc' ** S.pts_to vv vv1 ** S.pts_to mw vm1 **
    S.pts_to blk vblk1 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
    S.pts_to input #pin vin **
    pure (SZ.v vj <= SZ.v nblk /\ Seq.length vacc' == 8 /\
          Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
          Seq.length vblk1 == block_len #t /\ Seq.length vi == 8 /\
          reveal vi == G.reveal p.iv /\ sigma_ok vsg /\
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
    pad_block_run #t (reveal vin) (reveal s)
                  (SZ.v base) (SZ.v n0) (SZ.v vj) (SZ.v nblk);
    unfold_repeati_g (SZ.v n0 + SZ.v vj) (sstep p (reveal s)) (reveal h0);

    read_block #t blk input off;
    load_block #t mw blk;
    let ctr = SZ.add ctr0 (SZ.mul (SZ.add vj 1sz) bl);
    compress_impl p acc mw vv ivs sg ctr false;

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
             (acc: S.slice t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
             (ivs: S.slice t) (key: S.slice S8.t)
             (#vacc: erased (Seq.seq t)) (#vbuf: erased (Seq.seq S8.t))
             (#vtot: erased (Seq.seq SZ.t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to buf vbuf ** S.pts_to tot vtot **
         S.pts_to ivs #pi vi ** S.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
               Seq.length vtot == 1 /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\
               Seq.length vkey <= max_key_len #t /\
               3 * block_len #t < pow2 64)
ensures exists* (vacc': Seq.seq t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf vbuf' ** S.pts_to tot vtot' **
  S.pts_to ivs #pi vi ** S.pts_to key #pk vkey **
  pure (Seq.length vkey <= max_key_len #t /\
        stream_ok p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  S.pts_to_len acc;
  S.pts_to_len buf;
  S.pts_to_len tot;
  S.pts_to_len key;
  let bl = block_len_sz #t #w;
  let klen = S.len key;
  init_state p acc ivs klen;
  with vacc1. assert (S.pts_to acc vacc1);

  if SZ.gt klen 0sz
  ensures exists* (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
    S.pts_to acc vacc1 ** S.pts_to buf vbuf' ** S.pts_to tot vtot' **
    S.pts_to ivs #pi vi ** S.pts_to key #pk vkey **
    pure (Seq.length vbuf' == block_len #t /\ Seq.length vtot' == 1 /\
          Seq.length vkey <= max_key_len #t /\
          SZ.v (Seq.index vtot' 0) == Seq.length (stream #t vkey (Seq.empty #S8.t)) /\
          (forall (k: nat). k < brem_of #t (Seq.length (stream #t vkey (Seq.empty #S8.t))) ==>
             Seq.index vbuf' k ==
               Seq.index (stream #t vkey (Seq.empty #S8.t))
                 (nlast_of #t (Seq.length (stream #t vkey (Seq.empty #S8.t)))
                  * block_len #t + k)))
  {
    read_block #t buf key 0sz;
    S.((tot.(0sz) <- bl));
    stream_len #t (reveal vkey) (Seq.empty #S8.t);
    Seq.lemma_eq_intro (stream #t (reveal vkey) (Seq.empty #S8.t)) (pad_block #t (reveal vkey) 0);
    Seq.lemma_eq_elim (stream #t (reveal vkey) (Seq.empty #S8.t)) (pad_block #t (reveal vkey) 0);
    nlast_of_step #t 0 (block_len #t);
  }
  else
  {
    S.((tot.(0sz) <- 0sz));
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

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

fn update_full (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (acc: S.slice t) (vv: S.slice t) (mw: S.slice t) (blk: S.slice S8.t)
               (ivs: S.slice t) (sg: S.slice SZ.t)
               (buf: S.slice S8.t) (data: S.slice S8.t)
               (nlast: SZ.t) (blen: SZ.t)
               (h0: erased (Seq.lseq t 8))
               (s: erased (Seq.seq S8.t)) (s1: erased (Seq.seq S8.t))
               (#vacc: erased (Seq.seq t)) (#vv0: erased (Seq.seq t))
               (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#psg: perm) (#vsg: erased (Seq.seq SZ.t))
               (#vbuf: erased (Seq.seq S8.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to vv vv0 ** S.pts_to mw vm0 **
         S.pts_to blk vblk0 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
         S.pts_to buf vbuf ** S.pts_to data #pd vdata **
         pure (Seq.length vacc == 8 /\ Seq.length vv0 == 16 /\ Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\ sigma_ok vsg /\
               Seq.length vbuf == block_len #t /\
               reveal s1 == Seq.append (reveal s) (reveal vdata) /\
               Seq.length s == SZ.v nlast * block_len #t + SZ.v blen /\
               SZ.v blen <= block_len #t /\
               block_len #t < SZ.v blen + Seq.length vdata /\
               Seq.length s1 < pow2 64 /\ SZ.fits (Seq.length s1) /\
               reveal vacc == sabsorb p h0 s (SZ.v nlast) /\
               (forall (k: nat). k < SZ.v blen ==>
                  Seq.index vbuf k == Seq.index s (SZ.v nlast * block_len #t + k)))
ensures exists* (vacc': Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t)
                (vblk1: Seq.seq S8.t) (vbuf': Seq.seq S8.t).
  S.pts_to acc vacc' ** S.pts_to vv vv1 ** S.pts_to mw vm1 **
  S.pts_to blk vblk1 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
  S.pts_to buf vbuf' ** S.pts_to data #pd vdata **
  pure (Seq.length vacc' == 8 /\ Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\ Seq.length vbuf' == block_len #t /\
        vacc' == sabsorb p h0 s1 (nlast_of #t (Seq.length s1)) /\
        (forall (k: nat). k < brem_of #t (Seq.length s1) ==>
           Seq.index vbuf' k ==
             Seq.index s1 (nlast_of #t (Seq.length s1) * block_len #t + k)))
{
  S.pts_to_len acc;
  S.pts_to_len buf;
  S.pts_to_len data;
  let bl = block_len_sz #t #w;
  let dlen = S.len data;
  Seq.lemma_len_append (reveal s) (reveal vdata);

  (* Fill the buffer.  It now holds block [nlast] of [s1] in full. *)
  let fill = SZ.sub bl blen;
  copy_range buf blen data 0sz fill;
  with vbuf1. assert (S.pts_to buf vbuf1);
  buf_agrees (block_len #t) (reveal s) (reveal vdata) (reveal vbuf) (reveal vbuf1)
             (SZ.v nlast) (SZ.v blen) (SZ.v fill);

  Math.distributivity_add_left (SZ.v nlast) 1 (block_len #t);
  Math.lemma_mult_le_right (block_len #t) (SZ.v nlast) (SZ.v nlast + 1);
  SZ.fits_lte (SZ.v nlast * block_len #t) (Seq.length s1);
  let ctr0 = SZ.mul nlast bl;
  sabsorb_prefix p h0 (reveal s) (reveal vdata) (SZ.v nlast);
  absorb_blocks p acc vv mw blk ivs sg buf 0sz 1sz nlast ctr0 h0 s1;

  (* Whole blocks out of the caller's data, all but the last. *)
  let rest = SZ.sub dlen fill;
  let nblk = SZ.div (SZ.sub rest 1sz) bl;
  let tl = SZ.sub rest (SZ.mul nblk bl);
  update_split #t (SZ.v nlast) (SZ.v blen) (SZ.v dlen);
  Math.distributivity_add_left (SZ.v nlast + 1) (SZ.v nblk) (block_len #t);
  tail_agrees (block_len #t) (reveal s) (reveal vdata)
              (SZ.v nlast + 1) (SZ.v fill) (SZ.v nblk * block_len #t);
  Math.lemma_mult_le_right (block_len #t) 1 (SZ.v nlast + 1);
  SZ.fits_lte (SZ.v nlast + 1) (Seq.length s1);
  SZ.fits_lte ((SZ.v nlast + 1) * block_len #t) (Seq.length s1);
  absorb_blocks p acc vv mw blk ivs sg data fill nblk (SZ.add nlast 1sz)
                (SZ.add ctr0 bl) h0 s1;

  (* Keep the tail: between one and [block_len] bytes. *)
  nlast_of_step #t (SZ.v nlast + 1 + SZ.v nblk) (SZ.v tl);
  tail_agrees (block_len #t) (reveal s) (reveal vdata)
              (SZ.v nlast + 1 + SZ.v nblk) (SZ.v dlen - SZ.v tl) (SZ.v tl);
  copy_range buf 0sz data (SZ.sub dlen tl) tl;
}

#pop-options

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

fn update_impl (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (acc: S.slice t) (vv: S.slice t) (mw: S.slice t) (blk: S.slice S8.t)
               (ivs: S.slice t) (sg: S.slice SZ.t)
               (buf: S.slice S8.t) (tot: S.slice SZ.t) (data: S.slice S8.t)
               (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
               (#vacc: erased (Seq.seq t)) (#vv0: erased (Seq.seq t))
               (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#psg: perm) (#vsg: erased (Seq.seq SZ.t))
               (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to vv vv0 ** S.pts_to mw vm0 **
         S.pts_to blk vblk0 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
         S.pts_to buf vbuf ** S.pts_to tot vtot ** S.pts_to data #pd vdata **
         pure (Seq.length vv0 == 16 /\ Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\ sigma_ok vsg /\
               stream_ok p key seen vacc vbuf vtot /\
               Seq.length (stream #t key seen) + Seq.length vdata + 2 * block_len #t < pow2 64 /\
               SZ.fits (Seq.length (stream #t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t)
                (vblk1: Seq.seq S8.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to vv vv1 ** S.pts_to mw vm1 **
  S.pts_to blk vblk1 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
  S.pts_to buf vbuf' ** S.pts_to tot vtot' ** S.pts_to data #pd vdata **
  pure (Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\
        stream_ok p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  S.pts_to_len acc;
  S.pts_to_len buf;
  S.pts_to_len tot;
  S.pts_to_len data;
  let bl = block_len_sz #t #w;
  let tlen = S.(tot.(0sz));
  let nlast = nlast_sz #t #w tlen;
  let blen = SZ.sub tlen (SZ.mul nlast bl);
  let dlen = S.len data;

  let s = G.hide (stream #t (reveal key) (reveal seen));
  let s1 = G.hide (stream #t (reveal key) (Seq.append (reveal seen) (reveal vdata)));
  stream_append #t (reveal key) (reveal seen) (reveal vdata);
  Seq.lemma_len_append (reveal s) (reveal vdata);
  brem_bounds #t (Seq.length s);
  brem_bounds #t (Seq.length s1);

  if SZ.gt (SZ.add blen dlen) bl
  ensures exists* (vacc': Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t)
                  (vblk1: Seq.seq S8.t) (vbuf': Seq.seq S8.t).
    S.pts_to acc vacc' ** S.pts_to vv vv1 ** S.pts_to mw vm1 **
    S.pts_to blk vblk1 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
    S.pts_to buf vbuf' ** S.pts_to tot vtot ** S.pts_to data #pd vdata **
    pure (Seq.length vacc' == 8 /\ Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
          Seq.length vblk1 == block_len #t /\ Seq.length vbuf' == block_len #t /\
          brem_of #t (Seq.length s1) <= block_len #t /\
          Seq.length key <= max_key_len #t /\
          vacc' == sabsorb p (init p (Seq.length key)) s1 (nlast_of #t (Seq.length s1)) /\
          (forall (k: nat). k < brem_of #t (Seq.length s1) ==>
             Seq.index vbuf' k ==
               Seq.index s1 (nlast_of #t (Seq.length s1) * block_len #t + k)))
  {
    update_full p acc vv mw blk ivs sg buf data nlast blen
                (G.hide (init p (Seq.length key))) s s1;
  }
  else
  {
    (* Everything fits in the buffer, and the buffer is still the last block. *)
    copy_range buf blen data 0sz dlen;
    with vbuf1. assert (S.pts_to buf vbuf1);
    buf_agrees (block_len #t) (reveal s) (reveal vdata) (reveal vbuf) (reveal vbuf1)
               (SZ.v nlast) (SZ.v blen) (SZ.v dlen);
    nlast_of_step0 #t (SZ.v nlast) (SZ.v blen + SZ.v dlen);
    update_small p (init p (Seq.length key)) (reveal s) (reveal vdata)
                 (reveal vbuf1) (SZ.v nlast) (SZ.v blen);
    ()
  };

  S.((tot.(0sz) <- SZ.add tlen dlen));
  Seq.lemma_len_append (reveal seen) (reveal vdata);
}

#pop-options

(** {2 Digest}

    One flagged compression of the buffered tail, zero-padded, at the counter
    the state already holds.  The accumulator is copied first, so the state is
    left usable. *)

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

fn digest_impl (#t: Type0) {| w: word t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               (acc: S.slice t) (vv: S.slice t) (mw: S.slice t) (blk: S.slice S8.t)
               (ivs: S.slice t) (sg: S.slice SZ.t)
               (buf: S.slice S8.t) (tot: S.slice SZ.t) (out: S.slice S8.t)
               (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
               (#pa: perm) (#vacc: erased (Seq.seq t)) (#vv0: erased (Seq.seq t))
               (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#psg: perm) (#vsg: erased (Seq.seq SZ.t))
               (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
               (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
               (#vout: erased (Seq.seq S8.t))
requires S.pts_to acc #pa vacc ** S.pts_to vv vv0 ** S.pts_to mw vm0 **
         S.pts_to blk vblk0 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
         S.pts_to buf #pb vbuf ** S.pts_to tot #pt vtot ** S.pts_to out vout **
         pure (Seq.length vv0 == 16 /\ Seq.length vm0 == 16 /\
               Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\ sigma_ok vsg /\
               Seq.length vout == hash_bytes p /\
               stream_ok p key seen vacc vbuf vtot)
ensures exists* (vv1: Seq.seq t) (vm1: Seq.seq t) (vblk1: Seq.seq S8.t)
                (vout': Seq.seq S8.t).
  S.pts_to acc #pa vacc ** S.pts_to vv vv1 ** S.pts_to mw vm1 **
  S.pts_to blk vblk1 ** S.pts_to ivs #pi vi ** S.pts_to sg #psg vsg **
  S.pts_to buf #pb vbuf ** S.pts_to tot #pt vtot ** S.pts_to out vout' **
  pure (Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
        Seq.length vblk1 == block_len #t /\
        Seq.length key <= max_key_len #t /\
        vout' == blake2 p key seen)
{
  S.pts_to_len acc;
  S.pts_to_len buf;
  S.pts_to_len tot;
  S.pts_to_len out;
  let bl = block_len_sz #t #w;
  let tlen = S.(tot.(0sz));
  let nlast = nlast_sz #t #w tlen;
  let blen = SZ.sub tlen (SZ.mul nlast bl);
  let s = G.hide (stream #t (reveal key) (reveal seen));
  brem_bounds #t (Seq.length s);

  let z0: t = zero #t #w;
  let mut starr = [| z0; 8sz |];
  A.pts_to_len starr;
  let st = S.from_array starr 8sz;
  S.pts_to_len st;
  copy_state st acc;

  split3 (reveal vbuf) 0 (SZ.v blen);
  let sub = S.subslice buf 0sz blen;
  with vsub. assert (S.pts_to sub #pb vsub);
  read_block #t blk sub 0sz;
  last_block_is_buf #t (reveal s) (reveal vsub) (SZ.v nlast) (SZ.v blen);
  load_block #t mw blk;
  compress_impl p st mw vv ivs sg tlen true;
  blake2_stream p (reveal key) (reveal seen);
  write_digest_le p out st;

  unfold S.subslice_rest;
  S.join sub _ _;
  S.join _ _ buf;
  S.to_array st;
}

#pop-options
