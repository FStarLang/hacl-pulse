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

(** BLAKE2, one-shot, written once for both widths.

    The specification hashes [data key msg]: the key zero-padded to a block,
    followed by the message zero-padded to a block.  Building that would mean
    copying the message, so the implementation never does; it reads block [i]
    straight out of the key or the message through [Spec.Blake2.block_of], and
    [Spec.Blake2.block_at_data] is the proof that the two agree.

    The block counter is the number of message bytes absorbed so far, which
    for a keyed hash includes the key block.  It is two words wide -- 128 bits
    for BLAKE2b, 64 for BLAKE2s -- and is carried as a [size_t] and split by
    the [word] class's [of_sizet_lo] and [of_sizet_hi]. *)
module Hacl.Hash.Blake2

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Hacl.Spec.Loops
open Spec.Blake2
open Spec.Blake2.Constants
open Hacl.Hash.Blake2.Core

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module A = Pulse.Lib.Array
module U32 = FStar.UInt32
module G = FStar.Ghost

(** The block length as a machine value. *)
let block_len_sz (#t: Type0) {| w: word t |} : n: SZ.t { SZ.v n == block_len #t } =
  SZ.mul 16sz (nbytes #t #w)

(** How many bytes of [s] a block at [off] actually covers. *)
let block_avail (off len bl: SZ.t)
  : (n: SZ.t { SZ.v n <= SZ.v bl /\
               (0 < SZ.v n ==> SZ.v off + SZ.v n <= SZ.v len) /\
               (SZ.v n < SZ.v bl ==> SZ.v len <= SZ.v off + SZ.v n) })
  = if SZ.lt off len
    then (let a = SZ.sub len off in if SZ.lt a bl then a else bl)
    else 0sz

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** {2 Reading a block}

    [Spec.Blake2.pad_block]: the [block_len] bytes of [s] at [off], zero past
    the end of [s].  No bound on [off] -- past the end the whole block is
    zero, which is exactly what the specification says. *)
fn read_block (#t: Type0) {| w: word t |}
              (blk: S.slice S8.t) (s: S.slice S8.t) (off: SZ.t)
              (#vblk0: erased (Seq.seq S8.t))
              (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires S.pts_to blk vblk0 ** S.pts_to s #ps vs **
         pure (Seq.length vblk0 == block_len #t)
ensures S.pts_to blk (pad_block #t (reveal vs) (SZ.v off)) ** S.pts_to s #ps vs
{
  S.pts_to_len blk;
  S.pts_to_len s;
  let z8 = S8.classify 0uy;
  let bl = block_len_sz #t #w;
  let len = S.len s;
  let n = block_avail off len bl;

  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk n)
  invariant exists* (vk: SZ.t) (vb: Seq.seq S8.t).
    pts_to k vk ** S.pts_to blk vb ** S.pts_to s #ps vs **
    pure (SZ.v vk <= SZ.v n /\ SZ.v n <= block_len #t /\
          Seq.length vb == block_len #t /\
          (0 < SZ.v n ==> SZ.v off + SZ.v n <= Seq.length vs) /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index vb j == Seq.index (pad_block #t (reveal vs) (SZ.v off)) j))
  decreases (SZ.v n - SZ.v (!k))
  {
    let vk = !k;
    let x = S.(s.(SZ.add off vk));
    S.((blk.(vk) <- x));
    k := SZ.add vk 1sz;
  };

  let mut k2 = n;
  while (let vk = !k2; SZ.lt vk bl)
  invariant exists* (vk: SZ.t) (vb: Seq.seq S8.t).
    pts_to k2 vk ** S.pts_to blk vb ** S.pts_to s #ps vs **
    pure (SZ.v n <= SZ.v vk /\ SZ.v vk <= block_len #t /\
          Seq.length vb == block_len #t /\
          (0 < SZ.v n ==> SZ.v off + SZ.v n <= Seq.length vs) /\
          (SZ.v n < block_len #t ==> Seq.length vs <= SZ.v off + SZ.v n) /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index vb j == Seq.index (pad_block #t (reveal vs) (SZ.v off)) j))
  decreases (block_len #t - SZ.v (!k2))
  {
    let vk = !k2;
    S.((blk.(vk) <- z8));
    k2 := SZ.add vk 1sz;
  };
  with vb. assert (S.pts_to blk vb);
  Seq.lemma_eq_intro vb (pad_block #t (reveal vs) (SZ.v off));
  Seq.lemma_eq_elim vb (pad_block #t (reveal vs) (SZ.v off));
}

(** {2 A block as sixteen little-endian words} *)
fn load_block (#t: Type0) {| w: word t |}
              (mw: S.slice t) (blk: S.slice S8.t)
              (#vm0: erased (Seq.seq t))
              (#pb: perm) (#vb: erased (Seq.lseq S8.t (block_len #t)))
requires S.pts_to mw vm0 ** S.pts_to blk #pb vb **
         pure (Seq.length vm0 == 16)
ensures S.pts_to mw (words_from_le block_words (reveal vb)) ** S.pts_to blk #pb vb
{
  S.pts_to_len mw;
  S.pts_to_len blk;
  let nb = nbytes #t #w;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vm: Seq.seq t).
    pts_to i vi ** S.pts_to mw vm ** S.pts_to blk #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length vm == 16 /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vm j == Seq.index (words_from_le block_words (reveal vb)) j))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vi + 1) 16;
    let x = load_le #t blk (SZ.mul vi nb);
    w.v_extensional x (Seq.index (words_from_le block_words (reveal vb)) (SZ.v vi));
    S.((mw.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vm. assert (S.pts_to mw vm);
  Seq.lemma_eq_intro vm (words_from_le block_words (reveal vb));
  Seq.lemma_eq_elim vm (words_from_le block_words (reveal vb));
}

#pop-options

(** The parameter word, built with additions because its three fields do not
    overlap.  All of the work is showing that nothing wraps: every intermediate
    is below 2^32, and every word is at least that wide. *)
let param_word_word (#t: Type0) {| w: word t |} (klen nn: SZ.t)
  : Lemma (requires SZ.v klen <= 128 /\ SZ.v nn <= 128)
          (ensures (let one = of_sizet_lo #t 1sz in
                    let kw = of_sizet_lo #t klen in
                    let nw = of_sizet_lo #t nn in
                    v #t (add_mod #t (add_mod #t (shift_left #t one 24ul)
                                                 (shift_left #t one 16ul))
                                     (add_mod #t (shift_left #t kw 8ul) nw))
                    == 0x01010000 + SZ.v klen * 256 + SZ.v nn))
  = let b = bits #t in
    Math.pow2_le_compat b 32;
    Math.pow2_le_compat 64 1;
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 24 + pow2 16 == 0x01010000);
    assert_norm (0x01010000 + 128 * 256 + 128 < pow2 32);
    Math.lemma_mult_le_right (pow2 8) (SZ.v klen) 128;
    Math.small_mod 1 (pow2 64);
    Math.small_mod 1 b;
    Math.small_mod 1 (pow2 b);
    Math.small_mod (SZ.v klen) (pow2 64);
    Math.small_mod (SZ.v klen) (pow2 b);
    Math.small_mod (SZ.v nn) (pow2 64);
    Math.small_mod (SZ.v nn) (pow2 b);
    Math.small_mod (pow2 24) (pow2 b);
    Math.small_mod (pow2 16) (pow2 b);
    Math.small_mod (pow2 24 + pow2 16) (pow2 b);
    Math.small_mod (SZ.v klen * pow2 8) (pow2 b);
    Math.small_mod (SZ.v klen * pow2 8 + SZ.v nn) (pow2 b);
    Math.small_mod (pow2 24 + pow2 16 + (SZ.v klen * pow2 8 + SZ.v nn)) (pow2 b)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** {2 The initial state}

    The initialization vector with the parameter word xored into its first
    word.  The three fields of the parameter word do not overlap, so it is
    built with additions rather than disjunctions -- [add_mod]'s specification
    is arithmetic, and arithmetic is what [Spec.Blake2.param_word] is. *)
fn init_state (#t: Type0) {| w: word t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (h: S.slice t) (ivs: S.slice t) (klen: SZ.t)
              (#vh0: erased (Seq.seq t))
              (#pi: perm) (#vi: erased (Seq.seq t))
requires S.pts_to h vh0 ** S.pts_to ivs #pi vi **
         pure (Seq.length vh0 == 8 /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\ SZ.v klen <= max_key_len #t)
ensures exists* (vh: Seq.seq t). S.pts_to h vh ** S.pts_to ivs #pi vi **
  pure (SZ.v klen <= max_key_len #t /\ Seq.length vh == 8 /\ vh == init p (SZ.v klen))
{
  S.pts_to_len h;
  S.pts_to_len ivs;
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 8sz)
  invariant exists* (vi2: SZ.t) (vh: Seq.seq t).
    pts_to i vi2 ** S.pts_to h vh ** S.pts_to ivs #pi vi **
    pure (SZ.v vi2 <= 8 /\ Seq.length vh == 8 /\ Seq.length vi == 8 /\
          (forall (j: nat). j < SZ.v vi2 ==> Seq.index vh j == Seq.index (reveal vi) j))
  decreases (8 - SZ.v (!i))
  {
    let vi2 = !i;
    let x = S.(ivs.(vi2));
    S.((h.(vi2) <- x));
    i := SZ.add vi2 1sz;
  };
  with vh. assert (S.pts_to h vh);
  Seq.lemma_eq_intro vh (reveal vi);
  Seq.lemma_eq_elim vh (reveal vi);

  let one: t = of_sizet_lo #t 1sz;
  let kw: t = of_sizet_lo #t klen;
  let nw: t = of_sizet_lo #t p.nhash_bytes;
  let hi: t = add_mod #t (shift_left #t one 24ul) (shift_left #t one 16ul);
  let pw: t = add_mod #t hi (add_mod #t (shift_left #t kw 8ul) nw);
  Math.pow2_le_compat (bits #t) 32;
  param_word_word #t klen p.nhash_bytes;
  Math.small_mod (param_word (hash_bytes p) (SZ.v klen)) (pow2 (bits #t));
  w.v_extensional pw (small_word #t (param_word (hash_bytes p) (SZ.v klen)));

  let x0 = S.(h.(0sz));
  S.((h.(0sz) <- logxor #t x0 pw));
  with vh2. assert (S.pts_to h vh2);
  Seq.lemma_eq_intro vh2 (init p (SZ.v klen));
  Seq.lemma_eq_elim vh2 (init p (SZ.v klen));
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** {2 The digest}

    [Spec.Blake2.final]: the state serialized little-endian and truncated to
    the requested length.  The truncation is why the whole eight words are
    written to a scratch buffer first. *)
fn write_digest_le (#t: Type0) {| w: word t |}
                   ([@@@FStar.Attributes.monomorphize] p: params t)
                   (out: S.slice S8.t) (st: S.slice t)
                   (#vout: erased (Seq.seq S8.t)) (#pst: perm) (#vst: erased (Seq.lseq t 8))
requires S.pts_to out vout ** S.pts_to st #pst vst **
         pure (Seq.length vout == (hash_bytes p))
ensures S.pts_to out (final p vst) ** S.pts_to st #pst vst
{
  S.pts_to_len out;
  S.pts_to_len st;
  let nb = nbytes #t #w;
  let z8 = S8.classify 0uy;
  let dlen = SZ.mul 8sz nb;
  let mut darr = [| z8; dlen |];
  A.pts_to_len darr;
  let dig = S.from_array darr dlen;
  S.pts_to_len dig;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 8sz)
  invariant exists* (vj: SZ.t) (vd: Seq.seq S8.t).
    pts_to j vj ** S.pts_to dig vd ** S.pts_to st #pst vst ** S.is_from_array darr dig **
    pure (SZ.v vj <= 8 /\ Seq.length vd == 8 * bytes #t /\
          (forall (i: nat). i < SZ.v vj * bytes #t ==>
             Seq.index vd i == Seq.index (words_to_le 8 vst) i))
  decreases (8 - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vj + 1) 8;
    Math.distributivity_add_left (SZ.v vj) 1 (bytes #t);
    let x = S.(st.(vj));
    store_le #t dig (SZ.mul vj nb) x;
    with vd. assert (S.pts_to dig vd);
    digest_step_le #t 8 vst (SZ.v vj) (SZ.v (SZ.mul vj nb)) vd;
    j := SZ.add vj 1sz;
  };
  with vd. assert (S.pts_to dig vd);
  Seq.lemma_eq_intro vd (words_to_le 8 vst);
  Seq.lemma_eq_elim vd (words_to_le 8 vst);

  let hb = p.nhash_bytes;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi hb)
  invariant exists* (vi: SZ.t) (vo: Seq.seq S8.t).
    pts_to i vi ** S.pts_to out vo ** S.pts_to dig vd ** S.pts_to st #pst vst **
    S.is_from_array darr dig **
    pure (SZ.v vi <= (hash_bytes p) /\ Seq.length vo == (hash_bytes p) /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vo k == Seq.index vd k))
  decreases (hash_bytes p - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(dig.(vi));
    S.((out.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vo. assert (S.pts_to out vo);
  Seq.lemma_eq_intro vo (final p vst);
  Seq.lemma_eq_elim vo (final p vst);
  S.to_array dig;
}

(** Block [i] of the padded stream: the key block for [i < koff], a message
    block after that.  The branch lives in its own function so that both arms
    are checked against one written-down postcondition; Pulse will not invent
    the join itself. *)
fn read_block_of (#t: Type0) {| w: word t |}
                 (blk: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
                 (usekey: bool) (off: SZ.t)
                 (#vblk0: erased (Seq.seq S8.t))
                 (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to blk vblk0 ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vblk0 == block_len #t)
ensures exists* (vb: Seq.seq S8.t).
  S.pts_to blk vb ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vb == block_len #t /\
        vb == (if usekey then pad_block #t (reveal vkey) 0
               else pad_block #t (reveal vmsg) (SZ.v off)))
{
  if usekey {
    read_block #t blk key 0sz;
  } else {
    read_block #t blk msg off;
  }
}

#pop-options

(** How far the message offset advances after block [i]: not at all while the
    key block is being consumed. *)
let step_of (usekey: bool) (bl: SZ.t) : (n: SZ.t { SZ.v n == (if usekey then 0 else SZ.v bl) }) =
  if usekey then 0sz else bl

(** The block count, as the implementation computes it. *)
let nblocks_sz (klen mlen bl: SZ.t)
  : Pure SZ.t (requires 0 < SZ.v bl /\ SZ.fits (SZ.v mlen + 2 * SZ.v bl))
              (ensures fun n ->
                 SZ.v n == (if SZ.v klen = 0 && SZ.v mlen = 0 then 1
                            else (if SZ.v klen = 0 then 0 else 1) +
                                 (if SZ.v mlen % SZ.v bl = 0
                                  then SZ.v mlen / SZ.v bl
                                  else SZ.v mlen / SZ.v bl + 1)))
  = let q = SZ.div mlen bl in
    let r = SZ.rem mlen bl in
    let nmb = if SZ.eq r 0sz then q else SZ.add q 1sz in
    let k = if SZ.eq klen 0sz then 0sz else 1sz in
    let n = SZ.add k nmb in
    if SZ.eq n 0sz then 1sz else n

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** {2 Every block but the last}

    The counter passed with block [i] is [(i + 1) * block_len]: the number of
    bytes absorbed including this block. *)
fn blake2_blocks (#t: Type0) {| w: word t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (h: S.slice t) (vv: S.slice t) (mw: S.slice t) (blk: S.slice S8.t)
                 (ivs: S.slice t) (sg: S.slice SZ.t)
                 (key: S.slice S8.t) (msg: S.slice S8.t)
                 (koffsz: SZ.t) (nlast: SZ.t)
                 (#vh0: erased (Seq.seq t)) (#vv0: erased (Seq.seq t)) (#vm0: erased (Seq.seq t))
                 (#vblk0: erased (Seq.seq S8.t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#ps: perm) (#vs: erased (Seq.seq SZ.t))
                 (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires
  S.pts_to h vh0 ** S.pts_to vv vv0 ** S.pts_to mw vm0 ** S.pts_to blk vblk0 **
  S.pts_to ivs #pi vi ** S.pts_to sg #ps vs **
  S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vh0 == 8 /\ Seq.length vv0 == 16 /\ Seq.length vm0 == 16 /\
        Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
        reveal vi == G.reveal p.iv /\ sigma_ok vs /\
        Seq.length vkey <= max_key_len #t /\
        SZ.v koffsz == koff #t (reveal vkey) /\
        SZ.v nlast + 1 == nblocks #t (reveal vkey) (reveal vmsg) /\
        Seq.length vmsg + 2 * block_len #t < pow2 64 /\
        SZ.fits (Seq.length vmsg + 2 * block_len #t) /\
        reveal vh0 == init p (Seq.length vkey))
ensures exists* (vh: Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t) (vb1: Seq.seq S8.t).
  S.pts_to h vh ** S.pts_to vv vv1 ** S.pts_to mw vm1 ** S.pts_to blk vb1 **
  S.pts_to ivs #pi vi ** S.pts_to sg #ps vs **
  S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= max_key_len #t /\ Seq.length vh == 8 /\
        Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
        Seq.length vb1 == block_len #t /\
        vh == repeati_g (SZ.v nlast)
                (compress_at p (data #t (reveal vkey) (reveal vmsg)))
                (init p (Seq.length vkey)))
{
  S.pts_to_len h;
  S.pts_to_len msg;
  S.pts_to_len key;
  nblocks_exact #t (reveal vkey) (reveal vmsg);
  data_len_bound #t (reveal vkey) (reveal vmsg);
  let bl = block_len_sz #t #w;
  let mut i = 0sz;
  let mut off = 0sz;
  let mut ctr = bl;

  while (let vi2 = !i; SZ.lt vi2 nlast)
  invariant exists* (vi2: SZ.t) (voff: SZ.t) (vctr: SZ.t)
                    (vh: Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t) (vb1: Seq.seq S8.t).
    pts_to i vi2 ** pts_to off voff ** pts_to ctr vctr **
    S.pts_to h vh ** S.pts_to vv vv1 ** S.pts_to mw vm1 ** S.pts_to blk vb1 **
    S.pts_to ivs #pi vi ** S.pts_to sg #ps vs **
    S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
    pure (Seq.length vkey <= max_key_len #t /\
          SZ.v vi2 <= SZ.v nlast /\ Seq.length vh == 8 /\
          Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
          Seq.length vb1 == block_len #t /\ Seq.length vi == 8 /\
          reveal vi == G.reveal p.iv /\ sigma_ok vs /\
          SZ.v koffsz == koff #t (reveal vkey) /\
          SZ.v nlast + 1 == nblocks #t (reveal vkey) (reveal vmsg) /\
          Seq.length vmsg + 2 * block_len #t < pow2 64 /\
          SZ.fits (Seq.length vmsg + 2 * block_len #t) /\
          SZ.v vctr == (SZ.v vi2 + 1) * block_len #t /\
          SZ.v voff == (if SZ.v vi2 <= SZ.v koffsz then 0
                        else (SZ.v vi2 - SZ.v koffsz) * block_len #t) /\
          SZ.v voff <= Seq.length vmsg /\
          vh == repeati_g (SZ.v vi2)
                  (compress_at p (data #t (reveal vkey) (reveal vmsg)))
                  (init p (Seq.length vkey)))
  decreases (SZ.v nlast - SZ.v (!i))
  {
    let vi2 = !i;
    let voff = !off;
    let vctr = !ctr;
    let usekey = SZ.lt vi2 koffsz;

    block_at_data #t (reveal vkey) (reveal vmsg) (SZ.v vi2);
    nblocks_bound #t (reveal vkey) (reveal vmsg) (SZ.v vi2);
    unfold_repeati_g (SZ.v vi2) (compress_at p (data #t (reveal vkey) (reveal vmsg)))
                     (init p (Seq.length vkey));
    msg_blocks_bound #t (reveal vkey) (reveal vmsg) (SZ.v vi2 + 1 - SZ.v koffsz);
    Math.distributivity_add_left (SZ.v vi2) 1 (block_len #t);
    Math.distributivity_add_left (SZ.v vi2 + 1) 1 (block_len #t);
    Math.distributivity_add_left (SZ.v vi2 - SZ.v koffsz) 1 (block_len #t);
    Math.lemma_mult_le_right (block_len #t) (SZ.v vi2 + 2) (SZ.v nlast + 1);

    read_block_of #t blk key msg usekey voff;
    load_block #t mw blk;
    compress_impl p h mw vv ivs sg vctr false;

    off := SZ.add voff (step_of usekey bl);
    ctr := SZ.add vctr bl;
    i := SZ.add vi2 1sz;
  }
}

#pop-options
