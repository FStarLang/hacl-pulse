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

(** SHA-2, written once for the whole family.

    Every function takes the [Spec.SHA2.params] record as a monomorphized
    binder, so Custard emits one copy per algorithm with the rotation amounts,
    the round count and the digest length all folded to literals.  Nothing here
    branches on which algorithm is running.

    The round constants and the initial state arrive as slices rather than as
    fields of [p], which is erased: a record field would have to be
    materialized in C.  The caller passes the tables and proves them equal to
    [p.k] and [p.iv]; see [Hacl.Hash.SHA2].  The permission is fractional, so
    a caller may hand over the [static const] array itself. *)
module Hacl.Hash.SHA2.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Spec.SHA2
open Spec.SHA2.Lemmas
open Hacl.Spec.Loops

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast

(** {2 Byte counts as machine values} *)

let block_len_sz (#t: Type0) {| w: word t |} : n: SZ.t { SZ.v n == block_len #t } =
  SZ.mul 16sz (nbytes #t #w)

let len_len_sz (#t: Type0) {| w: word t |} : n: SZ.t { SZ.v n == len_len #t } =
  SZ.mul 2sz (nbytes #t #w)

(** A message short enough to hash has a bit length that fits in eight bytes. *)
let len_fits (n: nat) : Lemma (requires n < pow2 61) (ensures 8 * n < pow2 64)
  = Math.pow2_plus 61 3;
    assert_norm (pow2 3 == 8)

(** Every byte count in this file is at most two blocks, and a block is at most
    two hundred and fifty-six bytes, so [SizeT] arithmetic never overflows. *)
let small_fits (n: nat) : Lemma (requires n <= 512) (ensures SZ.fits n)
  = assert_norm (512 < pow2 16)

(** How much of the two-block scratch buffer the padding actually occupies: one
    block if the [0x80] byte and the length still fit beside the remainder, two
    otherwise. *)
inline_for_extraction
let tail_len (#t: Type0) {| w: word t |} (rem: (r: SZ.t { SZ.v r < block_len #t }))
  : n: SZ.t { 8 <= SZ.v n /\ SZ.v n <= 2 * block_len #t /\
              SZ.v n == (if SZ.v rem + 1 + len_len #t <= block_len #t
                         then block_len #t else 2 * block_len #t) } =
  let bl = block_len_sz #t #w in
  let ll = len_len_sz #t #w in
  if SZ.lte (SZ.add rem (SZ.add 1sz ll)) bl then bl else SZ.mul 2sz bl

(** {2 Message schedule} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn ws_expand (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (wsb: S.slice t) (block: S.slice S8.t) (off: SZ.t)
             (#vw0: erased (Seq.seq t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires S.pts_to wsb vw0 ** S.pts_to block #pb vb **
         pure (Seq.length vw0 == (rounds p) /\ SZ.v off + block_len #t <= Seq.length vb)
ensures S.pts_to wsb (ws p (words_from_be block_words (block_at #t vb (SZ.v off)))) **
        S.pts_to block #pb vb
{
  S.pts_to_len wsb;
  S.pts_to_len block;
  let nb = nbytes #t #w;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vw: Seq.seq t).
    pts_to i vi ** S.pts_to wsb vw ** S.pts_to block #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length vw == (rounds p) /\ SZ.v off + block_len #t <= Seq.length vb /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vw j == ws_at p (words_from_be block_words (block_at #t vb (SZ.v off))) j))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vi + 1) 16;
    Seq.slice_slice vb (SZ.v off) (SZ.v off + block_len #t)
                    (SZ.v vi * bytes #t) (SZ.v vi * bytes #t + bytes #t);
    let x = load_be #t block (SZ.add off (SZ.mul vi nb));
    w.v_extensional x (ws_at p (words_from_be block_words (block_at #t vb (SZ.v off))) (SZ.v vi));
    S.((wsb.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  let mut j = 16sz;
  while (let vj = !j; SZ.lt vj p.nrounds)
  invariant exists* (vj: SZ.t) (vw: Seq.seq t).
    pts_to j vj ** S.pts_to wsb vw ** S.pts_to block #pb vb **
    pure (16 <= SZ.v vj /\ SZ.v vj <= (rounds p) /\ Seq.length vw == (rounds p) /\
          SZ.v off + block_len #t <= Seq.length vb /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index vw k == ws_at p (words_from_be block_words (block_at #t vb (SZ.v off))) k))
  decreases (rounds p - SZ.v (!j))
  {
    let vj = !j;
    let a2 = S.(wsb.(SZ.sub vj 2sz));
    let a7 = S.(wsb.(SZ.sub vj 7sz));
    let a15 = S.(wsb.(SZ.sub vj 15sz));
    let a16 = S.(wsb.(SZ.sub vj 16sz));
    let x = add_mod #t (add_mod #t (add_mod #t (_sigma1 p a2) a7) (_sigma0 p a15)) a16;
    S.((wsb.(vj) <- x));
    j := SZ.add vj 1sz;
  };
  with vw. assert (S.pts_to wsb vw);
  Seq.lemma_eq_intro vw (ws p (words_from_be block_words (block_at #t vb (SZ.v off))));
  Seq.lemma_eq_elim vw (ws p (words_from_be block_words (block_at #t vb (SZ.v off))));
}

(** {2 One block}

    Eight registers, read at the top of the round and written back at the
    bottom, exactly as [Spec.SHA2.set8] describes.  Keeping the working state
    in a slice rather than in eight local variables is what lets the round be a
    loop at all; a C compiler keeps them in registers regardless. *)

fn update_block_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (kt: S.slice t) (wsb: S.slice t) (st: S.slice t) (block: S.slice S8.t) (off: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#vw0: erased (Seq.seq t)) (#vst0: erased (Seq.lseq t 8))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to wsb vw0 ** S.pts_to st vst0 ** S.pts_to block #pb vb **
         pure (Seq.length vw0 == (rounds p) /\ reveal vk == (reveal p.k <: Seq.seq t) /\
               SZ.v off + block_len #t <= Seq.length vb)
ensures exists* vw.
  S.pts_to kt #pk vk ** S.pts_to wsb vw ** S.pts_to st (update_block p (block_at #t vb (SZ.v off)) vst0) **
  S.pts_to block #pb vb ** pure (Seq.length vw == (rounds p))
{
  S.pts_to_len kt;
  S.pts_to_len st;
  ws_expand p wsb block off;
  let a0 = S.(st.(0sz));
  let b0 = S.(st.(1sz));
  let c0 = S.(st.(2sz));
  let d0 = S.(st.(3sz));
  let e0 = S.(st.(4sz));
  let f0 = S.(st.(5sz));
  let g0 = S.(st.(6sz));
  let h0 = S.(st.(7sz));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi p.nrounds)
  invariant exists* (vi: SZ.t) (vst: Seq.seq t).
    pts_to i vi ** S.pts_to kt #pk vk ** S.pts_to wsb (ws p (words_from_be block_words (block_at #t vb (SZ.v off)))) **
    S.pts_to st vst ** S.pts_to block #pb vb **
    pure (SZ.v vi <= (rounds p) /\ Seq.length vst == 8 /\
          vst == repeati_g (SZ.v vi) (shuffle_core p (ws p (words_from_be block_words (block_at #t vb (SZ.v off))))) vst0)
  decreases (rounds p - SZ.v (!i))
  {
    let vi = !i;
    let a = S.(st.(0sz));
    let b = S.(st.(1sz));
    let c = S.(st.(2sz));
    let d = S.(st.(3sz));
    let e = S.(st.(4sz));
    let f = S.(st.(5sz));
    let g = S.(st.(6sz));
    let hh = S.(st.(7sz));
    let ki = S.(kt.(vi));
    let wi = S.(wsb.(vi));
    let t1 = add_mod #t (add_mod #t (add_mod #t (add_mod #t hh (_Sigma1 p e)) (_Ch e f g)) ki) wi;
    let t2 = add_mod #t (_Sigma0 p a) (_Maj a b c);
    S.((st.(0sz) <- add_mod #t t1 t2));
    S.((st.(1sz) <- a));
    S.((st.(2sz) <- b));
    S.((st.(3sz) <- c));
    S.((st.(4sz) <- add_mod #t d t1));
    S.((st.(5sz) <- e));
    S.((st.(6sz) <- f));
    S.((st.(7sz) <- g));
    i := SZ.add vi 1sz;
  };
  let a1 = S.(st.(0sz));
  let b1 = S.(st.(1sz));
  let c1 = S.(st.(2sz));
  let d1 = S.(st.(3sz));
  let e1 = S.(st.(4sz));
  let f1 = S.(st.(5sz));
  let g1 = S.(st.(6sz));
  let h1 = S.(st.(7sz));
  with vsh. assert (S.pts_to st vsh);
  set8_irrelevant #t vsh vst0
    (add_mod #t a0 a1) (add_mod #t b0 b1) (add_mod #t c0 c1) (add_mod #t d0 d1)
    (add_mod #t e0 e1) (add_mod #t f0 f1) (add_mod #t g0 g1) (add_mod #t h0 h1);
  S.((st.(0sz) <- add_mod #t a0 a1));
  S.((st.(1sz) <- add_mod #t b0 b1));
  S.((st.(2sz) <- add_mod #t c0 c1));
  S.((st.(3sz) <- add_mod #t d0 d1));
  S.((st.(4sz) <- add_mod #t e0 e1));
  S.((st.(5sz) <- add_mod #t f0 f1));
  S.((st.(6sz) <- add_mod #t g0 g1));
  S.((st.(7sz) <- add_mod #t h0 h1));
}

(** {2 The last block or two}

    A scratch buffer of two blocks, zero-initialized so the zero padding costs
    nothing, receives the remainder of the message, the [0x80] byte and the
    eight low bytes of the bit length.  Everything else is already zero, which
    is what [Spec.SHA2.Lemmas.tail_bytes] checks against the specification. *)

(** The message length in bits, big-endian, in the last eight bytes of the
    padding.  Only eight: a message long enough to need more than [2^64] bits
    of length cannot be addressed, and the higher bytes of the length field are
    left at the zero the buffer was allocated with. *)

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"

fn write_len_be (b: S.slice S8.t) (off: SZ.t) (len: SZ.t)
                (#vb: erased (Seq.seq S8.t))
requires S.pts_to b vb ** pure (SZ.v off + 8 <= Seq.length vb /\ 8 * SZ.v len < pow2 64)
ensures exists* vb'. S.pts_to b vb' **
  pure (Seq.length vb' == Seq.length vb /\ SZ.v off + 8 <= Seq.length vb' /\
        (forall (j: nat). j < 8 ==>
           Seq.index vb' (SZ.v off + 7 - j) ==
             S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))) /\
        (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + 8 ==>
           Seq.index vb' k == Seq.index vb k))
{
  S.pts_to_len b;
  let bits8 = U64.mul 8uL (SZ.sizet_to_uint64 len);
  let mut d = 0sz;
  let mut sh = 0ul;
  while (let vd = !d; SZ.lt vd 8sz)
  invariant exists* (vd: SZ.t) (vsh: U32.t) (vb': Seq.seq S8.t).
    pts_to d vd ** pts_to sh vsh ** S.pts_to b vb' **
    pure (SZ.v vd <= 8 /\ U32.v vsh == 8 * SZ.v vd /\ Seq.length vb' == Seq.length vb /\
          (forall (j: nat). j < SZ.v vd ==>
             Seq.index vb' (SZ.v off + 7 - j) ==
               S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))) /\
          (forall (k: nat). k < Seq.length vb ==>
             k < SZ.v off + 8 - SZ.v vd \/ k >= SZ.v off + 8 ==>
             Seq.index vb' k == Seq.index vb k))
  decreases (8 - SZ.v (!d))
  {
    let vd = !d;
    let vsh = !sh;
    let c = Cast.uint64_to_uint8 (U64.shift_right bits8 vsh);
    let bs = S8.classify c;
    S.((b.(SZ.add off (SZ.sub 7sz vd)) <- bs));
    Math.distributivity_add_right 8 (SZ.v vd) 1;
    d := SZ.add vd 1sz;
    sh := U32.add vsh 8ul;
  };
}

#pop-options

(** {2 The last block or two}

    A scratch buffer of two blocks, zero-initialized so the zero padding costs
    nothing, receives the remainder of the message, the [0x80] byte and the
    bit length.  Everything else is already zero, which is what
    [Spec.SHA2.Lemmas.tail_bytes] checks against the specification. *)

#push-options "--z3rlimit 200"

fn build_tail (#t: Type0) {| w: word t |}
              (tl: S.slice S8.t) (input: S.slice S8.t) (len: SZ.t) (base: SZ.t)
              (rem: (r: SZ.t { SZ.v r < block_len #t }))
              (ntail: (n: SZ.t { 8 <= SZ.v n /\ SZ.v n <= 2 * block_len #t }))
              (#vt0: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to tl vt0 ** S.pts_to input #pin vin **
         pure (Seq.length vt0 == 2 * block_len #t /\
               (forall (k: nat). k < 2 * block_len #t ==> Seq.index vt0 k == S8.classify 0uy) /\
               Seq.length vin == SZ.v base + SZ.v rem /\ 8 * SZ.v len < pow2 64 /\
               SZ.v rem + 1 + len_len #t <= SZ.v ntail)
ensures exists* vt.
  S.pts_to tl vt ** S.pts_to input #pin vin **
  pure (Seq.length vt == 2 * block_len #t /\ SZ.v base + SZ.v rem == Seq.length vin /\
        (forall (k: nat). k < SZ.v rem ==> Seq.index vt k == Seq.index vin (SZ.v base + k)) /\
        Seq.index vt (SZ.v rem) == S8.classify 0x80uy /\
        (forall (k: nat). SZ.v rem < k /\ k < SZ.v ntail - 8 ==> Seq.index vt k == S8.classify 0uy) /\
        (forall (j: nat). j < 8 ==>
           Seq.index vt (SZ.v ntail - 1 - j) ==
             S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))))
{
  S.pts_to_len tl;
  S.pts_to_len input;
  let z8 = S8.classify 0uy;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc rem)
  invariant exists* (vc: SZ.t) (vt: Seq.seq S8.t).
    pts_to c vc ** S.pts_to tl vt ** S.pts_to input #pin vin **
    pure (SZ.v vc <= SZ.v rem /\ Seq.length vt == 2 * block_len #t /\
          (forall (k: nat). k < SZ.v vc ==> Seq.index vt k == Seq.index vin (SZ.v base + k)) /\
          (forall (k: nat). SZ.v vc <= k /\ k < 2 * block_len #t ==> Seq.index vt k == z8))
  decreases (SZ.v rem - SZ.v (!c))
  {
    let vc = !c;
    let x = S.(input.(SZ.add base vc));
    S.((tl.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  let x80 = S8.classify 0x80uy;
  S.((tl.(rem) <- x80));
  write_len_be tl (SZ.sub ntail 8sz) len;
}

(** {2 The digest}

    The state is written out big-endian into a scratch buffer of eight whole
    words and the first [hash_bytes] of it are handed to the caller; SHA-224
    and SHA-384 stop in the middle of a word, which is why the truncation is a
    byte copy rather than a shorter loop. *)

fn write_digest (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                (out: S.slice S8.t) (st: S.slice t)
                (#vout: erased (Seq.seq S8.t)) (#pst: perm) (#vst: erased (Seq.lseq t 8))
requires S.pts_to out vout ** S.pts_to st #pst vst **
         pure (Seq.length vout == (hash_bytes p))
ensures S.pts_to out (finish p vst) ** S.pts_to st #pst vst
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
             Seq.index vd i == Seq.index (words_to_be 8 vst) i))
  decreases (8 - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vj + 1) 8;
    Math.distributivity_add_left (SZ.v vj) 1 (bytes #t);
    let x = S.(st.(vj));
    store_be #t dig (SZ.mul vj nb) x;
    with vd. assert (S.pts_to dig vd);
    digest_step #t 8 vst (SZ.v vj) (SZ.v (SZ.mul vj nb)) vd;
    j := SZ.add vj 1sz;
  };
  with vd. assert (S.pts_to dig vd);
  Seq.lemma_eq_intro vd (words_to_be 8 vst);
  Seq.lemma_eq_elim vd (words_to_be 8 vst);

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
  Seq.lemma_eq_intro vo (finish p vst);
  Seq.lemma_eq_elim vo (finish p vst);
  S.to_array dig;
}

(** {2 The whole hash}

    One loop over the whole blocks of the message, then a two-block scratch
    buffer holding the last partial block together with the padding, then one
    or two more blocks from that.  The specification is a single fold over the
    padded message; [Hacl.Spec.Loops.repeati_g_split] is what lets it be run as
    two loops, and [Spec.SHA2.Lemmas.padded_index] is what identifies the bytes
    the second one sees. *)

#pop-options

#push-options "--z3rlimit 400"

(** The padding blocks and the digest.  Separated from [hash_impl] only so that
    each proof obligation sees a small context. *)

fn tail_and_finish (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                   (kt: S.slice t) (wsb: S.slice t) (st: S.slice t)
                   (out: S.slice S8.t) (input: S.slice S8.t)
                   (len: SZ.t) (nblocks: SZ.t) (base_in: SZ.t)
                   (rem: (r: SZ.t { SZ.v r < block_len #t }))
                   (pre: erased (Seq.seq S8.t))
                   (#pk: perm) (#vk: erased (Seq.seq t))
                   (#vw0: erased (Seq.seq t)) (#vst0: erased (Seq.lseq t 8))
                   (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to wsb vw0 ** S.pts_to st vst0 **
         S.pts_to out vout ** S.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length pre + Seq.length vin == SZ.v len /\
               Seq.length vin == SZ.v base_in + SZ.v rem /\
               SZ.v len < pow2 61 /\ SZ.v len < max_input #t /\
               SZ.v rem == SZ.v len % block_len #t /\
               SZ.v len - SZ.v rem == SZ.v nblocks * block_len #t /\
               reveal vst0 == repeati_g (SZ.v nblocks)
                                (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq t) (vst: Seq.lseq t 8) (vout': Seq.seq S8.t).
  S.pts_to kt #pk vk ** S.pts_to wsb vw ** S.pts_to st vst **
  S.pts_to out vout' ** S.pts_to input #pin vin **
  pure (Seq.length vw == (rounds p) /\
        Seq.length pre + Seq.length vin < max_input #t /\
        vout' == hash p (Seq.append pre vin))
{
  S.pts_to_len input;
  S.pts_to_len out;
  S.pts_to_len st;
  S.pts_to_len wsb;
  let bl = block_len_sz #t #w;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #t (Seq.append pre vin);
  let ntail = tail_len #t #w rem;
  let bl2 = SZ.mul 2sz bl;
  let base = SZ.sub len rem;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; bl2 |];
  A.pts_to_len tarr;
  let tl = S.from_array tarr bl2;
  S.pts_to_len tl;
  len_fits (SZ.v len);
  Math.euclidean_division_definition (SZ.v len) (block_len #t);
  build_tail #t tl input len base_in rem ntail;
  with vt. assert (S.pts_to tl vt);
  pad_zeros_alt #t (SZ.v len);
  append_index_at (reveal pre) (reveal vin) (SZ.v base) (SZ.v base_in) (SZ.v rem);
  tail_bytes #t (Seq.append pre vin) vt (SZ.v ntail) (SZ.v base);
  Math.multiple_division_lemma (SZ.v ntail / block_len #t) (block_len #t);
  Math.multiply_fractions (SZ.v ntail) (block_len #t);
  let ntb = SZ.div ntail bl;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj ntb)
  invariant exists* (vj: SZ.t) (vw: Seq.seq t) (vst: Seq.lseq t 8).
    pts_to j vj ** S.pts_to kt #pk vk ** S.pts_to wsb vw ** S.pts_to st vst **
    S.pts_to tl vt ** S.is_from_array tarr tl **
    pure (SZ.v vj <= SZ.v ntb /\ Seq.length vw == (rounds p) /\
          SZ.v ntb * block_len #t <= SZ.v ntail /\
          SZ.v base == SZ.v nblocks * block_len #t /\
          Seq.length (padded #t (Seq.append pre vin)) == SZ.v base + SZ.v ntail /\
          (forall (o: nat). o + block_len #t <= SZ.v ntail ==>
             block_at #t (padded #t (Seq.append pre vin)) (SZ.v base + o) == block_at #t vt o) /\
          vst == repeati_g (SZ.v nblocks + SZ.v vj)
                   (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
  decreases (SZ.v ntb - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right (block_len #t) (SZ.v vj) (SZ.v ntb);
    small_fits (SZ.v vj * block_len #t);
    Math.lemma_mult_le_right (block_len #t) (SZ.v vj + 1) (SZ.v ntb);
    Math.distributivity_add_left (SZ.v vj) 1 (block_len #t);
    Math.distributivity_add_left (SZ.v nblocks) (SZ.v vj) (block_len #t);
    Math.distributivity_add_left (SZ.v nblocks + SZ.v vj) 1 (block_len #t);
    unfold_repeati_g (SZ.v nblocks + SZ.v vj)
      (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv);
    assert (pure (block_at #t (padded #t (Seq.append pre vin))
                    ((SZ.v nblocks + SZ.v vj) * block_len #t) ==
                  block_at #t vt (SZ.v vj * block_len #t)));
    assert (pure ((SZ.v nblocks + SZ.v vj + 1) * block_len #t <=
                  Seq.length (padded #t (Seq.append pre vin))));
    update_block_impl p kt wsb st tl (SZ.mul vj bl);
    j := SZ.add vj 1sz;
  };
  Math.multiple_modulo_lemma 1 (block_len #t);
  Math.multiple_modulo_lemma 2 (block_len #t);
  Math.euclidean_division_definition (SZ.v ntail) (block_len #t);
  assert (pure (SZ.v ntb * block_len #t == SZ.v ntail));
  Math.distributivity_add_left (SZ.v nblocks) (SZ.v ntb) (block_len #t);
  Math.multiple_division_lemma (SZ.v nblocks + SZ.v ntb) (block_len #t);
  assert (pure (Seq.length (padded #t (Seq.append pre vin)) / block_len #t ==
                SZ.v nblocks + SZ.v ntb));
  assert (pure (update_all p (padded #t (Seq.append pre vin)) (reveal p.iv) ==
                repeati_g (SZ.v nblocks + SZ.v ntb)
                  (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv)));
  write_digest p out st;
  S.to_array tl;
}

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** The full blocks of the message, in place.  Split out of [hash_impl] so
    that the loop's proof obligation sees only the loop. *)

fn hash_blocks (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: S.slice t) (wsb: S.slice t) (st: S.slice t) (input: S.slice S8.t)
               (bl: (b: SZ.t { SZ.v b == block_len #t })) (nprev: SZ.t) (nfull: SZ.t)
               (pre: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#vw0: erased (Seq.seq t)) (#vst0: erased (Seq.lseq t 8))
               (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to wsb vw0 ** S.pts_to st vst0 ** S.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #t /\
               Seq.length pre + Seq.length vin < max_input #t /\
               SZ.v nfull == Seq.length vin / block_len #t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq t) (vst: Seq.lseq t 8).
  S.pts_to kt #pk vk ** S.pts_to wsb vw ** S.pts_to st vst ** S.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
{
  S.pts_to_len input;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #t (Seq.append pre vin);
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 nfull)
  invariant exists* (vi2: SZ.t) (vw: Seq.seq t) (vst: Seq.lseq t 8).
    pts_to i vi2 ** S.pts_to kt #pk vk ** S.pts_to wsb vw ** S.pts_to st vst **
    S.pts_to input #pin vin **
    pure (SZ.v vi2 <= SZ.v nfull /\ Seq.length vw == (rounds p) /\
          vst == repeati_g (SZ.v nprev + SZ.v vi2)
                   (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
  decreases (SZ.v nfull - SZ.v (!i))
  {
    let vi2 = !i;
    Math.lemma_mult_le_right (block_len #t) (SZ.v vi2 + 1) (SZ.v nfull);
    Math.lemma_mult_le_right (block_len #t) (SZ.v nfull) (Seq.length vin / block_len #t);
    padded_index_block_shift #t (reveal pre) (reveal vin) (SZ.v vi2 * block_len #t);
    Math.distributivity_add_left (SZ.v nprev) (SZ.v vi2) (block_len #t);
    Math.distributivity_add_left (SZ.v nprev) (SZ.v vi2 + 1) (block_len #t);
    unfold_repeati_g (SZ.v nprev + SZ.v vi2)
      (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv);
    assert (pure (block_at #t (padded #t (Seq.append pre vin))
                    ((SZ.v nprev + SZ.v vi2) * block_len #t) ==
                  block_at #t vin (SZ.v vi2 * block_len #t)));
    assert (pure ((SZ.v nprev + SZ.v vi2 + 1) * block_len #t <=
                  Seq.length (padded #t (Seq.append pre vin))));
    update_block_impl p kt wsb st input (SZ.mul vi2 bl);
    i := SZ.add vi2 1sz;
  };
}

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
fn hash_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (kt: S.slice t) (ivt: S.slice t) (out: S.slice S8.t) (input: S.slice S8.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout ** S.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vin < pow2 61 /\ Seq.length vin < max_input #t)
ensures exists* vout'.
  S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout' ** S.pts_to input #pin vin **
  pure (Seq.length vin < max_input #t /\ vout' == hash p vin)
{
  S.pts_to_len kt;
  S.pts_to_len ivt;
  S.pts_to_len out;
  S.pts_to_len input;
  let bl = block_len_sz #t #w;
  let ll = len_len_sz #t #w;
  let len = S.len input;
  let nfull = SZ.div len bl;
  let rem = SZ.rem len bl;
  let z0: t = zero #t #w;

  let mut starr = [| z0; 8sz |];
  A.pts_to_len starr;
  let st = S.from_array starr 8sz;
  S.pts_to_len st;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq t).
    pts_to c vc ** S.pts_to st vst ** S.pts_to ivt #pi vi ** S.is_from_array starr st **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==> Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = S.(ivt.(vc));
    S.((st.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (S.pts_to st vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq t);

  let mut wsarr = [| z0; p.nrounds |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr p.nrounds;
  S.pts_to_len wsb;

  let empty : erased (Seq.seq S8.t) = hide (Seq.empty #S8.t);
  Seq.lemma_eq_elim (Seq.append (reveal empty) (reveal vin)) (reveal vin);
  Math.euclidean_division_definition (SZ.v len) (block_len #t);
  hash_blocks p kt wsb st input bl 0sz nfull empty;
  tail_and_finish p kt wsb st out input len nfull (SZ.sub len rem) rem empty;

  S.to_array wsb;
  S.to_array st;
}

#pop-options

#pop-options


#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** {2 Hashing a message with a one-block prefix}

    [hash p (blk || input)] where [blk] is exactly one block, computed without
    ever building the concatenation: the prefix block is absorbed first and
    the rest of the message is read straight out of the caller's buffer.

    This is what HMAC's inner hash needs -- the prefix is [K0 ^ ipad] -- and it
    is the same generalization an incremental interface would use, which is
    why [hash_blocks] and [tail_and_finish] are stated for a ghost
    block-aligned prefix rather than for this special case. *)

fn hash_prefixed (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                 (kt: S.slice t) (ivt: S.slice t) (out: S.slice S8.t)
                 (blk: S.slice S8.t) (input: S.slice S8.t)
                 (#pk: perm) (#vk: erased (Seq.seq t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#vout: erased (Seq.seq S8.t))
                 (#pb: perm) (#vb: erased (Seq.seq S8.t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout **
         S.pts_to blk #pb vb ** S.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vb == block_len #t /\
               SZ.fits (block_len #t + Seq.length vin) /\
               block_len #t + Seq.length vin < pow2 61 /\
               block_len #t + Seq.length vin < max_input #t)
ensures exists* vout'.
  S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout' **
  S.pts_to blk #pb vb ** S.pts_to input #pin vin **
  pure (Seq.length vb + Seq.length vin < max_input #t /\
        vout' == hash p (Seq.append vb vin))
{
  S.pts_to_len kt;
  S.pts_to_len ivt;
  S.pts_to_len out;
  S.pts_to_len blk;
  S.pts_to_len input;
  let bl = block_len_sz #t #w;
  let lin = S.len input;
  let len = SZ.add bl lin;
  let nfull = SZ.div lin bl;
  let rem = SZ.rem lin bl;
  let z0: t = zero #t #w;

  let mut starr = [| z0; 8sz |];
  A.pts_to_len starr;
  let st = S.from_array starr 8sz;
  S.pts_to_len st;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq t).
    pts_to c vc ** S.pts_to st vst ** S.pts_to ivt #pi vi ** S.is_from_array starr st **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==> Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = S.(ivt.(vc));
    S.((st.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (S.pts_to st vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq t);

  let mut wsarr = [| z0; p.nrounds |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr p.nrounds;
  S.pts_to_len wsb;

  Seq.lemma_len_append (reveal vb) (reveal vin);
  padded_shape #t (Seq.append vb vin);
  padded_index_block #t (Seq.append vb vin) 0;
  append_first_block #t (reveal vb) (reveal vin);
  update_block_impl p kt wsb st blk 0sz;
  repeati_g_zero (update_step p (padded #t (Seq.append vb vin))) (reveal p.iv);
  unfold_repeati_g 0 (update_step p (padded #t (Seq.append vb vin))) (reveal p.iv);

  Math.lemma_mod_plus (SZ.v lin) 1 (block_len #t);
  assert (pure (SZ.v rem == SZ.v len % block_len #t));
  Math.euclidean_division_definition (SZ.v lin) (block_len #t);
  Math.distributivity_add_left 1 (SZ.v nfull) (block_len #t);
  assert (pure (SZ.v len - SZ.v rem == (1 + SZ.v nfull) * block_len #t));
  Math.multiply_fractions (SZ.v lin) (block_len #t);
  Math.lemma_mult_le_left (SZ.v nfull) 1 (block_len #t);
  SZ.fits_lte (1 + SZ.v nfull) (block_len #t + SZ.v lin);

  hash_blocks p kt wsb st input bl 1sz nfull vb;
  let nb = SZ.add 1sz nfull;
  let base_in = SZ.sub lin rem;
  tail_and_finish p kt wsb st out input len nb base_in rem vb;

  S.to_array wsb;
  S.to_array st;
}

#pop-options
