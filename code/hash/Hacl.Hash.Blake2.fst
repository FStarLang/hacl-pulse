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
open Hacl.Impl.Table
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module GA = Pulse.Lib.GlobalArray
module G = FStar.Ghost
module Mem = Hacl.Mem
module Cast = FStar.Int.Cast
module Classical = FStar.Classical

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

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"

(** {2 Reading a block}

    [Spec.Blake2.pad_block]: the [block_len] bytes of [s] at [off], zero past
    the end of [s].  No bound on [off] -- past the end the whole block is
    zero, which is exactly what the specification says. *)
fn read_block (#t: Type0) {| w: word t |}
              (blk: A.array S8.t) (s: A.array S8.t) (len: SZ.t) (off: SZ.t)
              (#vblk0: erased (Seq.seq S8.t))
              (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to blk vblk0 ** A.pts_to s #ps vs **
         pure (Seq.length vblk0 == block_len #t)
         ** pure (SZ.v len == Seq.length vs)
ensures A.pts_to blk (pad_block #t (reveal vs) (SZ.v off)) ** A.pts_to s #ps vs
{
  A.pts_to_len blk;
  A.pts_to_len s;
  let z8 = S8.classify 0uy;
  let bl = block_len_sz #t #w;
  let n = block_avail off len bl;

  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk n)
  invariant exists* (vk: SZ.t) (vb: Seq.seq S8.t).
    pts_to k vk ** A.pts_to blk vb ** A.pts_to s #ps vs **
    pure (SZ.v vk <= SZ.v n /\ SZ.v n <= block_len #t /\
          Seq.length vb == block_len #t /\
          (0 < SZ.v n ==> SZ.v off + SZ.v n <= Seq.length vs) /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index vb j == Seq.index (pad_block #t (reveal vs) (SZ.v off)) j))
  decreases (SZ.v n - SZ.v (!k))
  {
    let vk = !k;
    let x = A.(s.(SZ.add off vk));
    A.((blk.(vk) <- x));
    k := SZ.add vk 1sz;
  };

  let mut k2 = n;
  while (let vk = !k2; SZ.lt vk bl)
  invariant exists* (vk: SZ.t) (vb: Seq.seq S8.t).
    pts_to k2 vk ** A.pts_to blk vb ** A.pts_to s #ps vs **
    pure (SZ.v n <= SZ.v vk /\ SZ.v vk <= block_len #t /\
          Seq.length vb == block_len #t /\
          (0 < SZ.v n ==> SZ.v off + SZ.v n <= Seq.length vs) /\
          (SZ.v n < block_len #t ==> Seq.length vs <= SZ.v off + SZ.v n) /\
          (forall (j: nat). j < SZ.v vk ==>
             Seq.index vb j == Seq.index (pad_block #t (reveal vs) (SZ.v off)) j))
  decreases (block_len #t - SZ.v (!k2))
  {
    let vk = !k2;
    A.((blk.(vk) <- z8));
    k2 := SZ.add vk 1sz;
  };
  with vb. assert (A.pts_to blk vb);
  Seq.lemma_eq_intro vb (pad_block #t (reveal vs) (SZ.v off));
  Seq.lemma_eq_elim vb (pad_block #t (reveal vs) (SZ.v off));
}

(** {2 A block as sixteen little-endian words} *)
fn load_block (#t: Type0) {| w: word t |}
              (mw: A.array t) (blk: A.array S8.t)
              (#vm0: erased (Seq.seq t))
              (#pb: perm) (#vb: erased (Seq.lseq S8.t (block_len #t)))
requires A.pts_to mw vm0 ** A.pts_to blk #pb vb **
         pure (Seq.length vm0 == 16)
ensures A.pts_to mw (words_from_le block_words (reveal vb)) ** A.pts_to blk #pb vb
{
  A.pts_to_len mw;
  A.pts_to_len blk;
  let nb = nbytes #t #w;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vm: Seq.seq t).
    pts_to i vi ** A.pts_to mw vm ** A.pts_to blk #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length vm == 16 /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vm j == Seq.index (words_from_le block_words (reveal vb)) j))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vi + 1) 16;
    let x = load_le #t blk (SZ.mul vi nb);
    w.v_extensional x (Seq.index (words_from_le block_words (reveal vb)) (SZ.v vi));
    A.((mw.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vm. assert (A.pts_to mw vm);
  Seq.lemma_eq_intro vm (words_from_le block_words (reveal vb));
  Seq.lemma_eq_elim vm (words_from_le block_words (reveal vb));
}

#pop-options

(** {2 The parameter block}

    [Spec.Blake2.param_block], a byte at a time.  The first half -- every
    field but the salt and the personalization -- is [head_byte], computed
    from machine integers by shifting and truncating; the second half is two
    copies.  [head_byte] is zero past its last field, so writing it over the
    whole block and then never copying anything is the default block. *)

let sz_to_u8 (x: SZ.t { SZ.v x < 256 }) : r: U8.t { U8.v r == SZ.v x } =
  Math.small_mod (SZ.v x) (pow2 32);
  assert_norm (pow2 8 == 256);
  Cast.uint32_to_uint8 (SZ.sizet_to_uint32 x)

let le_byte_u32 (x: U32.t) (k: SZ.t { SZ.v k < 4 })
  : r: U8.t { U8.v r == le_byte (U32.v x) (SZ.v k) }
  = Math.small_mod (SZ.v k) (pow2 32);
    assert_norm (pow2 8 == 256);
    let s = U32.mul 8ul (SZ.sizet_to_uint32 k) in
    Cast.uint32_to_uint8 (U32.shift_right x s)

let le_byte_u64 (x: U64.t) (k: SZ.t { SZ.v k < 8 })
  : r: U8.t { U8.v r == le_byte (U64.v x) (SZ.v k) }
  = Math.small_mod (SZ.v k) (pow2 32);
    assert_norm (pow2 8 == 256);
    let s = U32.mul 8ul (SZ.sizet_to_uint32 k) in
    Cast.uint64_to_uint8 (U64.shift_right x s)

(* Inlined so that it is not extracted as a global, which would need
   Hacl_init_globals to be called before first use. *)
inline_for_extraction noextract
let node_offset_len_sz (#t: Type0) {| w: word t |}
  : n: SZ.t { SZ.v n == node_offset_len #t }
  = if SZ.eq (nbytes #t #w) 4sz then 6sz else 8sz

let head_byte_impl (#t: Type0) {| w: word t |}
                   (nn kk fo dp: U8.t) (leaf: U32.t) (off: U64.t) (nd il: U8.t) (i: SZ.t)
  : r: U8.t { U8.v r == head_byte #t (U8.v nn) (U8.v kk) (U8.v fo) (U8.v dp)
                                     (U32.v leaf) (U64.v off) (U8.v nd) (U8.v il) (SZ.v i) }
  = let ol = node_offset_len_sz #t #w in
    if SZ.eq i 0sz then nn
    else if SZ.eq i 1sz then kk
    else if SZ.eq i 2sz then fo
    else if SZ.eq i 3sz then dp
    else if SZ.lt i 8sz then le_byte_u32 leaf (SZ.sub i 4sz)
    else if SZ.lt i (SZ.add 8sz ol) then le_byte_u64 off (SZ.sub i 8sz)
    else if SZ.eq i (SZ.add 8sz ol) then nd
    else if SZ.eq i (SZ.add 9sz ol) then il
    else 0uy

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(** The block, given its head and its two tails index by index. *)
let param_block_intro (#t: Type0) {| word t |} (bp: blake2_params t)
                      (kk: nat { kk <= max_key_len #t }) (vpb: Seq.seq S8.t)
  : Lemma (requires Seq.length vpb == 8 * bytes #t /\
                    (forall (i: nat). i < 4 * bytes #t ==>
                       Seq.index vpb i ==
                         S8.classify (U8.uint_to_t
                           (head_byte #t bp.digest_length kk bp.fanout bp.depth
                                         bp.leaf_length bp.node_offset bp.node_depth
                                         bp.inner_length i))) /\
                    (forall (i: nat). i < salt_len #t ==>
                       Seq.index vpb (4 * bytes #t + i) == Seq.index bp.salt i) /\
                    (forall (i: nat). i < salt_len #t ==>
                       Seq.index vpb (6 * bytes #t + i) == Seq.index bp.personal i))
          (ensures vpb == param_block bp kk)
  = let w = bytes #t in
    let aux (i: nat { i < 8 * w }) : Lemma (Seq.index vpb i == Seq.index (param_block bp kk) i)
      = if i < 4 * w then ()
        else if i < 6 * w then assert (Seq.index vpb (4 * w + (i - 4 * w)) == Seq.index bp.salt (i - 4 * w))
        else assert (Seq.index vpb (6 * w + (i - 6 * w)) == Seq.index bp.personal (i - 6 * w))
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro vpb (param_block bp kk);
    Seq.lemma_eq_elim vpb (param_block bp kk)

(** The default block is all head: the salt and the personalization are
    zero, and so is [head_byte] past the first half. *)
let default_block_intro (#t: Type0) {| word t |}
                        (nn: nat { 0 < nn /\ nn <= 8 * bytes #t })
                        (kk: nat { kk <= max_key_len #t }) (vpb: Seq.seq S8.t)
  : Lemma (requires Seq.length vpb == 8 * bytes #t /\
                    (forall (i: nat). i < 8 * bytes #t ==>
                       Seq.index vpb i ==
                         S8.classify (U8.uint_to_t (head_byte #t nn kk 1 1 0 0 0 0 i))))
          (ensures vpb == param_block (default_params #t nn) kk)
  = let w = bytes #t in
    let bp = default_params #t nn in
    let aux (i: nat { i < salt_len #t })
      : Lemma (Seq.index vpb (4 * w + i) == Seq.index bp.salt i /\
               Seq.index vpb (6 * w + i) == Seq.index bp.personal i)
      = assert (Seq.index vpb (4 * w + i) == S8.classify (U8.uint_to_t 0));
        assert (Seq.index vpb (6 * w + i) == S8.classify (U8.uint_to_t 0));
        assert_norm (U8.uint_to_t 0 == 0uy)
    in
    Classical.forall_intro aux;
    param_block_intro bp kk vpb

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"

(** [pb[i] <- head_byte i] for the whole block. *)
fn write_head (#t: Type0) {| w: word t |}
              (pb: A.array S8.t) (nn kk fo dp: U8.t) (leaf: U32.t) (off: U64.t) (nd il: U8.t)
              (#vpb: erased (Seq.seq S8.t))
requires A.pts_to pb vpb ** pure (Seq.length vpb == 8 * bytes #t)
ensures exists* (vpb': Seq.seq S8.t). A.pts_to pb vpb' **
  pure (Seq.length vpb' == 8 * bytes #t /\
        (forall (i: nat). i < 8 * bytes #t ==>
           Seq.index vpb' i ==
             S8.classify (U8.uint_to_t
               (head_byte #t (U8.v nn) (U8.v kk) (U8.v fo) (U8.v dp)
                             (U32.v leaf) (U64.v off) (U8.v nd) (U8.v il) i))))
{
  A.pts_to_len pb;
  let n = SZ.mul 8sz (nbytes #t #w);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vp: Seq.seq S8.t).
    pts_to i vi ** A.pts_to pb vp **
    pure (SZ.v vi <= 8 * bytes #t /\ Seq.length vp == 8 * bytes #t /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vp j ==
               S8.classify (U8.uint_to_t
                 (head_byte #t (U8.v nn) (U8.v kk) (U8.v fo) (U8.v dp)
                               (U32.v leaf) (U64.v off) (U8.v nd) (U8.v il) j))))
  decreases (8 * bytes #t - SZ.v (!i))
  {
    let vi = !i;
    let b = head_byte_impl #t nn kk fo dp leaf off nd il vi;
    U8.uv_inv b;
    A.((pb.(vi) <- S8.classify b));
    i := SZ.add vi 1sz;
  };
}

(** [h[i] <- iv[i] ^ load_le pb (i * bytes)]: [Spec.Blake2.init_with] from
    the block. *)
fn init_from_block (#t: Type0) {| w: word t |}
                   (h: A.array t) (ivs: A.array t) (pb: A.array S8.t)
                   (#vh0: erased (Seq.seq t))
                   (#pi: perm) (#vi: erased (Seq.lseq t 8))
                   (#ppb: perm) (#vpb: erased (Seq.lseq S8.t (8 * bytes #t)))
requires A.pts_to h vh0 ** A.pts_to ivs #pi vi ** A.pts_to pb #ppb vpb **
         pure (Seq.length vh0 == 8)
ensures exists* (vh: Seq.seq t). A.pts_to h vh ** A.pts_to ivs #pi vi ** A.pts_to pb #ppb vpb **
  pure (Seq.length vh == 8 /\ vh == xor_words (reveal vi) (words_from_le 8 (reveal vpb)))
{
  A.pts_to_len h;
  A.pts_to_len ivs;
  A.pts_to_len pb;
  let nb = nbytes #t #w;
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 8sz)
  invariant exists* (vi2: SZ.t) (vh: Seq.seq t).
    pts_to i vi2 ** A.pts_to h vh ** A.pts_to ivs #pi vi ** A.pts_to pb #ppb vpb **
    pure (SZ.v vi2 <= 8 /\ Seq.length vh == 8 /\
          (forall (j: nat). j < SZ.v vi2 ==>
             Seq.index vh j == Seq.index (xor_words (reveal vi) (words_from_le 8 (reveal vpb))) j))
  decreases (8 - SZ.v (!i))
  {
    let vi2 = !i;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vi2 + 1) 8;
    let x = A.(ivs.(vi2));
    let y = load_le #t pb (SZ.mul vi2 nb);
    w.v_extensional y (Seq.index (words_from_le 8 (reveal vpb)) (SZ.v vi2));
    A.((h.(vi2) <- logxor #t x y));
    i := SZ.add vi2 1sz;
  };
  with vh. assert (A.pts_to h vh);
  Seq.lemma_eq_intro vh (xor_words (reveal vi) (words_from_le 8 (reveal vpb)));
  Seq.lemma_eq_elim vh (xor_words (reveal vi) (words_from_le 8 (reveal vpb)));
}

(** {2 The initial state} *)
fn init_state (#t: Type0) {| w: word t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (h: A.array t) (ivs: A.array t) (klen: SZ.t)
              (#vh0: erased (Seq.seq t))
              (#pi: perm) (#vi: erased (Seq.seq t))
requires A.pts_to h vh0 ** A.pts_to ivs #pi vi **
         pure (Seq.length vh0 == 8 /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\ SZ.v klen <= max_key_len #t)
ensures exists* (vh: Seq.seq t). A.pts_to h vh ** A.pts_to ivs #pi vi **
  pure (SZ.v klen <= max_key_len #t /\ Seq.length vh == 8 /\ vh == init p (SZ.v klen))
{
  let z8 = S8.classify 0uy;
  let n = SZ.mul 8sz (nbytes #t #w);
  let mut pb = [| z8; n |];
  Mem.track pb;
  A.pts_to_len pb;
  A.pts_to_len pb;
  write_head #t pb (sz_to_u8 p.nhash_bytes) (sz_to_u8 klen) 1uy 1uy 0ul 0uL 0uy 0uy;
  with vpb. assert (A.pts_to pb vpb);
  default_block_intro #t (hash_bytes p) (SZ.v klen) vpb;
  init_from_block #t h ivs pb;
  Mem.wipe pb n;
}

(** The initial state under the parameter block [bp], whose fields arrive
    as machine integers and two arrays. *)
fn init_state_params (#t: Type0) {| w: word t |}
                     ([@@@FStar.Attributes.monomorphize] p: params t)
                     (h: A.array t) (ivs: A.array t) (nn: SZ.t) (klen: SZ.t)
                     (fanout depth: U8.t) (leaf: U32.t) (off: U64.t) (nd il: U8.t)
                     (salt: A.array S8.t) (personal: A.array S8.t)
                     (bp: erased (blake2_params t))
                     (#vh0: erased (Seq.seq t))
                     (#pi: perm) (#vi: erased (Seq.seq t))
                     (#ps: perm) (#vs: erased (Seq.seq S8.t))
                     (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to h vh0 ** A.pts_to ivs #pi vi **
         A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
         pure (Seq.length vh0 == 8 /\ Seq.length vi == 8 /\
               reveal vi == G.reveal p.iv /\ SZ.v klen <= max_key_len #t /\
               params_match bp nn fanout depth leaf off nd il vs vp)
ensures exists* (vh: Seq.seq t). A.pts_to h vh ** A.pts_to ivs #pi vi **
  A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
  pure (SZ.v klen <= max_key_len #t /\ Seq.length vh == 8 /\
        vh == init_with p bp (SZ.v klen))
{
  let z8 = S8.classify 0uy;
  let nb = nbytes #t #w;
  let n = SZ.mul 8sz nb;
  let sl = SZ.mul 2sz nb;
  let mut pb = [| z8; n |];
  Mem.track pb;
  A.pts_to_len pb;
  A.pts_to_len pb;
  A.pts_to_len salt;
  A.pts_to_len personal;
  write_head #t pb (sz_to_u8 nn) (sz_to_u8 klen) fanout depth leaf off nd il;
  copy_at pb (SZ.mul 4sz nb) salt sl;
  copy_at pb (SZ.mul 6sz nb) personal sl;
  with vpb. assert (A.pts_to pb vpb);
  param_block_intro #t bp (SZ.v klen) vpb;
  init_from_block #t h ivs pb;
  Mem.wipe pb n;
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"

(** {2 The digest}

    [Spec.Blake2.final_n]: the state serialized little-endian and truncated to
    the requested length.  The truncation is why the whole eight words are
    written to a scratch buffer first. *)
fn write_digest_n (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                  (nn: SZ.t { SZ.v nn <= 8 * bytes #t }) (out: A.array S8.t) (st: A.array t)
                  (#vout: erased (Seq.seq S8.t)) (#pst: perm) (#vst: erased (Seq.lseq t 8))
requires A.pts_to out vout ** A.pts_to st #pst vst **
         pure (Seq.length vout == SZ.v nn /\ SZ.v nn <= 8 * bytes #t)
ensures A.pts_to out (final_n (SZ.v nn) vst) ** A.pts_to st #pst vst
{
  A.pts_to_len out;
  A.pts_to_len st;
  let nb = nbytes #t #w;
  let z8 = S8.classify 0uy;
  let dlen = SZ.mul 8sz nb;
  let mut darr = [| z8; dlen |];
  Mem.track darr;
  A.pts_to_len darr;
  A.pts_to_len darr;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 8sz)
  invariant exists* (vj: SZ.t) (vd: Seq.seq S8.t).
    pts_to j vj ** A.pts_to darr vd ** A.pts_to st #pst vst **
    pure (SZ.v vj <= 8 /\ Seq.length vd == 8 * bytes #t /\
          (forall (i: nat). i < SZ.v vj * bytes #t ==>
             Seq.index vd i == Seq.index (words_to_le 8 vst) i))
  decreases (8 - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vj + 1) 8;
    Math.distributivity_add_left (SZ.v vj) 1 (bytes #t);
    let x = A.(st.(vj));
    store_le #t darr (SZ.mul vj nb) x;
    with vd. assert (A.pts_to darr vd);
    digest_step_le #t 8 vst (SZ.v vj) (SZ.v (SZ.mul vj nb)) vd;
    j := SZ.add vj 1sz;
  };
  with vd. assert (A.pts_to darr vd);
  Seq.lemma_eq_intro vd (words_to_le 8 vst);
  Seq.lemma_eq_elim vd (words_to_le 8 vst);

  let hb = nn;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi hb)
  invariant exists* (vi: SZ.t) (vo: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out vo ** A.pts_to darr vd ** A.pts_to st #pst vst **
    pure (SZ.v vi <= SZ.v nn /\ Seq.length vo == SZ.v nn /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vo k == Seq.index vd k))
  decreases (SZ.v nn - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(darr.(vi));
    A.((out.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vo. assert (A.pts_to out vo);
  Seq.lemma_eq_intro vo (final_n (SZ.v nn) vst);
  Seq.lemma_eq_elim vo (final_n (SZ.v nn) vst);
  Mem.wipe darr dlen;
  ()
}

fn write_digest_le (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                   ([@@@FStar.Attributes.monomorphize] p: params t)
                   (out: A.array S8.t) (st: A.array t)
                   (#vout: erased (Seq.seq S8.t)) (#pst: perm) (#vst: erased (Seq.lseq t 8))
requires A.pts_to out vout ** A.pts_to st #pst vst **
         pure (Seq.length vout == (hash_bytes p))
ensures A.pts_to out (final p vst) ** A.pts_to st #pst vst
{
  write_digest_n #t p.nhash_bytes out st;
}

(** Block [i] of the padded stream: the key block for [i < koff], a message
    block after that.  The branch lives in its own function so that both arms
    are checked against one written-down postcondition; Pulse will not invent
    the join itself. *)
fn read_block_of (#t: Type0) {| w: word t |}
                 (blk: A.array S8.t) (key: A.array S8.t) (klen: SZ.t) (msg: A.array S8.t) (mlen: SZ.t)
                 (usekey: bool) (off: SZ.t)
                 (#vblk0: erased (Seq.seq S8.t))
                 (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to blk vblk0 ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vblk0 == block_len #t)
         ** pure (SZ.v klen == Seq.length vkey)
         ** pure (SZ.v mlen == Seq.length vmsg)
ensures exists* (vb: Seq.seq S8.t).
  A.pts_to blk vb ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vb == block_len #t /\
        vb == (if usekey then pad_block #t (reveal vkey) 0
               else pad_block #t (reveal vmsg) (SZ.v off)))
{
  if usekey {
    read_block #t blk key klen 0sz;
  } else {
    read_block #t blk msg mlen off;
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

#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"

(** {2 Every block but the last}

    The counter passed with block [i] is [(i + 1) * block_len]: the number of
    bytes absorbed including this block. *)
fn blake2_blocks (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                 ([@@@FStar.Attributes.monomorphize] p: params t)
                 (h: A.array t) (mw: A.array t) (blk: A.array S8.t)
                 (ivs: A.array t)
                 (key: A.array S8.t) (klen: SZ.t) (msg: A.array S8.t) (mlen: SZ.t)
                 (koffsz: SZ.t) (nlast: SZ.t) (h0: erased (Seq.lseq t 8))
                 (#vh0: erased (Seq.seq t)) (#vm0: erased (Seq.seq t))
                 (#vblk0: erased (Seq.seq S8.t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires
  A.pts_to h vh0 ** A.pts_to mw vm0 ** A.pts_to blk vblk0 **
  A.pts_to ivs #pi vi **
  A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vh0 == 8 /\ Seq.length vm0 == 16 /\
        Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
        reveal vi == G.reveal p.iv /\
        Seq.length vkey <= max_key_len #t /\
        SZ.v koffsz == koff #t (reveal vkey) /\
        SZ.v nlast + 1 == nblocks #t (reveal vkey) (reveal vmsg) /\
        Seq.length vmsg + 2 * block_len #t < pow2 64 /\
        SZ.fits (Seq.length vmsg + 2 * block_len #t) /\
        reveal vh0 == reveal h0)
         ** pure (SZ.v klen == Seq.length vkey)
         ** pure (SZ.v mlen == Seq.length vmsg)
ensures exists* (vh: Seq.seq t) (vm1: Seq.seq t) (vb1: Seq.seq S8.t).
  A.pts_to h vh ** A.pts_to mw vm1 ** A.pts_to blk vb1 **
  A.pts_to ivs #pi vi **
  A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= max_key_len #t /\ Seq.length vh == 8 /\
        Seq.length vm1 == 16 /\
        Seq.length vb1 == block_len #t /\
        vh == repeati_g (SZ.v nlast)
                (compress_at p (data #t (reveal vkey) (reveal vmsg)))
                (reveal h0))
{
  A.pts_to_len h;
  A.pts_to_len msg;
  A.pts_to_len key;
  nblocks_exact #t (reveal vkey) (reveal vmsg);
  data_len_bound #t (reveal vkey) (reveal vmsg);
  let bl = block_len_sz #t #w;
  let mut i = 0sz;
  let mut off = 0sz;
  let mut ctr = bl;

  while (let vi2 = !i; SZ.lt vi2 nlast)
  invariant exists* (vi2: SZ.t) (voff: SZ.t) (vctr: SZ.t)
                    (vh: Seq.seq t) (vm1: Seq.seq t) (vb1: Seq.seq S8.t).
    pts_to i vi2 ** pts_to off voff ** pts_to ctr vctr **
    A.pts_to h vh ** A.pts_to mw vm1 ** A.pts_to blk vb1 **
    A.pts_to ivs #pi vi **
    A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
    pure (Seq.length vkey <= max_key_len #t /\
          SZ.v vi2 <= SZ.v nlast /\ Seq.length vh == 8 /\
          Seq.length vm1 == 16 /\
          Seq.length vb1 == block_len #t /\ Seq.length vi == 8 /\
          reveal vi == G.reveal p.iv /\
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
                  (reveal h0))
  decreases (SZ.v nlast - SZ.v (!i))
  {
    let vi2 = !i;
    let voff = !off;
    let vctr = !ctr;
    let usekey = SZ.lt vi2 koffsz;

    block_at_data #t (reveal vkey) (reveal vmsg) (SZ.v vi2);
    nblocks_bound #t (reveal vkey) (reveal vmsg) (SZ.v vi2);
    unfold_repeati_g (SZ.v vi2) (compress_at p (data #t (reveal vkey) (reveal vmsg)))
                     (reveal h0);
    msg_blocks_bound #t (reveal vkey) (reveal vmsg) (SZ.v vi2 + 1 - SZ.v koffsz);
    Math.distributivity_add_left (SZ.v vi2) 1 (block_len #t);
    Math.distributivity_add_left (SZ.v vi2 + 1) 1 (block_len #t);
    Math.distributivity_add_left (SZ.v vi2 - SZ.v koffsz) 1 (block_len #t);
    Math.lemma_mult_le_right (block_len #t) (SZ.v vi2 + 2) (SZ.v nlast + 1);

    read_block_of #t blk key klen msg mlen usekey voff;
    load_block #t mw blk;
    compress_impl p h mw ivs vctr false;

    off := SZ.add voff (step_of usekey bl);
    ctr := SZ.add vctr bl;
    i := SZ.add vi2 1sz;
  }
}

#pop-options

let koff_sz (klen: SZ.t) : (n: SZ.t { SZ.v n == (if SZ.v klen = 0 then 0 else 1) }) =
  if SZ.eq klen 0sz then 0sz else 1sz

(** Where in the message the last block starts.  Zero if the last block is the
    key block, which happens exactly when a keyed hash is taken of the empty
    message. *)
let final_off (nlast koffsz bl: SZ.t)
  : Pure SZ.t
      (requires SZ.v koffsz <= SZ.v nlast ==>
                SZ.fits ((SZ.v nlast - SZ.v koffsz) * SZ.v bl))
      (ensures fun o -> SZ.v o == (if SZ.v nlast < SZ.v koffsz then 0
                                   else (SZ.v nlast - SZ.v koffsz) * SZ.v bl))
  = if SZ.lt nlast koffsz then 0sz else SZ.mul (SZ.sub nlast koffsz) bl

(** [Spec.Blake2.last_counter]. *)
let last_ctr (klen mlen bl: SZ.t)
  : Pure SZ.t (requires SZ.fits (SZ.v mlen + SZ.v bl))
              (ensures fun c -> SZ.v c == (if SZ.v klen = 0
                                           then SZ.v mlen else SZ.v mlen + SZ.v bl))
  = if SZ.eq klen 0sz then mlen else SZ.add mlen bl

(** [msg_blocks_bound], guarded: the last block need not be a message block,
    and if it is not then [nlast - koff] is not a natural number. *)
let msg_blocks_bound_opt (#t: Type0) {| word t |} (key msg: Seq.seq S8.t) (nlast koffs: nat)
  : Lemma (requires Seq.length key <= max_key_len #t /\
                    nlast + 1 == nblocks #t key msg /\ koffs == koff #t key)
          (ensures koffs <= nlast ==> (nlast - koffs) * block_len #t <= Seq.length msg)
  = if koffs <= nlast then msg_blocks_bound #t key msg (nlast - koffs)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"

(** {2 The hash}

    [blake2_run] is everything after initialization: [h] holds some initial
    state [h0], and what is written is [Spec.Blake2.blake2_from] at it.  The
    two entry points below differ only in how they fill [h]. *)
fn blake2_run (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (h: A.array t) (ivs: A.array t)
              (out: A.array S8.t) (nn: SZ.t)
              (key: A.array S8.t) (klen: SZ.t) (msg: A.array S8.t) (mlen: SZ.t)
              (h0: erased (Seq.lseq t 8))
              (#vh0: erased (Seq.seq t))
              (#pi: perm) (#vi: erased (Seq.seq t))
              (#vout: erased (Seq.seq S8.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
              (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to h vh0 ** A.pts_to ivs #pi vi ** A.pts_to out vout **
         A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vh0 == 8 /\ reveal vh0 == reveal h0 /\
               Seq.length vi == 8 /\ reveal vi == G.reveal p.iv /\
               Seq.length vout == SZ.v nn /\ SZ.v nn <= 8 * bytes #t /\
               Seq.length vkey <= max_key_len #t /\
               Seq.length vmsg + 2 * block_len #t < pow2 64 /\
               SZ.fits (Seq.length vmsg + 2 * block_len #t))
         ** pure (SZ.v klen == Seq.length vkey)
         ** pure (SZ.v mlen == Seq.length vmsg)
ensures exists* (vh: Seq.seq t) (vout': Seq.seq S8.t).
  A.pts_to h vh ** A.pts_to ivs #pi vi ** A.pts_to out vout' **
  A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vh == 8 /\ SZ.v nn <= 8 * bytes #t /\
        vout' == blake2_from p h0 (SZ.v nn) (reveal vkey) (reveal vmsg))
{
  A.pts_to_len h;
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;

  let bl = block_len_sz #t #w;
  let z0: t = zero #t #w;
  let z8 = S8.classify 0uy;

  let mut marr = [| z0; 16sz |];
  Mem.track marr;
  A.pts_to_len marr;
  let mut barr = [| z8; bl |];
  Mem.track barr;
  A.pts_to_len barr;
  A.pts_to_len marr;
  A.pts_to_len barr;

  nblocks_eq #t (reveal vkey) (reveal vmsg);
  nblocks_pos #t (reveal vkey) (reveal vmsg);
  nblocks_exact #t (reveal vkey) (reveal vmsg);
  data_len_bound #t (reveal vkey) (reveal vmsg);

  let koffsz = koff_sz klen;
  let nb = nblocks_sz klen mlen bl;
  let nlast = SZ.sub nb 1sz;

  blake2_blocks p h marr barr ivs key klen msg mlen koffsz nlast h0;

  msg_blocks_bound_opt #t (reveal vkey) (reveal vmsg) (SZ.v nlast) (SZ.v koffsz);
  block_at_data #t (reveal vkey) (reveal vmsg) (SZ.v nlast);

  let foff = final_off nlast koffsz bl;
  let usekey = SZ.lt nlast koffsz;
  read_block_of #t barr key klen msg mlen usekey foff;
  load_block #t marr barr;

  let lastc = last_ctr klen mlen bl;
  compress_impl p h marr ivs lastc true;
  write_digest_n #t nn out h;
  Mem.wipe barr bl;
  Mem.wipe marr 16sz;
}

fn blake2_impl (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               ([@@@FStar.Attributes.monomorphize] iva: GA.static_array t)
               (out: A.array S8.t)
               (key: A.array S8.t) (klen: SZ.t) (msg: A.array S8.t) (mlen: SZ.t)
               (#vout: erased (Seq.seq S8.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
               (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout **
         A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length (GA.static_array_elems iva) == 8 /\
               GA.static_array_elems iva == G.reveal p.iv /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vkey <= max_key_len #t /\
               Seq.length vmsg + 2 * block_len #t < pow2 64 /\
               SZ.fits (Seq.length vmsg + 2 * block_len #t))
         ** pure (SZ.v klen == Seq.length vkey)
         ** pure (SZ.v mlen == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' **
  A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= max_key_len #t /\ vout' == blake2 p (reveal vkey) (reveal vmsg))
{
  let ivs = table iva 8sz;
  A.pts_to_len ivs;
  A.pts_to_len key;
  let z0: t = zero #t #w;
  let mut harr = [| z0; 8sz |];
  Mem.track harr;
  A.pts_to_len harr;
  A.pts_to_len harr;

  init_state p harr ivs klen;
  blake2_run p harr ivs out p.nhash_bytes key klen msg mlen
             (G.hide (init p (SZ.v klen)));
  drop_table ivs;
  Mem.wipe harr 8sz;
}

fn blake2_params_impl (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                      ([@@@FStar.Attributes.monomorphize] p: params t)
                      ([@@@FStar.Attributes.monomorphize] iva: GA.static_array t)
                      (out: A.array S8.t) (nn: SZ.t)
                      (key: A.array S8.t) (klen: SZ.t) (msg: A.array S8.t) (mlen: SZ.t)
                      (salt: A.array S8.t) (personal: A.array S8.t)
                      (fanout depth: U8.t) (leaf: U32.t) (off: U64.t) (nd il: U8.t)
                      (bp: erased (blake2_params t))
                      (#vout: erased (Seq.seq S8.t))
                      (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                      (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
                      (#ps: perm) (#vs: erased (Seq.seq S8.t))
                      (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vout **
         A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
         pure (Seq.length (GA.static_array_elems iva) == 8 /\
               GA.static_array_elems iva == G.reveal p.iv /\
               params_match bp nn fanout depth leaf off nd il vs vp /\
               Seq.length vout == SZ.v nn /\
               Seq.length vkey <= max_key_len #t /\
               Seq.length vmsg + 2 * block_len #t < pow2 64 /\
               SZ.fits (Seq.length vmsg + 2 * block_len #t))
         ** pure (SZ.v klen == Seq.length vkey)
         ** pure (SZ.v mlen == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' **
  A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
  pure (Seq.length vkey <= max_key_len #t /\
        vout' == blake2_with_params p bp (reveal vkey) (reveal vmsg))
{
  let ivs = table iva 8sz;
  A.pts_to_len ivs;
  A.pts_to_len key;
  let z0: t = zero #t #w;
  let mut harr = [| z0; 8sz |];
  Mem.track harr;
  A.pts_to_len harr;
  A.pts_to_len harr;

  init_state_params p harr ivs nn klen fanout depth leaf off nd il salt personal bp;
  blake2_run p harr ivs out nn key klen msg mlen
             (G.hide (init_with p bp (SZ.v klen)));
  drop_table ivs;
  Mem.wipe harr 8sz;
}

#pop-options
