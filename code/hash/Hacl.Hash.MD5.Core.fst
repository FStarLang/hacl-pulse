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

(** The MD5 compression function and driver.

    Shaped like [Hacl.Hash.SHA1.Core], with three differences that come from
    the algorithm rather than from taste.  The block is read with [load_le]
    into sixteen words that are used as they are -- there is no schedule to
    expand -- and each round picks one of them through [Spec.MD5.g].  The
    rotation comes out of a table whose element type carries its own bound, so
    [rotate_left] needs no separate argument that the shift is in range.  And
    the bit length in the padding is written little-endian, which is the one
    place the SHA-2 padding code could not be reused. *)
module Hacl.Hash.MD5.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Hacl.Impl.Table
open Spec.MD5
open Spec.MD5.Lemmas
open Hacl.Hash.MD5.Tables
open Hacl.Spec.Loops

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module L2 = Spec.SHA2.Lemmas

(** {2 Sizes as machine values} *)

let rounds_sz : n: SZ.t { SZ.v n == rounds } = 64sz
let block_len_sz : n: SZ.t { SZ.v n == block_len } = 64sz

let len_fits (n: nat) : Lemma (requires n < pow2 61) (ensures 8 * n < pow2 64)
  = Math.pow2_plus 61 3;
    assert_norm (pow2 3 == 8)

let small_fits (n: nat) : Lemma (requires n <= 512) (ensures SZ.fits n)
  = assert_norm (512 < pow2 16)

(** How much of the two-block scratch buffer the padding occupies. *)
inline_for_extraction
let tail_len (rem: (r: SZ.t { SZ.v r < block_len }))
  : n: SZ.t { 8 <= SZ.v n /\ SZ.v n <= 2 * block_len /\
              SZ.v n == (if SZ.v rem + 1 + len_len <= block_len
                         then block_len else 2 * block_len) } =
  if SZ.lte (SZ.add rem 9sz) 64sz then 64sz else 128sz

(** {2 The round function, on a run-time round number}

    Each branch tests the same boundary as [Spec.MD5._f] and [Spec.MD5.g], so
    the postconditions close by unfolding. *)

fn f_impl (i: SZ.t) (b c d: S32.t)
requires emp
returns r: S32.t
ensures pure (SZ.v i < rounds ==> r == _f (SZ.v i) b c d)
{
  if SZ.lt i 16sz {
    _Ch b c d
  } else if SZ.lt i 32sz {
    _Ch d b c
  } else if SZ.lt i 48sz {
    _Par b c d
  } else {
    _I b c d
  }
}

fn g_impl (i: (j: SZ.t { SZ.v j < rounds }))
requires emp
returns r: SZ.t
ensures pure (SZ.v r == g (SZ.v i) /\ SZ.v r < block_words)
{
  if SZ.lt i 16sz {
    i
  } else if SZ.lt i 32sz {
    SZ.rem (SZ.add (SZ.mul 5sz i) 1sz) 16sz
  } else if SZ.lt i 48sz {
    SZ.rem (SZ.add (SZ.mul 3sz i) 5sz) 16sz
  } else {
    SZ.rem (SZ.mul 7sz i) 16sz
  }
}

(** {2 The block, as sixteen little-endian words} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn block_load (wb: A.array S32.t) (block: A.array S8.t) (off: SZ.t)
              (#vw0: erased (Seq.seq S32.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to wb vw0 ** A.pts_to block #pb vb **
         pure (Seq.length vw0 == block_words /\ SZ.v off + block_len <= Seq.length vb)
ensures A.pts_to wb (words_from_le #S32.t block_words (block_at vb (SZ.v off))) **
        A.pts_to block #pb vb
{
  A.pts_to_len wb;
  A.pts_to_len block;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vw: Seq.seq S32.t).
    pts_to i vi ** A.pts_to wb vw ** A.pts_to block #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length vw == block_words /\
          SZ.v off + block_len <= Seq.length vb /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vw j ==
               Seq.index (words_from_le #S32.t block_words (block_at vb (SZ.v off))) j))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right 4 (SZ.v vi + 1) 16;
    Seq.slice_slice vb (SZ.v off) (SZ.v off + block_len)
                    (SZ.v vi * 4) (SZ.v vi * 4 + 4);
    let x = load_le #S32.t block (SZ.add off (SZ.mul vi 4sz));
    S32.v_extensional x
      (Seq.index (words_from_le #S32.t block_words (block_at vb (SZ.v off))) (SZ.v vi));
    A.((wb.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vw. assert (A.pts_to wb vw);
  Seq.lemma_eq_intro vw (words_from_le #S32.t block_words (block_at vb (SZ.v off)));
  Seq.lemma_eq_elim vw (words_from_le #S32.t block_words (block_at vb (SZ.v off)));
}

(** {2 One block} *)

inline_for_extraction
fn update_block_impl (kt: A.array S32.t) (st: A.array rot)
                     (wb: A.array S32.t) (state: A.array S32.t)
                     (block: A.array S8.t) (off: SZ.t)
                     (#pk: perm) (#vk: erased (Seq.seq S32.t))
                     (#ps: perm) (#vs: erased (Seq.seq rot))
                     (#vw0: erased (Seq.seq S32.t))
                     (#vst0: erased (Seq.lseq S32.t state_words))
                     (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to st #ps vs ** A.pts_to wb vw0 **
         A.pts_to state vst0 ** A.pts_to block #pb vb **
         pure (reveal vk == (k_table <: Seq.seq S32.t) /\
               reveal vs == (s_table <: Seq.seq rot) /\
               Seq.length vw0 == block_words /\
               SZ.v off + block_len <= Seq.length vb)
ensures exists* vw.
  A.pts_to kt #pk vk ** A.pts_to st #ps vs ** A.pts_to wb vw **
  A.pts_to state (update_block (block_at vb (SZ.v off)) vst0) **
  A.pts_to block #pb vb ** pure (Seq.length vw == block_words)
{
  A.pts_to_len kt;
  A.pts_to_len st;
  A.pts_to_len state;
  block_load wb block off;
  let a0 = A.(state.(0sz));
  let b0 = A.(state.(1sz));
  let c0 = A.(state.(2sz));
  let d0 = A.(state.(3sz));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi rounds_sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S32.t).
    pts_to i vi ** A.pts_to kt #pk vk ** A.pts_to st #ps vs **
    A.pts_to wb (words_from_le #S32.t block_words (block_at vb (SZ.v off))) **
    A.pts_to state vst ** A.pts_to block #pb vb **
    pure (SZ.v vi <= rounds /\ Seq.length vst == state_words /\
          vst == repeati_g (SZ.v vi)
                   (shuffle_core
                      (words_from_le #S32.t block_words (block_at vb (SZ.v off))))
                   vst0)
  decreases (rounds - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(state.(0sz));
    let b = A.(state.(1sz));
    let c = A.(state.(2sz));
    let d = A.(state.(3sz));
    let fi = f_impl vi b c d;
    let gi = g_impl vi;
    let ki = A.(kt.(vi));
    let sh = A.(st.(vi));
    let wi = A.(wb.(gi));
    let t = S32.add_mod (S32.add_mod (S32.add_mod a fi) ki) wi;
    A.((state.(0sz) <- d));
    A.((state.(1sz) <- S32.add_mod b (S32.rotate_left t sh)));
    A.((state.(2sz) <- b));
    A.((state.(3sz) <- c));
    i := SZ.add vi 1sz;
  };
  let a1 = A.(state.(0sz));
  let b1 = A.(state.(1sz));
  let c1 = A.(state.(2sz));
  let d1 = A.(state.(3sz));
  with vsh. assert (A.pts_to state vsh);
  set4_irrelevant vsh vst0
    (S32.add_mod a0 a1) (S32.add_mod b0 b1) (S32.add_mod c0 c1) (S32.add_mod d0 d1);
  A.((state.(0sz) <- S32.add_mod a0 a1));
  A.((state.(1sz) <- S32.add_mod b0 b1));
  A.((state.(2sz) <- S32.add_mod c0 c1));
  A.((state.(3sz) <- S32.add_mod d0 d1));
}

#pop-options

(** {2 The padding}

    The bit length goes in little-endian, so byte [j] sits at [off + j] rather
    than at [off + 7 - j]; that one index is the whole of the difference from
    [Hacl.Hash.SHA2.Core.write_len_be]. *)

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"

fn write_len_le (b: A.array S8.t) (off: SZ.t) (len: SZ.t)
                (#vb: erased (Seq.seq S8.t))
requires A.pts_to b vb ** pure (SZ.v off + 8 <= Seq.length vb /\ 8 * SZ.v len < pow2 64)
ensures exists* vb'. A.pts_to b vb' **
  pure (Seq.length vb' == Seq.length vb /\ SZ.v off + 8 <= Seq.length vb' /\
        (forall (j: nat). j < 8 ==>
           Seq.index vb' (SZ.v off + j) ==
             S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))) /\
        (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + 8 ==>
           Seq.index vb' k == Seq.index vb k))
{
  A.pts_to_len b;
  let bits8 = U64.mul 8uL (SZ.sizet_to_uint64 len);
  let mut d = 0sz;
  let mut sh = 0ul;
  while (let vd = !d; SZ.lt vd 8sz)
  invariant exists* (vd: SZ.t) (vsh: U32.t) (vb': Seq.seq S8.t).
    pts_to d vd ** pts_to sh vsh ** A.pts_to b vb' **
    pure (SZ.v vd <= 8 /\ U32.v vsh == 8 * SZ.v vd /\ Seq.length vb' == Seq.length vb /\
          (forall (j: nat). j < SZ.v vd ==>
             Seq.index vb' (SZ.v off + j) ==
               S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))) /\
          (forall (k: nat). k < Seq.length vb ==>
             k < SZ.v off \/ k >= SZ.v off + SZ.v vd ==>
             Seq.index vb' k == Seq.index vb k))
  decreases (8 - SZ.v (!d))
  {
    let vd = !d;
    let vsh = !sh;
    let c = Cast.uint64_to_uint8 (U64.shift_right bits8 vsh);
    let bs = S8.classify c;
    A.((b.(SZ.add off vd) <- bs));
    Math.distributivity_add_right 8 (SZ.v vd) 1;
    d := SZ.add vd 1sz;
    sh := U32.add vsh 8ul;
  };
}

#pop-options

#push-options "--z3rlimit 200"

(** The two-block scratch buffer: the remainder of the message, the [0x80]
    byte, zeros, and the little-endian bit length. *)
fn build_tail (tl: A.array S8.t) (input: A.array S8.t) (len: SZ.t) (base: SZ.t)
              (rem: (r: SZ.t { SZ.v r < block_len }))
              (ntail: (n: SZ.t { 8 <= SZ.v n /\ SZ.v n <= 2 * block_len }))
              (#vt0: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to tl vt0 ** A.pts_to input #pin vin **
         pure (Seq.length vt0 == 2 * block_len /\
               (forall (k: nat). k < 2 * block_len ==> Seq.index vt0 k == S8.classify 0uy) /\
               Seq.length vin == SZ.v base + SZ.v rem /\ 8 * SZ.v len < pow2 64 /\
               SZ.v rem + 1 + len_len <= SZ.v ntail)
ensures exists* vt.
  A.pts_to tl vt ** A.pts_to input #pin vin **
  pure (Seq.length vt == 2 * block_len /\ SZ.v base + SZ.v rem == Seq.length vin /\
        (forall (k: nat). k < SZ.v rem ==> Seq.index vt k == Seq.index vin (SZ.v base + k)) /\
        Seq.index vt (SZ.v rem) == S8.classify 0x80uy /\
        (forall (k: nat). SZ.v rem < k /\ k < SZ.v ntail - 8 ==> Seq.index vt k == S8.classify 0uy) /\
        (forall (j: nat). j < 8 ==>
           Seq.index vt (SZ.v ntail - 8 + j) ==
             S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))))
{
  A.pts_to_len tl;
  A.pts_to_len input;
  let z8 = S8.classify 0uy;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc rem)
  invariant exists* (vc: SZ.t) (vt: Seq.seq S8.t).
    pts_to c vc ** A.pts_to tl vt ** A.pts_to input #pin vin **
    pure (SZ.v vc <= SZ.v rem /\ Seq.length vt == 2 * block_len /\
          (forall (k: nat). k < SZ.v vc ==> Seq.index vt k == Seq.index vin (SZ.v base + k)) /\
          (forall (k: nat). SZ.v vc <= k /\ k < 2 * block_len ==> Seq.index vt k == z8))
  decreases (SZ.v rem - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(input.(SZ.add base vc));
    A.((tl.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  let x80 = S8.classify 0x80uy;
  A.((tl.(rem) <- x80));
  write_len_le tl (SZ.sub ntail 8sz) len;
}

#pop-options

(** {2 The digest}

    Four words, sixteen bytes, little-endian. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn write_digest (out: A.array S8.t) (state: A.array S32.t)
                (#vout: erased (Seq.seq S8.t)) (#pst: perm)
                (#vst: erased (Seq.lseq S32.t state_words))
requires A.pts_to out vout ** A.pts_to state #pst vst **
         pure (Seq.length vout == hash_bytes)
ensures A.pts_to out (finish vst) ** A.pts_to state #pst vst
{
  A.pts_to_len out;
  A.pts_to_len state;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 4sz)
  invariant exists* (vj: SZ.t) (vo: Seq.seq S8.t).
    pts_to j vj ** A.pts_to out vo ** A.pts_to state #pst vst **
    pure (SZ.v vj <= 4 /\ Seq.length vo == hash_bytes /\
          (forall (i: nat). i < SZ.v vj * 4 ==>
             Seq.index vo i == Seq.index (words_to_le #S32.t state_words vst) i))
  decreases (4 - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right 4 (SZ.v vj + 1) 4;
    Math.distributivity_add_left (SZ.v vj) 1 4;
    let x = A.(state.(vj));
    store_le #S32.t out (SZ.mul vj 4sz) x;
    with vo. assert (A.pts_to out vo);
    digest_step_le #S32.t state_words vst (SZ.v vj) (SZ.v (SZ.mul vj 4sz)) vo;
    j := SZ.add vj 1sz;
  };
  with vo. assert (A.pts_to out vo);
  Seq.lemma_eq_intro vo (finish vst);
  Seq.lemma_eq_elim vo (finish vst);
  ()
}

#pop-options

(** {2 One block, with the tables acquired locally}

    [table] compiles to taking the address of a [static const] array, so the
    two acquisitions here cost nothing at run time and let the three driver
    functions below carry exactly the footprint SHA-1's carry.

    This is the function the three drivers call, and it is the one that is
    compiled: [update_block_impl] above is [inline_for_extraction] and lands
    here, so the sixty-four rounds exist once and the two tables are read from
    the program image inside the same function that uses them.  The other way
    round -- a compiled [update_block_impl] taking two pointers, inlined
    acquisitions at each of the three call sites -- leaves the table addresses
    to be recovered by interprocedural constant propagation, which is a budget
    gcc can run out of. *)
fn update_block_tbl (wb: A.array S32.t) (state: A.array S32.t)
                    (block: A.array S8.t) (off: SZ.t)
                    (#vw0: erased (Seq.seq S32.t))
                    (#vst0: erased (Seq.lseq S32.t state_words))
                    (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to wb vw0 ** A.pts_to state vst0 ** A.pts_to block #pb vb **
         pure (Seq.length vw0 == block_words /\ SZ.v off + block_len <= Seq.length vb)
ensures exists* vw.
  A.pts_to wb vw ** A.pts_to state (update_block (block_at vb (SZ.v off)) vst0) **
  A.pts_to block #pb vb ** pure (Seq.length vw == block_words)
{
  let kt = table k_arr rounds_sz;
  let stt = table s_arr rounds_sz;
  update_block_impl kt stt wb state block off;
  drop_table kt;
  drop_table stt;
}

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** The padding blocks and the digest. *)

fn tail_and_finish (wb: A.array S32.t) (st: A.array S32.t)
                   (out: A.array S8.t) (input: A.array S8.t)
                   (len: SZ.t) (nblocks: SZ.t) (base_in: SZ.t)
                   (rem: (r: SZ.t { SZ.v r < block_len }))
                   (pre: erased (Seq.seq S8.t))
                   (#vw0: erased (Seq.seq S32.t))
                   (#vst0: erased (Seq.lseq S32.t state_words))
                   (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to wb vw0 ** A.pts_to st vst0 **
         A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vw0 == block_words /\ Seq.length vout == hash_bytes /\
               Seq.length pre + Seq.length vin == SZ.v len /\
               Seq.length vin == SZ.v base_in + SZ.v rem /\
               SZ.v len < max_input /\
               SZ.v rem == SZ.v len % block_len /\
               SZ.v len - SZ.v rem == SZ.v nblocks * block_len /\
               reveal vst0 == repeati_g (SZ.v nblocks)
                                (update_step (padded (Seq.append pre vin))) iv)
ensures exists* (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words) (vout': Seq.seq S8.t).
  A.pts_to wb vw ** A.pts_to st vst **
  A.pts_to out vout' ** A.pts_to input #pin vin **
  pure (Seq.length vw == block_words /\ Seq.length pre + Seq.length vin < max_input /\
        vout' == hash (Seq.append pre vin))
{
  A.pts_to_len input;
  A.pts_to_len out;
  A.pts_to_len st;
  A.pts_to_len wb;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape (Seq.append pre vin);
  let ntail = tail_len rem;
  let base = SZ.sub len rem;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; 128sz |];
  A.pts_to_len tarr;
  A.pts_to_len tarr;
  len_fits (SZ.v len);
  Math.euclidean_division_definition (SZ.v len) block_len;
  build_tail tarr input len base_in rem ntail;
  with vt. assert (A.pts_to tarr vt);
  pad_zeros_alt (SZ.v len);
  L2.append_index_at (reveal pre) (reveal vin) (SZ.v base) (SZ.v base_in) (SZ.v rem);
  tail_bytes (Seq.append pre vin) vt (SZ.v ntail) (SZ.v base);
  Math.multiple_division_lemma (SZ.v ntail / block_len) block_len;
  Math.multiply_fractions (SZ.v ntail) block_len;
  let ntb = SZ.div ntail 64sz;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj ntb)
  invariant exists* (vj: SZ.t) (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words).
    pts_to j vj ** A.pts_to wb vw ** A.pts_to st vst ** A.pts_to tarr vt **
    pure (SZ.v vj <= SZ.v ntb /\ Seq.length vw == block_words /\
          SZ.v ntb * block_len <= SZ.v ntail /\
          SZ.v base == SZ.v nblocks * block_len /\
          Seq.length (padded (Seq.append pre vin)) == SZ.v base + SZ.v ntail /\
          (forall (o: nat). o + block_len <= SZ.v ntail ==>
             block_at (padded (Seq.append pre vin)) (SZ.v base + o) == block_at vt o) /\
          vst == repeati_g (SZ.v nblocks + SZ.v vj)
                   (update_step (padded (Seq.append pre vin))) iv)
  decreases (SZ.v ntb - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right block_len (SZ.v vj) (SZ.v ntb);
    small_fits (SZ.v vj * block_len);
    Math.lemma_mult_le_right block_len (SZ.v vj + 1) (SZ.v ntb);
    Math.distributivity_add_left (SZ.v vj) 1 block_len;
    Math.distributivity_add_left (SZ.v nblocks) (SZ.v vj) block_len;
    Math.distributivity_add_left (SZ.v nblocks + SZ.v vj) 1 block_len;
    unfold_repeati_g (SZ.v nblocks + SZ.v vj)
      (update_step (padded (Seq.append pre vin))) iv;
    assert (pure (block_at (padded (Seq.append pre vin))
                    ((SZ.v nblocks + SZ.v vj) * block_len) ==
                  block_at vt (SZ.v vj * block_len)));
    assert (pure ((SZ.v nblocks + SZ.v vj + 1) * block_len <=
                  Seq.length (padded (Seq.append pre vin))));
    update_block_tbl wb st tarr (SZ.mul vj 64sz);
    j := SZ.add vj 1sz;
  };
  Math.multiple_modulo_lemma 1 block_len;
  Math.multiple_modulo_lemma 2 block_len;
  Math.euclidean_division_definition (SZ.v ntail) block_len;
  assert (pure (SZ.v ntb * block_len == SZ.v ntail));
  Math.distributivity_add_left (SZ.v nblocks) (SZ.v ntb) block_len;
  Math.multiple_division_lemma (SZ.v nblocks + SZ.v ntb) block_len;
  assert (pure (Seq.length (padded (Seq.append pre vin)) / block_len ==
                SZ.v nblocks + SZ.v ntb));
  assert (pure (update_all (padded (Seq.append pre vin)) iv ==
                repeati_g (SZ.v nblocks + SZ.v ntb)
                  (update_step (padded (Seq.append pre vin))) iv));
  write_digest out st;
  ()
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** The full blocks of the message, in place. *)

fn hash_blocks (wb: A.array S32.t) (st: A.array S32.t) (input: A.array S8.t)
               (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
               (#vw0: erased (Seq.seq S32.t))
               (#vst0: erased (Seq.lseq S32.t state_words))
               (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to wb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (Seq.length vw0 == block_words /\
               Seq.length pre == SZ.v nprev * block_len /\
               Seq.length pre + Seq.length vin < max_input /\
               SZ.v nfull == Seq.length vin / block_len /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step (padded (Seq.append pre vin))) iv)
ensures exists* (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words).
  A.pts_to wb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input /\ Seq.length vw == block_words /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step (padded (Seq.append pre vin))) iv)
{
  A.pts_to_len input;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape (Seq.append pre vin);
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 nfull)
  invariant exists* (vi2: SZ.t) (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words).
    pts_to i vi2 ** A.pts_to wb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
    pure (SZ.v vi2 <= SZ.v nfull /\ Seq.length vw == block_words /\
          vst == repeati_g (SZ.v nprev + SZ.v vi2)
                   (update_step (padded (Seq.append pre vin))) iv)
  decreases (SZ.v nfull - SZ.v (!i))
  {
    let vi2 = !i;
    Math.lemma_mult_le_right block_len (SZ.v vi2 + 1) (SZ.v nfull);
    Math.lemma_mult_le_right block_len (SZ.v nfull) (Seq.length vin / block_len);
    padded_index_block_shift (reveal pre) (reveal vin) (SZ.v vi2 * block_len);
    Math.distributivity_add_left (SZ.v nprev) (SZ.v vi2) block_len;
    Math.distributivity_add_left (SZ.v nprev) (SZ.v vi2 + 1) block_len;
    unfold_repeati_g (SZ.v nprev + SZ.v vi2)
      (update_step (padded (Seq.append pre vin))) iv;
    assert (pure (block_at (padded (Seq.append pre vin))
                    ((SZ.v nprev + SZ.v vi2) * block_len) ==
                  block_at vin (SZ.v vi2 * block_len)));
    assert (pure ((SZ.v nprev + SZ.v vi2 + 1) * block_len <=
                  Seq.length (padded (Seq.append pre vin))));
    update_block_tbl wb st input (SZ.mul vi2 64sz);
    i := SZ.add vi2 1sz;
  };
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** The whole hash of a whole message. *)

fn hash_impl (out: A.array S8.t) (input: A.array S8.t) (len: SZ.t)
             (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vout == hash_bytes /\ Seq.length vin < max_input /\
               SZ.v len == Seq.length vin)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to input #pin vin **
  pure (Seq.length vin < max_input /\ vout' == hash vin)
{
  A.pts_to_len out;
  A.pts_to_len input;
  let nfull = SZ.div len 64sz;
  let rem = SZ.rem len 64sz;
  let z0 = S32.classify 0ul;

  let mut starr = [| z0; 4sz |];
  A.pts_to_len starr;
  A.pts_to_len starr;
  A.((starr.(0sz) <- S32.classify 0x67452301ul));
  A.((starr.(1sz) <- S32.classify 0xefcdab89ul));
  A.((starr.(2sz) <- S32.classify 0x98badcfeul));
  A.((starr.(3sz) <- S32.classify 0x10325476ul));
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (iv <: Seq.seq S32.t);
  Seq.lemma_eq_elim vst_init (iv <: Seq.seq S32.t);

  let mut warr = [| z0; 16sz |];
  A.pts_to_len warr;
  A.pts_to_len warr;

  let empty : erased (Seq.seq S8.t) = hide (Seq.empty #S8.t);
  Seq.lemma_eq_elim (Seq.append (reveal empty) (reveal vin)) (reveal vin);
  Math.euclidean_division_definition (SZ.v len) block_len;
  hash_blocks warr starr input 0sz nfull empty;
  tail_and_finish warr starr out input len nfull (SZ.sub len rem) rem empty;
  ()
}

#pop-options
