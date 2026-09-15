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

(** The SHA-1 compression function.

    The message schedule and the eighty rounds, with the same shape as
    [Hacl.Hash.SHA2.Core]: the schedule is filled in slot order so that the
    loop invariant is "slots below [i] are final", and the working state lives
    in a five-element array rather than five locals so that the round can be a
    loop at all -- a C compiler keeps them in registers regardless.

    Two things are simpler than in SHA-2.  There is no round-constant table:
    [k] is one of four values chosen by quarter, so the implementation
    branches on the round number instead of indexing an array, and no caller
    has to supply one.  And the state is five words instead of eight.

    One thing is harder.  [Spec.SHA1._f] and [Spec.SHA1.k] are defined by
    cases on a [nat], and the implementation has a [size_t]; the two are
    related by making the implementation branch on exactly the same
    boundaries, so each branch's obligation closes by unfolding. *)
module Hacl.Hash.SHA1.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Spec.SHA1
open Hacl.Spec.Loops
open Spec.SHA1.Lemmas
open Spec.SHA2.Lemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U32 = FStar.UInt32
module C2 = Hacl.Hash.SHA2.Core

(** {2 Sizes as machine values} *)

let rounds_sz : n: SZ.t { SZ.v n == rounds } = 80sz
let block_len_sz : n: SZ.t { SZ.v n == block_len } = 64sz

(** {2 The round function, on a run-time round number}

    Each branch tests the same boundary as [Spec.SHA1._f], so the
    postcondition closes by unfolding rather than by a case analysis the
    solver has to invent. *)

fn f_impl (i: SZ.t) (x y z: S32.t)
requires emp
returns r: S32.t
ensures pure (SZ.v i < rounds ==> r == _f (SZ.v i) x y z)
{
  if SZ.lt i 20sz {
    _Ch x y z
  } else if SZ.lt i 40sz {
    _Par x y z
  } else if SZ.lt i 60sz {
    _Maj x y z
  } else {
    _Par x y z
  }
}

fn k_impl (i: SZ.t)
requires emp
returns r: S32.t
ensures pure (SZ.v i < rounds ==> r == k (SZ.v i))
{
  if SZ.lt i 20sz {
    S32.classify 0x5a827999ul
  } else if SZ.lt i 40sz {
    S32.classify 0x6ed9eba1ul
  } else if SZ.lt i 60sz {
    S32.classify 0x8f1bbcdcul
  } else {
    S32.classify 0xca62c1d6ul
  }
}

(** {2 Message schedule} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn ws_expand (wsb: A.array S32.t) (block: A.array S8.t) (off: SZ.t)
             (#vw0: erased (Seq.seq S32.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to block #pb vb **
         pure (Seq.length vw0 == rounds /\ SZ.v off + block_len <= Seq.length vb)
ensures A.pts_to wsb (ws (words_from_be #S32.t block_words (block_at vb (SZ.v off)))) **
        A.pts_to block #pb vb
{
  A.pts_to_len wsb;
  A.pts_to_len block;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vw: Seq.seq S32.t).
    pts_to i vi ** A.pts_to wsb vw ** A.pts_to block #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length vw == rounds /\
          SZ.v off + block_len <= Seq.length vb /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vw j ==
               ws_at (words_from_be #S32.t block_words (block_at vb (SZ.v off))) j))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right 4 (SZ.v vi + 1) 16;
    Seq.slice_slice vb (SZ.v off) (SZ.v off + block_len)
                    (SZ.v vi * 4) (SZ.v vi * 4 + 4);
    let x = load_be #S32.t block (SZ.add off (SZ.mul vi 4sz));
    S32.v_extensional x
      (ws_at (words_from_be #S32.t block_words (block_at vb (SZ.v off))) (SZ.v vi));
    A.((wsb.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  let mut j = 16sz;
  while (let vj = !j; SZ.lt vj rounds_sz)
  invariant exists* (vj: SZ.t) (vw: Seq.seq S32.t).
    pts_to j vj ** A.pts_to wsb vw ** A.pts_to block #pb vb **
    pure (16 <= SZ.v vj /\ SZ.v vj <= rounds /\ Seq.length vw == rounds /\
          SZ.v off + block_len <= Seq.length vb /\
          (forall (m: nat). m < SZ.v vj ==>
             Seq.index vw m ==
               ws_at (words_from_be #S32.t block_words (block_at vb (SZ.v off))) m))
  decreases (rounds - SZ.v (!j))
  {
    let vj = !j;
    let a3 = A.(wsb.(SZ.sub vj 3sz));
    let a8 = A.(wsb.(SZ.sub vj 8sz));
    let a14 = A.(wsb.(SZ.sub vj 14sz));
    let a16 = A.(wsb.(SZ.sub vj 16sz));
    let x = S32.rotate_left
              (S32.logxor (S32.logxor (S32.logxor a3 a8) a14) a16) 1ul;
    A.((wsb.(vj) <- x));
    j := SZ.add vj 1sz;
  };
  with vw. assert (A.pts_to wsb vw);
  Seq.lemma_eq_intro vw (ws (words_from_be #S32.t block_words (block_at vb (SZ.v off))));
  Seq.lemma_eq_elim vw (ws (words_from_be #S32.t block_words (block_at vb (SZ.v off))));
}

(** {2 One block} *)

fn update_block_impl (wsb: A.array S32.t) (st: A.array S32.t)
                     (block: A.array S8.t) (off: SZ.t)
                     (#vw0: erased (Seq.seq S32.t))
                     (#vst0: erased (Seq.lseq S32.t state_words))
                     (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to block #pb vb **
         pure (Seq.length vw0 == rounds /\ SZ.v off + block_len <= Seq.length vb)
ensures exists* vw.
  A.pts_to wsb vw ** A.pts_to st (update_block (block_at vb (SZ.v off)) vst0) **
  A.pts_to block #pb vb ** pure (Seq.length vw == rounds)
{
  A.pts_to_len st;
  ws_expand wsb block off;
  let a0 = A.(st.(0sz));
  let b0 = A.(st.(1sz));
  let c0 = A.(st.(2sz));
  let d0 = A.(st.(3sz));
  let e0 = A.(st.(4sz));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi rounds_sz)
  invariant exists* (vi: SZ.t) (vst: Seq.seq S32.t).
    pts_to i vi **
    A.pts_to wsb (ws (words_from_be #S32.t block_words (block_at vb (SZ.v off)))) **
    A.pts_to st vst ** A.pts_to block #pb vb **
    pure (SZ.v vi <= rounds /\ Seq.length vst == state_words /\
          vst == repeati_g (SZ.v vi)
                   (shuffle_core
                      (ws (words_from_be #S32.t block_words (block_at vb (SZ.v off)))))
                   vst0)
  decreases (rounds - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(st.(0sz));
    let b = A.(st.(1sz));
    let c = A.(st.(2sz));
    let d = A.(st.(3sz));
    let e = A.(st.(4sz));
    let wi = A.(wsb.(vi));
    let fi = f_impl vi b c d;
    let ki = k_impl vi;
    let tt = S32.add_mod
               (S32.add_mod (S32.add_mod (S32.add_mod (S32.rotate_left a 5ul) fi) e) ki)
               wi;
    A.((st.(0sz) <- tt));
    A.((st.(1sz) <- a));
    A.((st.(2sz) <- S32.rotate_left b 30ul));
    A.((st.(3sz) <- c));
    A.((st.(4sz) <- d));
    i := SZ.add vi 1sz;
  };
  let a1 = A.(st.(0sz));
  let b1 = A.(st.(1sz));
  let c1 = A.(st.(2sz));
  let d1 = A.(st.(3sz));
  let e1 = A.(st.(4sz));
  with vsh. assert (A.pts_to st vsh);
  set5_irrelevant vsh vst0
    (S32.add_mod a0 a1) (S32.add_mod b0 b1) (S32.add_mod c0 c1)
    (S32.add_mod d0 d1) (S32.add_mod e0 e1);
  A.((st.(0sz) <- S32.add_mod a0 a1));
  A.((st.(1sz) <- S32.add_mod b0 b1));
  A.((st.(2sz) <- S32.add_mod c0 c1));
  A.((st.(3sz) <- S32.add_mod d0 d1));
  A.((st.(4sz) <- S32.add_mod e0 e1));
}

#pop-options

(** {2 The digest}

    Five whole words, twenty bytes, no truncation: unlike SHA-224 and SHA-384
    the digest is exactly the state, so this writes straight into the caller's
    buffer with no scratch copy. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn write_digest (out: A.array S8.t) (st: A.array S32.t)
                (#vout: erased (Seq.seq S8.t)) (#pst: perm)
                (#vst: erased (Seq.lseq S32.t state_words))
requires A.pts_to out vout ** A.pts_to st #pst vst **
         pure (Seq.length vout == hash_bytes)
ensures A.pts_to out (finish vst) ** A.pts_to st #pst vst
{
  A.pts_to_len out;
  A.pts_to_len st;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 5sz)
  invariant exists* (vj: SZ.t) (vo: Seq.seq S8.t).
    pts_to j vj ** A.pts_to out vo ** A.pts_to st #pst vst **
    pure (SZ.v vj <= 5 /\ Seq.length vo == hash_bytes /\
          (forall (i: nat). i < SZ.v vj * 4 ==>
             Seq.index vo i == Seq.index (words_to_be #S32.t state_words vst) i))
  decreases (5 - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right 4 (SZ.v vj + 1) 5;
    Math.distributivity_add_left (SZ.v vj) 1 4;
    let x = A.(st.(vj));
    store_be #S32.t out (SZ.mul vj 4sz) x;
    with vo. assert (A.pts_to out vo);
    digest_step #S32.t state_words vst (SZ.v vj) (SZ.v (SZ.mul vj 4sz)) vo;
    j := SZ.add vj 1sz;
  };
  with vo. assert (A.pts_to out vo);
  Seq.lemma_eq_intro vo (finish vst);
  Seq.lemma_eq_elim vo (finish vst);
  ()
}

#pop-options

(** {2 The whole hash}

    The same two-phase drive as SHA-2: one loop over the whole blocks of the
    message, then a two-block scratch buffer holding the last partial block
    together with the padding.  Because SHA-1's padding {i is} SHA-2's padding
    at 32 bits ([Spec.SHA1.Lemmas]), both the byte-level lemmas and
    [build_tail] itself are reused rather than restated. *)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** The padding blocks and the digest.  Separated from [hash_impl] only so
    that each proof obligation sees a small context. *)

fn tail_and_finish (wsb: A.array S32.t) (st: A.array S32.t)
                   (out: A.array S8.t) (input: A.array S8.t)
                   (len: SZ.t) (nblocks: SZ.t) (base_in: SZ.t)
                   (rem: (r: SZ.t { SZ.v r < block_len }))
                   (pre: erased (Seq.seq S8.t))
                   (#vw0: erased (Seq.seq S32.t))
                   (#vst0: erased (Seq.lseq S32.t state_words))
                   (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to st vst0 **
         A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vw0 == rounds /\ Seq.length vout == hash_bytes /\
               Seq.length pre + Seq.length vin == SZ.v len /\
               Seq.length vin == SZ.v base_in + SZ.v rem /\
               SZ.v len < max_input /\
               SZ.v rem == SZ.v len % block_len /\
               SZ.v len - SZ.v rem == SZ.v nblocks * block_len /\
               reveal vst0 == repeati_g (SZ.v nblocks)
                                (update_step (padded (Seq.append pre vin))) iv)
ensures exists* (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words) (vout': Seq.seq S8.t).
  A.pts_to wsb vw ** A.pts_to st vst **
  A.pts_to out vout' ** A.pts_to input #pin vin **
  pure (Seq.length vw == rounds /\ Seq.length pre + Seq.length vin < max_input /\
        vout' == hash (Seq.append pre vin))
{
  A.pts_to_len input;
  A.pts_to_len out;
  A.pts_to_len st;
  A.pts_to_len wsb;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #S32.t (Seq.append pre vin);
  let ntail = C2.tail_len #S32.t rem;
  let base = SZ.sub len rem;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; 128sz |];
  A.pts_to_len tarr;
  A.pts_to_len tarr;
  C2.len_fits (SZ.v len);
  Math.euclidean_division_definition (SZ.v len) block_len;
  C2.build_tail #S32.t tarr input len base_in rem ntail;
  with vt. assert (A.pts_to tarr vt);
  pad_zeros_alt #S32.t (SZ.v len);
  append_index_at (reveal pre) (reveal vin) (SZ.v base) (SZ.v base_in) (SZ.v rem);
  tail_bytes #S32.t (Seq.append pre vin) vt (SZ.v ntail) (SZ.v base);
  Math.multiple_division_lemma (SZ.v ntail / block_len) block_len;
  Math.multiply_fractions (SZ.v ntail) block_len;
  let ntb = SZ.div ntail 64sz;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj ntb)
  invariant exists* (vj: SZ.t) (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words).
    pts_to j vj ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to tarr vt **
    pure (SZ.v vj <= SZ.v ntb /\ Seq.length vw == rounds /\
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
    C2.small_fits (SZ.v vj * block_len);
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
    update_block_impl wsb st tarr (SZ.mul vj 64sz);
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

fn hash_blocks (wsb: A.array S32.t) (st: A.array S32.t) (input: A.array S8.t)
               (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
               (#vw0: erased (Seq.seq S32.t))
               (#vst0: erased (Seq.lseq S32.t state_words))
               (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (Seq.length vw0 == rounds /\
               Seq.length pre == SZ.v nprev * block_len /\
               Seq.length pre + Seq.length vin < max_input /\
               SZ.v nfull == Seq.length vin / block_len /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step (padded (Seq.append pre vin))) iv)
ensures exists* (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words).
  A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input /\ Seq.length vw == rounds /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step (padded (Seq.append pre vin))) iv)
{
  A.pts_to_len input;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #S32.t (Seq.append pre vin);
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 nfull)
  invariant exists* (vi2: SZ.t) (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t state_words).
    pts_to i vi2 ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
    pure (SZ.v vi2 <= SZ.v nfull /\ Seq.length vw == rounds /\
          vst == repeati_g (SZ.v nprev + SZ.v vi2)
                   (update_step (padded (Seq.append pre vin))) iv)
  decreases (SZ.v nfull - SZ.v (!i))
  {
    let vi2 = !i;
    Math.lemma_mult_le_right block_len (SZ.v vi2 + 1) (SZ.v nfull);
    Math.lemma_mult_le_right block_len (SZ.v nfull) (Seq.length vin / block_len);
    padded_index_block_shift #S32.t (reveal pre) (reveal vin) (SZ.v vi2 * block_len);
    Math.distributivity_add_left (SZ.v nprev) (SZ.v vi2) block_len;
    Math.distributivity_add_left (SZ.v nprev) (SZ.v vi2 + 1) block_len;
    unfold_repeati_g (SZ.v nprev + SZ.v vi2)
      (update_step (padded (Seq.append pre vin))) iv;
    assert (pure (block_at (padded (Seq.append pre vin))
                    ((SZ.v nprev + SZ.v vi2) * block_len) ==
                  block_at vin (SZ.v vi2 * block_len)));
    assert (pure ((SZ.v nprev + SZ.v vi2 + 1) * block_len <=
                  Seq.length (padded (Seq.append pre vin))));
    update_block_impl wsb st input (SZ.mul vi2 64sz);
    i := SZ.add vi2 1sz;
  };
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

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

  let mut starr = [| z0; 5sz |];
  A.pts_to_len starr;
  A.pts_to_len starr;
  A.((starr.(0sz) <- S32.classify 0x67452301ul));
  A.((starr.(1sz) <- S32.classify 0xefcdab89ul));
  A.((starr.(2sz) <- S32.classify 0x98badcfeul));
  A.((starr.(3sz) <- S32.classify 0x10325476ul));
  A.((starr.(4sz) <- S32.classify 0xc3d2e1f0ul));
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (iv <: Seq.seq S32.t);
  Seq.lemma_eq_elim vst_init (iv <: Seq.seq S32.t);

  let mut wsarr = [| z0; rounds_sz |];
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;

  let empty : erased (Seq.seq S8.t) = hide (Seq.empty #S8.t);
  Seq.lemma_eq_elim (Seq.append (reveal empty) (reveal vin)) (reveal vin);
  Math.euclidean_division_definition (SZ.v len) block_len;
  hash_blocks wsarr starr input 0sz nfull empty;
  tail_and_finish wsarr starr out input len nfull (SZ.sub len rem) rem empty;
  ()
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** {2 Hashing a message with a one-block prefix}

    [hash (blk || input)] where [blk] is exactly one block, computed without
    ever building the concatenation: the prefix block is absorbed first and
    the rest of the message is read straight out of the caller's buffer.
    This is what HMAC's inner hash needs -- the prefix is [K0 ^ ipad] -- and
    it is why [hash_blocks] and [tail_and_finish] above are stated for a ghost
    block-aligned prefix rather than for the empty one. *)

fn hash_prefixed (out: A.array S8.t) (blk: A.array S8.t) (input: A.array S8.t) (lin: SZ.t)
                 (#vout: erased (Seq.seq S8.t))
                 (#pb: perm) (#vb: erased (Seq.seq S8.t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to blk #pb vb ** A.pts_to input #pin vin **
         pure (Seq.length vout == hash_bytes /\ Seq.length vb == block_len /\
               SZ.fits (block_len + Seq.length vin) /\
               block_len + Seq.length vin < max_input)
         ** pure (SZ.v lin == Seq.length vin)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to blk #pb vb ** A.pts_to input #pin vin **
  pure (Seq.length vb + Seq.length vin < max_input /\ vout' == hash (Seq.append vb vin))
{
  A.pts_to_len out;
  A.pts_to_len blk;
  A.pts_to_len input;
  let len = SZ.add 64sz lin;
  let nfull = SZ.div lin 64sz;
  let rem = SZ.rem lin 64sz;
  let z0 = S32.classify 0ul;

  let mut starr = [| z0; 5sz |];
  A.pts_to_len starr;
  A.pts_to_len starr;
  A.((starr.(0sz) <- S32.classify 0x67452301ul));
  A.((starr.(1sz) <- S32.classify 0xefcdab89ul));
  A.((starr.(2sz) <- S32.classify 0x98badcfeul));
  A.((starr.(3sz) <- S32.classify 0x10325476ul));
  A.((starr.(4sz) <- S32.classify 0xc3d2e1f0ul));
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (iv <: Seq.seq S32.t);
  Seq.lemma_eq_elim vst_init (iv <: Seq.seq S32.t);

  let mut wsarr = [| z0; rounds_sz |];
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;

  Seq.lemma_len_append (reveal vb) (reveal vin);
  padded_shape #S32.t (Seq.append vb vin);
  padded_index_block #S32.t (Seq.append vb vin) 0;
  append_first_block #S32.t (reveal vb) (reveal vin);
  update_block_impl wsarr starr blk 0sz;
  repeati_g_zero (update_step (padded (Seq.append vb vin))) iv;
  unfold_repeati_g 0 (update_step (padded (Seq.append vb vin))) iv;

  Math.lemma_mod_plus (SZ.v lin) 1 block_len;
  assert (pure (SZ.v rem == SZ.v len % block_len));
  Math.euclidean_division_definition (SZ.v lin) block_len;
  Math.distributivity_add_left 1 (SZ.v nfull) block_len;
  assert (pure (SZ.v len - SZ.v rem == (1 + SZ.v nfull) * block_len));
  Math.multiply_fractions (SZ.v lin) block_len;
  Math.lemma_mult_le_left (SZ.v nfull) 1 block_len;
  SZ.fits_lte (1 + SZ.v nfull) (block_len + SZ.v lin);

  hash_blocks wsarr starr input 1sz nfull vb;
  let nb = SZ.add 1sz nfull;
  let base_in = SZ.sub lin rem;
  tail_and_finish wsarr starr out input len nb base_in rem vb;

  ()
}

#pop-options
