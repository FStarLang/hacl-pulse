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

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U32 = FStar.UInt32

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
