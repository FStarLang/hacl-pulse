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

(** ChaCha20's block function.

    Everything here is in place, on a sixteen-word slice.  There is no type
    class and no monomorphized parameter record: ChaCha20 is a 32-bit design,
    so the extracted C is a single copy with every index and rotation distance
    already a literal.

    The one buffer that has to be kept is the pre-round state, because the
    block function adds it back at the end.  [core] therefore takes two
    sixteen-word slices, one of which it leaves holding the input state. *)
module Hacl.Chacha20.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Hacl.Impl.Bytes
open Spec.Chacha20

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module A = Pulse.Lib.Array
module U32 = FStar.UInt32
module G = FStar.Ghost

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Half a quarter round}

    [a += b; d ^= a; d <<<= s].  Note that [d] is read {i after} [a] has been
    written, which is what the specification says too; the two happen to agree
    trivially because the four indices of a quarter round are distinct, but
    writing it in the same order means the proof does not have to know
    that. *)
fn line_impl (st: S.slice S32.t) (a b d: SZ.t) (s: rotval)
             (#v0: erased (Seq.seq S32.t))
requires S.pts_to st v0 **
         pure (Seq.length v0 == 16 /\ SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v d < 16)
ensures exists* (v1: Seq.seq S32.t). S.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v d < 16 /\
        Seq.length v1 == 16 /\ v1 == line (SZ.v a) (SZ.v b) (SZ.v d) s v0)
{
  S.pts_to_len st;
  let ra = S.(st.(a));
  let rb = S.(st.(b));
  S.((st.(a) <- S32.add_mod ra rb));
  let rd = S.(st.(d));
  let ra' = S.(st.(a));
  S.((st.(d) <- S32.rotate_left (S32.logxor rd ra') s));
}

fn quarter_round_impl (st: S.slice S32.t) (a b c d: SZ.t)
                      (#v0: erased (Seq.seq S32.t))
requires S.pts_to st v0 **
         pure (Seq.length v0 == 16 /\
               SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16)
ensures exists* (v1: Seq.seq S32.t). S.pts_to st v1 **
  pure (Seq.length v0 == 16 /\
        SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16 /\
        Seq.length v1 == 16 /\
        v1 == quarter_round (SZ.v a) (SZ.v b) (SZ.v c) (SZ.v d) v0)
{
  line_impl st a b d 16ul;
  line_impl st c d b 12ul;
  line_impl st a b d 8ul;
  line_impl st c d b 7ul;
}

(** {2 A double round} *)

fn column_round_impl (st: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq S32.t). S.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ v1 == column_round v0)
{
  quarter_round_impl st 0sz 4sz  8sz 12sz;
  quarter_round_impl st 1sz 5sz  9sz 13sz;
  quarter_round_impl st 2sz 6sz 10sz 14sz;
  quarter_round_impl st 3sz 7sz 11sz 15sz;
}

fn diagonal_round_impl (st: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq S32.t). S.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ v1 == diagonal_round v0)
{
  quarter_round_impl st 0sz 5sz 10sz 15sz;
  quarter_round_impl st 1sz 6sz 11sz 12sz;
  quarter_round_impl st 2sz 7sz  8sz 13sz;
  quarter_round_impl st 3sz 4sz  9sz 14sz;
}

fn double_round_impl (st: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq S32.t). S.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ v1 == double_round v0)
{
  column_round_impl st;
  diagonal_round_impl st;
}

(** {2 Twenty rounds} *)

fn rounds_impl (st: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq S32.t). S.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ v1 == rounds v0)
{
  S.pts_to_len st;
  repeati_zero (fun _ m -> double_round m) (reveal v0);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 10sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
    pts_to i vi ** S.pts_to st v **
    pure (SZ.v vi <= 10 /\ Seq.length v0 == 16 /\ Seq.length v == 16 /\
          v == repeati (SZ.v vi) (fun _ m -> double_round m) v0)
  decreases (10 - SZ.v (!i))
  {
    let vi = !i;
    double_round_impl st;
    unfold_repeati (SZ.v vi) (fun _ m -> double_round m) (reveal v0);
    i := SZ.add vi 1sz;
  }
}

#pop-options

(** {2 The block function}

    [core ks st ctr] leaves the keystream words in [ks] and the pre-round
    state -- that is, [with_counter st ctr] -- in [st] itself.  Overwriting
    the caller's state with its own counter is harmless: every caller sets the
    counter on every call anyway. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn core_impl (ks: S.slice S32.t) (st: S.slice S32.t) (ctr: U32.t)
             (#vks: erased (Seq.seq S32.t)) (#v0: erased (Seq.seq S32.t))
requires S.pts_to ks vks ** S.pts_to st v0 **
         pure (Seq.length vks == 16 /\ Seq.length v0 == 16)
ensures exists* (vk1: Seq.seq S32.t) (vs1: Seq.seq S32.t).
  S.pts_to ks vk1 ** S.pts_to st vs1 **
  pure (Seq.length v0 == 16 /\ Seq.length vk1 == 16 /\ Seq.length vs1 == 16 /\
        vs1 == with_counter v0 ctr /\ vk1 == core v0 ctr)
{
  S.pts_to_len ks;
  S.pts_to_len st;

  S.((st.(12sz) <- S32.classify ctr));

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 16sz)
  invariant exists* (vj: SZ.t) (vk: Seq.seq S32.t) (vs: Seq.seq S32.t).
    pts_to j vj ** S.pts_to ks vk ** S.pts_to st vs **
    pure (SZ.v vj <= 16 /\ Seq.length v0 == 16 /\ Seq.length vk == 16 /\
          Seq.length vs == 16 /\ vs == with_counter v0 ctr /\
          (forall (k: nat). k < SZ.v vj ==> Seq.index vk k == Seq.index vs k))
  decreases (16 - SZ.v (!j))
  {
    let vj = !j;
    let x = S.(st.(vj));
    S.((ks.(vj) <- x));
    j := SZ.add vj 1sz;
  };

  with vk. assert (S.pts_to ks vk);
  with vs. assert (S.pts_to st vs);
  Seq.lemma_eq_intro vk vs;
  Seq.lemma_eq_elim vk vs;

  rounds_impl ks;

  let mut n = 0sz;
  while (let vn = !n; SZ.lt vn 16sz)
  invariant exists* (vn: SZ.t) (vk: Seq.seq S32.t) (vs: Seq.seq S32.t).
    pts_to n vn ** S.pts_to ks vk ** S.pts_to st vs **
    pure (SZ.v vn <= 16 /\ Seq.length v0 == 16 /\ Seq.length vk == 16 /\
          Seq.length vs == 16 /\ vs == with_counter v0 ctr /\
          (forall (k: nat). k < SZ.v vn ==> Seq.index vk k == Seq.index (core v0 ctr) k) /\
          (forall (k: nat). SZ.v vn <= k /\ k < 16 ==>
             Seq.index vk k == Seq.index (rounds (with_counter v0 ctr)) k))
  decreases (16 - SZ.v (!n))
  {
    let vn = !n;
    let x = S.(ks.(vn));
    let y = S.(st.(vn));
    S.((ks.(vn) <- S32.add_mod x y));
    n := SZ.add vn 1sz;
  };

  with vk. assert (S.pts_to ks vk);
  Seq.lemma_eq_intro vk (core v0 ctr);
  Seq.lemma_eq_elim vk (core v0 ctr);
}

#pop-options

(** {2 The keystream as bytes}

    Sixteen little-endian stores, exactly as the SHA-2 and BLAKE2 digest
    writers do it. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn write_keystream (out: S.slice S8.t) (ks: S.slice S32.t)
                   (#vout: erased (Seq.seq S8.t)) (#pk: perm)
                   (#vk: erased (Seq.lseq S32.t 16))
requires S.pts_to out vout ** S.pts_to ks #pk vk **
         pure (Seq.length vout == 64)
ensures S.pts_to out (words_to_le #S32.t 16 vk) ** S.pts_to ks #pk vk
{
  S.pts_to_len out;
  S.pts_to_len ks;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 16sz)
  invariant exists* (vj: SZ.t) (vo: Seq.seq S8.t).
    pts_to j vj ** S.pts_to out vo ** S.pts_to ks #pk vk **
    pure (SZ.v vj <= 16 /\ Seq.length vo == 64 /\
          (forall (i: nat). i < SZ.v vj * 4 ==>
             Seq.index vo i == Seq.index (words_to_le #S32.t 16 vk) i))
  decreases (16 - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right 4 (SZ.v vj + 1) 16;
    Math.distributivity_add_left (SZ.v vj) 1 4;
    let x = S.(ks.(vj));
    store_le #S32.t out (SZ.mul vj 4sz) x;
    with vo. assert (S.pts_to out vo);
    digest_step_le #S32.t 16 vk (SZ.v vj) (SZ.v (SZ.mul vj 4sz)) vo;
    j := SZ.add vj 1sz;
  };
  with vo. assert (S.pts_to out vo);
  Seq.lemma_eq_intro vo (words_to_le #S32.t 16 vk);
  Seq.lemma_eq_elim vo (words_to_le #S32.t 16 vk);
}

#pop-options
