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

(** ChaCha20, eight blocks at a time, on AVX2.

    {2 The shape}

    The state is sixteen vectors, and vector [i] holds word [i] of eight
    consecutive blocks, one per lane.  Seen down a lane, that is exactly the
    scalar state of one block, so the round function is the scalar one with
    every word replaced by a vector -- the same quarter round at the same
    indices with the same rotation distances -- and the proof of each step is
    the scalar specification applied once per lane.  [lane_state vs j] is
    that view: the scalar state of block [j].  Nothing about ChaCha20 is
    restated here; every postcondition says that lane [j] has advanced by
    one step of [Spec.Chacha20].

    The only part with no scalar counterpart is the end.  After the
    feed-forward, block [j]'s keystream is spread across lane [j] of sixteen
    registers, and a message is contiguous.  Two 8 x 8 transposes of 32-bit
    words, each three rounds of shuffles, turn the sixteen word-vectors into
    sixteen half-block-vectors, and each of those is one load, one
    exclusive-or and one store of message.  [transpose] proves where each
    word lands; [vv_lanes] says that a register's bytes are its lanes written
    little-endian, which is what turns that into a statement about the bytes
    of [Spec.Chacha20.keystream].

    {2 Where it is called}

    [Hacl.Chacha20.encrypt] calls [encrypt_blocks8] when [Hacl.Vec256.supported]
    says the machine has AVX2, and it consumes every whole multiple of 512
    bytes; the scalar loop finishes the rest from the counter where this left
    it.  Everything here carries [target("avx2")] and nothing outside
    reaches it except through that guard. *)
module Hacl.Chacha20.Vec256

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Spec.Chacha20

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U32 = FStar.UInt32
module G = FStar.Ghost
module V = Hacl.Vec256
module Sub = Hacl.Impl.Sub
module Classical = FStar.Classical

(** {2 Looking down a lane} *)

let vstate = s: Seq.seq V.t { Seq.length s == 16 }

let lane_state (vs: vstate) (j: nat { j < 8 }) : GTot state =
  Seq.init_ghost 16 (fun i -> V.lane (Seq.index vs i) j)

let lane_state_index (vs: vstate) (j: nat { j < 8 }) (i: nat { i < 16 })
  : Lemma (Seq.index (lane_state vs j) i == V.lane (Seq.index vs i) j)
          [SMTPat (Seq.index (lane_state vs j) i)]
  = ()

(** Every lane of [v1] is [f] of the same lane of [v0]. *)
let lanes_step (v0 v1: vstate) (f: state -> state) : prop =
  forall (j: nat). j < 8 ==> lane_state v1 j == f (lane_state v0 j)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** The vector form of [Spec.Chacha20.line], in the order the code does it. *)
let line_v (v0: vstate) (a b d: idx) (s: rotval) : GTot vstate =
  let x = V.add32 (Seq.index v0 a) (Seq.index v0 b) in
  let v1 = Seq.upd v0 a x in
  Seq.upd v1 d (V.rotl (V.vxor (Seq.index v1 d) x) s)

let line_lanes (v0: vstate) (a b d: idx) (s: rotval)
  : Lemma (lanes_step v0 (line_v v0 a b d s) (line a b d s))
  = let v1 = line_v v0 a b d s in
    let aux (j: nat { j < 8 })
      : Lemma (lane_state v1 j == line a b d s (lane_state v0 j))
      = Seq.lemma_eq_intro (lane_state v1 j) (line a b d s (lane_state v0 j))
    in
    Classical.forall_intro aux

let lanes_step_trans (v0 v1 v2: vstate) (f g: state -> state)
  : Lemma (requires lanes_step v0 v1 f /\ lanes_step v1 v2 g)
          (ensures lanes_step v0 v2 (fun m -> g (f m)))
  = ()

#pop-options

(** {2 The round function, on eight lanes}

    Each of these is [inline_for_extraction] so that the whole of the twenty
    rounds is one C function over one local array with literal indices,
    which the C compiler keeps in registers. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

inline_for_extraction
fn line_vec (st: A.array V.t) (a b d: SZ.t) (s: rotval) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 **
         pure (Seq.length v0 == 16 /\ SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v d < 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v d < 16 /\
        Seq.length v1 == 16 /\
        lanes_step v0 v1 (line (SZ.v a) (SZ.v b) (SZ.v d) s))
{
  A.pts_to_len st;
  let ra = A.(st.(a));
  let rb = A.(st.(b));
  let x = V.add32 ra rb;
  A.((st.(a) <- x));
  let rd = A.(st.(d));
  let y = V.rotl (V.vxor rd x) s;
  A.((st.(d) <- y));
  with v1. assert (A.pts_to st v1);
  Seq.lemma_eq_elim v1 (line_v v0 (SZ.v a) (SZ.v b) (SZ.v d) s);
  line_lanes v0 (SZ.v a) (SZ.v b) (SZ.v d) s;
  assert (pure (lanes_step v0 v1 (line (SZ.v a) (SZ.v b) (SZ.v d) s)));
}

inline_for_extraction
fn quarter_round_vec (st: A.array V.t) (a b c d: SZ.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 **
         pure (Seq.length v0 == 16 /\
               SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\
        SZ.v a < 16 /\ SZ.v b < 16 /\ SZ.v c < 16 /\ SZ.v d < 16 /\
        Seq.length v1 == 16 /\
        lanes_step v0 v1 (quarter_round (SZ.v a) (SZ.v b) (SZ.v c) (SZ.v d)))
{
  line_vec st a b d 16ul;
  line_vec st c d b 12ul;
  line_vec st a b d 8ul;
  line_vec st c d b 7ul;
}

inline_for_extraction
fn column_round_vec (st: A.array V.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ lanes_step v0 v1 column_round)
{
  quarter_round_vec st 0sz 4sz  8sz 12sz;
  quarter_round_vec st 1sz 5sz  9sz 13sz;
  quarter_round_vec st 2sz 6sz 10sz 14sz;
  quarter_round_vec st 3sz 7sz 11sz 15sz;
}

inline_for_extraction
fn diagonal_round_vec (st: A.array V.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ lanes_step v0 v1 diagonal_round)
{
  quarter_round_vec st 0sz 5sz 10sz 15sz;
  quarter_round_vec st 1sz 6sz 11sz 12sz;
  quarter_round_vec st 2sz 7sz  8sz 13sz;
  quarter_round_vec st 3sz 4sz  9sz 14sz;
}

inline_for_extraction
fn double_round_vec (st: A.array V.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ lanes_step v0 v1 double_round)
{
  column_round_vec st;
  diagonal_round_vec st;
}

#pop-options

let rounds_upto (k: nat) (m: state) : state = repeati k (fun _ m -> double_round m) m

let rounds_upto_step (v0 v v': vstate) (k: nat)
  : Lemma (requires (forall (j: nat). j < 8 ==> lane_state v j == rounds_upto k (lane_state v0 j)) /\
                    lanes_step v v' double_round)
          (ensures forall (j: nat). j < 8 ==> lane_state v' j == rounds_upto (k + 1) (lane_state v0 j))
  = let aux (j: nat { j < 8 })
      : Lemma (lane_state v' j == rounds_upto (k + 1) (lane_state v0 j))
      = unfold_repeati k (fun _ m -> double_round m) (lane_state v0 j)
    in
    Classical.forall_intro aux

let rounds_upto_zero (v0: vstate)
  : Lemma (forall (j: nat). j < 8 ==> lane_state v0 j == rounds_upto 0 (lane_state v0 j))
  = let aux (j: nat { j < 8 })
      : Lemma (lane_state v0 j == rounds_upto 0 (lane_state v0 j))
      = repeati_zero (fun _ m -> double_round m) (lane_state v0 j)
    in
    Classical.forall_intro aux

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

inline_for_extraction
fn rounds_vec (st: A.array V.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ lanes_step v0 v1 rounds)
{
  A.pts_to_len st;
  rounds_upto_zero v0;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 10sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq V.t).
    pts_to i vi ** A.pts_to st v **
    pure (SZ.v vi <= 10 /\ Seq.length v0 == 16 /\ Seq.length v == 16 /\
          (forall (j: nat). j < 8 ==> lane_state v j == rounds_upto (SZ.v vi) (lane_state v0 j)))
  decreases (10 - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to st v);
    double_round_vec st;
    with v'. assert (A.pts_to st v');
    rounds_upto_step v0 v v' (SZ.v vi);
    i := SZ.add vi 1sz;
  }
}

#pop-options

(** {2 The initial state and the block function} *)

(** The counter of lane [j]. *)
let lane_ctr (c: U32.t { U32.v c + 8 <= pow2 32 }) (j: nat { j < 8 }) : U32.t =
  U32.uint_to_t (U32.v c + j)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"

let init_lanes (s0: state) (c: U32.t { U32.v c + 8 <= pow2 32 }) (vs: vstate)
  : Lemma
      (requires
        (forall (i: nat). i < 16 /\ i <> 12 ==>
           (forall (j: nat). j < 8 ==> V.lane (Seq.index vs i) j == Seq.index s0 i)) /\
        (forall (j: nat). j < 8 ==> S32.v (V.lane (Seq.index vs 12) j) == U32.v c + j))
      (ensures forall (j: nat). j < 8 ==> lane_state vs j == with_counter s0 (lane_ctr c j))
  = let aux (j: nat { j < 8 })
      : Lemma (lane_state vs j == with_counter s0 (lane_ctr c j))
      = Seq.lemma_eq_intro (lane_state vs j) (with_counter s0 (lane_ctr c j))
    in
    Classical.forall_intro aux

let ctr_lanes (c: U32.t { U32.v c + 8 <= pow2 32 }) (cb io: V.t)
  : Lemma (requires (forall (i: nat). i < 8 ==> V.lane cb i == S32.classify c) /\
                    (forall (i: nat). i < 8 ==> S32.v (V.lane io i) == i))
          (ensures forall (j: nat). j < 8 ==> S32.v (V.lane (V.add32 cb io) j) == U32.v c + j)
  = let aux (j: nat { j < 8 })
      : Lemma (S32.v (V.lane (V.add32 cb io) j) == U32.v c + j)
      = Math.small_mod (U32.v c + j) (pow2 32)
    in
    Classical.forall_intro aux

let set12_lanes (s0: state) (c: U32.t { U32.v c + 8 <= pow2 32 }) (v: vstate) (cv: V.t)
  : Lemma (requires (forall (k: nat). k < 16 ==>
             (forall (j: nat). j < 8 ==> V.lane (Seq.index v k) j == Seq.index s0 k)) /\
             (forall (j: nat). j < 8 ==> S32.v (V.lane cv j) == U32.v c + j))
          (ensures forall (j: nat). j < 8 ==>
             lane_state (Seq.upd v 12 cv) j == with_counter s0 (lane_ctr c j))
  = init_lanes s0 c (Seq.upd v 12 cv)

(** Lane [j] of [vst] is the state of block [c + j]. *)
inline_for_extraction
fn init_vec (vst: A.array V.t) (st: A.array S32.t) (c: U32.t)
            (#vv0: erased (Seq.seq V.t)) (#ps: perm) (#s0: erased (Seq.seq S32.t))
requires A.pts_to vst vv0 ** A.pts_to st #ps s0 **
         pure (Seq.length vv0 == 16 /\ Seq.length s0 == 16 /\ U32.v c + 8 <= pow2 32)
ensures exists* (vv1: Seq.seq V.t). A.pts_to vst vv1 ** A.pts_to st #ps s0 **
  pure (Seq.length s0 == 16 /\ U32.v c + 8 <= pow2 32 /\ Seq.length vv1 == 16 /\
        (forall (j: nat). j < 8 ==> lane_state vv1 j == with_counter s0 (lane_ctr c j)))
{
  A.pts_to_len vst;
  A.pts_to_len st;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq V.t).
    pts_to i vi ** A.pts_to vst v ** A.pts_to st #ps s0 **
    pure (SZ.v vi <= 16 /\ Seq.length v == 16 /\ Seq.length s0 == 16 /\
          (forall (k: nat). k < SZ.v vi ==>
             (forall (j: nat). j < 8 ==> V.lane (Seq.index v k) j == Seq.index s0 k)))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let w = A.(st.(vi));
    A.((vst.(vi) <- V.bcast w));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to vst v);
  let cb = V.bcast (S32.classify c);
  let io = V.iota ();
  let cv = V.add32 cb io;
  ctr_lanes c cb io;
  set12_lanes s0 c v cv;
  A.((vst.(12sz) <- cv));
}

let core_lanes (vst ks1 ks2: vstate) (f: (j: nat { j < 8 }) -> GTot state)
  : Lemma
      (requires
        (forall (j: nat). j < 8 ==> lane_state vst j == f j) /\
        lanes_step vst ks1 rounds /\
        (forall (i: nat). i < 16 ==>
           Seq.index ks2 i == V.add32 (Seq.index ks1 i) (Seq.index vst i)))
      (ensures forall (j: nat). j < 8 ==> lane_state ks2 j == core_of (f j))
  = let aux (j: nat { j < 8 })
      : Lemma (lane_state ks2 j == core_of (f j))
      = Seq.lemma_eq_intro (lane_state ks2 j) (core_of (f j))
    in
    Classical.forall_intro aux

(** [ks] gets the eight keystream blocks, one per lane, before
    serialization; [vst] is left alone. *)
inline_for_extraction
fn core_vec (ks: A.array V.t) (vst: A.array V.t)
            (f: G.erased ((j: nat { j < 8 }) -> GTot state))
            (#vk0: erased (Seq.seq V.t)) (#vs: erased (Seq.seq V.t))
requires A.pts_to ks vk0 ** A.pts_to vst vs **
         pure (Seq.length vk0 == 16 /\ Seq.length vs == 16 /\
               (forall (j: nat). j < 8 ==> lane_state vs j == G.reveal f j))
ensures exists* (vk1: Seq.seq V.t). A.pts_to ks vk1 ** A.pts_to vst vs **
  pure (Seq.length vs == 16 /\ Seq.length vk1 == 16 /\
        (forall (j: nat). j < 8 ==> lane_state vk1 j == core_of (G.reveal f j)))
{
  A.pts_to_len ks;
  A.pts_to_len vst;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq V.t).
    pts_to i vi ** A.pts_to ks v ** A.pts_to vst vs **
    pure (SZ.v vi <= 16 /\ Seq.length v == 16 /\ Seq.length vs == 16 /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index vs k))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(vst.(vi));
    A.((ks.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with k0. assert (A.pts_to ks k0);
  Seq.lemma_eq_elim k0 vs;
  rewrite (A.pts_to ks k0) as (A.pts_to ks vs);
  rounds_vec ks;
  with k1. assert (A.pts_to ks k1);
  let mut n = 0sz;
  while (let vn = !n; SZ.lt vn 16sz)
  invariant exists* (vn: SZ.t) (v: Seq.seq V.t).
    pts_to n vn ** A.pts_to ks v ** A.pts_to vst vs **
    pure (SZ.v vn <= 16 /\ Seq.length v == 16 /\ Seq.length vs == 16 /\
          Seq.length k1 == 16 /\
          (forall (k: nat). k < SZ.v vn ==>
             Seq.index v k == V.add32 (Seq.index k1 k) (Seq.index vs k)) /\
          (forall (k: nat). SZ.v vn <= k /\ k < 16 ==> Seq.index v k == Seq.index k1 k))
  decreases (16 - SZ.v (!n))
  {
    let vn = !n;
    let x = A.(ks.(vn));
    let y = A.(vst.(vn));
    A.((ks.(vn) <- V.add32 x y));
    n := SZ.add vn 1sz;
  };
  with k2. assert (A.pts_to ks k2);
  assert (pure (forall (j: nat). j < 8 ==> lane_state vs j == G.reveal f j));
  assert (pure (lanes_step vs k1 rounds));
  assert (pure (forall (i: nat). i < 16 ==>
           Seq.index k2 i == V.add32 (Seq.index k1 i) (Seq.index vs i)));
  core_lanes vs k1 k2 f;
  assert (pure (forall (j: nat). j < 8 ==> lane_state k2 j == core_of (G.reveal f j)));
  assert (pure (Seq.length k2 == 16));
}

#pop-options

(** {2 From lanes to bytes} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** A register's bytes are its lanes, written out little-endian. *)
let vv_lanes (x: V.t) (q: nat { q < 32 })
  : Lemma (Seq.index (V.vv x) q ==
           Seq.index (word_to_le #S32.t (V.lane x (q / 4))) (q % 4))
  = let sb = sub_block #S32.t 8 (V.vv x) (q / 4) in
    le_nat_bound sb;
    le_nat_byte sb (q % 4);
    nat_to_le_index 4 (le_nat sb) (q % 4);
    Math.euclidean_division_definition q 4;
    S8.v_extensional (Seq.index (V.vv x) q)
                     (Seq.index (word_to_le #S32.t (V.lane x (q / 4))) (q % 4))

(** Byte [32h + q] of a block of sixteen words is byte [q % 4] of word
    [8h + q / 4]. *)
let words_to_le_half (w: Seq.lseq S32.t 16) (h: nat { h < 2 }) (q: nat { q < 32 })
  : Lemma (Seq.index (words_to_le #S32.t 16 w) (32 * h + q) ==
           Seq.index (word_to_le #S32.t (Seq.index w (8 * h + q / 4))) (q % 4))
  = Math.lemma_div_plus q (8 * h) 4;
    Math.lemma_mod_plus q (8 * h) 4

(** A register whose lanes are words [8h .. 8h+7] of [w] holds bytes
    [32h .. 32h+31] of [w] written out. *)
let half_bytes (x: V.t) (w: Seq.lseq S32.t 16) (h: nat { h < 2 })
  : Lemma (requires forall (k: nat). k < 8 ==> V.lane x k == Seq.index w (8 * h + k))
          (ensures forall (q: nat). q < 32 ==>
             Seq.index (V.vv x) q == Seq.index (words_to_le #S32.t 16 w) (32 * h + q))
  = let aux (q: nat { q < 32 })
      : Lemma (Seq.index (V.vv x) q == Seq.index (words_to_le #S32.t 16 w) (32 * h + q))
      = vv_lanes x q; words_to_le_half w h q
    in
    Classical.forall_intro aux

#pop-options

(** {2 The transpose}

    Rows [8h .. 8h+7] of [ks] hold words [8h .. 8h+7] of eight blocks, a
    block per lane.  Three rounds of shuffles turn them into eight registers
    of which the [j]th holds those eight words of block [j], and register
    [j] goes to [t.(2j + h)] -- so that once both halves are done, [t] is
    the keystream in memory order, thirty-two bytes at a time. *)

let tr_ok (vk: vstate) (h: nat { h < 2 }) (x: V.t) (j: nat { j < 8 }) : prop =
  forall (k: nat). k < 8 ==> V.lane x k == V.lane (Seq.index vk (8 * h + k)) j

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

inline_for_extraction
fn transpose (t: A.array V.t) (ks: A.array V.t) (h: SZ.t)
             (#vt: erased (Seq.seq V.t)) (#vk: erased (Seq.seq V.t))
requires A.pts_to t vt ** A.pts_to ks vk **
         pure (Seq.length vt == 16 /\ Seq.length vk == 16 /\ SZ.v h < 2)
ensures exists* (vt': Seq.seq V.t). A.pts_to t vt' ** A.pts_to ks vk **
  pure (Seq.length vt == 16 /\ Seq.length vk == 16 /\ SZ.v h < 2 /\
        Seq.length vt' == 16 /\
        (forall (j: nat). j < 8 ==> tr_ok vk (SZ.v h) (Seq.index vt' (2 * j + SZ.v h)) j) /\
        (forall (i: nat). i < 16 /\ i % 2 <> SZ.v h ==> Seq.index vt' i == Seq.index vt i))
{
  A.pts_to_len t;
  A.pts_to_len ks;
  let o = SZ.mul 8sz h;
  let r0 = A.(ks.(o));
  let r1 = A.(ks.(SZ.add o 1sz));
  let r2 = A.(ks.(SZ.add o 2sz));
  let r3 = A.(ks.(SZ.add o 3sz));
  let r4 = A.(ks.(SZ.add o 4sz));
  let r5 = A.(ks.(SZ.add o 5sz));
  let r6 = A.(ks.(SZ.add o 6sz));
  let r7 = A.(ks.(SZ.add o 7sz));
  let a0 = V.unpacklo32 r0 r1;
  let a1 = V.unpackhi32 r0 r1;
  let a2 = V.unpacklo32 r2 r3;
  let a3 = V.unpackhi32 r2 r3;
  let a4 = V.unpacklo32 r4 r5;
  let a5 = V.unpackhi32 r4 r5;
  let a6 = V.unpacklo32 r6 r7;
  let a7 = V.unpackhi32 r6 r7;
  let b0 = V.unpacklo64 a0 a2;
  let b1 = V.unpackhi64 a0 a2;
  let b2 = V.unpacklo64 a1 a3;
  let b3 = V.unpackhi64 a1 a3;
  let b4 = V.unpacklo64 a4 a6;
  let b5 = V.unpackhi64 a4 a6;
  let b6 = V.unpacklo64 a5 a7;
  let b7 = V.unpackhi64 a5 a7;
  let x0 = V.lo128 b0 b4;
  let x1 = V.lo128 b1 b5;
  let x2 = V.lo128 b2 b6;
  let x3 = V.lo128 b3 b7;
  let x4 = V.hi128 b0 b4;
  let x5 = V.hi128 b1 b5;
  let x6 = V.hi128 b2 b6;
  let x7 = V.hi128 b3 b7;
  assert (pure (tr_ok vk (SZ.v h) x0 0));
  assert (pure (tr_ok vk (SZ.v h) x1 1));
  assert (pure (tr_ok vk (SZ.v h) x2 2));
  assert (pure (tr_ok vk (SZ.v h) x3 3));
  assert (pure (tr_ok vk (SZ.v h) x4 4));
  assert (pure (tr_ok vk (SZ.v h) x5 5));
  assert (pure (tr_ok vk (SZ.v h) x6 6));
  assert (pure (tr_ok vk (SZ.v h) x7 7));
  A.((t.(h) <- x0));
  A.((t.(SZ.add h 2sz) <- x1));
  A.((t.(SZ.add h 4sz) <- x2));
  A.((t.(SZ.add h 6sz) <- x3));
  A.((t.(SZ.add h 8sz) <- x4));
  A.((t.(SZ.add h 10sz) <- x5));
  A.((t.(SZ.add h 12sz) <- x6));
  A.((t.(SZ.add h 14sz) <- x7));
}

#pop-options

(** {2 Thirty-two bytes of message} *)

(** Refinement subtyping does not cross [erased], so the window a load wants
    is reached through an explicit coercion. *)
let as32 (s: Seq.seq S8.t { Seq.length s == 32 })
  : Pure (Seq.lseq S8.t 32) (requires True) (ensures fun r -> r == s)
  = s

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

inline_for_extraction
fn xor32 (out: A.array S8.t) (msg: A.array S8.t) (o: SZ.t) (x: V.t)
         (#vo: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to msg #pm vm **
         pure (Seq.length vo == Seq.length vm /\ SZ.v o + 32 <= Seq.length vm)
ensures exists* (vo': Seq.seq S8.t). A.pts_to out vo' ** A.pts_to msg #pm vm **
  pure (Seq.length vo == Seq.length vm /\ SZ.v o + 32 <= Seq.length vm /\
        Seq.length vo' == Seq.length vo /\
        (forall (p: nat). p < Seq.length vo ==>
           Seq.index vo' p ==
             (if SZ.v o <= p && p < SZ.v o + 32
              then S8.logxor (Seq.index vm p) (Seq.index (V.vv x) (p - SZ.v o))
              else Seq.index vo p)))
{
  A.pts_to_len out;
  A.pts_to_len msg;
  let o2 = SZ.add o 32sz;
  let mb = Sub.sub msg o o2;
  let mv = V.load mb #(as32 (Seq.slice vm (SZ.v o) (SZ.v o2)));
  Sub.unsub_id msg (SZ.v o) (SZ.v o2) mb;
  let r = V.vxor mv x;
  let ob = Sub.sub out o o2;
  V.store ob r #(as32 (Seq.slice vo (SZ.v o) (SZ.v o2)));
  Sub.unsub out (SZ.v o) (SZ.v o2) ob;
  ()
}

#pop-options

(** {2 Five hundred and twelve bytes}

    The keystream that block [j] of a chunk exclusive-ors in. *)

let chunk_ks (s0: state) (c: U32.t { U32.v c + 8 <= pow2 32 }) (q: nat { q < 512 }) : GTot S8.t =
  Seq.index (keystream s0 (lane_ctr c (q / 64))) (q % 64)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Abstract in the predicate, so that the solver does not unfold it. *)
let transpose_both (p: (h: nat { h < 2 }) -> V.t -> (j: nat { j < 8 }) -> prop)
                   (vt1 vt2: vstate)
  : Lemma
      (requires
        (forall (j: nat). j < 8 ==> p 0 (Seq.index vt1 (2 * j)) j) /\
        (forall (j: nat). j < 8 ==> p 1 (Seq.index vt2 (2 * j + 1)) j) /\
        (forall (i: nat). i < 16 /\ i % 2 <> 1 ==> Seq.index vt2 i == Seq.index vt1 i))
      (ensures forall (i: nat). i < 16 ==> p (i % 2) (Seq.index vt2 i) (i / 2))
  = let aux (i: nat { i < 16 })
      : Lemma (p (i % 2) (Seq.index vt2 i) (i / 2))
      = let j = i / 2 in
        Math.euclidean_division_definition i 2;
        if i % 2 = 0 then assert (p 0 (Seq.index vt1 (2 * j)) j)
        else assert (p 1 (Seq.index vt2 (2 * j + 1)) j)
    in
    Classical.forall_intro aux

let chunk_arith (i: nat) (q: nat)
  : Lemma (32 * i + q == (32 * (i % 2) + q) + (i / 2) * 64)
  = Math.euclidean_division_definition i 2

let chunk_byte (s0: state) (c: U32.t { U32.v c + 8 <= pow2 32 })
               (vk: vstate) (x: V.t) (i: nat { i < 16 }) (q: nat { q < 32 })
  : Lemma
      (requires
        (forall (j: nat). j < 8 ==> lane_state vk j == core s0 (lane_ctr c j)) /\
        tr_ok vk (i % 2) x (i / 2))
      (ensures Seq.index (V.vv x) q == chunk_ks s0 c (32 * i + q))
  = let j = i / 2 in
    let h = i % 2 in
    let w = core s0 (lane_ctr c j) in
    assert (forall (k: nat). k < 8 ==> V.lane x k == Seq.index (lane_state vk j) (8 * h + k));
    half_bytes x w h;
    chunk_arith i q;
    Math.lemma_div_plus (32 * h + q) j 64;
    Math.lemma_mod_plus (32 * h + q) j 64;
    Math.small_div (32 * h + q) 64;
    Math.small_mod (32 * h + q) 64;
    assert (32 * i + q == (32 * h + q) + j * 64)

#pop-options

let chunk_inv (s0: state) (c: U32.t { U32.v c + 8 <= pow2 32 })
              (vo vm v: Seq.seq S8.t) (off: nat) (n: nat) : prop =
  Seq.length v == Seq.length vo /\ Seq.length vo == Seq.length vm /\
  off + 512 <= Seq.length vm /\ n <= 16 /\
  (forall (p: nat). p < Seq.length vo ==>
     Seq.index v p ==
       (if off <= p && p < off + 32 * n
        then S8.logxor (Seq.index vm p) (chunk_ks s0 c (p - off))
        else Seq.index vo p))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let chunk_step (s0: state) (c: U32.t { U32.v c + 8 <= pow2 32 })
               (vo vm v v': Seq.seq S8.t) (off: nat) (n: nat { n < 16 }) (x: V.t)
  : Lemma
      (requires
        chunk_inv s0 c vo vm v off n /\
        (forall (q: nat). q < 32 ==> Seq.index (V.vv x) q == chunk_ks s0 c (32 * n + q)) /\
        Seq.length v' == Seq.length v /\
        (forall (p: nat). p < Seq.length v ==>
           Seq.index v' p ==
             (if off + 32 * n <= p && p < off + 32 * n + 32
              then S8.logxor (Seq.index vm p) (Seq.index (V.vv x) (p - (off + 32 * n)))
              else Seq.index v p)))
      (ensures chunk_inv s0 c vo vm v' off (n + 1))
  = let aux (p: nat { p < Seq.length vo })
      : Lemma (Seq.index v' p ==
                 (if off <= p && p < off + 32 * (n + 1)
                  then S8.logxor (Seq.index vm p) (chunk_ks s0 c (p - off))
                  else Seq.index vo p))
      = assert (Seq.index v p ==
                 (if off <= p && p < off + 32 * n
                  then S8.logxor (Seq.index vm p) (chunk_ks s0 c (p - off))
                  else Seq.index vo p));
        if off + 32 * n <= p && p < off + 32 * n + 32 then begin
          let q = p - (off + 32 * n) in
          assert (Seq.index (V.vv x) q == chunk_ks s0 c (32 * n + q));
          assert (32 * n + q == p - off)
        end
    in
    Classical.forall_intro aux

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Exclusive-or [chunk_ks s0 c] into [msg[off .. off+512]], writing [out]. *)
inline_for_extraction
fn chunk_vec (out: A.array S8.t) (msg: A.array S8.t) (off: SZ.t)
             (st: A.array S32.t) (c: U32.t)
             (vst: A.array V.t) (ks: A.array V.t) (t: A.array V.t)
             (#vo: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
             (#ps: perm) (#s0: erased (Seq.seq S32.t))
             (#vv0 #vk0 #vt0: erased (Seq.seq V.t))
requires A.pts_to out vo ** A.pts_to msg #pm vm ** A.pts_to st #ps s0 **
         A.pts_to vst vv0 ** A.pts_to ks vk0 ** A.pts_to t vt0 **
         pure (Seq.length vo == Seq.length vm /\ SZ.v off + 512 <= Seq.length vm /\
               Seq.length s0 == 16 /\ U32.v c + 8 <= pow2 32 /\
               Seq.length vv0 == 16 /\ Seq.length vk0 == 16 /\ Seq.length vt0 == 16)
ensures exists* (vo': Seq.seq S8.t) (vv1 vk1 vt1: Seq.seq V.t).
  A.pts_to out vo' ** A.pts_to msg #pm vm ** A.pts_to st #ps s0 **
  A.pts_to vst vv1 ** A.pts_to ks vk1 ** A.pts_to t vt1 **
  pure (Seq.length vo == Seq.length vm /\ SZ.v off + 512 <= Seq.length vm /\
        Seq.length s0 == 16 /\ U32.v c + 8 <= pow2 32 /\
        Seq.length vv1 == 16 /\ Seq.length vk1 == 16 /\ Seq.length vt1 == 16 /\
        chunk_inv s0 c vo vm vo' (SZ.v off) 16)
{
  A.pts_to_len out;
  A.pts_to_len msg;
  init_vec vst st c;
  core_vec ks vst (G.hide (fun (j: nat { j < 8 }) -> with_counter s0 (lane_ctr c j)));
  with vk. assert (A.pts_to ks vk);
  assert (pure (forall (j: nat). j < 8 ==> lane_state vk j == core s0 (lane_ctr c j)));
  transpose t ks 0sz;
  with vt1. assert (A.pts_to t vt1);
  transpose t ks 1sz;
  with vt. assert (A.pts_to t vt);
  transpose_both (tr_ok vk) vt1 vt;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to msg #pm vm ** A.pts_to t vt **
    pure (chunk_inv s0 c vo vm v (SZ.v off) (SZ.v vi))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(t.(vi));
    let ob = SZ.add off (SZ.mul 32sz vi);
    with v. assert (A.pts_to out v);
    Classical.forall_intro (chunk_byte s0 c vk x (SZ.v vi));
    xor32 out msg ob x;
    with v'. assert (A.pts_to out v');
    chunk_step s0 c vo vm v v' (SZ.v off) (SZ.v vi) x;
    i := SZ.add vi 1sz;
  };
}

#pop-options

(** {2 The driver} *)

(** The first [n] bytes of [vo] are the specification's; shared with
    [Hacl.Chacha20.Vec512], whose prefix this path continues. *)
let encrypt_prefix = Hacl.Chacha20.Vec512.encrypt_prefix

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** One chunk's bytes are the specification's. *)
let mod512_64 (b: nat)
  : Lemma (requires b % 512 == 0) (ensures b % 64 == 0 /\ b == (b / 64) * 64)
  = let k = b / 512 in
    Math.euclidean_division_definition b 512;
    Math.paren_mul_right k 8 64;
    Math.cancel_mul_mod (k * 8) 64;
    Math.euclidean_division_definition b 64

let chunk_spec (st0: state) (ctr0: U32.t)
               (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
               (b: nat) (c: U32.t) (p: nat)
  : Lemma
      (requires b % 512 == 0 /\ b + 512 <= Seq.length msg /\
                U32.v c == U32.v ctr0 + b / 64 /\ U32.v c + 8 <= pow2 32 /\
                b <= p /\ p < b + 512)
      (ensures Seq.index (encrypt_bytes st0 ctr0 msg) p ==
               S8.logxor (Seq.index msg p) (chunk_ks st0 c (p - b)))
  = let q = p - b in
    div_lt size_block p (pow2 32 - U32.v ctr0);
    mod512_64 b;
    Math.lemma_div_plus q (b / 64) 64;
    Math.lemma_mod_plus q (b / 64) 64;
    assert (p / 64 == q / 64 + b / 64);
    assert (p % 64 == q % 64);
    assert (ctr_at ctr0 p == lane_ctr c (q / 64));
    assert (Seq.index (encrypt_bytes st0 ctr0 msg) p ==
            S8.logxor (Seq.index msg p) (ks_byte st0 ctr0 p))

let chunk_ext (st0: state) (ctr0: U32.t)
              (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
              (vo vo': Seq.seq S8.t) (b: nat) (c: U32.t)
  : Lemma
      (requires encrypt_prefix st0 ctr0 msg vo b /\
                b % 512 == 0 /\ b + 512 <= Seq.length msg /\
                U32.v c == U32.v ctr0 + b / 64 /\ U32.v c + 8 <= pow2 32 /\
                chunk_inv st0 c vo msg vo' b 16)
      (ensures encrypt_prefix st0 ctr0 msg vo' (b + 512))
  = let aux (p: nat { p < b + 512 })
      : Lemma (Seq.index vo' p == Seq.index (encrypt_bytes st0 ctr0 msg) p)
      = if b <= p then chunk_spec st0 ctr0 msg b c p
    in
    Classical.forall_intro aux

let chunk_ctr (ctr0: U32.t) (len: nat) (b: nat)
  : Lemma (requires len <= max_len ctr0 /\ b % 512 == 0 /\ b + 512 <= len)
          (ensures U32.v ctr0 + b / 64 + 8 <= pow2 32 /\ b / 64 < pow2 32 /\
                   (b + 512) % 512 == 0)
  = mod512_64 b;
    Math.lemma_div_plus b 8 64;
    Math.lemma_div_le (b + 512) len 64;
    Math.lemma_div_le len (max_len ctr0) 64;
    Math.cancel_mul_div (pow2 32 - U32.v ctr0) 64;
    Math.lemma_mod_plus b 1 512

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Given that [out] already holds the first [b0] bytes, encrypt on from
    there in 512-byte chunks for as long as a whole chunk remains, and say
    where it stopped.  [st] holds the initial state; its counter word is not
    read. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_prologue "__attribute__((target(\"avx2\")))" ""]
fn encrypt_blocks8 (out: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t)
                   (st: A.array S32.t) (ctr0: U32.t)
                   (st0: G.erased state) (b0: SZ.t)
                   (#vo: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
                   (#ps: perm)
requires A.pts_to out vo ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
         pure (Seq.length vo == Seq.length vm /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= max_len ctr0 /\
               SZ.v b0 % 512 == 0 /\ SZ.v b0 <= SZ.v mlen /\
               encrypt_prefix st0 ctr0 vm vo (SZ.v b0))
returns n: SZ.t
ensures exists* (vo': Seq.seq S8.t).
  A.pts_to out vo' ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
  pure (Seq.length vm <= max_len ctr0 /\
        SZ.v n % 512 == 0 /\ SZ.v n <= SZ.v mlen /\ SZ.v mlen - SZ.v n < 512 /\
        encrypt_prefix st0 ctr0 vm vo' (SZ.v n))
{
  A.pts_to_len out;
  A.pts_to_len msg;
  let z = V.zero ();
  let mut vst = [| z; 16sz |];
  let mut ks = [| z; 16sz |];
  let mut t = [| z; 16sz |];
  let mut base = b0;
  while (let b = !base; SZ.lte 512sz (SZ.sub mlen b))
  invariant exists* (b: SZ.t) (v: Seq.seq S8.t) (vv vk vt: Seq.seq V.t).
    pts_to base b ** A.pts_to out v ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
    A.pts_to vst vv ** A.pts_to ks vk ** A.pts_to t vt **
    pure (Seq.length vm <= max_len ctr0 /\ Seq.length vm == SZ.v mlen /\
          Seq.length vv == 16 /\ Seq.length vk == 16 /\ Seq.length vt == 16 /\
          SZ.v b % 512 == 0 /\ SZ.v b <= SZ.v mlen /\
          encrypt_prefix st0 ctr0 vm v (SZ.v b))
  decreases (SZ.v mlen - SZ.v (!base))
  {
    let b = !base;
    with v. assert (A.pts_to out v);
    chunk_ctr ctr0 (SZ.v mlen) (SZ.v b);
    let c = U32.add ctr0 (SZ.sizet_to_uint32 (SZ.div b 64sz));
    A.pts_to_len vst;
    A.pts_to_len ks;
    A.pts_to_len t;
    chunk_vec out msg b st c vst ks t;
    with v'. assert (A.pts_to out v');
    Math.small_mod (SZ.v b / 64) (pow2 32);
    assert (pure (U32.v (SZ.sizet_to_uint32 (SZ.div b 64sz)) == SZ.v b / 64));
    assert (pure (U32.v c == U32.v ctr0 + SZ.v b / 64));
    assert (pure (U32.v c + 8 <= pow2 32));
    assert (pure (encrypt_prefix st0 ctr0 vm v (SZ.v b)));
    assert (pure (chunk_inv st0 c v vm v' (SZ.v b) 16));
    chunk_ext st0 ctr0 vm v v' (SZ.v b) c;
    base := SZ.add b 512sz;
  };
  let n = !base;
  n
}

#pop-options

(** {2 Dispatch} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let mod1024_512 (n: nat)
  : Lemma (requires n % 1024 == 0) (ensures n % 512 == 0)
  = Math.euclidean_division_definition n 1024;
    Math.paren_mul_right (n / 1024) 2 512;
    Math.cancel_mul_mod (n / 1024 * 2) 512

let blocks8_facts (ctr0: U32.t) (len: nat) (n: nat)
  : Lemma (requires len <= max_len ctr0 /\ n % 512 == 0 /\ n <= len)
          (ensures n % size_block == 0 /\
                   (n < len ==> U32.v ctr0 + n / size_block < pow2 32))
  = mod512_64 n;
    if n < len then div_lt size_block n (pow2 32 - U32.v ctr0)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Sixteen blocks at a time when the processor has AVX-512F; nothing
    otherwise. *)
inline_for_extraction
fn encrypt_avx512 (out: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t)
                  (st: A.array S32.t) (ctr0: U32.t)
                  (st0: G.erased state)
                  (#vo: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
                  (#ps: perm)
requires A.pts_to out vo ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
         pure (Seq.length vo == Seq.length vm /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= max_len ctr0)
returns n: SZ.t
ensures exists* (vo': Seq.seq S8.t).
  A.pts_to out vo' ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
  pure (Seq.length vm <= max_len ctr0 /\ Seq.length vo' == Seq.length vm /\
        Seq.length vm == SZ.v mlen /\
        SZ.v n % 512 == 0 /\ SZ.v n <= SZ.v mlen /\
        encrypt_prefix st0 ctr0 vm vo' (SZ.v n))
{
  A.pts_to_len out;
  if (SZ.lte 1024sz mlen && Hacl.Vec512.supported ()) {
    let n = Hacl.Chacha20.Vec512.encrypt_blocks16 out msg mlen st ctr0 st0;
    mod1024_512 (SZ.v n);
    with v1. assert (A.pts_to out v1);
    A.pts_to_len out;
    n
  } else {
    0sz
  }
}

(** The vector paths, as far as the processor allows, and nothing on a
    processor with neither.  Sixteen blocks at a time with AVX-512F, then
    eight at a time with AVX2 while a whole 512 bytes remain.  Messages
    shorter than one 512-byte chunk do not go near either.  Returns how many
    leading bytes of [out] it wrote, a whole number of blocks; the caller does
    the rest one block at a time, from block counter [ctr0 + n / 64].  This
    function itself is compiled for the baseline target, so that the
    [supported] tests run everywhere. *)
fn encrypt_vec (out: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t)
               (st: A.array S32.t) (ctr0: U32.t)
               (st0: G.erased state)
               (#vo: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
               (#ps: perm)
requires A.pts_to out vo ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
         pure (Seq.length vo == Seq.length vm /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= max_len ctr0)
returns n: SZ.t
ensures exists* (vo': Seq.seq S8.t).
  A.pts_to out vo' ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
  pure (Seq.length vm <= max_len ctr0 /\ Seq.length vo' == Seq.length vm /\
        Seq.length vm == SZ.v mlen /\
        SZ.v n <= SZ.v mlen /\ SZ.v n % size_block == 0 /\
        (SZ.v n < SZ.v mlen ==> U32.v ctr0 + SZ.v n / size_block < pow2 32) /\
        (forall (p: nat). p < SZ.v n ==>
           Seq.index vo' p == Seq.index (encrypt_bytes st0 ctr0 vm) p))
{
  A.pts_to_len out;
  if (SZ.lte 512sz mlen) {
    let n1 = encrypt_avx512 out msg mlen st ctr0 st0;
    with v1. assert (A.pts_to out v1);
    A.pts_to_len out;
    if (V.supported ()) {
      let n = encrypt_blocks8 out msg mlen st ctr0 st0 n1;
      blocks8_facts ctr0 (SZ.v mlen) (SZ.v n);
      n
    } else {
      blocks8_facts ctr0 (SZ.v mlen) (SZ.v n1);
      n1
    }
  } else {
    0sz
  }
}

#pop-options
