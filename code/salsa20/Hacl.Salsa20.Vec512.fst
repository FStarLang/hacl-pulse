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

(** Salsa20, sixteen blocks at a time, on AVX-512F.

    {2 The shape}

    [Hacl.Chacha20.Vec512] with Salsa20's round: vector [i] holds word [i]
    of sixteen consecutive blocks, one per lane, every round function is the
    scalar one with every word replaced by a vector, and every postcondition
    says that lane [j] has advanced by one step of [Spec.Salsa20].  Salsa20's
    quarter round, [a ^= (b + c) <<< s], wants its rotations at 7, 9, 13 and
    18 bits, none a whole number of bytes; [VPROLD] does each in one
    instruction, where AVX2 needs three.  The counter is word 8 rather than
    12.  The 16 x 16 transpose and everything after it are ChaCha20's
    unchanged, because the keystream is serialized the same way.

    {2 Where it is called}

    [Hacl.Salsa20.Vec256.encrypt_vec] calls [encrypt_blocks16] when
    [Hacl.Vec512.supported] says the machine has AVX-512F; it consumes every
    whole multiple of 1024 bytes, and the eight-way AVX2 path and then the
    scalar loop continue from where it stopped. *)
module Hacl.Salsa20.Vec512

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Spec.Salsa20

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U32 = FStar.UInt32
module G = FStar.Ghost
module V = Hacl.Vec512
module Sub = Hacl.Impl.Sub
module Classical = FStar.Classical

(** {2 Looking down a lane} *)

let vstate = s: Seq.seq V.t { Seq.length s == 16 }

let lane_state (vs: vstate) (j: nat { j < 16 }) : GTot state =
  Seq.init_ghost 16 (fun i -> V.lane (Seq.index vs i) j)

let lane_state_index (vs: vstate) (j: nat { j < 16 }) (i: nat { i < 16 })
  : Lemma (Seq.index (lane_state vs j) i == V.lane (Seq.index vs i) j)
          [SMTPat (Seq.index (lane_state vs j) i)]
  = ()

(** Every lane of [v1] is [f] of the same lane of [v0]. *)
let lanes_step (v0 v1: vstate) (f: state -> state) : prop =
  forall (j: nat). j < 16 ==> lane_state v1 j == f (lane_state v0 j)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** The vector form of [Spec.Salsa20.line], in the order the code does it. *)
let line_v (v0: vstate) (a b d: idx) (s: rotval) : GTot vstate =
  let x = V.rotl (V.add32 (Seq.index v0 b) (Seq.index v0 d)) s in
  Seq.upd v0 a (V.vxor (Seq.index v0 a) x)

let line_lanes (v0: vstate) (a b d: idx) (s: rotval)
  : Lemma (lanes_step v0 (line_v v0 a b d s) (line a b d s))
  = let v1 = line_v v0 a b d s in
    let aux (j: nat { j < 16 })
      : Lemma (lane_state v1 j == line a b d s (lane_state v0 j))
      = Seq.lemma_eq_intro (lane_state v1 j) (line a b d s (lane_state v0 j))
    in
    Classical.forall_intro aux

let lanes_step_trans (v0 v1 v2: vstate) (f g: state -> state)
  : Lemma (requires lanes_step v0 v1 f /\ lanes_step v1 v2 g)
          (ensures lanes_step v0 v2 (fun m -> g (f m)))
  = ()

#pop-options

(** {2 The round function, on sixteen lanes}

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
  let rb = A.(st.(b));
  let rd = A.(st.(d));
  let x = V.rotl (V.add32 rb rd) s;
  let ra = A.(st.(a));
  A.((st.(a) <- V.vxor ra x));
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
  line_vec st b a d 7ul;
  line_vec st c b a 9ul;
  line_vec st d c b 13ul;
  line_vec st a d c 18ul;
}

inline_for_extraction
fn column_round_vec (st: A.array V.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ lanes_step v0 v1 column_round)
{
  quarter_round_vec st  0sz  4sz  8sz 12sz;
  quarter_round_vec st  5sz  9sz 13sz  1sz;
  quarter_round_vec st 10sz 14sz  2sz  6sz;
  quarter_round_vec st 15sz  3sz  7sz 11sz;
}

inline_for_extraction
fn row_round_vec (st: A.array V.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ lanes_step v0 v1 row_round)
{
  quarter_round_vec st  0sz  1sz  2sz  3sz;
  quarter_round_vec st  5sz  6sz  7sz  4sz;
  quarter_round_vec st 10sz 11sz  8sz  9sz;
  quarter_round_vec st 15sz 12sz 13sz 14sz;
}

inline_for_extraction
fn double_round_vec (st: A.array V.t) (#v0: erased (Seq.seq V.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == 16)
ensures exists* (v1: Seq.seq V.t). A.pts_to st v1 **
  pure (Seq.length v0 == 16 /\ Seq.length v1 == 16 /\ lanes_step v0 v1 double_round)
{
  column_round_vec st;
  row_round_vec st;
}

#pop-options

let rounds_upto (k: nat) (m: state) : state = repeati k (fun _ m -> double_round m) m

let rounds_upto_step (v0 v v': vstate) (k: nat)
  : Lemma (requires (forall (j: nat). j < 16 ==> lane_state v j == rounds_upto k (lane_state v0 j)) /\
                    lanes_step v v' double_round)
          (ensures forall (j: nat). j < 16 ==> lane_state v' j == rounds_upto (k + 1) (lane_state v0 j))
  = let aux (j: nat { j < 16 })
      : Lemma (lane_state v' j == rounds_upto (k + 1) (lane_state v0 j))
      = unfold_repeati k (fun _ m -> double_round m) (lane_state v0 j)
    in
    Classical.forall_intro aux

let rounds_upto_zero (v0: vstate)
  : Lemma (forall (j: nat). j < 16 ==> lane_state v0 j == rounds_upto 0 (lane_state v0 j))
  = let aux (j: nat { j < 16 })
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
          (forall (j: nat). j < 16 ==> lane_state v j == rounds_upto (SZ.v vi) (lane_state v0 j)))
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
let lane_ctr (c: U32.t { U32.v c + 16 <= pow2 32 }) (j: nat { j < 16 }) : U32.t =
  U32.uint_to_t (U32.v c + j)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"

let init_lanes (s0: state) (c: U32.t { U32.v c + 16 <= pow2 32 }) (vs: vstate)
  : Lemma
      (requires
        (forall (i: nat). i < 16 /\ i <> 8 ==>
           (forall (j: nat). j < 16 ==> V.lane (Seq.index vs i) j == Seq.index s0 i)) /\
        (forall (j: nat). j < 16 ==> S32.v (V.lane (Seq.index vs 8) j) == U32.v c + j))
      (ensures forall (j: nat). j < 16 ==> lane_state vs j == with_counter s0 (lane_ctr c j))
  = let aux (j: nat { j < 16 })
      : Lemma (lane_state vs j == with_counter s0 (lane_ctr c j))
      = Seq.lemma_eq_intro (lane_state vs j) (with_counter s0 (lane_ctr c j))
    in
    Classical.forall_intro aux

let ctr_lanes (c: U32.t { U32.v c + 16 <= pow2 32 }) (cb io: V.t)
  : Lemma (requires (forall (i: nat). i < 16 ==> V.lane cb i == S32.classify c) /\
                    (forall (i: nat). i < 16 ==> S32.v (V.lane io i) == i))
          (ensures forall (j: nat). j < 16 ==> S32.v (V.lane (V.add32 cb io) j) == U32.v c + j)
  = let aux (j: nat { j < 16 })
      : Lemma (S32.v (V.lane (V.add32 cb io) j) == U32.v c + j)
      = Math.small_mod (U32.v c + j) (pow2 32)
    in
    Classical.forall_intro aux

let set8_lanes (s0: state) (c: U32.t { U32.v c + 16 <= pow2 32 }) (v: vstate) (cv: V.t)
  : Lemma (requires (forall (k: nat). k < 16 ==>
             (forall (j: nat). j < 16 ==> V.lane (Seq.index v k) j == Seq.index s0 k)) /\
             (forall (j: nat). j < 16 ==> S32.v (V.lane cv j) == U32.v c + j))
          (ensures forall (j: nat). j < 16 ==>
             lane_state (Seq.upd v 8 cv) j == with_counter s0 (lane_ctr c j))
  = init_lanes s0 c (Seq.upd v 8 cv)

(** Lane [j] of [vst] is the state of block [c + j]. *)
inline_for_extraction
fn init_vec (vst: A.array V.t) (st: A.array S32.t) (c: U32.t)
            (#vv0: erased (Seq.seq V.t)) (#ps: perm) (#s0: erased (Seq.seq S32.t))
requires A.pts_to vst vv0 ** A.pts_to st #ps s0 **
         pure (Seq.length vv0 == 16 /\ Seq.length s0 == 16 /\ U32.v c + 16 <= pow2 32)
ensures exists* (vv1: Seq.seq V.t). A.pts_to vst vv1 ** A.pts_to st #ps s0 **
  pure (Seq.length s0 == 16 /\ U32.v c + 16 <= pow2 32 /\ Seq.length vv1 == 16 /\
        (forall (j: nat). j < 16 ==> lane_state vv1 j == with_counter s0 (lane_ctr c j)))
{
  A.pts_to_len vst;
  A.pts_to_len st;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq V.t).
    pts_to i vi ** A.pts_to vst v ** A.pts_to st #ps s0 **
    pure (SZ.v vi <= 16 /\ Seq.length v == 16 /\ Seq.length s0 == 16 /\
          (forall (k: nat). k < SZ.v vi ==>
             (forall (j: nat). j < 16 ==> V.lane (Seq.index v k) j == Seq.index s0 k)))
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
  set8_lanes s0 c v cv;
  A.((vst.(8sz) <- cv));
}

let core_lanes (vst ks1 ks2: vstate) (f: (j: nat { j < 16 }) -> GTot state)
  : Lemma
      (requires
        (forall (j: nat). j < 16 ==> lane_state vst j == f j) /\
        lanes_step vst ks1 rounds /\
        (forall (i: nat). i < 16 ==>
           Seq.index ks2 i == V.add32 (Seq.index ks1 i) (Seq.index vst i)))
      (ensures forall (j: nat). j < 16 ==> lane_state ks2 j == core_of (f j))
  = let aux (j: nat { j < 16 })
      : Lemma (lane_state ks2 j == core_of (f j))
      = Seq.lemma_eq_intro (lane_state ks2 j) (core_of (f j))
    in
    Classical.forall_intro aux

(** [ks] gets the sixteen keystream blocks, one per lane, before
    serialization; [vst] is left alone. *)
inline_for_extraction
fn core_vec (ks: A.array V.t) (vst: A.array V.t)
            (f: G.erased ((j: nat { j < 16 }) -> GTot state))
            (#vk0: erased (Seq.seq V.t)) (#vs: erased (Seq.seq V.t))
requires A.pts_to ks vk0 ** A.pts_to vst vs **
         pure (Seq.length vk0 == 16 /\ Seq.length vs == 16 /\
               (forall (j: nat). j < 16 ==> lane_state vs j == G.reveal f j))
ensures exists* (vk1: Seq.seq V.t). A.pts_to ks vk1 ** A.pts_to vst vs **
  pure (Seq.length vs == 16 /\ Seq.length vk1 == 16 /\
        (forall (j: nat). j < 16 ==> lane_state vk1 j == core_of (G.reveal f j)))
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
  assert (pure (forall (j: nat). j < 16 ==> lane_state vs j == G.reveal f j));
  assert (pure (lanes_step vs k1 rounds));
  assert (pure (forall (i: nat). i < 16 ==>
           Seq.index k2 i == V.add32 (Seq.index k1 i) (Seq.index vs i)));
  core_lanes vs k1 k2 f;
  assert (pure (forall (j: nat). j < 16 ==> lane_state k2 j == core_of (G.reveal f j)));
  assert (pure (Seq.length k2 == 16));
}

#pop-options

(** {2 From lanes to bytes} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** A register's bytes are its lanes, written out little-endian. *)
let vv_lanes (x: V.t) (q: nat { q < 64 })
  : Lemma (Seq.index (V.vv x) q ==
           Seq.index (word_to_le #S32.t (V.lane x (q / 4))) (q % 4))
  = let sb = sub_block #S32.t 16 (V.vv x) (q / 4) in
    le_nat_bound sb;
    le_nat_byte sb (q % 4);
    nat_to_le_index 4 (le_nat sb) (q % 4);
    Math.euclidean_division_definition q 4;
    S8.v_extensional (Seq.index (V.vv x) q)
                     (Seq.index (word_to_le #S32.t (V.lane x (q / 4))) (q % 4))

#pop-options

(** {2 The transpose}

    Row [w] of [ks] holds word [w] of sixteen blocks, a block per lane; the
    transpose leaves block [j] in register [j], whole.  It is done in two
    steps of two rounds each.  The first works on each quad of rows
    [4q .. 4q+3] separately, and transposes it within every 128-bit group,
    exactly as the first two rounds of the AVX2 transpose do; register
    [4q + m] then holds, in group [g], words [4q .. 4q+3] of block [4g + m].
    The second step moves whole groups: block [4g + m] is group [g] of
    registers [m], [4 + m], [8 + m] and [12 + m], in that order. *)

let tr_ok (vk: vstate) (x: V.t) (j: nat { j < 16 }) : prop =
  forall (w: nat). w < 16 ==> V.lane x w == V.lane (Seq.index vk w) j

(** Register [x] is quad [q], in-group position [m], of the first step. *)
let qa_ok (vk: vstate) (q: nat { q < 4 }) (x: V.t) (m: nat { m < 4 }) : prop =
  forall (g k: nat). g < 4 /\ k < 4 ==>
    V.lane x (4 * g + k) == V.lane (Seq.index vk (4 * q + k)) (4 * g + m)

(** Register [x] is group [g] of registers [m], [4 + m], [8 + m], [12 + m]. *)
let qb_ok (vu: vstate) (g: nat { g < 4 }) (x: V.t) (m: nat { m < 4 }) : prop =
  forall (q k: nat). q < 4 /\ k < 4 ==>
    V.lane x (4 * q + k) == V.lane (Seq.index vu (4 * q + m)) (4 * g + k)

let all16 (p: (i: nat { i < 16 }) -> prop)
  : Lemma (requires p 0 /\ p 1 /\ p 2 /\ p 3 /\ p 4 /\ p 5 /\ p 6 /\ p 7 /\
                    p 8 /\ p 9 /\ p 10 /\ p 11 /\ p 12 /\ p 13 /\ p 14 /\ p 15)
          (ensures forall (i: nat { i < 16 }). p i)
  = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let qa_intro (vk: vstate) (q: nat { q < 4 }) (x: V.t) (m: nat { m < 4 })
  : Lemma (requires
             (let r (k: nat { k < 4 }) = Seq.index vk (4 * q + k) in
              V.lane x 0 == V.lane (r 0) m /\ V.lane x 1 == V.lane (r 1) m /\
              V.lane x 2 == V.lane (r 2) m /\ V.lane x 3 == V.lane (r 3) m /\
              V.lane x 4 == V.lane (r 0) (4 + m) /\ V.lane x 5 == V.lane (r 1) (4 + m) /\
              V.lane x 6 == V.lane (r 2) (4 + m) /\ V.lane x 7 == V.lane (r 3) (4 + m) /\
              V.lane x 8 == V.lane (r 0) (8 + m) /\ V.lane x 9 == V.lane (r 1) (8 + m) /\
              V.lane x 10 == V.lane (r 2) (8 + m) /\ V.lane x 11 == V.lane (r 3) (8 + m) /\
              V.lane x 12 == V.lane (r 0) (12 + m) /\ V.lane x 13 == V.lane (r 1) (12 + m) /\
              V.lane x 14 == V.lane (r 2) (12 + m) /\ V.lane x 15 == V.lane (r 3) (12 + m)))
          (ensures qa_ok vk q x m)
  = ()

let qb_intro (vu: vstate) (g: nat { g < 4 }) (x: V.t) (m: nat { m < 4 })
  : Lemma (requires
             (let r (q: nat { q < 4 }) = Seq.index vu (4 * q + m) in
              V.lane x 0 == V.lane (r 0) (4 * g) /\ V.lane x 1 == V.lane (r 0) (4 * g + 1) /\
              V.lane x 2 == V.lane (r 0) (4 * g + 2) /\ V.lane x 3 == V.lane (r 0) (4 * g + 3) /\
              V.lane x 4 == V.lane (r 1) (4 * g) /\ V.lane x 5 == V.lane (r 1) (4 * g + 1) /\
              V.lane x 6 == V.lane (r 1) (4 * g + 2) /\ V.lane x 7 == V.lane (r 1) (4 * g + 3) /\
              V.lane x 8 == V.lane (r 2) (4 * g) /\ V.lane x 9 == V.lane (r 2) (4 * g + 1) /\
              V.lane x 10 == V.lane (r 2) (4 * g + 2) /\ V.lane x 11 == V.lane (r 2) (4 * g + 3) /\
              V.lane x 12 == V.lane (r 3) (4 * g) /\ V.lane x 13 == V.lane (r 3) (4 * g + 1) /\
              V.lane x 14 == V.lane (r 3) (4 * g + 2) /\ V.lane x 15 == V.lane (r 3) (4 * g + 3)))
          (ensures qb_ok vu g x m)
  = ()

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The first step, for quad [q]: [u.(4q + m)] gets [qa_ok vk q _ m]. *)
inline_for_extraction
fn transpose_a (u: A.array V.t) (ks: A.array V.t) (q: SZ.t)
               (#vu: erased (Seq.seq V.t)) (#vk: erased (Seq.seq V.t))
requires A.pts_to u vu ** A.pts_to ks vk **
         pure (Seq.length vu == 16 /\ Seq.length vk == 16 /\ SZ.v q < 4)
ensures exists* (vu': Seq.seq V.t). A.pts_to u vu' ** A.pts_to ks vk **
  pure (Seq.length vu == 16 /\ Seq.length vk == 16 /\ SZ.v q < 4 /\
        Seq.length vu' == 16 /\
        (forall (m: nat). m < 4 ==> qa_ok vk (SZ.v q) (Seq.index vu' (4 * SZ.v q + m)) m) /\
        (forall (i: nat). i < 16 /\ (i < 4 * SZ.v q \/ 4 * SZ.v q + 4 <= i) ==>
           Seq.index vu' i == Seq.index vu i))
{
  A.pts_to_len u;
  A.pts_to_len ks;
  let o = SZ.mul 4sz q;
  let r0 = A.(ks.(o));
  let r1 = A.(ks.(SZ.add o 1sz));
  let r2 = A.(ks.(SZ.add o 2sz));
  let r3 = A.(ks.(SZ.add o 3sz));
  let a0 = V.unpacklo32 r0 r1;
  let a1 = V.unpackhi32 r0 r1;
  let a2 = V.unpacklo32 r2 r3;
  let a3 = V.unpackhi32 r2 r3;
  let b0 = V.unpacklo64 a0 a2;
  let b1 = V.unpackhi64 a0 a2;
  let b2 = V.unpacklo64 a1 a3;
  let b3 = V.unpackhi64 a1 a3;
  qa_intro vk (SZ.v q) b0 0;
  qa_intro vk (SZ.v q) b1 1;
  qa_intro vk (SZ.v q) b2 2;
  qa_intro vk (SZ.v q) b3 3;
  A.((u.(o) <- b0));
  A.((u.(SZ.add o 1sz) <- b1));
  A.((u.(SZ.add o 2sz) <- b2));
  A.((u.(SZ.add o 3sz) <- b3));
}

(** The second step, for position [m]: [t.(4g + m)] gets [qb_ok vu g _ m]. *)
inline_for_extraction
fn transpose_b (t: A.array V.t) (u: A.array V.t) (m: SZ.t)
               (#vt: erased (Seq.seq V.t)) (#vu: erased (Seq.seq V.t))
requires A.pts_to t vt ** A.pts_to u vu **
         pure (Seq.length vt == 16 /\ Seq.length vu == 16 /\ SZ.v m < 4)
ensures exists* (vt': Seq.seq V.t). A.pts_to t vt' ** A.pts_to u vu **
  pure (Seq.length vt == 16 /\ Seq.length vu == 16 /\ SZ.v m < 4 /\
        Seq.length vt' == 16 /\
        (forall (g: nat). g < 4 ==> qb_ok vu g (Seq.index vt' (4 * g + SZ.v m)) (SZ.v m)) /\
        (forall (g k: nat). g < 4 /\ k < 4 /\ k <> SZ.v m ==>
           Seq.index vt' (4 * g + k) == Seq.index vt (4 * g + k)))
{
  A.pts_to_len t;
  A.pts_to_len u;
  let r0 = A.(u.(m));
  let r1 = A.(u.(SZ.add m 4sz));
  let r2 = A.(u.(SZ.add m 8sz));
  let r3 = A.(u.(SZ.add m 12sz));
  let c0 = V.sel_lo r0 r1;
  let c1 = V.sel_hi r0 r1;
  let c2 = V.sel_lo r2 r3;
  let c3 = V.sel_hi r2 r3;
  let x0 = V.sel_even c0 c2;
  let x1 = V.sel_odd c0 c2;
  let x2 = V.sel_even c1 c3;
  let x3 = V.sel_odd c1 c3;
  qb_intro vu 0 x0 (SZ.v m);
  qb_intro vu 1 x1 (SZ.v m);
  qb_intro vu 2 x2 (SZ.v m);
  qb_intro vu 3 x3 (SZ.v m);
  A.((t.(m) <- x0));
  A.((t.(SZ.add m 4sz) <- x1));
  A.((t.(SZ.add m 8sz) <- x2));
  A.((t.(SZ.add m 12sz) <- x3));
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The two steps compose to the transpose.  Abstract in the predicates, so
    that the solver does not unfold them where it does not need to. *)
let qa_all (vk vu: vstate) : prop =
  forall (q m: nat). q < 4 /\ m < 4 ==> qa_ok vk q (Seq.index vu (4 * q + m)) m

let qb_all (vu vt: vstate) : prop =
  forall (g m: nat). g < 4 /\ m < 4 ==> qb_ok vu g (Seq.index vt (4 * g + m)) m

let compose_one (vk vu: vstate) (x: V.t) (g m: (n: nat { n < 4 }))
  : Lemma (requires qa_all vk vu /\ qb_ok vu g x m)
          (ensures tr_ok vk x (4 * g + m))
  = let aux (w: nat { w < 16 })
      : Lemma (V.lane x w == V.lane (Seq.index vk w) (4 * g + m))
      = let q = w / 4 in
        let k = w % 4 in
        Math.euclidean_division_definition w 4;
        assert (V.lane x (4 * q + k) == V.lane (Seq.index vu (4 * q + m)) (4 * g + k));
        assert (qa_ok vk q (Seq.index vu (4 * q + m)) m)
    in
    Classical.forall_intro aux

let compose (vk vu vt: vstate)
  : Lemma (requires qa_all vk vu /\ qb_all vu vt)
          (ensures forall (j: nat). j < 16 ==> tr_ok vk (Seq.index vt j) j)
  = let aux (j: nat { j < 16 })
      : Lemma (tr_ok vk (Seq.index vt j) j)
      = let g = j / 4 in
        let m = j % 4 in
        Math.euclidean_division_definition j 4;
        compose_one vk vu (Seq.index vt (4 * g + m)) g m
    in
    Classical.forall_intro aux

(** Four calls of a step, each touching its own quarter, add up. *)
let qa_collect (vk: vstate) (u0 u1 u2 u3 u4: vstate)
  : Lemma
      (requires
        (forall (m: nat). m < 4 ==> qa_ok vk 0 (Seq.index u1 m) m) /\
        (forall (i: nat). i < 16 /\ (i < 0 \/ 4 <= i) ==> Seq.index u1 i == Seq.index u0 i) /\
        (forall (m: nat). m < 4 ==> qa_ok vk 1 (Seq.index u2 (4 + m)) m) /\
        (forall (i: nat). i < 16 /\ (i < 4 \/ 8 <= i) ==> Seq.index u2 i == Seq.index u1 i) /\
        (forall (m: nat). m < 4 ==> qa_ok vk 2 (Seq.index u3 (8 + m)) m) /\
        (forall (i: nat). i < 16 /\ (i < 8 \/ 12 <= i) ==> Seq.index u3 i == Seq.index u2 i) /\
        (forall (m: nat). m < 4 ==> qa_ok vk 3 (Seq.index u4 (12 + m)) m) /\
        (forall (i: nat). i < 16 /\ (i < 12 \/ 16 <= i) ==> Seq.index u4 i == Seq.index u3 i))
      (ensures qa_all vk u4)
  = let aux (q m: nat)
      : Lemma (q < 4 /\ m < 4 ==> qa_ok vk q (Seq.index u4 (4 * q + m)) m)
      = ()
    in
    Classical.forall_intro_2 aux

let qb_collect (vu: vstate) (t0 t1 t2 t3 t4: vstate)
  : Lemma
      (requires
        (forall (g: nat). g < 4 ==> qb_ok vu g (Seq.index t1 (4 * g)) 0) /\
        (forall (g k: nat). g < 4 /\ k < 4 /\ k <> 0 ==>
           Seq.index t1 (4 * g + k) == Seq.index t0 (4 * g + k)) /\
        (forall (g: nat). g < 4 ==> qb_ok vu g (Seq.index t2 (4 * g + 1)) 1) /\
        (forall (g k: nat). g < 4 /\ k < 4 /\ k <> 1 ==>
           Seq.index t2 (4 * g + k) == Seq.index t1 (4 * g + k)) /\
        (forall (g: nat). g < 4 ==> qb_ok vu g (Seq.index t3 (4 * g + 2)) 2) /\
        (forall (g k: nat). g < 4 /\ k < 4 /\ k <> 2 ==>
           Seq.index t3 (4 * g + k) == Seq.index t2 (4 * g + k)) /\
        (forall (g: nat). g < 4 ==> qb_ok vu g (Seq.index t4 (4 * g + 3)) 3) /\
        (forall (g k: nat). g < 4 /\ k < 4 /\ k <> 3 ==>
           Seq.index t4 (4 * g + k) == Seq.index t3 (4 * g + k)))
      (ensures qb_all vu t4)
  = let aux (g m: nat)
      : Lemma (g < 4 /\ m < 4 ==> qb_ok vu g (Seq.index t4 (4 * g + m)) m)
      = ()
    in
    Classical.forall_intro_2 aux

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

inline_for_extraction
fn transpose (t: A.array V.t) (u: A.array V.t) (ks: A.array V.t)
             (#vt: erased (Seq.seq V.t)) (#vu: erased (Seq.seq V.t))
             (#vk: erased (Seq.seq V.t))
requires A.pts_to t vt ** A.pts_to u vu ** A.pts_to ks vk **
         pure (Seq.length vt == 16 /\ Seq.length vu == 16 /\ Seq.length vk == 16)
ensures exists* (vt' vu': Seq.seq V.t). A.pts_to t vt' ** A.pts_to u vu' ** A.pts_to ks vk **
  pure (Seq.length vk == 16 /\ Seq.length vt' == 16 /\ Seq.length vu' == 16 /\
        (forall (j: nat). j < 16 ==> tr_ok vk (Seq.index vt' j) j))
{
  with u0. assert (A.pts_to u u0);
  transpose_a u ks 0sz;
  with u1. assert (A.pts_to u u1);
  transpose_a u ks 1sz;
  with u2. assert (A.pts_to u u2);
  transpose_a u ks 2sz;
  with u3. assert (A.pts_to u u3);
  transpose_a u ks 3sz;
  with u4. assert (A.pts_to u u4);
  qa_collect vk u0 u1 u2 u3 u4;
  with t0. assert (A.pts_to t t0);
  transpose_b t u 0sz;
  with t1. assert (A.pts_to t t1);
  transpose_b t u 1sz;
  with t2. assert (A.pts_to t t2);
  transpose_b t u 2sz;
  with t3. assert (A.pts_to t t3);
  transpose_b t u 3sz;
  with t4. assert (A.pts_to t t4);
  qb_collect u4 t0 t1 t2 t3 t4;
  compose vk u4 t4;
}

#pop-options

(** {2 Sixty-four bytes of message} *)

let as64 (s: Seq.seq S8.t { Seq.length s == 64 })
  : Pure (Seq.lseq S8.t 64) (requires True) (ensures fun r -> r == s)
  = s

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

inline_for_extraction
fn xor64 (out: A.array S8.t) (msg: A.array S8.t) (o: SZ.t) (x: V.t)
         (#vo: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to msg #pm vm **
         pure (Seq.length vo == Seq.length vm /\ SZ.v o + 64 <= Seq.length vm)
ensures exists* (vo': Seq.seq S8.t). A.pts_to out vo' ** A.pts_to msg #pm vm **
  pure (Seq.length vo == Seq.length vm /\ SZ.v o + 64 <= Seq.length vm /\
        Seq.length vo' == Seq.length vo /\
        (forall (p: nat). p < Seq.length vo ==>
           Seq.index vo' p ==
             (if SZ.v o <= p && p < SZ.v o + 64
              then S8.logxor (Seq.index vm p) (Seq.index (V.vv x) (p - SZ.v o))
              else Seq.index vo p)))
{
  A.pts_to_len out;
  A.pts_to_len msg;
  let o2 = SZ.add o 64sz;
  let mb = Sub.sub msg o o2;
  let mv = V.load mb #(as64 (Seq.slice vm (SZ.v o) (SZ.v o2)));
  Sub.unsub_id msg (SZ.v o) (SZ.v o2) mb;
  let r = V.vxor mv x;
  let ob = Sub.sub out o o2;
  V.store ob r #(as64 (Seq.slice vo (SZ.v o) (SZ.v o2)));
  Sub.unsub out (SZ.v o) (SZ.v o2) ob;
  ()
}

#pop-options

(** {2 A thousand and twenty-four bytes}

    The keystream that block [j] of a chunk exclusive-ors in. *)

let chunk_ks (s0: state) (c: U32.t { U32.v c + 16 <= pow2 32 }) (q: nat { q < 1024 }) : GTot S8.t =
  Seq.index (keystream s0 (lane_ctr c (q / 64))) (q % 64)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let chunk_byte (s0: state) (c: U32.t { U32.v c + 16 <= pow2 32 })
               (vk: vstate) (x: V.t) (i: nat { i < 16 }) (q: nat { q < 64 })
  : Lemma
      (requires
        (forall (j: nat). j < 16 ==> lane_state vk j == core s0 (lane_ctr c j)) /\
        tr_ok vk x i)
      (ensures Seq.index (V.vv x) q == chunk_ks s0 c (64 * i + q))
  = let w = core s0 (lane_ctr c i) in
    vv_lanes x q;
    assert (V.lane x (q / 4) == Seq.index (lane_state vk i) (q / 4));
    Math.lemma_div_plus q i 64;
    Math.lemma_mod_plus q i 64;
    Math.small_div q 64;
    Math.small_mod q 64;
    assert ((64 * i + q) / 64 == i);
    assert ((64 * i + q) % 64 == q);
    assert (Seq.index (keystream s0 (lane_ctr c i)) q ==
            Seq.index (word_to_le #S32.t (Seq.index w (q / 4))) (q % 4))

#pop-options

let chunk_inv (s0: state) (c: U32.t { U32.v c + 16 <= pow2 32 })
              (vo vm v: Seq.seq S8.t) (off: nat) (n: nat) : prop =
  Seq.length v == Seq.length vo /\ Seq.length vo == Seq.length vm /\
  off + 1024 <= Seq.length vm /\ n <= 16 /\
  (forall (p: nat). p < Seq.length vo ==>
     Seq.index v p ==
       (if off <= p && p < off + 64 * n
        then S8.logxor (Seq.index vm p) (chunk_ks s0 c (p - off))
        else Seq.index vo p))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let chunk_step (s0: state) (c: U32.t { U32.v c + 16 <= pow2 32 })
               (vo vm v v': Seq.seq S8.t) (off: nat) (n: nat { n < 16 }) (x: V.t)
  : Lemma
      (requires
        chunk_inv s0 c vo vm v off n /\
        (forall (q: nat). q < 64 ==> Seq.index (V.vv x) q == chunk_ks s0 c (64 * n + q)) /\
        Seq.length v' == Seq.length v /\
        (forall (p: nat). p < Seq.length v ==>
           Seq.index v' p ==
             (if off + 64 * n <= p && p < off + 64 * n + 64
              then S8.logxor (Seq.index vm p) (Seq.index (V.vv x) (p - (off + 64 * n)))
              else Seq.index v p)))
      (ensures chunk_inv s0 c vo vm v' off (n + 1))
  = let aux (p: nat { p < Seq.length vo })
      : Lemma (Seq.index v' p ==
                 (if off <= p && p < off + 64 * (n + 1)
                  then S8.logxor (Seq.index vm p) (chunk_ks s0 c (p - off))
                  else Seq.index vo p))
      = assert (Seq.index v p ==
                 (if off <= p && p < off + 64 * n
                  then S8.logxor (Seq.index vm p) (chunk_ks s0 c (p - off))
                  else Seq.index vo p));
        if off + 64 * n <= p && p < off + 64 * n + 64 then begin
          let q = p - (off + 64 * n) in
          assert (Seq.index (V.vv x) q == chunk_ks s0 c (64 * n + q));
          assert (64 * n + q == p - off)
        end
    in
    Classical.forall_intro aux

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Exclusive-or [chunk_ks s0 c] into [msg[off .. off+1024]], writing [out]. *)
inline_for_extraction
fn chunk_vec (out: A.array S8.t) (msg: A.array S8.t) (off: SZ.t)
             (st: A.array S32.t) (c: U32.t)
             (vst: A.array V.t) (ks: A.array V.t) (u: A.array V.t) (t: A.array V.t)
             (#vo: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
             (#ps: perm) (#s0: erased (Seq.seq S32.t))
             (#vv0 #vk0 #vu0 #vt0: erased (Seq.seq V.t))
requires A.pts_to out vo ** A.pts_to msg #pm vm ** A.pts_to st #ps s0 **
         A.pts_to vst vv0 ** A.pts_to ks vk0 ** A.pts_to u vu0 ** A.pts_to t vt0 **
         pure (Seq.length vo == Seq.length vm /\ SZ.v off + 1024 <= Seq.length vm /\
               Seq.length s0 == 16 /\ U32.v c + 16 <= pow2 32 /\
               Seq.length vv0 == 16 /\ Seq.length vk0 == 16 /\
               Seq.length vu0 == 16 /\ Seq.length vt0 == 16)
ensures exists* (vo': Seq.seq S8.t) (vv1 vk1 vu1 vt1: Seq.seq V.t).
  A.pts_to out vo' ** A.pts_to msg #pm vm ** A.pts_to st #ps s0 **
  A.pts_to vst vv1 ** A.pts_to ks vk1 ** A.pts_to u vu1 ** A.pts_to t vt1 **
  pure (Seq.length vo == Seq.length vm /\ SZ.v off + 1024 <= Seq.length vm /\
        Seq.length s0 == 16 /\ U32.v c + 16 <= pow2 32 /\
        Seq.length vv1 == 16 /\ Seq.length vk1 == 16 /\
        Seq.length vu1 == 16 /\ Seq.length vt1 == 16 /\
        chunk_inv s0 c vo vm vo' (SZ.v off) 16)
{
  A.pts_to_len out;
  A.pts_to_len msg;
  init_vec vst st c;
  core_vec ks vst (G.hide (fun (j: nat { j < 16 }) -> with_counter s0 (lane_ctr c j)));
  with vk. assert (A.pts_to ks vk);
  assert (pure (forall (j: nat). j < 16 ==> lane_state vk j == core s0 (lane_ctr c j)));
  transpose t u ks;
  with vt. assert (A.pts_to t vt);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to msg #pm vm ** A.pts_to t vt **
    pure (chunk_inv s0 c vo vm v (SZ.v off) (SZ.v vi))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(t.(vi));
    let ob = SZ.add off (SZ.mul 64sz vi);
    with v. assert (A.pts_to out v);
    Classical.forall_intro (chunk_byte s0 c vk x (SZ.v vi));
    xor64 out msg ob x;
    with v'. assert (A.pts_to out v');
    chunk_step s0 c vo vm v v' (SZ.v off) (SZ.v vi) x;
    i := SZ.add vi 1sz;
  };
}

#pop-options

(** {2 The driver} *)

(** The first [n] bytes of [vo] are the specification's.  [Hacl.Salsa20.Vec256]
    picks up from here. *)
let encrypt_prefix (st0: state) (ctr0: U32.t)
                   (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
                   (vo: Seq.seq S8.t) (n: nat) : prop =
  Seq.length vo == Seq.length msg /\ n <= Seq.length msg /\
  (forall (p: nat). p < n ==> Seq.index vo p == Seq.index (encrypt_bytes st0 ctr0 msg) p)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let mod1024_64 (b: nat)
  : Lemma (requires b % 1024 == 0) (ensures b % 64 == 0 /\ b == (b / 64) * 64)
  = let k = b / 1024 in
    Math.euclidean_division_definition b 1024;
    Math.paren_mul_right k 16 64;
    Math.cancel_mul_mod (k * 16) 64;
    Math.euclidean_division_definition b 64

let chunk_spec (st0: state) (ctr0: U32.t)
               (msg: Seq.seq S8.t { Seq.length msg <= max_len ctr0 })
               (b: nat) (c: U32.t) (p: nat)
  : Lemma
      (requires b % 1024 == 0 /\ b + 1024 <= Seq.length msg /\
                U32.v c == U32.v ctr0 + b / 64 /\ U32.v c + 16 <= pow2 32 /\
                b <= p /\ p < b + 1024)
      (ensures Seq.index (encrypt_bytes st0 ctr0 msg) p ==
               S8.logxor (Seq.index msg p) (chunk_ks st0 c (p - b)))
  = let q = p - b in
    div_lt size_block p (pow2 32 - U32.v ctr0);
    mod1024_64 b;
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
                b % 1024 == 0 /\ b + 1024 <= Seq.length msg /\
                U32.v c == U32.v ctr0 + b / 64 /\ U32.v c + 16 <= pow2 32 /\
                chunk_inv st0 c vo msg vo' b 16)
      (ensures encrypt_prefix st0 ctr0 msg vo' (b + 1024))
  = let aux (p: nat { p < b + 1024 })
      : Lemma (Seq.index vo' p == Seq.index (encrypt_bytes st0 ctr0 msg) p)
      = if b <= p then chunk_spec st0 ctr0 msg b c p
    in
    Classical.forall_intro aux

let chunk_ctr (ctr0: U32.t) (len: nat) (b: nat)
  : Lemma (requires len <= max_len ctr0 /\ b % 1024 == 0 /\ b + 1024 <= len)
          (ensures U32.v ctr0 + b / 64 + 16 <= pow2 32 /\ b / 64 < pow2 32 /\
                   (b + 1024) % 1024 == 0)
  = mod1024_64 b;
    Math.lemma_div_plus b 16 64;
    Math.lemma_div_le (b + 1024) len 64;
    Math.lemma_div_le len (max_len ctr0) 64;
    Math.cancel_mul_div (pow2 32 - U32.v ctr0) 64;
    Math.lemma_mod_plus b 1 1024

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Encrypt the longest prefix of [msg] that is a whole number of
    1024-byte chunks, and say how long it was.  [st] holds the initial
    state; its counter word is not read. *)
[@@CPrologue "__attribute__((target(\"avx512f\")))";
  custard_c_closure_prologue "__attribute__((target(\"avx512f\")))" ""]
fn encrypt_blocks16 (out: A.array S8.t) (msg: A.array S8.t) (mlen: SZ.t)
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
  pure (Seq.length vm <= max_len ctr0 /\
        SZ.v n % 1024 == 0 /\ SZ.v n <= SZ.v mlen /\ SZ.v mlen - SZ.v n < 1024 /\
        encrypt_prefix st0 ctr0 vm vo' (SZ.v n))
{
  A.pts_to_len out;
  A.pts_to_len msg;
  let z = V.zero ();
  let mut vst = [| z; 16sz |];
  let mut ks = [| z; 16sz |];
  let mut u = [| z; 16sz |];
  let mut t = [| z; 16sz |];
  let mut base = 0sz;
  while (let b = !base; SZ.lte 1024sz (SZ.sub mlen b))
  invariant exists* (b: SZ.t) (v: Seq.seq S8.t) (vv vk vu vt: Seq.seq V.t).
    pts_to base b ** A.pts_to out v ** A.pts_to msg #pm vm ** A.pts_to st #ps (G.reveal st0) **
    A.pts_to vst vv ** A.pts_to ks vk ** A.pts_to u vu ** A.pts_to t vt **
    pure (Seq.length vm <= max_len ctr0 /\ Seq.length vm == SZ.v mlen /\
          Seq.length vv == 16 /\ Seq.length vk == 16 /\
          Seq.length vu == 16 /\ Seq.length vt == 16 /\
          SZ.v b % 1024 == 0 /\ SZ.v b <= SZ.v mlen /\
          encrypt_prefix st0 ctr0 vm v (SZ.v b))
  decreases (SZ.v mlen - SZ.v (!base))
  {
    let b = !base;
    with v. assert (A.pts_to out v);
    chunk_ctr ctr0 (SZ.v mlen) (SZ.v b);
    let c = U32.add ctr0 (SZ.sizet_to_uint32 (SZ.div b 64sz));
    A.pts_to_len vst;
    A.pts_to_len ks;
    A.pts_to_len u;
    A.pts_to_len t;
    chunk_vec out msg b st c vst ks u t;
    with v'. assert (A.pts_to out v');
    assert (pure (U32.v (SZ.sizet_to_uint32 (SZ.div b 64sz)) == SZ.v b / 64));
    assert (pure (U32.v c == U32.v ctr0 + SZ.v b / 64));
    assert (pure (U32.v c + 16 <= pow2 32));
    assert (pure (encrypt_prefix st0 ctr0 vm v (SZ.v b)));
    assert (pure (chunk_inv st0 c v vm v' (SZ.v b) 16));
    chunk_ext st0 ctr0 vm v v' (SZ.v b) c;
    base := SZ.add b 1024sz;
  };
  let n = !base;
  n
}

#pop-options
