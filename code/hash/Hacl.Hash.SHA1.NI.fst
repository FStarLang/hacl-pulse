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

(** One SHA-1 block on the SHA instructions.

    [Hacl.Hash.SHA1.Core.update_block_impl] dispatches here on a machine
    with the SHA extensions.  The shape is [Hacl.Hash.SHA2.NI]'s: the
    schedule is computed into the caller's eighty-word array, four slots at
    a time with [SHA1MSG1]/[SHA1MSG2], and the rounds read it back, four at
    a time with [SHA1RNDS4].  Each group of four is stored with its lanes
    reversed, which is the order the instructions want, so neither loop
    shuffles.

    The fifth state word lives in no register: the first group of rounds
    takes it added to the first message word, and every later group gets it
    from [SHA1NEXTE] applied to the state four rounds back.  [Spec.SHA1NI]
    is the dictionary. *)
module Hacl.Hash.SHA1.NI

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Spec.SHA1
open Spec.SHA1NI
open Spec.SHA1.Lemmas

module A = Pulse.Lib.Array
module Vec = Hacl.Vec128
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module N2 = Hacl.Hash.SHA2.NI
module SHANI = Spec.SHANI

(** The sixteen words of the block at [off]. *)
let bwords (vb: Seq.seq S8.t) (off: nat) : GTot (Seq.lseq S32.t block_words) =
  words_from_be #S32.t block_words (block_at vb off)

(** {2 Bookkeeping lemmas} *)

let ws_low (b: Seq.lseq S32.t block_words) (i: nat)
  : Lemma (requires i < 16) (ensures ws_at b i == Seq.index b i)
  = assert_norm (ws_at b i == Seq.index b i)

let wsr_at (b: Seq.lseq S32.t block_words) (t: nat) (m: nat { m < 4 })
  : Lemma (requires t % 4 == 0) (ensures wsr b (t + m) == ws_at b (t + 3 - m))
  = Math.lemma_div_mod t 4;
    wsr_group b (t / 4) m

let sub_mod4 (j: nat) (g: nat)
  : Lemma (requires j % 4 == 0 /\ 4 * g <= j) (ensures (j - 4 * g) % 4 == 0)
  = Math.lemma_mod_plus (j - 4 * g) g 4

(** A group read back from the array holds the schedule words. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let load_holds (b: Seq.lseq S32.t block_words) (vw: Seq.seq S32.t) (n t: nat) (r: reg)
  : Lemma (requires t % 4 == 0 /\ t + 4 <= n /\ n <= Seq.length vw /\
                    (forall (s: nat). s < n ==> Seq.index vw s == wsr b s) /\
                    (forall (m: nat). m < 4 ==> lane r m == Seq.index vw (t + m)))
          (ensures holds b t r)
  = wsr_at b t 0; wsr_at b t 1; wsr_at b t 2; wsr_at b t 3
#pop-options

#push-options "--fuel 0 --ifuel 0"
let holds_lane (b: Seq.lseq S32.t block_words) (t: nat) (r: reg) (m: nat { m < 4 })
  : Lemma (requires holds b t r) (ensures lane r m == ws_at b (t + 3 - m))
  = if m = 0 then () else if m = 1 then () else if m = 2 then () else ()
#pop-options

(** Storing a group that holds the next four words extends the prefix. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let store_holds (b: Seq.lseq S32.t block_words) (vw vw': Seq.seq S32.t) (t: nat) (r: reg)
  : Lemma (requires t % 4 == 0 /\ t + 4 <= Seq.length vw /\
                    Seq.length vw' == Seq.length vw /\
                    (forall (s: nat). s < t ==> Seq.index vw s == wsr b s) /\
                    holds b t r /\
                    (forall (k: nat). k < Seq.length vw' ==>
                       Seq.index vw' k == (if t <= k && k < t + 4
                                           then lane r (k - t) else Seq.index vw k)))
          (ensures forall (s: nat). s < t + 4 ==> Seq.index vw' s == wsr b s)
  = let aux (s: nat) : Lemma (s < t + 4 ==> Seq.index vw' s == wsr b s)
      = if s < t then ()
        else if s < t + 4 then begin
          let m : (m: nat { m < 4 }) = s - t in
          wsr_at b t m;
          holds_lane b t r m;
          assert (s == t + m)
        end
    in
    FStar.Classical.forall_intro aux
#pop-options

(** {2 The schedule} *)

(** Store a group that holds the next four words. *)
#push-options "--z3rlimit 50 --fuel 0 --ifuel 1"
inline_for_extraction
fn store_group (wsb: A.array S32.t) (j: SZ.t) (r: Vec.t)
               (#b: erased (Seq.lseq S32.t block_words)) (#vw: erased (Seq.seq S32.t))
requires A.pts_to wsb vw **
         pure (SZ.v j + 4 <= rounds /\ SZ.v j % 4 == 0 /\
               Seq.length vw == rounds /\ Seq.length vw == A.length wsb /\
               holds b (SZ.v j) (Vec.vv r) /\
               (forall (s: nat). s < SZ.v j ==> Seq.index vw s == wsr b s))
ensures exists* (vw': Seq.seq S32.t). A.pts_to wsb vw' **
  pure (Seq.length vw' == rounds /\ SZ.v j + 4 <= Seq.length vw' /\
        (forall (s: nat). s < SZ.v j + 4 ==> Seq.index vw' s == wsr b s))
{
  N2.store4 wsb j r;
  with vw'. assert (A.pts_to wsb vw');
  store_holds b vw vw' (SZ.v j) (Vec.vv r);
  assert (pure (forall (s: nat). s < SZ.v j + 4 ==> Seq.index vw' s == wsr b s));
  assert (pure (Seq.length vw' == rounds));
}
#pop-options

(** The block, reversed four words at a time. *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
inline_for_extraction
fn load_all (block: A.array S8.t) (off: SZ.t) (wsb: A.array S32.t)
            (#pb: perm) (#vb: erased (Seq.seq S8.t))
            (#vw0: erased (Seq.seq S32.t))
requires A.pts_to block #pb vb ** A.pts_to wsb vw0 **
         pure (Seq.length vw0 == rounds /\ Seq.length vw0 == A.length wsb /\
               SZ.v off + block_len <= Seq.length vb)
ensures exists* (vw: Seq.seq S32.t). A.pts_to block #pb vb ** A.pts_to wsb vw **
  pure (Seq.length vw == rounds /\
        (forall (s: nat). s < 16 ==> Seq.index vw s == wsr (bwords vb (SZ.v off)) s))
{
  A.pts_to_len block;
  A.pts_to_len wsb;
  let mut q = 0sz;
  while (let vq = !q; SZ.lt vq 4sz)
  invariant exists* (vq: SZ.t) (vw: Seq.seq S32.t).
    pts_to q vq ** A.pts_to block #pb vb ** A.pts_to wsb vw **
    pure (SZ.v vq <= 4 /\ Seq.length vw == rounds /\
          (forall (s: nat). s < 4 * SZ.v vq ==> Seq.index vw s == wsr (bwords vb (SZ.v off)) s))
  decreases (4 - SZ.v (!q))
  {
    let vq = !q;
    let r = N2.load_group block off vq;
    let rv = Vec.shuffle_reverse r;
    ws_low (bwords vb (SZ.v off)) (4 * SZ.v vq);
    ws_low (bwords vb (SZ.v off)) (4 * SZ.v vq + 1);
    ws_low (bwords vb (SZ.v off)) (4 * SZ.v vq + 2);
    ws_low (bwords vb (SZ.v off)) (4 * SZ.v vq + 3);
    assert (pure (holds (bwords vb (SZ.v off)) (4 * SZ.v vq) (Vec.vv rv)));
    Math.lemma_mod_plus 0 (SZ.v vq) 4;
    store_group wsb (SZ.mul 4sz vq) rv #(hide (bwords vb (SZ.v off)));
    q := SZ.add vq 1sz;
  };
}
#pop-options

(** One group of four schedule words. *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
inline_for_extraction
fn sched_group (wsb: A.array S32.t) (j: SZ.t)
               (#b: erased (Seq.lseq S32.t block_words)) (#vw: erased (Seq.seq S32.t))
requires A.pts_to wsb vw **
         pure (16 <= SZ.v j /\ SZ.v j + 4 <= rounds /\ SZ.v j % 4 == 0 /\
               Seq.length vw == rounds /\ Seq.length vw == A.length wsb /\
               (forall (s: nat). s < SZ.v j ==> Seq.index vw s == wsr b s))
ensures exists* (vw': Seq.seq S32.t). A.pts_to wsb vw' **
  pure (Seq.length vw' == rounds /\ SZ.v j + 4 <= Seq.length vw' /\
        (forall (s: nat). s < SZ.v j + 4 ==> Seq.index vw' s == wsr b s))
{
  A.pts_to_len wsb;
  let p16 = N2.load4 wsb (SZ.sub j 16sz);
  let p12 = N2.load4 wsb (SZ.sub j 12sz);
  let m1 = Vec.sha1msg1 p16 p12;
  let p8 = N2.load4 wsb (SZ.sub j 8sz);
  let x = Vec.xor32 m1 p8;
  let p4 = N2.load4 wsb (SZ.sub j 4sz);
  let m2 = Vec.sha1msg2 x p4;
  sub_mod4 (SZ.v j) 4; sub_mod4 (SZ.v j) 3; sub_mod4 (SZ.v j) 2; sub_mod4 (SZ.v j) 1;
  load_holds b vw (SZ.v j) (SZ.v j - 16) (Vec.vv p16);
  load_holds b vw (SZ.v j) (SZ.v j - 12) (Vec.vv p12);
  load_holds b vw (SZ.v j) (SZ.v j - 8) (Vec.vv p8);
  load_holds b vw (SZ.v j) (SZ.v j - 4) (Vec.vv p4);
  sched b (SZ.v j) (Vec.vv p16) (Vec.vv p12) (Vec.vv p8) (Vec.vv p4)
        (Vec.vv m1) (Vec.vv x) (Vec.vv m2);
  store_group wsb j m2 #b;
}
#pop-options

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
inline_for_extraction
fn sched_all (wsb: A.array S32.t)
             (#b: erased (Seq.lseq S32.t block_words)) (#vw0: erased (Seq.seq S32.t))
requires A.pts_to wsb vw0 **
         pure (Seq.length vw0 == rounds /\ Seq.length vw0 == A.length wsb /\
               (forall (s: nat). s < 16 ==> Seq.index vw0 s == wsr b s))
ensures exists* (vw: Seq.seq S32.t). A.pts_to wsb vw **
  pure (Seq.length vw == rounds /\
        (forall (s: nat). s < rounds ==> Seq.index vw s == wsr b s))
{
  A.pts_to_len wsb;
  let mut q = 16sz;
  while (let vj = !q; SZ.lt vj 80sz)
  invariant exists* (vj: SZ.t) (vw: Seq.seq S32.t).
    pts_to q vj ** A.pts_to wsb vw **
    pure (16 <= SZ.v vj /\ SZ.v vj <= 80 /\ SZ.v vj % 4 == 0 /\
          Seq.length vw == rounds /\
          (forall (s: nat). s < SZ.v vj ==> Seq.index vw s == wsr b s))
  decreases (80 - SZ.v (!q))
  {
    let vj = !q;
    sched_group wsb vj #b;
    Math.lemma_mod_plus (SZ.v vj) 1 4;
    q := SZ.add vj 4sz;
  };
}
#pop-options

(** {2 The rounds} *)

let div20 (j: nat) (q: nat)
  : Lemma (requires 20 * q <= j /\ j < 20 * q + 20) (ensures j / 20 == q)
  = Math.small_div (j - 20 * q) 20;
    Math.lemma_div_plus (j - 20 * q) q 20

(** The immediate is the quarter, which the round number gives. *)
inline_for_extraction
fn rnds4_at (j: SZ.t) (a x: Vec.t)
requires pure (SZ.v j < 80)
returns r: Vec.t
ensures pure (SZ.v j / 20 < 4 /\ rnds4_out (SZ.v j / 20) (Vec.vv a) (Vec.vv x) (Vec.vv r))
{
  if (SZ.lt j 20sz) {
    div20 (SZ.v j) 0;
    Vec.sha1rnds4_0 a x
  } else if (SZ.lt j 40sz) {
    div20 (SZ.v j) 1;
    Vec.sha1rnds4_1 a x
  } else if (SZ.lt j 60sz) {
    div20 (SZ.v j) 2;
    Vec.sha1rnds4_2 a x
  } else {
    div20 (SZ.v j) 3;
    Vec.sha1rnds4_3 a x
  }
}

(** A message group read back for the rounds: its high lane is the first of
    its four words. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let msg_lanes (b: Seq.lseq S32.t block_words) (vw: Seq.seq S32.t) (j: nat) (m: reg)
  : Lemma (requires j % 4 == 0 /\ j + 4 <= rounds /\ Seq.length vw == rounds /\
                    (forall (s: nat). s < rounds ==> Seq.index vw s == wsr b s) /\
                    (forall (i: nat). i < 4 ==> lane m i == Seq.index vw (j + i)))
          (ensures lane m 3 == Seq.index (ws b) j /\ lane m 2 == Seq.index (ws b) (j + 1) /\
                   lane m 1 == Seq.index (ws b) (j + 2) /\ lane m 0 == Seq.index (ws b) (j + 3))
  = load_holds b vw rounds j m
#pop-options

(** The state, read into an [ABCD] register and an [e]. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let state_in (h: Seq.lseq S32.t state_words) (lo abcd: reg)
  : Lemma (requires (forall (i: nat). i < 4 ==> lane lo i == Seq.index h i) /\
                    lane abcd 0 == lane lo 3 /\ lane abcd 1 == lane lo 2 /\
                    lane abcd 2 == lane lo 1 /\ lane abcd 3 == lane lo 0)
          (ensures h == unpack abcd (Seq.index h 4))
  = Seq.lemma_eq_intro h (unpack abcd (Seq.index h 4))
#pop-options

(** The state written back: [ABCD] reversed into four words and [e] out of
    the high lane of the [SHA1NEXTE] that adds it. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let state_out (h0: Seq.lseq S32.t state_words) (abcd0 ev cv pv na ne out: reg)
              (vst1 vfin: Seq.seq S32.t)
  : Lemma (requires
             h0 == unpack abcd0 (Seq.index h0 4) /\
             lane ev 3 == Seq.index h0 4 /\
             (forall (i: nat). i < 4 ==> lane na i == S32.add_mod (lane abcd0 i) (lane cv i)) /\
             (forall (i: nat). i < 4 ==> lane ne i == nexte pv ev i) /\
             lane out 0 == lane na 3 /\ lane out 1 == lane na 2 /\
             lane out 2 == lane na 1 /\ lane out 3 == lane na 0 /\
             Seq.length vst1 == state_words /\
             (forall (k: nat). k < 4 ==> Seq.index vst1 k == lane out k) /\
             vfin == Seq.upd vst1 4 (lane ne 3))
          (ensures vfin == add_state h0 (unpack cv (rol30 (lane pv 3))))
  = SHANI.add_mod_comm (rol30 (lane pv 3)) (Seq.index h0 4);
    Seq.lemma_eq_intro vfin (add_state h0 (unpack cv (rol30 (lane pv 3))))
#pop-options

(** The block's rounds and the final addition. *)
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"
inline_for_extraction
fn shuffle_block (wsb: A.array S32.t) (st: A.array S32.t)
                 (#b: erased (Seq.lseq S32.t block_words))
                 (#vw: erased (Seq.seq S32.t))
                 (#vst0: erased (Seq.lseq S32.t state_words))
requires A.pts_to wsb vw ** A.pts_to st vst0 **
         pure (Seq.length vw == rounds /\ Seq.length vw == A.length wsb /\
               (forall (s: nat). s < rounds ==> Seq.index vw s == wsr b s))
ensures A.pts_to wsb vw ** A.pts_to st (add_state vst0 (shuffle (ws b) vst0))
{
  A.pts_to_len wsb;
  A.pts_to_len st;
  let lo = N2.load4 st 0sz;
  let abcd0 = Vec.shuffle_reverse lo;
  let e0 = A.(st.(4sz));
  state_in vst0 (Vec.vv lo) (Vec.vv abcd0);
  let ev = Vec.high_lane e0;
  let m0 = N2.load4 wsb 0sz;
  msg_lanes b vw 0 (Vec.vv m0);
  let x0 = Vec.add32 ev m0;
  add_zero (lane (Vec.vv m0) 0);
  add_zero (lane (Vec.vv m0) 1);
  add_zero (lane (Vec.vv m0) 2);
  let c1 = Vec.sha1rnds4_0 abcd0 x0;
  repeati_g_zero (shuffle_core (ws b)) vst0;
  group (ws b) vst0 0 0 (Vec.vv abcd0) (Vec.vv x0) (Vec.vv c1) e0;

  let mut prev = abcd0;
  let mut cur = c1;
  let mut q = 4sz;
  while (let vj = !q; SZ.lt vj 80sz)
  invariant exists* (vj: SZ.t) (pv: Vec.t) (cv: Vec.t).
    pts_to q vj ** pts_to prev pv ** pts_to cur cv **
    A.pts_to wsb vw ** A.pts_to st vst0 **
    pure (4 <= SZ.v vj /\ SZ.v vj <= 80 /\ SZ.v vj % 4 == 0 /\
          repeati_g (SZ.v vj) (shuffle_core (ws b)) vst0 ==
            unpack (Vec.vv cv) (rol30 (lane (Vec.vv pv) 3)))
  decreases (80 - SZ.v (!q))
  {
    let vj = !q;
    let m = N2.load4 wsb vj;
    msg_lanes b vw (SZ.v vj) (Vec.vv m);
    let pv = !prev;
    let cv = !cur;
    let x = Vec.sha1nexte pv m;
    quarter (SZ.v vj);
    let n = rnds4_at vj cv x;
    group (ws b) vst0 (SZ.v vj / 20) (SZ.v vj) (Vec.vv cv) (Vec.vv x) (Vec.vv n)
          (rol30 (lane (Vec.vv pv) 3));
    prev := cv;
    cur := n;
    Math.lemma_mod_plus (SZ.v vj) 1 4;
    q := SZ.add vj 4sz;
  };

  let pv = !prev;
  let cv = !cur;
  assert (pure (shuffle (ws b) vst0 == unpack (Vec.vv cv) (rol30 (lane (Vec.vv pv) 3))));
  let na = Vec.add32 abcd0 cv;
  let ne = Vec.sha1nexte pv ev;
  let out = Vec.shuffle_reverse na;
  N2.store4 st 0sz out;
  with vst1. assert (A.pts_to st vst1);
  let e1 = Vec.get_high_lane ne;
  A.(st.(4sz) <- e1);
  with vfin. assert (A.pts_to st vfin);
  state_out vst0 (Vec.vv abcd0) (Vec.vv ev) (Vec.vv cv) (Vec.vv pv) (Vec.vv na)
            (Vec.vv ne) (Vec.vv out) vst1 vfin;
  assert (pure (vfin == add_state vst0 (shuffle (ws b) vst0)));
}
#pop-options

(** {2 The block} *)

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"

[@@CPrologue "__attribute__((target(\"ssse3,sse4.1,sha\")))";
  custard_c_closure_prologue "__attribute__((target(\"ssse3,sse4.1,sha\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn update_block_ni (wsb: A.array S32.t) (st: A.array S32.t)
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
  A.pts_to_len wsb;
  A.pts_to_len st;
  A.pts_to_len block;
  load_all block off wsb;
  sched_all wsb #(hide (bwords vb (SZ.v off)));
  shuffle_block wsb st #(hide (bwords vb (SZ.v off)));
}
#pop-options
