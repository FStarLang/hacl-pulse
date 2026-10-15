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

(** One SHA-256 block on the SHA instructions.

    [Hacl.Hash.SHA2.Core.update_block_impl] is sixty-four rounds of scalar
    code.  This is the same function with [SHA256RNDS2] doing two rounds at a
    time and [SHA256MSG1]/[SHA256MSG2] doing four schedule slots at a time,
    and it is what runs on a machine with the SHA extensions.

    It has the same signature as the scalar version, including the message
    schedule array: the schedule is computed into that array first and the
    rounds read it back, rather than being kept in registers across the whole
    block.  That costs a store and a few loads per group of four and buys
    three plain loops -- one per stage -- instead of a hundred-line unrolled
    body whose register roles rotate with period four.  The instructions are
    where the time goes, and they are unaffected.

    [Spec.SHANI] is the dictionary: it says what each instruction does in
    terms of [Spec.SHA2], so that everything below is bookkeeping about which
    lane holds which word. *)
module Hacl.Hash.SHA2.NI

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Spec.SHA2
open Spec.SHANI
open Spec.SHA2.Lemmas
open Hacl.Hash.SHA2.Core

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module Vec = Hacl.Vec128
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module G = FStar.Ghost

unfold let sha_prologue : string = "__attribute__((target(\"ssse3,sse4.1,sha\")))"

(** {2 Four words at a time, to and from memory} *)

inline_for_extraction
fn load4 (a: A.array S32.t) (off: SZ.t) (#pm: perm) (#v: erased (Seq.seq S32.t))
requires A.pts_to a #pm v **
         pure (SZ.v off + 4 <= Seq.length v /\ Seq.length v == A.length a)
returns r: Vec.t
ensures A.pts_to a #pm v **
        pure (SZ.v off + 4 <= Seq.length v /\
              (forall (m: nat). m < 4 ==>
                 lane (Vec.vv r) m == Seq.index v (SZ.v off + m)))
{
  A.pts_to_len a;
  let e = SZ.add off 4sz;
  let b = Sub.sub a off e;
  let r = Vec.load32 b;
  Sub.unsub_id a (SZ.v off) (SZ.v e) b;
  r
}

inline_for_extraction
fn store4 (a: A.array S32.t) (off: SZ.t) (x: Vec.t) (#v: erased (Seq.seq S32.t))
requires A.pts_to a v **
         pure (SZ.v off + 4 <= Seq.length v /\ Seq.length v == A.length a)
ensures exists* (w: Seq.seq S32.t). A.pts_to a w **
  pure (Seq.length w == Seq.length v /\
        (forall (k: nat). k < Seq.length w ==>
           Seq.index w k == (if SZ.v off <= k && k < SZ.v off + 4
                             then lane (Vec.vv x) (k - SZ.v off)
                             else Seq.index v k)))
{
  A.pts_to_len a;
  let e = SZ.add off 4sz;
  let b = Sub.sub a off e;
  Vec.store32 b x;
  Sub.unsub a (SZ.v off) (SZ.v e) b;
}

(** The offsets [load_group] computes fit in a [size_t]: they are bounded by
    the length of an array. *)
let group_fits (#a: Type0) (x: A.array a) (off q: nat)
  : Lemma (requires q < 4 /\ off + 64 <= A.length x)
          (ensures SZ.fits (16 * q) /\ SZ.fits (off + 16 * q) /\
                   SZ.fits (off + 16 * q + 16))
  = SZ.fits_lte (off + 16 * q + 16) (A.length x);
    SZ.fits_lte (off + 16 * q) (A.length x);
    SZ.fits_lte (16 * q) (A.length x)

(** Sixteen bytes of the message block, read big-endian. *)
#push-options "--fuel 0 --ifuel 0"
inline_for_extraction
fn load_group (block: A.array S8.t) (off: SZ.t) (q: SZ.t)
              (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to block #pb vb **
         pure (SZ.v q < 4 /\ SZ.v off + block_len #S32.t <= Seq.length vb /\
               Seq.length vb == A.length block)
returns r: Vec.t
ensures A.pts_to block #pb vb **
        pure (SZ.v q < 4 /\ (forall (m: nat). m < 4 ==>
                lane (Vec.vv r) m ==
                  Seq.index (words_from_be block_words (block_at #S32.t vb (SZ.v off)))
                            (4 * SZ.v q + m)))
{
  A.pts_to_len block;
  group_fits block (SZ.v off) (SZ.v q);
  let i0 = SZ.add off (SZ.mul 16sz q);
  block_group vb (SZ.v off) (SZ.v q);
  let i1 = SZ.add i0 16sz;
  let s = Sub.sub block i0 i1;
  let r = Vec.load_be32 s;
  Sub.unsub_id block (SZ.v i0) (SZ.v i1) s;
  r
}
#pop-options

(** Storing a group extends the run of final slots by four.  A lemma of its
    own because the store's postcondition is pointwise over the whole array
    and the invariant is about a prefix. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let extend (p: params S32.t) (bw: Seq.lseq S32.t 16) (j: nat)
           (vw vw': Seq.seq S32.t) (r: reg)
  : Lemma (requires
             Seq.length vw' == Seq.length vw /\ j + 4 <= Seq.length vw /\
             (forall (i: nat). i < j ==> Seq.index vw i == ws_at p bw i) /\
             holds_ws p bw j r /\
             (forall (k: nat). k < Seq.length vw' ==>
                Seq.index vw' k == (if j <= k && k < j + 4
                                    then lane r (k - j) else Seq.index vw k)))
          (ensures forall (i: nat). i < j + 4 ==> Seq.index vw' i == ws_at p bw i)
  = ()
#pop-options

(** {2 One group of four schedule slots}

    Factored out so that its proof is a query of its own: the block function
    below is long, and Z3 does far better on three small goals than on one
    that has all of them in scope at once. *)
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"
inline_for_extraction
fn sched_group ([@@@FStar.Attributes.monomorphize] p: params S32.t)
               (wsb: A.array S32.t) (j: SZ.t)
               (#bw: erased (Seq.lseq S32.t 16)) (#vw: erased (Seq.seq S32.t))
requires A.pts_to wsb vw **
         pure (is_sha256 p /\ 16 <= SZ.v j /\ SZ.v j + 4 <= rounds p /\
               Seq.length vw == rounds p /\ Seq.length vw == A.length wsb /\
               (forall (i: nat). i < SZ.v j ==> Seq.index vw i == ws_at p bw i))
ensures exists* (vw': Seq.seq S32.t). A.pts_to wsb vw' **
  pure (Seq.length vw' == Seq.length vw /\ SZ.v j + 4 <= Seq.length vw' /\
        (forall (i: nat). i < SZ.v j + 4 ==> Seq.index vw' i == ws_at p bw i))
{
  A.pts_to_len wsb;
  let x = load4 wsb (SZ.sub j 16sz);
  let y = load4 wsb (SZ.sub j 12sz);
  let bb = Vec.sha256msg1 x y;
  let c = load4 wsb (SZ.sub j 8sz);
  let a = load4 wsb (SZ.sub j 4sz);
  let tmp = Vec.align_right_4 a c;
  let bt = Vec.add32 bb tmp;
  let rb = Vec.sha256msg2 bt a;
  four (Vec.vv tmp)
       (fun m -> if m < 3 then lane (Vec.vv c) (m + 1) else lane (Vec.vv a) 0);
  assert (pure (holds_ws p (reveal bw) (SZ.v j - 16) (Vec.vv x)));
  assert (pure (holds_ws p (reveal bw) (SZ.v j - 12) (Vec.vv y)));
  assert (pure (holds_ws p (reveal bw) (SZ.v j - 8) (Vec.vv c)));
  assert (pure (holds_ws p (reveal bw) (SZ.v j - 4) (Vec.vv a)));
  msg1_holds p (reveal bw) (SZ.v j - 16) (Vec.vv x) (Vec.vv y) (Vec.vv bb);
  quad_holds p (reveal bw) (SZ.v j) (Vec.vv a) (Vec.vv c) (Vec.vv bb)
               (Vec.vv tmp) (Vec.vv bt) (Vec.vv rb);
  store4 wsb j rb;
  with vw'. assert (A.pts_to wsb vw');
  extend p (reveal bw) (SZ.v j) (reveal vw) vw' (Vec.vv rb);
}
#pop-options

(** {2 Four rounds}

    The two registers are passed as references rather than returned, which
    keeps the caller's loop a plain [while] over two locals. *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
inline_for_extraction
fn rnds_group ([@@@FStar.Attributes.monomorphize] p: params S32.t)
              (kt: A.array S32.t) (wsb: A.array S32.t) (j: SZ.t)
              (s0: ref Vec.t) (s1: ref Vec.t)
              (#pk: perm) (#vk: erased (Seq.seq S32.t))
              (#vw: erased (Seq.seq S32.t)) (#w: erased (Seq.lseq S32.t (rounds p)))
              (#h0: erased (Seq.lseq S32.t 8))
              (#vs0: erased Vec.t) (#vs1: erased Vec.t)
requires A.pts_to kt #pk vk ** A.pts_to wsb vw ** pts_to s0 vs0 ** pts_to s1 vs1 **
         pure (is_sha256 p /\ SZ.v j + 4 <= rounds p /\
               reveal vk == (reveal p.k <: Seq.seq S32.t) /\
               Seq.length vk == rounds p /\ Seq.length vk == A.length kt /\
               Seq.length vw == rounds p /\ Seq.length vw == A.length wsb /\
               (forall (i: nat). i < rounds p ==> Seq.index vw i == Seq.index w i) /\
               unpack (Vec.vv vs0) (Vec.vv vs1) ==
                 repeati_g (SZ.v j) (shuffle_core p w) h0)
ensures exists* (n0: Vec.t) (n1: Vec.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** pts_to s0 n0 ** pts_to s1 n1 **
  pure (unpack (Vec.vv n0) (Vec.vv n1) ==
          repeati_g (SZ.v j + 4) (shuffle_core p w) h0)
{
  A.pts_to_len kt;
  A.pts_to_len wsb;
  let mw = load4 wsb j;
  let kw = load4 kt j;
  let m = Vec.add32 kw mw;
  let a = !s0;
  let c = !s1;
  let n1 = Vec.sha256rnds2 c a m;
  let m2 = Vec.shuffle_high_pair m;
  let n0 = Vec.sha256rnds2 a n1 m2;
  rnds4 p (reveal w) (reveal h0) (SZ.v j)
        (Vec.vv a) (Vec.vv c) (Vec.vv n0) (Vec.vv n1) (Vec.vv m) (Vec.vv m2);
  s0 := n0;
  s1 := n1;
}
#pop-options

(** The two stores at the end of [store_state] write the whole state. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let store_two (h: Seq.lseq S32.t 8) (lo hi: reg) (v0 v1 v2: Seq.seq S32.t)
  : Lemma (requires
             Seq.length v0 == 8 /\ Seq.length v1 == Seq.length v0 /\
             Seq.length v2 == Seq.length v1 /\
             (forall (m: nat). m < 4 ==> lane lo m == Seq.index h m) /\
             (forall (m: nat). m < 4 ==> lane hi m == Seq.index h (m + 4)) /\
             (forall (k: nat). k < Seq.length v1 ==>
                Seq.index v1 k == (if 0 <= k && k < 4 then lane lo (k - 0)
                                   else Seq.index v0 k)) /\
             (forall (k: nat). k < Seq.length v2 ==>
                Seq.index v2 k == (if 4 <= k && k < 8 then lane hi (k - 4)
                                   else Seq.index v1 k)))
          (ensures v2 == h)
  = let aux (k: nat { k < 8 }) : Lemma (Seq.index v2 k == Seq.index h k)
      = if k < 4 then () else assert (Seq.index v2 k == lane hi (k - 4))
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro v2 h
#pop-options

(** The tail: unpack the shuffled state, add the saved state back and write
    it out.  A helper of its own so that the main function's query stays
    small. *)
#push-options "--fuel 0 --ifuel 0"
inline_for_extraction
fn store_state (st: A.array S32.t) (f0: Vec.t) (f1: Vec.t)
               (#vst0: erased (Seq.lseq S32.t 8))
               (#hs: erased (Seq.lseq S32.t 8))
requires A.pts_to st vst0 **
         pure (Seq.length vst0 == A.length st /\ unpack (Vec.vv f0) (Vec.vv f1) == reveal hs)
ensures A.pts_to st (add_state (reveal vst0) (reveal hs))
{
  A.pts_to_len st;
  let lo = load4 st 0sz;
  let hi = load4 st 4sz;
  let t = Vec.shuffle_swap_pairs lo;
  let u = Vec.shuffle_reverse hi;
  let a0 = Vec.align_right_8 t u;
  let c0 = Vec.blend_high u t;
  pack_state (Vec.vv lo) (Vec.vv hi) (Vec.vv a0) (Vec.vv c0) (reveal vst0);
  let r0 = Vec.add32 a0 f0;
  let r1 = Vec.add32 c0 f1;
  add_state_packed (reveal vst0) (reveal hs)
                   (Vec.vv a0) (Vec.vv c0) (Vec.vv f0) (Vec.vv f1)
                   (Vec.vv r0) (Vec.vv r1);
  let t2 = Vec.shuffle_reverse r0;
  let u2 = Vec.shuffle_swap_pairs r1;
  let lo2 = Vec.blend_high t2 u2;
  let hi2 = Vec.align_right_8 u2 t2;
  unpack_state (Vec.vv r0) (Vec.vv r1) (Vec.vv lo2) (Vec.vv hi2)
               (add_state (reveal vst0) (reveal hs));
  store4 st 0sz lo2;
  with v1. assert (A.pts_to st v1);
  store4 st 4sz hi2;
  with vfin. assert (A.pts_to st vfin);
  store_two (add_state (reveal vst0) (reveal hs)) (Vec.vv lo2) (Vec.vv hi2)
            (reveal vst0) v1 vfin;
  assert (pure (Seq.length vfin == 8));
  assert (pure (vfin == add_state (reveal vst0) (reveal hs)));
}
#pop-options

(** {2 The three loops}

    Each loop is a function of its own: a Pulse [fn] is a single SMT query,
    and the three of them together are far beyond what Z3 will chew. *)

(** The block itself, sixteen bytes at a time. *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
inline_for_extraction
fn load_all (block: A.array S8.t) (off: SZ.t) (wsb: A.array S32.t)
            (#pb: perm) (#vb: erased (Seq.seq S8.t))
            (#vw0: erased (Seq.seq S32.t))
requires A.pts_to block #pb vb ** A.pts_to wsb vw0 **
         pure (Seq.length vw0 == 64 /\ Seq.length vw0 == A.length wsb /\
               Seq.length vb == A.length block /\
               SZ.v off + block_len #S32.t <= Seq.length vb)
ensures exists* (vw: Seq.seq S32.t). A.pts_to block #pb vb ** A.pts_to wsb vw **
  pure (Seq.length vw == 64 /\
        (forall (i: nat). i < 16 ==>
           Seq.index vw i ==
             Seq.index (words_from_be block_words (block_at #S32.t vb (SZ.v off))) i))
{
  A.pts_to_len block;
  A.pts_to_len wsb;
  let mut q = 0sz;
  while (let vq = !q; SZ.lt vq 4sz)
  invariant exists* (vq: SZ.t) (vw: Seq.seq S32.t).
    pts_to q vq ** A.pts_to block #pb vb ** A.pts_to wsb vw **
    pure (SZ.v vq <= 4 /\ Seq.length vw == 64 /\
          (forall (i: nat). i < 4 * SZ.v vq ==>
             Seq.index vw i ==
               Seq.index (words_from_be block_words (block_at #S32.t vb (SZ.v off))) i))
  decreases (4 - SZ.v (!q))
  {
    let vq = !q;
    let r = load_group block off vq;
    store4 wsb (SZ.mul 4sz vq) r;
    q := SZ.add vq 1sz;
  };
}
#pop-options

(** The first sixteen slots of the schedule are the block itself; stated as a
    lemma because [sched_all] runs at [--fuel 0]. *)
let ws_at_low (p: params S32.t) (b: Seq.lseq S32.t 16)
  : Lemma (forall (i: nat). i < 16 ==> ws_at p b i == Seq.index b i)
  = ()

(** The schedule.  Group [j] needs the four preceding groups. *)
#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
inline_for_extraction
fn sched_all ([@@@FStar.Attributes.monomorphize] p: params S32.t)
             (wsb: A.array S32.t)
             (#bw: erased (Seq.lseq S32.t 16)) (#vw0: erased (Seq.seq S32.t))
requires A.pts_to wsb vw0 **
         pure (is_sha256 p /\ Seq.length vw0 == rounds p /\
               Seq.length vw0 == A.length wsb /\
               (forall (i: nat). i < 16 ==> Seq.index vw0 i == Seq.index bw i))
ensures exists* (vw: Seq.seq S32.t). A.pts_to wsb vw **
  pure (Seq.length vw == rounds p /\
        (forall (i: nat). i < rounds p ==>
           Seq.index vw i == Seq.index (ws p (reveal bw)) i))
{
  A.pts_to_len wsb;
  ws_at_low p (reveal bw);
  let mut q = 16sz;
  while (let vj = !q; SZ.lt vj 64sz)
  invariant exists* (vj: SZ.t) (vw: Seq.seq S32.t).
    pts_to q vj ** A.pts_to wsb vw **
    pure (16 <= SZ.v vj /\ SZ.v vj <= 64 /\ SZ.v vj % 4 == 0 /\
          Seq.length vw == rounds p /\
          (forall (i: nat). i < SZ.v vj ==> Seq.index vw i == ws_at p (reveal bw) i))
  decreases (64 - SZ.v (!q))
  {
    let vj = !q;
    sched_group p wsb vj #bw;
    Math.lemma_mod_plus (SZ.v vj) 1 4;
    q := SZ.add vj 4sz;
  };
}
#pop-options

(** The rounds: load the state, pack it, shuffle, add and store.  The two
    packed registers never leave this function. *)
#push-options "--z3rlimit 150 --fuel 0 --ifuel 1"
inline_for_extraction
fn shuffle_block ([@@@FStar.Attributes.monomorphize] p: params S32.t)
                 (kt: A.array S32.t) (wsb: A.array S32.t) (st: A.array S32.t)
                 (#pk: perm) (#vk: erased (Seq.seq S32.t))
                 (#vw: erased (Seq.seq S32.t))
                 (#w: erased (Seq.lseq S32.t (rounds p)))
                 (#vst0: erased (Seq.lseq S32.t 8))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst0 **
         pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\
               Seq.length vk == rounds p /\ Seq.length vk == A.length kt /\
               Seq.length vw == rounds p /\ Seq.length vw == A.length wsb /\
               Seq.length vst0 == A.length st /\
               (forall (i: nat). i < rounds p ==> Seq.index vw i == Seq.index w i))
ensures A.pts_to kt #pk vk ** A.pts_to wsb vw **
        A.pts_to st (add_state (reveal vst0) (shuffle p (reveal w) (reveal vst0)))
{
  A.pts_to_len kt;
  A.pts_to_len wsb;
  A.pts_to_len st;
  let lo = load4 st 0sz;
  let hi = load4 st 4sz;
  let t = Vec.shuffle_swap_pairs lo;
  let u = Vec.shuffle_reverse hi;
  let a0 = Vec.align_right_8 t u;
  let c0 = Vec.blend_high u t;
  pack_state (Vec.vv lo) (Vec.vv hi) (Vec.vv a0) (Vec.vv c0) (reveal vst0);
  repeati_g_zero (shuffle_core p (reveal w)) (reveal vst0);

  let mut s0 = a0;
  let mut s1 = c0;
  let mut q = 0sz;
  while (let vj = !q; SZ.lt vj 64sz)
  invariant exists* (vj: SZ.t) (vs0: Vec.t) (vs1: Vec.t).
    pts_to q vj ** pts_to s0 vs0 ** pts_to s1 vs1 **
    A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst0 **
    pure (SZ.v vj <= 64 /\ SZ.v vj % 4 == 0 /\
          unpack (Vec.vv vs0) (Vec.vv vs1) ==
            repeati_g (SZ.v vj) (shuffle_core p (reveal w)) (reveal vst0))
  decreases (64 - SZ.v (!q))
  {
    let vj = !q;
    rnds_group p kt wsb vj s0 s1 #pk #vk #vw #(reveal w) #(reveal vst0);
    Math.lemma_mod_plus (SZ.v vj) 1 4;
    q := SZ.add vj 4sz;
  };

  let f0 = !s0;
  let f1 = !s1;
  assert (pure (shuffle p (reveal w) (reveal vst0) ==
                repeati_g 64 (shuffle_core p (reveal w)) (reveal vst0)));
  store_state st f0 f1 #vst0 #(hide (shuffle p (reveal w) (reveal vst0)));
}
#pop-options

(** {2 The block} *)

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"

[@@CPrologue "__attribute__((target(\"ssse3,sse4.1,sha\")))";
  custard_c_closure_prologue "__attribute__((target(\"ssse3,sse4.1,sha\")))" ""]
fn update_block_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
                   (kt: A.array S32.t) (wsb: A.array S32.t) (st: A.array S32.t)
                   (block: A.array S8.t) (off: SZ.t)
                   (#pk: perm) (#vk: erased (Seq.seq S32.t))
                   (#vw0: erased (Seq.seq S32.t)) (#vst0: erased (Seq.lseq S32.t 8))
                   (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 **
         A.pts_to block #pb vb **
         pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\
               Seq.length vw0 == rounds p /\
               SZ.v off + block_len #S32.t <= Seq.length vb)
ensures exists* (vw: Seq.seq S32.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw **
  A.pts_to st (update_block p (block_at #S32.t vb (SZ.v off)) vst0) **
  A.pts_to block #pb vb ** pure (Seq.length vw == rounds p)
{
  A.pts_to_len kt;
  A.pts_to_len wsb;
  A.pts_to_len st;
  A.pts_to_len block;

  let bw : erased (Seq.lseq S32.t 16) =
    hide (words_from_be block_words (block_at #S32.t vb (SZ.v off)));

  load_all block off wsb;
  sched_all p wsb #bw;
  shuffle_block p kt wsb st #pk #vk #_ #(hide (ws p (reveal bw))) #vst0;
}
#pop-options

(** {2 The driver}

    [Hacl.Hash.SHA2.Core]'s [hash_blocks] and [hash_impl] are generic in the
    word type, so they cannot branch on "this is SHA-256 with thirty-two bit
    words"; these are the two of them specialized.  The padding blocks go
    through [tail_and_finish] unchanged -- there are at most two of them, and
    the saving would not pay for a third copy. *)

(** One step of [hash_blocks_ni], in a small context: the block it hashes,
    and the size_t facts its offset arithmetic needs. *)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let blocks_ni_step (p: params S32.t) (pre vin: Seq.seq S8.t) (nprev: nat)
                   (vi2 nfull: SZ.t) (h: Seq.lseq S32.t 8)
  : Lemma (requires Seq.length pre == nprev * block_len #S32.t /\
                    Seq.length pre + Seq.length vin < max_input #S32.t /\
                    SZ.v nfull == Seq.length vin / block_len #S32.t /\
                    SZ.v vi2 < SZ.v nfull /\ SZ.fits (Seq.length vin))
          (ensures SZ.fits (SZ.v vi2 * 64) /\ SZ.fits (SZ.v vi2 + 1) /\
                   SZ.v vi2 * 64 + block_len #S32.t <= Seq.length vin /\
                   update_step p (padded #S32.t (Seq.append pre vin)) (nprev + SZ.v vi2) h ==
                   update_block p (block_at #S32.t vin (SZ.v vi2 * 64)) h)
  = assert_norm (block_len #S32.t == 64);
    hash_blocks_step #S32.t p pre vin nprev (SZ.v vi2) (SZ.v nfull) h;
    SZ.fits_lte (SZ.v vi2 + 1) (SZ.v nfull);
    SZ.fits_lte (SZ.v vi2 * 64) (Seq.length vin)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"

fn hash_blocks_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
                  (kt: A.array S32.t) (wsb: A.array S32.t) (st: A.array S32.t)
                  (input: A.array S8.t) (nprev: SZ.t) (nfull: SZ.t)
                  (pre: erased (Seq.seq S8.t))
                  (#pk: perm) (#vk: erased (Seq.seq S32.t))
                  (#vw0: erased (Seq.seq S32.t)) (#vst0: erased (Seq.lseq S32.t 8))
                  (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 **
         A.pts_to input #pin vin **
         pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\
               Seq.length vw0 == rounds p /\
               Seq.length pre == SZ.v nprev * block_len #S32.t /\
               Seq.length pre + Seq.length vin < max_input #S32.t /\
               SZ.v nfull == Seq.length vin / block_len #S32.t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #S32.t (Seq.append pre vin)))
                                (reveal p.iv))
ensures exists* (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #S32.t /\ Seq.length vw == rounds p /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #S32.t (Seq.append pre vin))) (reveal p.iv))
{
  A.pts_to_len input;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #S32.t (Seq.append pre vin);
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 nfull)
  invariant exists* (vi2: SZ.t) (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t 8).
    pts_to i vi2 ** A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst **
    A.pts_to input #pin vin **
    pure (SZ.v vi2 <= SZ.v nfull /\ Seq.length vw == rounds p /\
          vst == repeati_g (SZ.v nprev + SZ.v vi2)
                   (update_step p (padded #S32.t (Seq.append pre vin))) (reveal p.iv))
  decreases (SZ.v nfull - SZ.v (!i))
  {
    let vi2 = !i;
    with vst. assert (A.pts_to st vst);
    blocks_ni_step p (reveal pre) (reveal vin) (SZ.v nprev) vi2 nfull vst;
    unfold_repeati_g (SZ.v nprev + SZ.v vi2)
      (update_step p (padded #S32.t (Seq.append pre vin))) (reveal p.iv);
    update_block_ni p kt wsb st input (SZ.mul vi2 64sz);
    i := SZ.add vi2 1sz;
  };
  with vi2. assert (pts_to i vi2);
  assert (pure (SZ.v vi2 == SZ.v nfull));
}
#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn hash_impl_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
                (kt: A.array S32.t) (ivt: A.array S32.t) (out: A.array S8.t)
                (input: A.array S8.t) (len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq S32.t))
                (#pi: perm) (#vi: erased (Seq.seq S32.t))
                (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to input #pin vin **
         pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\
               reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
               Seq.length vout == hash_bytes p /\
               Seq.length vin < pow2 61 /\ Seq.length vin < max_input #S32.t)
         ** pure (SZ.v len == Seq.length vin)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to input #pin vin **
  pure (Seq.length vin < max_input #S32.t /\ vout' == hash p vin)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len input;
  let nfull = SZ.div len 64sz;
  let rem = SZ.rem len 64sz;
  let z0: S32.t = zero #S32.t;

  let mut starr = [| z0; 8sz |];
  A.pts_to_len starr;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq S32.t).
    pts_to c vc ** A.pts_to starr vst ** A.pts_to ivt #pi vi **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==>
             Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq S32.t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(ivt.(vc));
    A.((starr.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq S32.t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq S32.t);

  let mut wsarr = [| z0; p.nrounds |];
  A.pts_to_len wsarr;

  let empty : erased (Seq.seq S8.t) = hide (Seq.empty #S8.t);
  Seq.lemma_eq_elim (Seq.append (reveal empty) (reveal vin)) (reveal vin);
  Math.euclidean_division_definition (SZ.v len) (block_len #S32.t);
  hash_blocks_ni p kt wsarr starr input 0sz nfull empty;
  tail_and_finish p kt wsarr starr out input len nfull (SZ.sub len rem) rem empty;
  ()
}
#pop-options

(** {2 The prefixed hash}

    HMAC hashes a block it has just built -- [K0 ^ ipad], or [K0 ^ opad] --
    followed by a message it must not copy, so it cannot call [hash_impl] on
    a contiguous buffer and it does not.  [Hacl.Hash.SHA2.Core.hash_prefixed]
    absorbs the prefix block and then reads the rest out of the caller's
    array, which is why HMAC of a gigabyte costs no more memory than HMAC of
    a byte.  That function is generic in the word type, so like [hash_impl]
    it cannot branch into the SHA instructions; this is it specialized.

    Without this, every HMAC-SHA-256 in the library ran the scalar block
    function even on a machine whose SHA-256 was using [SHA256RNDS2], which
    made HMAC of a long message about five times the cost of hashing the
    same bytes.  HKDF, HMAC-DRBG and every caller of either inherited it. *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn hash_prefixed_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
                    (kt: A.array S32.t) (ivt: A.array S32.t) (out: A.array S8.t)
                    (blk: A.array S8.t) (input: A.array S8.t) (lin: SZ.t)
                    (#pk: perm) (#vk: erased (Seq.seq S32.t))
                    (#pi: perm) (#vi: erased (Seq.seq S32.t))
                    (#vout: erased (Seq.seq S8.t))
                    (#pb: perm) (#vb: erased (Seq.seq S8.t))
                    (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to blk #pb vb ** A.pts_to input #pin vin **
         pure (is_sha256 p /\
               reveal vk == (reveal p.k <: Seq.seq S32.t) /\
               reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vb == block_len #S32.t /\
               SZ.fits (block_len #S32.t + Seq.length vin) /\
               block_len #S32.t + Seq.length vin < pow2 61 /\
               block_len #S32.t + Seq.length vin < max_input #S32.t)
         ** pure (SZ.v lin == Seq.length vin)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to blk #pb vb ** A.pts_to input #pin vin **
  pure (Seq.length vb + Seq.length vin < max_input #S32.t /\
        vout' == hash p (Seq.append vb vin))
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len blk;
  A.pts_to_len input;
  let len = SZ.add 64sz lin;
  let nfull = SZ.div lin 64sz;
  let rem = SZ.rem lin 64sz;
  let z0: S32.t = zero #S32.t;

  let mut starr = [| z0; 8sz |];
  A.pts_to_len starr;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq S32.t).
    pts_to c vc ** A.pts_to starr vst ** A.pts_to ivt #pi vi **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==>
             Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq S32.t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(ivt.(vc));
    A.((starr.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq S32.t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq S32.t);

  let mut wsarr = [| z0; p.nrounds |];
  A.pts_to_len wsarr;

  Seq.lemma_len_append (reveal vb) (reveal vin);
  padded_shape #S32.t (Seq.append vb vin);
  padded_index_block #S32.t (Seq.append vb vin) 0;
  append_first_block #S32.t (reveal vb) (reveal vin);
  update_block_ni p kt wsarr starr blk 0sz;
  repeati_g_zero (update_step p (padded #S32.t (Seq.append vb vin))) (reveal p.iv);
  unfold_repeati_g 0 (update_step p (padded #S32.t (Seq.append vb vin))) (reveal p.iv);

  Math.lemma_mod_plus (SZ.v lin) 1 (block_len #S32.t);
  assert (pure (SZ.v rem == SZ.v len % block_len #S32.t));
  Math.euclidean_division_definition (SZ.v lin) (block_len #S32.t);
  Math.distributivity_add_left 1 (SZ.v nfull) (block_len #S32.t);
  assert (pure (SZ.v len - SZ.v rem == (1 + SZ.v nfull) * block_len #S32.t));
  Math.multiply_fractions (SZ.v lin) (block_len #S32.t);
  Math.lemma_mult_le_left (SZ.v nfull) 1 (block_len #S32.t);
  SZ.fits_lte (1 + SZ.v nfull) (block_len #S32.t + SZ.v lin);

  hash_blocks_ni p kt wsarr starr input 1sz nfull vb;
  let nb = SZ.add 1sz nfull;
  let base_in = SZ.sub lin rem;
  tail_and_finish p kt wsarr starr out input len nb base_in rem vb;

  ()
}

#pop-options
