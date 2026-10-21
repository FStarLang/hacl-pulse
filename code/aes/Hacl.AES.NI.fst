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

(** The AES block cipher on the AES instructions.

    This is a drop-in replacement for [Hacl.AES.Cipher.cipher_portable]: same
    arguments, same postcondition, one [AESENC] where the portable path has
    fifteen field multiplications per byte.  [Hacl.AES.Cipher.cipher_impl]
    chooses between them once per block with [Hacl.Vec128.supported], which is
    a perfectly predicted branch next to the work it guards, so CTR, GCM and
    everything above them get the fast path with no change of their own.

    The key schedule is {i not} done here.  [Hacl.AES.Key] computes it, with
    [AESKEYGENASSIST] under [Hacl.AES.SubWord] when the machine has it, and
    it happens once per message rather than once per block.  This module
    reads the expanded key sixteen bytes at a time, exactly as the portable
    cipher does.

    The two attributes are what put [target("aes,...")] on this function and
    on everything it exclusively reaches; see [Hacl.Vec128]. *)
module Hacl.AES.NI

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Cipher
open Hacl.AES.Counter

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub
module Vec = Hacl.Vec128

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Refinement subtyping does not cross [erased], so the sixteen-byte
    window a load wants is reached through an explicit coercion rather than
    by hoping the solver sees through the [hide]. *)
let as_blk (s: Seq.seq S8.t { Seq.length s == blocklen })
  : Pure (Seq.lseq S8.t blocklen) (requires True) (ensures fun r -> r == s)
  = s

(** [xor_block] and [Seq.slice] are both [Seq.init]-shaped, so their indices
    have to be given to the solver explicitly before it will push an
    equation about a whole block down to a single byte. *)
let xor_block_index (a b: block) (i: nat { i < blocklen })
  : Lemma (Seq.index (xor_block a b) i == Seq.index a i ^^ Seq.index b i)
          [SMTPat (Seq.index (xor_block a b) i)]
  = ()

let slice_index (s: Seq.seq elem) (lo: nat) (hi: nat { lo <= hi /\ hi <= Seq.length s })
                (i: nat { i < hi - lo })
  : Lemma (Seq.index (Seq.slice s lo hi) i == Seq.index s (lo + i))
          [SMTPat (Seq.index (Seq.slice s lo hi) i)]
  = ()

(** {2 The cipher, on a register}

    The block never has to be in memory: it arrives in a register, every
    round leaves it in a register, and it leaves in one.  [cipher_ni] below
    is this with a load in front and a store behind, for callers that do hold
    their block in an array; [Hacl.AES.CTR]'s driver instead keeps the whole
    counter-mode step in registers and never materialises the keystream. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn cipher_vec ([@@@FStar.Attributes.monomorphize] p: params)
              (x0: Vec.t) (w: A.array S8.t)
              (#v0 #vw: erased (Seq.seq S8.t))
requires A.pts_to w vw ** pure (
  Seq.length v0 == blocklen /\ Seq.length vw == xkeylen p.pv /\
  Vec.bv x0 == vals v0)
returns r: Vec.t
ensures A.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length v0 == blocklen /\
  Vec.bv r == cipher p.pv (vals vw) (vals v0))
{
  A.pts_to_len w;

  (* Round key zero, added before the first round. *)
  let k0 = Sub.sub w 0sz 16sz;
  round_key_slice p.pv (vals vw) 0;
  vals_slice vw 0 16;
  let kv0 = Vec.load k0 #(as_blk (Seq.slice vw 0 16));
  Sub.unsub_id w (SZ.v 0sz) (SZ.v 16sz) k0;
  cipher_start p.pv (vals vw) (vals v0);

  let mut s = Vec.vxor x0 kv0;
  let mut i = 1sz;
  let mut off = 16sz;

  while (let vi = !i; SZ.lt vi p.pnr)
  invariant exists* (vi: SZ.t) (vo: SZ.t) (vs: Vec.t).
    pts_to i vi ** pts_to off vo ** pts_to s vs ** A.pts_to w vw **
    pure (1 <= SZ.v vi /\ SZ.v vi <= nr p.pv /\ SZ.v vo == 16 * SZ.v vi /\
          Seq.length vw == xkeylen p.pv /\ Seq.length v0 == blocklen /\
          rounds p.pv (vals vw) (Vec.bv vs) (SZ.v vi) ==
            cipher p.pv (vals vw) (vals v0))
  decreases (nr p.pv - SZ.v (!i))
  {
    let vi = !i;
    let vo = !off;
    let vs = !s;
    round_key_slice p.pv (vals vw) (SZ.v vi);
    vals_slice vw (SZ.v vo) (SZ.v vo + 16);
    rounds_step p.pv (vals vw) (Vec.bv vs) (SZ.v vi);
    let vo2 = SZ.add vo 16sz;
    let kb = Sub.sub w vo vo2;
    let kv = Vec.load kb #(as_blk (Seq.slice vw (SZ.v vo) (SZ.v vo2)));
    Sub.unsub_id w (SZ.v vo) (SZ.v vo2) kb;
    s := Vec.aesenc vs kv;
    i := SZ.add vi 1sz;
    off := SZ.add vo 16sz;
  };

  let vn = !i;
  let vo = !off;
  let vs = !s;
  round_key_slice p.pv (vals vw) (SZ.v vn);
  vals_slice vw (SZ.v vo) (SZ.v vo + 16);
  rounds_last p.pv (vals vw) (Vec.bv vs);
  let vo2 = SZ.add vo 16sz;
  let kb = Sub.sub w vo vo2;
  let kv = Vec.load kb #(as_blk (Seq.slice vw (SZ.v vo) (SZ.v vo2)));
  Sub.unsub_id w (SZ.v vo) (SZ.v vo2) kb;
  let r = Vec.aesenclast vs kv;
  r
}

(** {2 The cipher, in place on an array} *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn cipher_ni ([@@@FStar.Attributes.monomorphize] p: params)
             (st: A.array S8.t) (w: A.array S8.t)
             (#v0 #vw: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to w vw ** pure (
  Seq.length v0 == blocklen /\ Seq.length vw == xkeylen p.pv)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 ** A.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length v0 == blocklen /\
  Seq.length v1 == blocklen /\
  vals v1 == cipher p.pv (vals vw) (vals v0))
{
  A.pts_to_len st;
  A.pts_to_len w;
  let x0 = Vec.load st #(as_blk v0);
  let r = cipher_vec p x0 w #v0;
  Vec.store st r #(as_blk v0);
  vals_len (Vec.vv r);
  ()
}

(** {2 One register, exclusive-ored into an array}

    The keystream never has to be in memory either.  The sixteen-byte
    scratch block that the portable driver copies the counter into,
    encrypts, and then reads back a byte at a time does not exist on this
    path: the result of the cipher goes straight from the register it was
    computed in into the message.  That scratch block is what made the
    portable driver expensive, and not only for the byte traffic -- it was
    written by a vector store and read by sixteen scalar loads, which is a
    store-forwarding stall on every block. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn xor_at_ni (msg: A.array S8.t) (idx: SZ.t) (ks: Vec.t)
             (#vm: erased (Seq.seq S8.t))
requires A.pts_to msg vm ** pure (SZ.v idx + blocklen <= Seq.length vm)
ensures exists* (vm': Seq.seq S8.t). A.pts_to msg vm' ** pure (
  SZ.v idx + blocklen <= Seq.length vm /\
  Seq.length vm' == Seq.length vm /\
  (forall (k: nat). k < Seq.length vm ==>
     Seq.index (vals vm') k ==
       (if SZ.v idx <= k && k < SZ.v idx + blocklen
        then Seq.index (vals vm) k ^^ Seq.index (Vec.bv ks) (k - SZ.v idx)
        else Seq.index (vals vm) k)))
{
  A.pts_to_len msg;
  let idx2 = SZ.add idx 16sz;
  let mb = Sub.sub msg idx idx2;
  vals_slice vm (SZ.v idx) (SZ.v idx2);
  let mv = Vec.load mb #(as_blk (Seq.slice vm (SZ.v idx) (SZ.v idx2)));
  let r = Vec.vxor mv ks;
  Vec.store mb r #(as_blk (Seq.slice vm (SZ.v idx) (SZ.v idx2)));
  vals_len (Vec.vv r);
  Sub.unsub msg (SZ.v idx) (SZ.v idx2) mb;
  with vm'. assert A.pts_to msg vm';
  assert (pure (Seq.length vm' == Seq.length vm));
  assert (pure (Vec.bv r == xor_block (Vec.bv mv) (Vec.bv ks)));
  assert (pure (Vec.bv mv == Seq.slice (vals vm) (SZ.v idx) (SZ.v idx2)));
  assert (pure (forall (k: nat). SZ.v idx <= k /\ k < SZ.v idx2 ==>
    Seq.index vm' k == Seq.index (Vec.vv r) (k - SZ.v idx)));
  assert (pure (forall (k: nat). SZ.v idx <= k /\ k < SZ.v idx2 ==>
    Seq.index (vals vm') k == Seq.index (Vec.bv r) (k - SZ.v idx)));
  assert (pure (forall (k: nat). SZ.v idx <= k /\ k < SZ.v idx2 ==>
    Seq.index (vals vm') k ==
      Seq.index (Vec.bv mv) (k - SZ.v idx) ^^ Seq.index (Vec.bv ks) (k - SZ.v idx)));
  assert (pure (forall (k: nat). k < Seq.length vm /\
                                ~(SZ.v idx <= k /\ k < SZ.v idx2) ==>
    Seq.index (vals vm') k == Seq.index (vals vm) k));
  ()
}

(** {2 One counter-mode block}

    The whole of a counter-mode step, with the keystream never written down:
    the counter is loaded into a register, encrypted there, exclusive-ored
    into the message in place, and discarded. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn ctr_block_ni ([@@@FStar.Attributes.monomorphize] p: params)
                (msg: A.array S8.t) (idx: SZ.t) (w: A.array S8.t) (ctr: A.array S8.t)
                (#vm #vw #vc: erased (Seq.seq S8.t))
requires A.pts_to msg vm ** A.pts_to w vw ** A.pts_to ctr vc ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
  SZ.v idx + blocklen <= Seq.length vm)
ensures exists* (vm': Seq.seq S8.t).
  A.pts_to msg vm' ** A.pts_to w vw ** A.pts_to ctr vc ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
  SZ.v idx + blocklen <= Seq.length vm /\
  Seq.length vm' == Seq.length vm /\
  (forall (k: nat). k < Seq.length vm ==>
     Seq.index (vals vm') k ==
       (if SZ.v idx <= k && k < SZ.v idx + blocklen
        then Seq.index (vals vm) k ^^
             Seq.index (cipher p.pv (vals vw) (vals vc)) (k - SZ.v idx)
        else Seq.index (vals vm) k)))
{
  A.pts_to_len msg;
  A.pts_to_len w;
  A.pts_to_len ctr;

  let c0 = Vec.load ctr #(as_blk vc);
  let ks = cipher_vec p c0 w #vc;
  xor_at_ni msg idx ks;
  ()
}


(** {2 The counter, in a register}

    [Hacl.AES.Counter.inc32_impl] is a constant-time carry chain over four
    bytes of an array.  It is correct and it is what the portable driver
    uses, but in the vector driver it is in the wrong place: four counters
    per turn means four carry chains, and each one ends in a four-byte store
    that the next sixteen-byte load has to read back, which no store-forward
    network will do.  Reversing the block instead moves the counter to lane
    zero and turns its big-endian reading into a little-endian one, a packed
    add of [Hacl.Vec128.lane_one] increments it without carrying into the
    twelve bytes above, and reversing again puts it back: three instructions,
    all in registers.  [Hacl.AES.Counter.inc32_lanes] is the proof. *)

inline_for_extraction
let inc32_vec (c: Vec.t) : Vec.t =
  Vec.bswap (Vec.add32 (Vec.bswap c) (Vec.lane_one ()))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"
(** The same, for a counter already held reversed: [a] is [c] reversed,
    and the packed add gives the next counter, still reversed.  A loop that
    makes several counters in a row keeps them reversed between steps and
    reverses each one once, rather than twice. *)
let inc32_sw_ok (c a: Vec.t)
  : Lemma (requires Vec.bv a == Spec.CLMUL.bswap (Vec.bv c))
          (ensures Vec.bv (Vec.bswap (Vec.add32 a (Vec.lane_one ()))) == inc32 (Vec.bv c) /\
                   Vec.bv (Vec.add32 a (Vec.lane_one ())) ==
                     Spec.CLMUL.bswap (inc32 (Vec.bv c)))
  = let one = Vec.lane_one () in
    let s = Vec.add32 a one in
    assert (Vec.bv (Vec.bswap s) == Spec.CLMUL.bswap (Vec.bv s));
    Spec.CLMUL.bswap_involutive (Vec.bv s);
    assert_norm (pow2 32 == 4294967296);
    let aux (i: nat { i < 4 })
      : Lemma (S32.v (Spec.SHANI.lane (Vec.vv s) i) ==
                 (lane_of (Vec.bv a) i + S32.v (Spec.SHANI.lane (Vec.vv one) i))
                 % pow2 32)
      = lane_of_reg (Vec.vv a) i;
        lane_of_reg (Vec.vv s) i
    in
    aux 0; aux 1; aux 2; aux 3;
    lane_of_reg (Vec.vv s) 0; lane_of_reg (Vec.vv s) 1;
    lane_of_reg (Vec.vv s) 2; lane_of_reg (Vec.vv s) 3;
    lane_of_bound (Vec.bv a) 1; lane_of_bound (Vec.bv a) 2;
    lane_of_bound (Vec.bv a) 3;
    Math.small_mod (lane_of (Vec.bv a) 1) (pow2 32);
    Math.small_mod (lane_of (Vec.bv a) 2) (pow2 32);
    Math.small_mod (lane_of (Vec.bv a) 3) (pow2 32);
    inc32_lanes (Vec.bv c) (Vec.bv s)

let inc32_vec_ok (c: Vec.t)
  : Lemma (Vec.bv (inc32_vec c) == inc32 (Vec.bv c))
  = inc32_sw_ok c (Vec.bswap c)
#pop-options

(** {2 Four counter-mode blocks at once}

    A single [AESENC] has a latency of several cycles and the rounds of one
    block form a chain, so a driver that encrypts one block at a time leaves
    the cipher unit idle most of the time.  Counter mode's blocks are
    independent, so four of them can be pushed through the same round-key
    loop together: the four chains interleave, each round costs one key load
    and four [AESENC], and the cipher runs at the throughput of the hardware
    rather than at the latency of one chain.  The round keys are loaded once
    for the four rather than four times.

    The counter is advanced here rather than by the caller, so that the four
    counter blocks are produced and consumed without the message ever being
    touched in between. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn ctr_block4_ni ([@@@FStar.Attributes.monomorphize] p: params)
                 (msg: A.array S8.t) (idx: SZ.t) (w: A.array S8.t) (ctr: A.array S8.t)
                 (#vm #vw #vc: erased (Seq.seq S8.t))
requires A.pts_to msg vm ** A.pts_to w vw ** A.pts_to ctr vc ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
  SZ.fits (SZ.v idx + 4 * blocklen) /\
  SZ.v idx + 4 * blocklen <= Seq.length vm)
ensures exists* (vm' vc': Seq.seq S8.t).
  A.pts_to msg vm' ** A.pts_to w vw ** A.pts_to ctr vc' ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
  Seq.length vc' == blocklen /\
  SZ.v idx + 4 * blocklen <= Seq.length vm /\
  Seq.length vm' == Seq.length vm /\
  vals vc' == counter_block (vals vc) 4 /\
  (forall (k: nat). k < Seq.length vm ==>
     Seq.index (vals vm') k ==
       (if SZ.v idx <= k && k < SZ.v idx + blocklen
        then Seq.index (vals vm) k ^^
             Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 0))
                       (k - SZ.v idx)
        else if SZ.v idx + blocklen <= k && k < SZ.v idx + 2 * blocklen
        then Seq.index (vals vm) k ^^
             Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 1))
                       (k - SZ.v idx - blocklen)
        else if SZ.v idx + 2 * blocklen <= k && k < SZ.v idx + 3 * blocklen
        then Seq.index (vals vm) k ^^
             Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 2))
                       (k - SZ.v idx - 2 * blocklen)
        else if SZ.v idx + 3 * blocklen <= k && k < SZ.v idx + 4 * blocklen
        then Seq.index (vals vm) k ^^
             Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 3))
                       (k - SZ.v idx - 3 * blocklen)
        else Seq.index (vals vm) k)))
{
  A.pts_to_len msg;
  A.pts_to_len w;
  A.pts_to_len ctr;
  counter_unfold (vals vc);

  (* The four counter blocks, in registers, before anything else happens.
     The counter is advanced in registers too, and written back once. *)
  let c0 = Vec.load ctr #(as_blk vc);
  let c1 = inc32_vec c0;
  let c2 = inc32_vec c1;
  let c3 = inc32_vec c2;
  let c4 = inc32_vec c3;
  inc32_vec_ok c0;
  inc32_vec_ok c1;
  inc32_vec_ok c2;
  inc32_vec_ok c3;
  Vec.store ctr c4 #(as_blk vc);

  (* Round key zero, added to all four. *)
  let k0 = Sub.sub w 0sz 16sz;
  round_key_slice p.pv (vals vw) 0;
  vals_slice vw 0 16;
  let kv0 = Vec.load k0 #(as_blk (Seq.slice vw 0 16));
  Sub.unsub_id w (SZ.v 0sz) (SZ.v 16sz) k0;
  cipher_start p.pv (vals vw) (counter_block (vals vc) 0);
  cipher_start p.pv (vals vw) (counter_block (vals vc) 1);
  cipher_start p.pv (vals vw) (counter_block (vals vc) 2);
  cipher_start p.pv (vals vw) (counter_block (vals vc) 3);

  let mut s0 = Vec.vxor c0 kv0;
  let mut s1 = Vec.vxor c1 kv0;
  let mut s2 = Vec.vxor c2 kv0;
  let mut s3 = Vec.vxor c3 kv0;
  let mut i = 1sz;
  let mut off = 16sz;

  while (let vi = !i; SZ.lt vi p.pnr)
  invariant exists* (vi: SZ.t) (vo: SZ.t) (u0: Vec.t) (u1: Vec.t)
                    (u2: Vec.t) (u3: Vec.t).
    pts_to i vi ** pts_to off vo ** pts_to s0 u0 ** pts_to s1 u1 **
    pts_to s2 u2 ** pts_to s3 u3 ** A.pts_to w vw **
    pure (1 <= SZ.v vi /\ SZ.v vi <= nr p.pv /\ SZ.v vo == 16 * SZ.v vi /\
          Seq.length vw == xkeylen p.pv /\
          Seq.length vc == blocklen /\
          rounds p.pv (vals vw) (Vec.bv u0) (SZ.v vi) ==
            cipher p.pv (vals vw) (counter_block (vals vc) 0) /\
          rounds p.pv (vals vw) (Vec.bv u1) (SZ.v vi) ==
            cipher p.pv (vals vw) (counter_block (vals vc) 1) /\
          rounds p.pv (vals vw) (Vec.bv u2) (SZ.v vi) ==
            cipher p.pv (vals vw) (counter_block (vals vc) 2) /\
          rounds p.pv (vals vw) (Vec.bv u3) (SZ.v vi) ==
            cipher p.pv (vals vw) (counter_block (vals vc) 3))
  decreases (nr p.pv - SZ.v (!i))
  {
    let vi = !i;
    let vo = !off;
    let u0 = !s0;
    let u1 = !s1;
    let u2 = !s2;
    let u3 = !s3;
    round_key_slice p.pv (vals vw) (SZ.v vi);
    vals_slice vw (SZ.v vo) (SZ.v vo + 16);
    rounds_step p.pv (vals vw) (Vec.bv u0) (SZ.v vi);
    rounds_step p.pv (vals vw) (Vec.bv u1) (SZ.v vi);
    rounds_step p.pv (vals vw) (Vec.bv u2) (SZ.v vi);
    rounds_step p.pv (vals vw) (Vec.bv u3) (SZ.v vi);
    let vo2 = SZ.add vo 16sz;
    let kb = Sub.sub w vo vo2;
    let kv = Vec.load kb #(as_blk (Seq.slice vw (SZ.v vo) (SZ.v vo2)));
    Sub.unsub_id w (SZ.v vo) (SZ.v vo2) kb;
    s0 := Vec.aesenc u0 kv;
    s1 := Vec.aesenc u1 kv;
    s2 := Vec.aesenc u2 kv;
    s3 := Vec.aesenc u3 kv;
    i := SZ.add vi 1sz;
    off := SZ.add vo 16sz;
  };

  let vn = !i;
  let vo = !off;
  let u0 = !s0;
  let u1 = !s1;
  let u2 = !s2;
  let u3 = !s3;
  round_key_slice p.pv (vals vw) (SZ.v vn);
  vals_slice vw (SZ.v vo) (SZ.v vo + 16);
  rounds_last p.pv (vals vw) (Vec.bv u0);
  rounds_last p.pv (vals vw) (Vec.bv u1);
  rounds_last p.pv (vals vw) (Vec.bv u2);
  rounds_last p.pv (vals vw) (Vec.bv u3);
  let vo2 = SZ.add vo 16sz;
  let kb = Sub.sub w vo vo2;
  let kv = Vec.load kb #(as_blk (Seq.slice vw (SZ.v vo) (SZ.v vo2)));
  Sub.unsub_id w (SZ.v vo) (SZ.v vo2) kb;
  let r0 = Vec.aesenclast u0 kv;
  let r1 = Vec.aesenclast u1 kv;
  let r2 = Vec.aesenclast u2 kv;
  let r3 = Vec.aesenclast u3 kv;

  assert (pure (Vec.bv r0 == cipher p.pv (vals vw) (counter_block (vals vc) 0)));
  assert (pure (Vec.bv r1 == cipher p.pv (vals vw) (counter_block (vals vc) 1)));
  assert (pure (Vec.bv r2 == cipher p.pv (vals vw) (counter_block (vals vc) 2)));
  assert (pure (Vec.bv r3 == cipher p.pv (vals vw) (counter_block (vals vc) 3)));

  (* The four stores.  Each one is stated against the value the previous one
     left behind; the ranges are disjoint, so composing them is a case split
     per byte, but the solver will not do it without being shown each step. *)
  let i1 = SZ.add idx 16sz;
  let i2 = SZ.add idx 32sz;
  let i3 = SZ.add idx 48sz;

  xor_at_ni msg idx r0;
  with vmA. assert A.pts_to msg vmA;
  assert (pure (Seq.length vmA == Seq.length vm /\
    (forall (k: nat). k < Seq.length vm ==>
       Seq.index (vals vmA) k ==
         (if SZ.v idx <= k && k < SZ.v idx + blocklen
          then Seq.index (vals vm) k ^^ Seq.index (Vec.bv r0) (k - SZ.v idx)
          else Seq.index (vals vm) k))));

  xor_at_ni msg i1 r1;
  with vmB. assert A.pts_to msg vmB;
  assert (pure (Seq.length vmB == Seq.length vm /\
    (forall (k: nat). k < Seq.length vm ==>
       Seq.index (vals vmB) k ==
         (if SZ.v i1 <= k && k < SZ.v i1 + blocklen
          then Seq.index (vals vmA) k ^^ Seq.index (Vec.bv r1) (k - SZ.v i1)
          else Seq.index (vals vmA) k))));

  xor_at_ni msg i2 r2;
  with vmC. assert A.pts_to msg vmC;
  assert (pure (Seq.length vmC == Seq.length vm /\
    (forall (k: nat). k < Seq.length vm ==>
       Seq.index (vals vmC) k ==
         (if SZ.v i2 <= k && k < SZ.v i2 + blocklen
          then Seq.index (vals vmB) k ^^ Seq.index (Vec.bv r2) (k - SZ.v i2)
          else Seq.index (vals vmB) k))));

  xor_at_ni msg i3 r3;
  with vmD. assert A.pts_to msg vmD;
  assert (pure (Seq.length vmD == Seq.length vm /\
    (forall (k: nat). k < Seq.length vm ==>
       Seq.index (vals vmD) k ==
         (if SZ.v i3 <= k && k < SZ.v i3 + blocklen
          then Seq.index (vals vmC) k ^^ Seq.index (Vec.bv r3) (k - SZ.v i3)
          else Seq.index (vals vmC) k))));

  assert (pure (forall (k: nat). k < Seq.length vm ==>
    Seq.index (vals vmD) k ==
      (if SZ.v idx <= k && k < SZ.v idx + blocklen
       then Seq.index (vals vm) k ^^ Seq.index (Vec.bv r0) (k - SZ.v idx)
       else if SZ.v idx + blocklen <= k && k < SZ.v idx + 2 * blocklen
       then Seq.index (vals vm) k ^^
            Seq.index (Vec.bv r1) (k - SZ.v idx - blocklen)
       else if SZ.v idx + 2 * blocklen <= k && k < SZ.v idx + 3 * blocklen
       then Seq.index (vals vm) k ^^
            Seq.index (Vec.bv r2) (k - SZ.v idx - 2 * blocklen)
       else if SZ.v idx + 3 * blocklen <= k && k < SZ.v idx + 4 * blocklen
       then Seq.index (vals vm) k ^^
            Seq.index (Vec.bv r3) (k - SZ.v idx - 3 * blocklen)
       else Seq.index (vals vm) k)));
  ()
}

#pop-options
