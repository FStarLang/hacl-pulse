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

    The key schedule is {i not} done here.  [Hacl.AES.Key] already computes it
    portably and in constant time, it happens once per message rather than
    once per block, and doing it with [AESKEYGENASSIST] would need a separate
    extern per round constant.  This module reads the expanded key sixteen
    bytes at a time, exactly as the portable cipher does.

    The two attributes are what put [target("aes,...")] on this function and
    on everything it exclusively reaches; see [Hacl.Vec128]. *)
module Hacl.AES.NI

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Cipher

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
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
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
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
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
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

(** {2 One counter-mode block}

    The whole of a counter-mode step, with the keystream never written down.
    The counter is loaded into a register, encrypted there, exclusive-ored
    into the message in place, and discarded; the sixteen-byte scratch block
    that [Hacl.AES.CTR] would otherwise copy the counter into, encrypt, and
    read back a byte at a time does not exist on this path.  That scratch
    block is what made the portable driver expensive: it was written by a
    vector store and read by sixteen scalar loads, which is a store-
    forwarding stall on every block on top of the byte traffic. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
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
  assert (pure (Vec.bv ks == cipher p.pv (vals vw) (vals vc)));
  assert (pure (Vec.bv mv == Seq.slice (vals vm) (SZ.v idx) (SZ.v idx2)));
  assert (pure (forall (k: nat). SZ.v idx <= k /\ k < SZ.v idx2 ==>
    Seq.index vm' k == Seq.index (Vec.vv r) (k - SZ.v idx)));
  assert (pure (forall (k: nat). SZ.v idx <= k /\ k < SZ.v idx2 ==>
    Seq.index (vals vm') k == Seq.index (Vec.bv r) (k - SZ.v idx)));
  assert (pure (forall (k: nat). SZ.v idx <= k /\ k < SZ.v idx2 ==>
    Seq.index (vals vm') k ==
      Seq.index (Vec.bv mv) (k - SZ.v idx) ^^ Seq.index (Vec.bv ks) (k - SZ.v idx)));
  assert (pure (forall (k: nat). SZ.v idx <= k /\ k < SZ.v idx2 ==>
    Seq.index (vals vm') k ==
      Seq.index (vals vm) k ^^
      Seq.index (cipher p.pv (vals vw) (vals vc)) (k - SZ.v idx)));
  assert (pure (forall (k: nat). k < Seq.length vm /\
                                ~(SZ.v idx <= k /\ k < SZ.v idx2) ==>
    Seq.index (vals vm') k == Seq.index (vals vm) k));
  ()
}

#pop-options
