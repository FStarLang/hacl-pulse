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

(** {2 The cipher} *)

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
  Vec.store st r #(as_blk v0);
  vals_len (Vec.vv r);
  ()
}

#pop-options
