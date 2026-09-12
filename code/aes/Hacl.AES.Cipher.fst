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

(** The cipher of FIPS 197 section 5.1, and counter mode on top of it.

    The round loop's invariant is the whole remaining computation: at round
    [i] the state is such that [rounds w st i] is still the answer the caller
    was promised.  That is exactly one unfolding of [Spec.AES.rounds] per
    step, forwards, with no accumulator and no arithmetic on the round index
    beyond the round key's offset -- which is carried alongside rather than
    multiplied out, so that no [SizeT] multiplication appears.

    There is no inverse cipher.  Every mode this library offers -- counter
    mode and, on top of it, GCM -- uses the forward direction only, and the
    equipment for decryption (InvSubBytes, InvMixColumns, and a second
    thousand-line S-box) would be dead weight. *)
module Hacl.AES.Cipher

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core
open Hacl.AES

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The pure side} *)

let round_key_slice (v: variant) (w: Seq.lseq elem (xkeylen v)) (i: nat { i <= nr v })
  : Lemma (round_key v w i == Seq.slice w (16 * i) (16 * i + 16))
  = ()

let round_unfold (k st: block)
  : Lemma (round k st == add_round_key (mix_columns (shift_rows (sub_bytes st))) k)
  = ()

let last_round_unfold (k st: block)
  : Lemma (last_round k st == add_round_key (shift_rows (sub_bytes st)) k)
  = ()

#push-options "--fuel 2 --ifuel 1"

let cipher_start (v: variant) (w: Seq.lseq elem (xkeylen v)) (st: block)
  : Lemma (rounds v w (add_round_key st (round_key v w 0)) 1 == cipher v w st)
  = ()

let rounds_step (v: variant) (w: Seq.lseq elem (xkeylen v)) (st: block) (i: nat)
  : Lemma (requires 1 <= i /\ i < nr v)
          (ensures rounds v w st i ==
                   rounds v w (round (round_key v w i) st) (i + 1))
  = ()

let rounds_last (v: variant) (w: Seq.lseq elem (xkeylen v)) (st: block)
  : Lemma (rounds v w st (nr v) == last_round (round_key v w (nr v)) st)
  = ()

#pop-options

(** {2 The cipher} *)

fn cipher_impl ([@@@FStar.Attributes.monomorphize] p: params)
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
  round_key_slice p.pv (vals vw) 0;
  add_round_key_impl st w 0sz;
  with va. assert A.pts_to st va;
  cipher_start p.pv (vals vw) (vals v0);

  let mut i = 1sz;
  let mut off = 16sz;
  while (let vi = !i; SZ.lt vi p.pnr)
  invariant exists* (vi: SZ.t) (vo: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** pts_to off vo ** A.pts_to st v ** A.pts_to w vw **
    pure (1 <= SZ.v vi /\ SZ.v vi <= nr p.pv /\ SZ.v vo == 16 * SZ.v vi /\
          Seq.length vw == xkeylen p.pv /\ Seq.length v0 == blocklen /\
          Seq.length v == blocklen /\
          rounds p.pv (vals vw) (vals v) (SZ.v vi) ==
            cipher p.pv (vals vw) (vals v0))
  decreases (nr p.pv - SZ.v (!i))
  {
    let vi = !i;
    let vo = !off;
    with v. assert A.pts_to st v;
    rounds_step p.pv (vals vw) (vals v) (SZ.v vi);
    round_key_slice p.pv (vals vw) (SZ.v vi);
    sub_bytes_impl st;
    shift_rows_impl st;
    mix_columns_impl st;
    add_round_key_impl st w vo;
    with v'. assert A.pts_to st v';
    round_unfold (Seq.slice (vals vw) (SZ.v vo) (SZ.v vo + blocklen)) (vals v);
    i := SZ.add vi 1sz;
    off := SZ.add vo 16sz;
  };
  let vn = !i;
  let vo = !off;
  with v. assert A.pts_to st v;
  rounds_last p.pv (vals vw) (vals v);
  round_key_slice p.pv (vals vw) (SZ.v vn);
  sub_bytes_impl st;
  shift_rows_impl st;
  add_round_key_impl st w vo;
  with v'. assert A.pts_to st v';
  last_round_unfold (Seq.slice (vals vw) (SZ.v vo) (SZ.v vo + blocklen)) (vals v);
  A.pts_to_len st;
}

#pop-options
