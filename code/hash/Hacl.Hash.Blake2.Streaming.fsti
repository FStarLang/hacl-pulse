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

(** BLAKE2 as a stream: init, update, digest.

    The three functions below are the whole of what the named streaming
    hashes in [Hacl.Streaming.Blake2] need.  Each is stated against
    [Spec.Blake2.Streaming]'s [stream_ok], which relates the accumulator,
    the buffer and the stored length to the bytes seen so far, so a caller
    never has to know how the state is laid out or where the block
    boundary falls.

    The implementation is long -- the overflow branch of [update] alone
    fills a buffer, compresses it, compresses [(rest - 1) / block_len]
    more blocks straight out of the caller's data and keeps the last one --
    and it is by a wide margin the most expensive module in the library to
    check.  None of that cost belongs to its clients, and with this
    interface none of it is paid by them: [Hacl.Streaming.Blake2] is
    checked against the three statements below while the implementation is
    still being checked beside it. *)
module Hacl.Hash.Blake2.Streaming

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Spec.Blake2
open Spec.Blake2.Streaming
open Hacl.Hash.Blake2.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost

(** Reset to the empty message under [key].  A nonempty key goes straight
    into the buffer as a full block and the stored length starts at one
    block; an empty key leaves both at zero. *)
val init_impl (#t: Type0) {| w: word t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (acc: A.array t) (buf: A.array S8.t) (tot: A.array SZ.t)
              (ivs: A.array t) (key: A.array S8.t) (klen: SZ.t)
              (#vacc: erased (Seq.seq t)) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
              (#pi: perm) (#vi: erased (Seq.seq t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
              A.pts_to ivs #pi vi ** A.pts_to key #pk vkey **
              pure (Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
                    Seq.length vtot == 1 /\ Seq.length vi == 8 /\
                    reveal vi == G.reveal p.iv /\
                    Seq.length vkey <= max_key_len #t /\
                    3 * block_len #t < pow2 64)
              ** pure (SZ.v klen == Seq.length vkey))
    (ensures fun _ ->
             exists* (vacc': Seq.seq t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
             A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
             A.pts_to ivs #pi vi ** A.pts_to key #pk vkey **
             pure (Seq.length vkey <= max_key_len #t /\
                   stream_ok p vkey (Seq.empty #S8.t) vacc' vbuf' vtot'))

(** Absorb [dlen] more bytes.  [vv], [mw] and [blk] are scratch the caller
    owns; their contents on exit are unspecified beyond their lengths. *)
val update_impl (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] p: params t)
                (acc: A.array t) (vv: A.array t) (mw: A.array t) (blk: A.array S8.t)
                (ivs: A.array t) (sg: A.array SZ.t)
                (buf: A.array S8.t) (tot: A.array SZ.t) (data: A.array S8.t) (dlen: SZ.t)
                (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq t)) (#vv0: erased (Seq.seq t))
                (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#psg: perm) (#vsg: erased (Seq.seq SZ.t))
                (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to acc vacc ** A.pts_to vv vv0 ** A.pts_to mw vm0 **
              A.pts_to blk vblk0 ** A.pts_to ivs #pi vi ** A.pts_to sg #psg vsg **
              A.pts_to buf vbuf ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
              pure (Seq.length vv0 == 16 /\ Seq.length vm0 == 16 /\
                    Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
                    reveal vi == G.reveal p.iv /\ sigma_ok vsg /\
                    stream_ok p key seen vacc vbuf vtot /\
                    Seq.length (stream #t key seen) + Seq.length vdata +
                      2 * block_len #t < pow2 64 /\
                    SZ.fits (Seq.length (stream #t key seen) + Seq.length vdata))
              ** pure (SZ.v dlen == Seq.length vdata))
    (ensures fun _ ->
             exists* (vacc': Seq.seq t) (vv1: Seq.seq t) (vm1: Seq.seq t)
                     (vblk1: Seq.seq S8.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
             A.pts_to acc vacc' ** A.pts_to vv vv1 ** A.pts_to mw vm1 **
             A.pts_to blk vblk1 ** A.pts_to ivs #pi vi ** A.pts_to sg #psg vsg **
             A.pts_to buf vbuf' ** A.pts_to tot vtot' ** A.pts_to data #pd vdata **
             pure (Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
                   Seq.length vblk1 == block_len #t /\
                   stream_ok p key (Seq.append seen vdata) vacc' vbuf' vtot'))

(** Write the hash of what has been seen.  The state is left usable: the
    accumulator is copied and a copy of the buffer is padded, so digests
    and updates may be interleaved. *)
val digest_impl (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] p: params t)
                (acc: A.array t) (vv: A.array t) (mw: A.array t) (blk: A.array S8.t)
                (ivs: A.array t) (sg: A.array SZ.t)
                (buf: A.array S8.t) (tot: A.array SZ.t) (out: A.array S8.t)
                (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq t)) (#vv0: erased (Seq.seq t))
                (#vm0: erased (Seq.seq t)) (#vblk0: erased (Seq.seq S8.t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#psg: perm) (#vsg: erased (Seq.seq SZ.t))
                (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to acc #pa vacc ** A.pts_to vv vv0 ** A.pts_to mw vm0 **
              A.pts_to blk vblk0 ** A.pts_to ivs #pi vi ** A.pts_to sg #psg vsg **
              A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot ** A.pts_to out vout **
              pure (Seq.length vv0 == 16 /\ Seq.length vm0 == 16 /\
                    Seq.length vblk0 == block_len #t /\ Seq.length vi == 8 /\
                    reveal vi == G.reveal p.iv /\ sigma_ok vsg /\
                    Seq.length vout == hash_bytes p /\
                    stream_ok p key seen vacc vbuf vtot))
    (ensures fun _ ->
             exists* (vv1: Seq.seq t) (vm1: Seq.seq t) (vblk1: Seq.seq S8.t)
                     (vout': Seq.seq S8.t).
             A.pts_to acc #pa vacc ** A.pts_to vv vv1 ** A.pts_to mw vm1 **
             A.pts_to blk vblk1 ** A.pts_to ivs #pi vi ** A.pts_to sg #psg vsg **
             A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot ** A.pts_to out vout' **
             pure (Seq.length vv1 == 16 /\ Seq.length vm1 == 16 /\
                   Seq.length vblk1 == block_len #t /\
                   Seq.length key <= max_key_len #t /\
                   vout' == blake2 p key seen))
