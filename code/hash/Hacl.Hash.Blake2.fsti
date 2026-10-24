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

(** One-shot BLAKE2.

    [blake2_impl] is the whole hash: set up the state from the parameters,
    compress every block of the (optional) key and the message, then write
    the state out little endian.  The pieces it is built from are shared
    with the streaming interface, so they are exported too, but the block
    loop and its invariants are not. *)
module Hacl.Hash.Blake2

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Hacl.Spec.Loops
open Spec.Blake2
open Spec.Blake2.Constants
open Hacl.Hash.Blake2.Core
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module U32 = FStar.UInt32
module G = FStar.Ghost
module GA = Pulse.Lib.GlobalArray

(** The block length as a machine integer.  The refinement is the whole
    content: clients index and bound with it, they never unfold it. *)
val block_len_sz (#t: Type0) {| w: word t |} : n: SZ.t { SZ.v n == block_len #t }

val read_block (#t: Type0) {| w: word t |}
              (blk: A.array S8.t) (s: A.array S8.t) (len: SZ.t) (off: SZ.t)
              (#vblk0: erased (Seq.seq S8.t))
              (#ps: perm) (#vs: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to blk vblk0 ** A.pts_to s #ps vs **
             pure (Seq.length vblk0 == block_len #t)
             ** pure (SZ.v len == Seq.length vs))
    (ensures fun _ -> A.pts_to blk (pad_block #t (reveal vs) (SZ.v off)) ** A.pts_to s #ps vs)

val load_block (#t: Type0) {| w: word t |}
              (mw: A.array t) (blk: A.array S8.t)
              (#vm0: erased (Seq.seq t))
              (#pb: perm) (#vb: erased (Seq.lseq S8.t (block_len #t)))
  : stt unit
    (requires A.pts_to mw vm0 ** A.pts_to blk #pb vb **
             pure (Seq.length vm0 == 16))
    (ensures fun _ -> A.pts_to mw (words_from_le block_words (reveal vb)) ** A.pts_to blk #pb vb)

val init_state (#t: Type0) {| w: word t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (h: A.array t) (ivs: A.array t) (klen: SZ.t)
              (#vh0: erased (Seq.seq t))
              (#pi: perm) (#vi: erased (Seq.seq t))
  : stt unit
    (requires A.pts_to h vh0 ** A.pts_to ivs #pi vi **
             pure (Seq.length vh0 == 8 /\ Seq.length vi == 8 /\
                   reveal vi == G.reveal p.iv /\ SZ.v klen <= max_key_len #t))
    (ensures fun _ -> exists* (vh: Seq.seq t). A.pts_to h vh ** A.pts_to ivs #pi vi **
      pure (SZ.v klen <= max_key_len #t /\ Seq.length vh == 8 /\ vh == init p (SZ.v klen)))

val write_digest_le (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                   ([@@@FStar.Attributes.monomorphize] p: params t)
                   (out: A.array S8.t) (st: A.array t)
                   (#vout: erased (Seq.seq S8.t)) (#pst: perm) (#vst: erased (Seq.lseq t 8))
  : stt unit
    (requires A.pts_to out vout ** A.pts_to st #pst vst **
             pure (Seq.length vout == (hash_bytes p)))
    (ensures fun _ -> A.pts_to out (final p vst) ** A.pts_to st #pst vst)

val blake2_impl (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
               ([@@@FStar.Attributes.monomorphize] p: params t)
               ([@@@FStar.Attributes.monomorphize] iva: GA.static_array t)
               (out: A.array S8.t)
               (key: A.array S8.t) (klen: SZ.t) (msg: A.array S8.t) (mlen: SZ.t)
               (#vout: erased (Seq.seq S8.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
               (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to out vout **
             A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
             pure (Seq.length (GA.static_array_elems iva) == 8 /\
                   GA.static_array_elems iva == G.reveal p.iv /\
                   Seq.length vout == (hash_bytes p) /\
                   Seq.length vkey <= max_key_len #t /\
                   Seq.length vmsg + 2 * block_len #t < pow2 64 /\
                   SZ.fits (Seq.length vmsg + 2 * block_len #t))
             ** pure (SZ.v klen == Seq.length vkey)
             ** pure (SZ.v mlen == Seq.length vmsg))
    (ensures fun _ -> exists* (vout': Seq.seq S8.t).
      A.pts_to out vout' **
      A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
      pure (Seq.length vkey <= max_key_len #t /\ vout' == blake2 p (reveal vkey) (reveal vmsg)))

