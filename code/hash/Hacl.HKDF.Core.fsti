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

(** HKDF-Expand.

    [expand] is a chain of HMACs, each over the previous block, the info
    string and a counter byte, truncated to the requested length.  Running
    it is one loop with a scratch buffer whose size depends on the info
    string; none of that is visible to [Hacl.HKDF] or to HPKE's labeled
    wrapper, which need only that the output is [Spec.HKDF.expand]. *)
module Hacl.HKDF.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.SHANI
open Spec.HMAC
open Spec.HKDF

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32

val expand_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (ivt: A.array t) (out: A.array S8.t) (len: SZ.t)
               (prk: A.array S8.t) (plen: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#vout: erased (Seq.seq S8.t))
               (#pp: perm) (#vprk: erased (Seq.seq S8.t))
               (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
             A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
             pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
                   Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p vinfo /\
                   block_len #t + (hash_bytes p) + Seq.length vinfo + 1 < pow2 61 /\
                   SZ.fits (block_len #t + (hash_bytes p) + Seq.length vinfo + 1) /\
                   Seq.length vout <= 255 * (hash_bytes p) /\
                   SZ.v len == Seq.length vout /\ SZ.v ilen == Seq.length vinfo)
             ** pure (SZ.v plen == Seq.length vprk))
    (ensures fun _ -> exists* vout'.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
      pure (prk_ok p vprk /\ info_ok p vinfo /\
            Seq.length vout' == Seq.length vout /\
            Seq.length vout' <= 255 * (hash_bytes p) /\
            vout' == expand p vprk vinfo (Seq.length vout')))

(** The same, over the SHA extensions; see the implementation for why this
    is a copy rather than a branch. *)
val expand_impl_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
               (kt: A.array S32.t) (ivt: A.array S32.t) (out: A.array S8.t) (len: SZ.t)
               (prk: A.array S8.t) (plen: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
               (#pk: perm) (#vk: erased (Seq.seq S32.t))
               (#pi: perm) (#vi: erased (Seq.seq S32.t))
               (#vout: erased (Seq.seq S8.t))
               (#pp: perm) (#vprk: erased (Seq.seq S8.t))
               (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
             A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
             pure (is_sha256 p /\ reveal vk == (reveal p.k <: Seq.seq S32.t) /\ reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
                   Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p vinfo /\
                   block_len #S32.t + (hash_bytes p) + Seq.length vinfo + 1 < pow2 61 /\
                   SZ.fits (block_len #S32.t + (hash_bytes p) + Seq.length vinfo + 1) /\
                   Seq.length vout <= 255 * (hash_bytes p) /\
                   SZ.v len == Seq.length vout /\ SZ.v ilen == Seq.length vinfo)
             ** pure (SZ.v plen == Seq.length vprk))
    (ensures fun _ -> exists* vout'.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
      pure (prk_ok p vprk /\ info_ok p vinfo /\
            Seq.length vout' == Seq.length vout /\
            Seq.length vout' <= 255 * (hash_bytes p) /\
            vout' == expand p vprk vinfo (Seq.length vout')))
