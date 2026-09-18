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

(** HPKE's labeled KDF.

    RFC 9180 never calls HKDF directly: every extract and expand is domain
    separated by the protocol version, the ciphersuite identifier and a
    label.  These three functions are that convention, and they are all
    [Hacl.HPKE] and [Hacl.HPKE.KEM] use of the KDF.  Assembling the
    prefixes into a scratch buffer is [Hacl.HPKE.Labeled]'s business. *)
module Hacl.HPKE.Labeled

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HPKE

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

(** The scratch buffer is the version, the suite identifier, the label and
    the caller's string, and the first three are bounded by construction.
    Restating the bound as a machine fact once keeps [SZ.fits] obligations
    out of the three functions below. *)
val prefix_bound (#t: Type0) {| word t |} (p: params t) (n: nat)
  : Lemma (requires n < pow2 32)
          (ensures fits p n /\ block_len #t <= 256 /\ hash_bytes p <= 128 /\
                   9 + 16 + 16 + n < pow2 61 /\
                   block_len #t + hash_bytes p + 9 + 16 + 16 + n + 1 < pow2 61 /\
                   block_len #t + hash_bytes p + 9 + 16 + 16 + n + 1 < max_input #t)

val labeled_extract_impl (#t: Type0) {| w: word t |}
                        ([@@@FStar.Attributes.monomorphize] p: params t)
                        (kt: A.array t) (ivt: A.array t)
                        (out: A.array S8.t)
                        (sid: A.array S8.t) (sid_len: SZ.t)
                        (salt: A.array S8.t) (salt_len: SZ.t)
                        (lbl: A.array S8.t) (lbl_len: SZ.t)
                        (ikm: A.array S8.t) (ikm_len: SZ.t)
                        (#pk: perm) (#vk: erased (Seq.seq t))
                        (#pi: perm) (#vi: erased (Seq.seq t))
                        (#vout: erased (Seq.seq S8.t))
                        (#pd: perm) (#vsid: erased (Seq.seq S8.t))
                        (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
                        (#pl: perm) (#vlabel: erased (Seq.seq S8.t))
                        (#pm: perm) (#vikm: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
             A.pts_to sid #pd vsid ** A.pts_to salt #ps vsalt **
             A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
             pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
                   Seq.length vout == hash_bytes p /\
                   Seq.length vsid <= 16 /\ Seq.length vsalt <= 64 /\
                   Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\
                   SZ.fits (block_len #t + 7 + Seq.length vsid + Seq.length vlabel + Seq.length vikm))
             ** pure (SZ.v sid_len == Seq.length vsid)
             ** pure (SZ.v salt_len == Seq.length vsalt)
             ** pure (SZ.v lbl_len == Seq.length vlabel)
             ** pure (SZ.v ikm_len == Seq.length vikm))
    (ensures fun _ -> exists* vout'.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to sid #pd vsid ** A.pts_to salt #ps vsalt **
      A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
      pure (Seq.length vsid <= 16 /\ Seq.length vsalt <= 64 /\
            Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\ fits p (Seq.length vikm) /\
            vout' == labeled_extract p vsid vsalt vlabel vikm))

val labeled_expand_impl (#t: Type0) {| w: word t |}
                       ([@@@FStar.Attributes.monomorphize] p: params t)
                       (kt: A.array t) (ivt: A.array t)
                       (out: A.array S8.t) (out_len: SZ.t)
                       (prk: A.array S8.t) (prk_len: SZ.t)
                       (sid: A.array S8.t) (sid_len: SZ.t)
                       (lbl: A.array S8.t) (lbl_len: SZ.t)
                       (info: A.array S8.t) (info_len: SZ.t)
                       (#pk: perm) (#vk: erased (Seq.seq t))
                       (#pi: perm) (#vi: erased (Seq.seq t))
                       (#vout: erased (Seq.seq S8.t))
                       (#pp: perm) (#vprk: erased (Seq.seq S8.t))
                       (#pd: perm) (#vsid: erased (Seq.seq S8.t))
                       (#pl: perm) (#vlabel: erased (Seq.seq S8.t))
                       (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
             A.pts_to prk #pp vprk ** A.pts_to sid #pd vsid **
             A.pts_to lbl #pl vlabel ** A.pts_to info #pf vinfo **
             pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
                   Seq.length vprk <= 64 /\
                   Seq.length vsid <= 16 /\ Seq.length vlabel <= 16 /\
                   Seq.length vinfo < pow2 32 /\
                   Seq.length vout < 65536 /\ Seq.length vout <= 255 * hash_bytes p /\
                   SZ.fits (block_len #t + hash_bytes p + 9 + Seq.length vsid + Seq.length vlabel +
                            Seq.length vinfo + 1))
             ** pure (SZ.v out_len == Seq.length vout)
             ** pure (SZ.v prk_len == Seq.length vprk)
             ** pure (SZ.v sid_len == Seq.length vsid)
             ** pure (SZ.v lbl_len == Seq.length vlabel)
             ** pure (SZ.v info_len == Seq.length vinfo))
    (ensures fun _ -> exists* vout'.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to prk #pp vprk ** A.pts_to sid #pd vsid **
      A.pts_to lbl #pl vlabel ** A.pts_to info #pf vinfo **
      pure (Seq.length vsid <= 16 /\ Seq.length vlabel <= 16 /\ Seq.length vprk <= 64 /\
            Seq.length vinfo < pow2 32 /\ fits p (Seq.length vinfo) /\
            Seq.length vout' == Seq.length vout /\
            Seq.length vout' < 65536 /\ Seq.length vout' <= 255 * hash_bytes p /\
            vout' == labeled_expand p vsid vprk vlabel vinfo (Seq.length vout')))

val labeled_extract_nosalt (#t: Type0) {| w: word t |}
                          ([@@@FStar.Attributes.monomorphize] p: params t)
                          (kt: A.array t) (ivt: A.array t)
                          (out: A.array S8.t)
                          (sid: A.array S8.t) (sid_len: SZ.t)
                          (lbl: A.array S8.t) (lbl_len: SZ.t)
                          (ikm: A.array S8.t) (ikm_len: SZ.t)
                          (#pk: perm) (#vk: erased (Seq.seq t))
                          (#pi: perm) (#vi: erased (Seq.seq t))
                          (#vout: erased (Seq.seq S8.t))
                          (#pd: perm) (#vsid: erased (Seq.seq S8.t))
                          (#pl: perm) (#vlabel: erased (Seq.seq S8.t))
                          (#pm: perm) (#vikm: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
             A.pts_to sid #pd vsid ** A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
             pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
                   Seq.length vout == hash_bytes p /\
                   Seq.length vsid <= 16 /\
                   Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\
                   SZ.fits (block_len #t + 7 + Seq.length vsid + Seq.length vlabel + Seq.length vikm))
             ** pure (SZ.v sid_len == Seq.length vsid)
             ** pure (SZ.v lbl_len == Seq.length vlabel)
             ** pure (SZ.v ikm_len == Seq.length vikm))
    (ensures fun _ -> exists* vout'.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
      A.pts_to sid #pd vsid ** A.pts_to lbl #pl vlabel ** A.pts_to ikm #pm vikm **
      pure (Seq.length vsid <= 16 /\
            Seq.length vlabel <= 16 /\ Seq.length vikm < pow2 32 /\ fits p (Seq.length vikm) /\
            vout' == labeled_extract p vsid Seq.empty vlabel vikm))

