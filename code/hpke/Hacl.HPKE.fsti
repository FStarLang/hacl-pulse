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

(** HPKE, base and auth modes.

    Setup derives a key schedule from an encapsulated secret; seal and open
    are single-shot encryption and decryption under that schedule.  The
    suite identifier, the key schedule itself and the labeled KDF calls are
    all internal. *)
module Hacl.HPKE

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HPKE
open Hacl.Secret.Word.Instances
open Hacl.Impl.Bytes
open Hacl.HPKE.Tables
open Hacl.HPKE.Labeled
open Hacl.HPKE.KEM
open Hacl.HPKE.AEAD
open Hacl.Impl.Copy
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module B = Hacl.Spec.Bytes
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub

val setup_base_s (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                ([@@@FStar.Attributes.monomorphize] blocks: Hacl.Hash.SHA2.Core.blocks_t cs.kdf)
                (kt: A.array t) (ivt: A.array t)
                (enc: A.array S8.t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (skE: A.array S8.t) (pkR: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#venc: erased (Seq.seq S8.t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pe: perm) (#vskE: erased (Seq.seq S8.t))
                (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc venc **
             A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
             A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
             A.pts_to info #pf vinfo **
             pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
                   reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
                   Seq.length venc == size_dh_public cs.kem /\
                   Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
                   Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
                   Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
                   Seq.length vinfo < pow2 32 /\
                   SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
                   SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
             ** pure (SZ.v info_len == Seq.length vinfo))
    (ensures fun r -> exists* wenc wkey wbn wsq wexp.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc wenc **
      A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
      A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
      A.pts_to info #pf vinfo **
      pure (Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
            Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
            Seq.length wenc == size_dh_public cs.kem /\
            Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
            Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
            r == Some? (setup_s cs Base vskE None vpkR vinfo Seq.empty Seq.empty) /\
            (r ==> (let (e1, c1) =
                      Some?.v (setup_s cs Base vskE None vpkR vinfo Seq.empty Seq.empty) in
                    wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                    wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0))))

val setup_base_r (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                ([@@@FStar.Attributes.monomorphize] blocks: Hacl.Hash.SHA2.Core.blocks_t cs.kdf)
                (kt: A.array t) (ivt: A.array t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (enc: A.array S8.t) (skR: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pn: perm) (#venc: erased (Seq.seq S8.t))
                (#pr: perm) (#vskR: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
             A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
             A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
             A.pts_to info #pf vinfo **
             pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
                   reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
                   Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
                   Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
                   Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
                   Seq.length vinfo < pow2 32 /\
                   SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
                   SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
             ** pure (SZ.v info_len == Seq.length vinfo))
    (ensures fun r -> exists* wkey wbn wsq wexp.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
      A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
      A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
      A.pts_to info #pf vinfo **
      pure (Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
            Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
            Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
            Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
            r == Some? (setup_r cs Base venc vskR None vinfo Seq.empty Seq.empty) /\
            (r ==> (let c1 =
                      Some?.v (setup_r cs Base venc vskR None vinfo Seq.empty Seq.empty) in
                    wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                    wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0))))

val seal_base (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
             ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                { ~(ExportOnly? cs.aead) })
             ([@@@FStar.Attributes.monomorphize] blocks: Hacl.Hash.SHA2.Core.blocks_t cs.kdf)
             (kt: A.array t) (ivt: A.array t)
             (enc: A.array S8.t) (ct: A.array S8.t) (tag: A.array S8.t)
             (skE: A.array S8.t) (pkR: A.array S8.t)
             (info: A.array S8.t) (info_len: SZ.t)
             (aad: A.array S8.t) (aad_len: SZ.t)
             (pt: A.array S8.t) (pt_len: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#venc: erased (Seq.seq S8.t))
             (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
             (#pe: perm) (#vskE: erased (Seq.seq S8.t))
             (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
             (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pp: perm) (#vpt: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc venc **
             A.pts_to ct vct ** A.pts_to tag vtag **
             A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
             A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
             pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
                   reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
                   Seq.length venc == size_dh_public cs.kem /\
                   Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
                   Seq.length vct == Seq.length vpt /\ Seq.length vtag == size_tag cs /\
                   Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
                   Seq.length vpt < pow2 32 /\
                   SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
                   SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1) /\
                   SZ.fits (Seq.length vpt + 16) /\ SZ.fits (Seq.length vaad + 16))
             ** pure (SZ.v info_len == Seq.length vinfo)
             ** pure (SZ.v aad_len == Seq.length vaad)
             ** pure (SZ.v pt_len == Seq.length vpt))
    (ensures fun r -> exists* wenc wct wtag.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc wenc **
      A.pts_to ct wct ** A.pts_to tag wtag **
      A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
      A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
      pure (Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
            Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
            Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
            Seq.length wenc == size_dh_public cs.kem /\
            Seq.length wct == Seq.length vpt /\ Seq.length wtag == size_tag cs /\
            r == Some? (seal_base cs vskE vpkR vinfo vaad vpt) /\
            (r ==> (let (e1, c1, t1) = Some?.v (seal_base cs vskE vpkR vinfo vaad vpt) in
                    wenc == e1 /\ wct == c1 /\ wtag == t1))))

val open_base (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |}
             ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                { ~(ExportOnly? cs.aead) })
             ([@@@FStar.Attributes.monomorphize] blocks: Hacl.Hash.SHA2.Core.blocks_t cs.kdf)
             (kt: A.array t) (ivt: A.array t)
             (pt: A.array S8.t)
             (enc: A.array S8.t) (skR: A.array S8.t)
             (info: A.array S8.t) (info_len: SZ.t)
             (aad: A.array S8.t) (aad_len: SZ.t)
             (ct: A.array S8.t) (ct_len: SZ.t) (tag: A.array S8.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vpt: erased (Seq.seq S8.t))
             (#pn: perm) (#venc: erased (Seq.seq S8.t))
             (#pr: perm) (#vskR: erased (Seq.seq S8.t))
             (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pc: perm) (#vct: erased (Seq.seq S8.t))
             (#pg: perm) (#vtag: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to pt vpt **
             A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
             A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
             A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
             pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
                   reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
                   Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
                   Seq.length vpt == Seq.length vct /\ Seq.length vtag == size_tag cs /\
                   Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
                   Seq.length vct < pow2 32 /\
                   SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
                   SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1) /\
                   SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
             ** pure (SZ.v info_len == Seq.length vinfo)
             ** pure (SZ.v aad_len == Seq.length vaad)
             ** pure (SZ.v ct_len == Seq.length vct))
    (ensures fun r -> exists* wpt.
      A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to pt wpt **
      A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
      A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
      A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
      pure (Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
            Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
            Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
            Seq.length vtag == size_tag cs /\ Seq.length wpt == Seq.length vct /\
            (r <==> open_base_ok cs venc vskR vinfo vaad vct vtag) /\
            (r ==> Some? (open_base cs venc vskR vinfo vct) /\
                   wpt == Some?.v (open_base cs venc vskR vinfo vct))))

