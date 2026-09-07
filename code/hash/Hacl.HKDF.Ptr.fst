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

(** The flat C interface to HKDF.

      void Hacl_HKDF_Ptr_extract_sha256(uint8_t *out,
                                        uint8_t *salt, size_t salt_len,
                                        uint8_t *ikm, size_t ikm_len);
      void Hacl_HKDF_Ptr_expand_sha256(uint8_t *out, size_t out_len,
                                       uint8_t *prk, size_t prk_len,
                                       uint8_t *info, size_t info_len);

    These are the only functions that should be passed to [--custard_entry]. *)
module Hacl.HKDF.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HKDF

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** HKDF-Extract with sha224.  [out] must have room for 28 bytes. *)
fn extract_sha224 (out: AP.ptr S8.t) (salt: AP.ptr S8.t) (salt_len: SZ.t)
    (ikm: AP.ptr S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
         pure (Seq.length vout == 28 /\
               Seq.length vsalt == SZ.v salt_len /\ Seq.length vsalt < pow2 61 /\
               Seq.length vikm == SZ.v ikm_len /\
               SZ.fits (block_len #S32.t + Seq.length vikm) /\
               block_len #S32.t + Seq.length vikm < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S32.t /\
        block_len #S32.t + Seq.length vikm < max_input #S32.t /\
        vout' == extract sha2_224 vsalt vikm)
{
  let so = S.arrayptr_to_slice_intro out 28sz;
  let ss = S.arrayptr_to_slice_intro salt salt_len;
  let si = S.arrayptr_to_slice_intro ikm ikm_len;
  Hacl.HKDF.extract_sha224 so ss si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim so;
}


(** HKDF-Expand with sha224.  [out_len] may be up to 255*28 = 7140. *)
fn expand_sha224 (out: AP.ptr S8.t) (out_len: SZ.t) (prk: AP.ptr S8.t) (prk_len: SZ.t)
    (info: AP.ptr S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
         pure (Seq.length vout == SZ.v out_len /\
               Seq.length vprk == SZ.v prk_len /\ Seq.length vprk < pow2 61 /\
               Seq.length vinfo == SZ.v info_len /\
               block_len #S32.t + 28 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + 28 + Seq.length vinfo + 1) /\
               Seq.length vout <= 7140)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
  pure (prk_ok sha2_224 vprk /\ info_ok sha2_224 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_224) /\
        vout' == expand sha2_224 vprk vinfo (Seq.length vout'))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let sp = S.arrayptr_to_slice_intro prk prk_len;
  let sf = S.arrayptr_to_slice_intro info info_len;
  Hacl.HKDF.expand_sha224 so sp sf;
  S.arrayptr_to_slice_elim sf;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim so;
}


(** HKDF-Extract with sha256.  [out] must have room for 32 bytes. *)
fn extract_sha256 (out: AP.ptr S8.t) (salt: AP.ptr S8.t) (salt_len: SZ.t)
    (ikm: AP.ptr S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
         pure (Seq.length vout == 32 /\
               Seq.length vsalt == SZ.v salt_len /\ Seq.length vsalt < pow2 61 /\
               Seq.length vikm == SZ.v ikm_len /\
               SZ.fits (block_len #S32.t + Seq.length vikm) /\
               block_len #S32.t + Seq.length vikm < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S32.t /\
        block_len #S32.t + Seq.length vikm < max_input #S32.t /\
        vout' == extract sha2_256 vsalt vikm)
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let ss = S.arrayptr_to_slice_intro salt salt_len;
  let si = S.arrayptr_to_slice_intro ikm ikm_len;
  Hacl.HKDF.extract_sha256 so ss si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim so;
}


(** HKDF-Expand with sha256.  [out_len] may be up to 255*32 = 8160. *)
fn expand_sha256 (out: AP.ptr S8.t) (out_len: SZ.t) (prk: AP.ptr S8.t) (prk_len: SZ.t)
    (info: AP.ptr S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
         pure (Seq.length vout == SZ.v out_len /\
               Seq.length vprk == SZ.v prk_len /\ Seq.length vprk < pow2 61 /\
               Seq.length vinfo == SZ.v info_len /\
               block_len #S32.t + 32 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + 32 + Seq.length vinfo + 1) /\
               Seq.length vout <= 8160)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
  pure (prk_ok sha2_256 vprk /\ info_ok sha2_256 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_256) /\
        vout' == expand sha2_256 vprk vinfo (Seq.length vout'))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let sp = S.arrayptr_to_slice_intro prk prk_len;
  let sf = S.arrayptr_to_slice_intro info info_len;
  Hacl.HKDF.expand_sha256 so sp sf;
  S.arrayptr_to_slice_elim sf;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim so;
}


(** HKDF-Extract with sha384.  [out] must have room for 48 bytes. *)
fn extract_sha384 (out: AP.ptr S8.t) (salt: AP.ptr S8.t) (salt_len: SZ.t)
    (ikm: AP.ptr S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
         pure (Seq.length vout == 48 /\
               Seq.length vsalt == SZ.v salt_len /\ Seq.length vsalt < pow2 61 /\
               Seq.length vikm == SZ.v ikm_len /\
               SZ.fits (block_len #S64.t + Seq.length vikm) /\
               block_len #S64.t + Seq.length vikm < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S64.t /\
        block_len #S64.t + Seq.length vikm < max_input #S64.t /\
        vout' == extract sha2_384 vsalt vikm)
{
  let so = S.arrayptr_to_slice_intro out 48sz;
  let ss = S.arrayptr_to_slice_intro salt salt_len;
  let si = S.arrayptr_to_slice_intro ikm ikm_len;
  Hacl.HKDF.extract_sha384 so ss si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim so;
}


(** HKDF-Expand with sha384.  [out_len] may be up to 255*48 = 12240. *)
fn expand_sha384 (out: AP.ptr S8.t) (out_len: SZ.t) (prk: AP.ptr S8.t) (prk_len: SZ.t)
    (info: AP.ptr S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
         pure (Seq.length vout == SZ.v out_len /\
               Seq.length vprk == SZ.v prk_len /\ Seq.length vprk < pow2 61 /\
               Seq.length vinfo == SZ.v info_len /\
               block_len #S64.t + 48 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S64.t + 48 + Seq.length vinfo + 1) /\
               Seq.length vout <= 12240)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
  pure (prk_ok sha2_384 vprk /\ info_ok sha2_384 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_384) /\
        vout' == expand sha2_384 vprk vinfo (Seq.length vout'))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let sp = S.arrayptr_to_slice_intro prk prk_len;
  let sf = S.arrayptr_to_slice_intro info info_len;
  Hacl.HKDF.expand_sha384 so sp sf;
  S.arrayptr_to_slice_elim sf;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim so;
}


(** HKDF-Extract with sha512.  [out] must have room for 64 bytes. *)
fn extract_sha512 (out: AP.ptr S8.t) (salt: AP.ptr S8.t) (salt_len: SZ.t)
    (ikm: AP.ptr S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
         pure (Seq.length vout == 64 /\
               Seq.length vsalt == SZ.v salt_len /\ Seq.length vsalt < pow2 61 /\
               Seq.length vikm == SZ.v ikm_len /\
               SZ.fits (block_len #S64.t + Seq.length vikm) /\
               block_len #S64.t + Seq.length vikm < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to salt #ps vsalt ** AP.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S64.t /\
        block_len #S64.t + Seq.length vikm < max_input #S64.t /\
        vout' == extract sha2_512 vsalt vikm)
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let ss = S.arrayptr_to_slice_intro salt salt_len;
  let si = S.arrayptr_to_slice_intro ikm ikm_len;
  Hacl.HKDF.extract_sha512 so ss si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim so;
}


(** HKDF-Expand with sha512.  [out_len] may be up to 255*64 = 16320. *)
fn expand_sha512 (out: AP.ptr S8.t) (out_len: SZ.t) (prk: AP.ptr S8.t) (prk_len: SZ.t)
    (info: AP.ptr S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
         pure (Seq.length vout == SZ.v out_len /\
               Seq.length vprk == SZ.v prk_len /\ Seq.length vprk < pow2 61 /\
               Seq.length vinfo == SZ.v info_len /\
               block_len #S64.t + 64 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S64.t + 64 + Seq.length vinfo + 1) /\
               Seq.length vout <= 16320)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to prk #pp vprk ** AP.pts_to info #pf vinfo **
  pure (prk_ok sha2_512 vprk /\ info_ok sha2_512 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_512) /\
        vout' == expand sha2_512 vprk vinfo (Seq.length vout'))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let sp = S.arrayptr_to_slice_intro prk prk_len;
  let sf = S.arrayptr_to_slice_intro info info_len;
  Hacl.HKDF.expand_sha512 so sp sf;
  S.arrayptr_to_slice_elim sf;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim so;
}

