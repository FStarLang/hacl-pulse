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

(** HKDF-SHA-224/256/384/512, RFC 5869.

    [extract salt ikm] is HMAC and forwards to [Hacl.HMAC]; [expand] lays out
    the round-constant table and the initial state and calls
    [Hacl.HKDF.Core.expand_impl]. *)
module Hacl.HKDF

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HKDF
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Tables
open Hacl.Impl.Table
open Hacl.HKDF.Core

module Vec = Hacl.Vec128

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

(** HKDF-Extract with sha224.  [out] must have room for 28 bytes. *)
fn extract_sha224 (out: A.array S8.t) (salt: A.array S8.t) (salt_len: SZ.t) (ikm: A.array S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
         pure (Seq.length vout == 28 /\ Seq.length vsalt < pow2 61 /\
               SZ.fits (block_len #S32.t + Seq.length vikm) /\
               block_len #S32.t + Seq.length vikm < pow2 61)
         ** pure (SZ.v salt_len == Seq.length vsalt)
         ** pure (SZ.v ikm_len == Seq.length vikm)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S32.t /\
        block_len #S32.t + Seq.length vikm < max_input #S32.t /\
        vout' == extract sha2_224 vsalt vikm)
{
  Hacl.HMAC.hmac_sha224 out salt salt_len ikm ikm_len;
}

(** HKDF-Expand with sha224.  [out] may be up to 255*28 = 7140 bytes. *)
fn expand_sha224 (out: A.array S8.t) (out_len: SZ.t) (prk: A.array S8.t) (prk_len: SZ.t) (info: A.array S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (Seq.length vprk < pow2 61 /\
               block_len #S32.t + 28 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + 28 + Seq.length vinfo + 1) /\
               Seq.length vout <= 7140)
         ** pure (SZ.v out_len == Seq.length vout)
         ** pure (SZ.v prk_len == Seq.length vprk)
         ** pure (SZ.v info_len == Seq.length vinfo)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
  pure (prk_ok sha2_224 vprk /\ info_ok sha2_224 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_224) /\
        vout' == expand sha2_224 vprk vinfo (Seq.length vout'))
{
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len info;
  let kt = table k256_arr 64sz;
  let ivt = table iv224_arr 8sz;
  max_input_bound ();
  let ni = Vec.sha_supported ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if ni
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    pure (prk_ok sha2_224 vprk /\ info_ok sha2_224 vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vout' <= 255 * (hash_bytes sha2_224) /\
          vout' == expand sha2_224 vprk vinfo (Seq.length vout'))
  {
    expand_impl sha2_224 (Hacl.Hash.SHA2.NI.blocks_ni sha2_224) kt ivt out out_len prk prk_len info info_len;
  } else {
    expand_impl sha2_224 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_224) kt ivt out out_len prk prk_len info info_len;
  };
  drop_table ivt;
  drop_table kt;
}

(** HKDF-Extract with sha256.  [out] must have room for 32 bytes. *)
fn extract_sha256 (out: A.array S8.t) (salt: A.array S8.t) (salt_len: SZ.t) (ikm: A.array S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
         pure (Seq.length vout == 32 /\ Seq.length vsalt < pow2 61 /\
               SZ.fits (block_len #S32.t + Seq.length vikm) /\
               block_len #S32.t + Seq.length vikm < pow2 61)
         ** pure (SZ.v salt_len == Seq.length vsalt)
         ** pure (SZ.v ikm_len == Seq.length vikm)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S32.t /\
        block_len #S32.t + Seq.length vikm < max_input #S32.t /\
        vout' == extract sha2_256 vsalt vikm)
{
  Hacl.HMAC.hmac_sha256 out salt salt_len ikm ikm_len;
}

(** HKDF-Expand with sha256.  [out] may be up to 255*32 = 8160 bytes. *)
fn expand_sha256 (out: A.array S8.t) (out_len: SZ.t) (prk: A.array S8.t) (prk_len: SZ.t) (info: A.array S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (Seq.length vprk < pow2 61 /\
               block_len #S32.t + 32 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + 32 + Seq.length vinfo + 1) /\
               Seq.length vout <= 8160)
         ** pure (SZ.v out_len == Seq.length vout)
         ** pure (SZ.v prk_len == Seq.length vprk)
         ** pure (SZ.v info_len == Seq.length vinfo)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
  pure (prk_ok sha2_256 vprk /\ info_ok sha2_256 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_256) /\
        vout' == expand sha2_256 vprk vinfo (Seq.length vout'))
{
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len info;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  max_input_bound ();
  let ni = Vec.sha_supported ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if ni
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    pure (prk_ok sha2_256 vprk /\ info_ok sha2_256 vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vout' <= 255 * (hash_bytes sha2_256) /\
          vout' == expand sha2_256 vprk vinfo (Seq.length vout'))
  {
    expand_impl sha2_256 (Hacl.Hash.SHA2.NI.blocks_ni sha2_256) kt ivt out out_len prk prk_len info info_len;
  } else {
    expand_impl sha2_256 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_256) kt ivt out out_len prk prk_len info info_len;
  };
  drop_table ivt;
  drop_table kt;
}

(** HKDF-Extract with sha384.  [out] must have room for 48 bytes. *)
(* The eighty-entry [k512] is enough bigger than the sixty-four-entry [k256]
   that relating the array to [params512_with]'s [k] field no longer fits in
   the default budget. *)
#push-options "--z3rlimit 40"

fn extract_sha384 (out: A.array S8.t) (salt: A.array S8.t) (salt_len: SZ.t) (ikm: A.array S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
         pure (Seq.length vout == 48 /\ Seq.length vsalt < pow2 61 /\
               SZ.fits (block_len #S64.t + Seq.length vikm) /\
               block_len #S64.t + Seq.length vikm < pow2 61)
         ** pure (SZ.v salt_len == Seq.length vsalt)
         ** pure (SZ.v ikm_len == Seq.length vikm)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S64.t /\
        block_len #S64.t + Seq.length vikm < max_input #S64.t /\
        vout' == extract sha2_384 vsalt vikm)
{
  Hacl.HMAC.hmac_sha384 out salt salt_len ikm ikm_len;
}

(** HKDF-Expand with sha384.  [out] may be up to 255*48 = 12240 bytes. *)
fn expand_sha384 (out: A.array S8.t) (out_len: SZ.t) (prk: A.array S8.t) (prk_len: SZ.t) (info: A.array S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (Seq.length vprk < pow2 61 /\
               block_len #S64.t + 48 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S64.t + 48 + Seq.length vinfo + 1) /\
               Seq.length vout <= 12240)
         ** pure (SZ.v out_len == Seq.length vout)
         ** pure (SZ.v prk_len == Seq.length vprk)
         ** pure (SZ.v info_len == Seq.length vinfo)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
  pure (prk_ok sha2_384 vprk /\ info_ok sha2_384 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_384) /\
        vout' == expand sha2_384 vprk vinfo (Seq.length vout'))
{
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len info;
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  max_input_bound ();
  expand_impl sha2_384 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_384) kt ivt out out_len prk prk_len info info_len;
  drop_table ivt;
  drop_table kt;
}

(** HKDF-Extract with sha512.  [out] must have room for 64 bytes. *)
fn extract_sha512 (out: A.array S8.t) (salt: A.array S8.t) (salt_len: SZ.t) (ikm: A.array S8.t) (ikm_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#ps: perm) (#vsalt: erased (Seq.seq S8.t))
    (#pi: perm) (#vikm: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
         pure (Seq.length vout == 64 /\ Seq.length vsalt < pow2 61 /\
               SZ.fits (block_len #S64.t + Seq.length vikm) /\
               block_len #S64.t + Seq.length vikm < pow2 61)
         ** pure (SZ.v salt_len == Seq.length vsalt)
         ** pure (SZ.v ikm_len == Seq.length vikm)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to salt #ps vsalt ** A.pts_to ikm #pi vikm **
  pure (Seq.length vsalt < max_input #S64.t /\
        block_len #S64.t + Seq.length vikm < max_input #S64.t /\
        vout' == extract sha2_512 vsalt vikm)
{
  Hacl.HMAC.hmac_sha512 out salt salt_len ikm ikm_len;
}

(** HKDF-Expand with sha512.  [out] may be up to 255*64 = 16320 bytes. *)
fn expand_sha512 (out: A.array S8.t) (out_len: SZ.t) (prk: A.array S8.t) (prk_len: SZ.t) (info: A.array S8.t) (info_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pp: perm) (#vprk: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (Seq.length vprk < pow2 61 /\
               block_len #S64.t + 64 + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S64.t + 64 + Seq.length vinfo + 1) /\
               Seq.length vout <= 16320)
         ** pure (SZ.v out_len == Seq.length vout)
         ** pure (SZ.v prk_len == Seq.length vprk)
         ** pure (SZ.v info_len == Seq.length vinfo)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
  pure (prk_ok sha2_512 vprk /\ info_ok sha2_512 vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes sha2_512) /\
        vout' == expand sha2_512 vprk vinfo (Seq.length vout'))
{
  A.pts_to_len out;
  A.pts_to_len prk;
  A.pts_to_len info;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  max_input_bound ();
  expand_impl sha2_512 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_512) kt ivt out out_len prk prk_len info info_len;
  drop_table ivt;
  drop_table kt;
}

#pop-options
