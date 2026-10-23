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
module V256 = Hacl.Vec256

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

(** [expand_impl] over the SHA instructions.  A function of its own so
    that it can carry the x86-64 guard, which then covers every
    [blocks_ni] instance it reaches. *)
[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn expand_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t { Spec.SHANI.is_sha256 p })
             (kt: A.array S32.t) (ivt: A.array S32.t) (out: A.array S8.t) (len: SZ.t)
             (prk: A.array S8.t) (plen: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq S32.t))
             (#pi: perm) (#vi: erased (Seq.seq S32.t))
             (#vout: erased (Seq.seq S8.t))
             (#pp: perm) (#vprk: erased (Seq.seq S8.t))
             (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal p.k <: Seq.seq S32.t) /\ reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p vinfo /\
               block_len #S32.t + (hash_bytes p) + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S32.t + (hash_bytes p) + Seq.length vinfo + 1) /\
               Seq.length vout <= 255 * (hash_bytes p) /\
               SZ.v len == Seq.length vout /\ SZ.v ilen == Seq.length vinfo)
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
  pure (prk_ok p vprk /\ info_ok p vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes p) /\
        vout' == expand p vprk vinfo (Seq.length vout'))
{
  expand_impl p (Hacl.Hash.SHA2.NI.blocks_ni p) kt ivt out len prk plen info ilen
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
  sha2_224_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    pure (prk_ok sha2_224 vprk /\ info_ok sha2_224 vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vout' <= 255 * (hash_bytes sha2_224) /\
          vout' == expand sha2_224 vprk vinfo (Seq.length vout'))
  {
    if (Vec.sha_supported ())
    {
      expand_ni sha2_224 kt ivt out out_len prk prk_len info info_len;
    } else {
      expand_impl sha2_224 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_224) kt ivt out out_len prk prk_len info info_len;
    }
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
  sha2_256_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    pure (prk_ok sha2_256 vprk /\ info_ok sha2_256 vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vout' <= 255 * (hash_bytes sha2_256) /\
          vout' == expand sha2_256 vprk vinfo (Seq.length vout'))
  {
    if (Vec.sha_supported ())
    {
      expand_ni sha2_256 kt ivt out out_len prk prk_len info info_len;
    } else {
      expand_impl sha2_256 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_256) kt ivt out out_len prk prk_len info info_len;
    }
  } else {
    expand_impl sha2_256 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_256) kt ivt out out_len prk prk_len info info_len;
  };
  drop_table ivt;
  drop_table kt;
}

(** What [expand_impl] asks of its lengths, for the two sixty-four bit
    parameter sets, discharged outside the call's query: the sizes depend on
    [bytes #S64.t], i.e. on [bits / 8] for the sixty-four bit word. *)
let s64_sizes (_: unit)
  : Lemma (bytes #S64.t == 8 /\ block_len #S64.t == 128 /\ pow2 61 <= max_input #S64.t)
  = assert_norm (bits #S64.t == 64);
    max_input_bound ()

let expand_lengths_s64 (p: params S64.t) (vprk vinfo vout: Seq.seq S8.t)
  : Lemma (requires Seq.length vprk < pow2 61 /\
                    block_len #S64.t + hash_bytes p + Seq.length vinfo + 1 < pow2 61 /\
                    Seq.length vout <= 255 * hash_bytes p)
          (ensures prk_ok p vprk /\ info_ok p vinfo)
  = s64_sizes ()

(** [expand_impl] over [Hacl.Hash.SHA2.AVX2].  A function of its own so
    that it can carry the x86-64 guard, which then covers every
    [blocks_avx2] instance it reaches. *)
[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn expand_avx2 ([@@@FStar.Attributes.monomorphize] p: params S64.t { Hacl.Hash.SHA2.AVX2.is_sha512 p })
             (kt: A.array S64.t) (ivt: A.array S64.t) (out: A.array S8.t) (len: SZ.t)
             (prk: A.array S8.t) (plen: SZ.t) (info: A.array S8.t) (ilen: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq S64.t))
             (#pi: perm) (#vi: erased (Seq.seq S64.t))
             (#vout: erased (Seq.seq S8.t))
             (#pp: perm) (#vprk: erased (Seq.seq S8.t))
             (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal p.k <: Seq.seq S64.t) /\ reveal vi == (reveal p.iv <: Seq.seq S64.t) /\
               Seq.length vprk < pow2 61 /\ prk_ok p vprk /\ info_ok p vinfo /\
               block_len #S64.t + (hash_bytes p) + Seq.length vinfo + 1 < pow2 61 /\
               SZ.fits (block_len #S64.t + (hash_bytes p) + Seq.length vinfo + 1) /\
               Seq.length vout <= 255 * (hash_bytes p) /\
               SZ.v len == Seq.length vout /\ SZ.v ilen == Seq.length vinfo)
         ** pure (SZ.v plen == Seq.length vprk)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
  pure (prk_ok p vprk /\ info_ok p vinfo /\
        Seq.length vout' == Seq.length vout /\
        Seq.length vout' <= 255 * (hash_bytes p) /\
        vout' == expand p vprk vinfo (Seq.length vout'))
{
  expand_impl p (Hacl.Hash.SHA2.AVX2.blocks_avx2 p) kt ivt out len prk plen info ilen
}

(** HKDF-Extract with sha384.  [out] must have room for 48 bytes. *)
(* The eighty-entry [k512] is enough bigger than the sixty-four-entry [k256]
   that relating the array to [params512_with]'s [k] field is best done
   outside the call's query ([sha2_384_facts], [sha2_512_facts]); a little
   headroom over the default budget is kept for the call itself. *)
#push-options "--z3rlimit 10"

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

#push-options "--fuel 0 --ifuel 0"
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
  sha2_384_facts ();
  expand_lengths_s64 sha2_384 vprk vinfo vout;
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    pure (prk_ok sha2_384 vprk /\ info_ok sha2_384 vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vout' <= 255 * (hash_bytes sha2_384) /\
          vout' == expand sha2_384 vprk vinfo (Seq.length vout'))
  {
    if (V256.supported ())
    {
      expand_avx2 sha2_384 kt ivt out out_len prk prk_len info info_len;
    } else {
      expand_impl sha2_384 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_384) kt ivt out out_len prk prk_len info info_len;
    }
  } else {
    expand_impl sha2_384 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_384) kt ivt out out_len prk prk_len info info_len;
  };
  drop_table ivt;
  drop_table kt;
}
#pop-options

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

#push-options "--fuel 0 --ifuel 0"
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
  sha2_512_facts ();
  expand_lengths_s64 sha2_512 vprk vinfo vout;
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to prk #pp vprk ** A.pts_to info #pf vinfo **
    pure (prk_ok sha2_512 vprk /\ info_ok sha2_512 vinfo /\
          Seq.length vout' == Seq.length vout /\
          Seq.length vout' <= 255 * (hash_bytes sha2_512) /\
          vout' == expand sha2_512 vprk vinfo (Seq.length vout'))
  {
    if (V256.supported ())
    {
      expand_avx2 sha2_512 kt ivt out out_len prk prk_len info info_len;
    } else {
      expand_impl sha2_512 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_512) kt ivt out out_len prk prk_len info info_len;
    }
  } else {
    expand_impl sha2_512 (Hacl.Hash.SHA2.Core.blocks_scalar sha2_512) kt ivt out out_len prk prk_len info info_len;
  };
  drop_table ivt;
  drop_table kt;
}
#pop-options

#pop-options
