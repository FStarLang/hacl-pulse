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

(** HMAC-SHA-224/256/384/512.

    Each entry point names its [Spec.SHA2.params] value and lays out the round
    constants and the initial state, exactly as [Hacl.Hash.SHA2] does for the
    bare hash; everything else is in [Hacl.HMAC.Core]. *)
module Hacl.HMAC

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HMAC
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Tables
open Hacl.Impl.Table
open Hacl.HMAC.Core
open Hacl.HMAC.NI
open Hacl.HMAC.AVX2

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Vec = Hacl.Vec128
module V256 = Hacl.Vec256

(* SHA-224 and SHA-256 are the two that have an implementation on the SHA
   instructions; the dispatch is the same shape as the one in
   [Hacl.Hash.SHA2], and for the same reason -- the generic [hmac_impl]
   cannot ask whether its word type is thirty-two bits wide. *)

(** HMAC-SHA-224.  [out] must have room for 28 bytes. *)
fn hmac_sha224 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 28 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S32.t + Seq.length vmsg) /\
               block_len #S32.t + Seq.length vmsg < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S32.t /\
        block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
        vout' == hmac sha2_224 vkey vmsg)
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  let kt = table k256_arr 64sz;
  let ivt = table iv224_arr 8sz;
  max_input_bound ();
  sha2_224_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
    pure (Seq.length vkey < max_input #S32.t /\
          block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
          vout' == hmac sha2_224 vkey vmsg)
  {
    if (Vec.sha_supported ())
    {
      hmac_impl_ni sha2_224 kt ivt out key key_len msg msg_len;
    } else {
      hmac_impl sha2_224 kt ivt out key key_len msg msg_len;
    }
  } else {
    hmac_impl sha2_224 kt ivt out key key_len msg msg_len;
  };
  drop_table ivt;
  drop_table kt;
}

(** HMAC-SHA-256.  [out] must have room for 32 bytes. *)
fn hmac_sha256 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 32 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S32.t + Seq.length vmsg) /\
               block_len #S32.t + Seq.length vmsg < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S32.t /\
        block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
        vout' == hmac sha2_256 vkey vmsg)
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  max_input_bound ();
  sha2_256_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
    pure (Seq.length vkey < max_input #S32.t /\
          block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
          vout' == hmac sha2_256 vkey vmsg)
  {
    if (Vec.sha_supported ())
    {
      hmac_impl_ni sha2_256 kt ivt out key key_len msg msg_len;
    } else {
      hmac_impl sha2_256 kt ivt out key key_len msg msg_len;
    }
  } else {
    hmac_impl sha2_256 kt ivt out key key_len msg msg_len;
  };
  drop_table ivt;
  drop_table kt;
}

(** HMAC-SHA-384.  [out] must have room for 48 bytes. *)
(* The eighty-entry [k512] is enough bigger than the sixty-four-entry [k256]
   that relating the array to [params512_with]'s [k] field no longer fits in
   the default budget. *)
#push-options "--z3rlimit 40"

fn hmac_sha384 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 48 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S64.t + Seq.length vmsg) /\
               block_len #S64.t + Seq.length vmsg < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S64.t /\
        block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
        vout' == hmac sha2_384 vkey vmsg)
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  max_input_bound ();
  sha2_384_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
    pure (Seq.length vkey < max_input #S64.t /\
          block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
          vout' == hmac sha2_384 vkey vmsg)
  {
    if (V256.supported ())
    {
      hmac_impl_avx2 sha2_384 kt ivt out key key_len msg msg_len;
    } else {
      hmac_impl sha2_384 kt ivt out key key_len msg msg_len;
    }
  } else {
    hmac_impl sha2_384 kt ivt out key key_len msg msg_len;
  };
  drop_table ivt;
  drop_table kt;
}

(** HMAC-SHA-512.  [out] must have room for 64 bytes. *)
fn hmac_sha512 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 64 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S64.t + Seq.length vmsg) /\
               block_len #S64.t + Seq.length vmsg < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S64.t /\
        block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
        vout' == hmac sha2_512 vkey vmsg)
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  max_input_bound ();
  sha2_512_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
    pure (Seq.length vkey < max_input #S64.t /\
          block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
          vout' == hmac sha2_512 vkey vmsg)
  {
    if (V256.supported ())
    {
      hmac_impl_avx2 sha2_512 kt ivt out key key_len msg msg_len;
    } else {
      hmac_impl sha2_512 kt ivt out key key_len msg msg_len;
    }
  } else {
    hmac_impl sha2_512 kt ivt out key key_len msg msg_len;
  };
  drop_table ivt;
  drop_table kt;
}

#pop-options
