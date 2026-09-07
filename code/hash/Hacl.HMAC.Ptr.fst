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

(** The flat C interface to HMAC.

    As in [Hacl.Hash.SHA2.Ptr], the slices the library uses internally are
    replaced by a bare pointer and a [size_t] at the boundary:

      void Hacl_HMAC_Ptr_hmac_sha256(uint8_t *out,
                                     uint8_t *key, size_t key_len,
                                     uint8_t *msg, size_t msg_len);

    These are the only functions that should be passed to [--custard_entry]. *)
module Hacl.HMAC.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HMAC

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** HMAC-SHA-224.  [out] must have room for 28 bytes. *)
fn hmac_sha224 (out: AP.ptr S8.t) (key: AP.ptr S8.t) (key_len: SZ.t)
    (msg: AP.ptr S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 28 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey < pow2 61 /\
               Seq.length vmsg == SZ.v msg_len /\
               SZ.fits (block_len #S32.t + Seq.length vmsg) /\
               block_len #S32.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S32.t /\
        block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
        vout' == hmac sha2_224 vkey vmsg)
{
  let so = S.arrayptr_to_slice_intro out 28sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.HMAC.hmac_sha224 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** HMAC-SHA-256.  [out] must have room for 32 bytes. *)
fn hmac_sha256 (out: AP.ptr S8.t) (key: AP.ptr S8.t) (key_len: SZ.t)
    (msg: AP.ptr S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 32 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey < pow2 61 /\
               Seq.length vmsg == SZ.v msg_len /\
               SZ.fits (block_len #S32.t + Seq.length vmsg) /\
               block_len #S32.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S32.t /\
        block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
        vout' == hmac sha2_256 vkey vmsg)
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.HMAC.hmac_sha256 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** HMAC-SHA-384.  [out] must have room for 48 bytes. *)
fn hmac_sha384 (out: AP.ptr S8.t) (key: AP.ptr S8.t) (key_len: SZ.t)
    (msg: AP.ptr S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 48 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey < pow2 61 /\
               Seq.length vmsg == SZ.v msg_len /\
               SZ.fits (block_len #S64.t + Seq.length vmsg) /\
               block_len #S64.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S64.t /\
        block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
        vout' == hmac sha2_384 vkey vmsg)
{
  let so = S.arrayptr_to_slice_intro out 48sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.HMAC.hmac_sha384 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** HMAC-SHA-512.  [out] must have room for 64 bytes. *)
fn hmac_sha512 (out: AP.ptr S8.t) (key: AP.ptr S8.t) (key_len: SZ.t)
    (msg: AP.ptr S8.t) (msg_len: SZ.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 64 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey < pow2 61 /\
               Seq.length vmsg == SZ.v msg_len /\
               SZ.fits (block_len #S64.t + Seq.length vmsg) /\
               block_len #S64.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  AP.pts_to out vout' ** AP.pts_to key #pkey vkey ** AP.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S64.t /\
        block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
        vout' == hmac sha2_512 vkey vmsg)
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.HMAC.hmac_sha512 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}
