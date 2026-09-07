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
open Hacl.HMAC.Core

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** HMAC-SHA-224.  [out] must have room for 28 bytes. *)
fn hmac_sha224 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 28 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S32.t + Seq.length vmsg) /\
               block_len #S32.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  S.pts_to out vout' ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S32.t /\
        block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
        vout' == hmac sha2_224 vkey vmsg)
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv224 ivt;
  max_input_bound ();
  hmac_impl sha2_224 kt ivt out key msg;
  S.to_array ivt;
  S.to_array kt;
}


(** HMAC-SHA-256.  [out] must have room for 32 bytes. *)
fn hmac_sha256 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 32 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S32.t + Seq.length vmsg) /\
               block_len #S32.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  S.pts_to out vout' ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S32.t /\
        block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
        vout' == hmac sha2_256 vkey vmsg)
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv256 ivt;
  max_input_bound ();
  hmac_impl sha2_256 kt ivt out key msg;
  S.to_array ivt;
  S.to_array kt;
}


(** HMAC-SHA-384.  [out] must have room for 48 bytes. *)
fn hmac_sha384 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 48 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S64.t + Seq.length vmsg) /\
               block_len #S64.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  S.pts_to out vout' ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S64.t /\
        block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
        vout' == hmac sha2_384 vkey vmsg)
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv384 ivt;
  max_input_bound ();
  hmac_impl sha2_384 kt ivt out key msg;
  S.to_array ivt;
  S.to_array kt;
}


(** HMAC-SHA-512.  [out] must have room for 64 bytes. *)
fn hmac_sha512 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
    (#vout: erased (Seq.seq S8.t)) (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
    (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 64 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (block_len #S64.t + Seq.length vmsg) /\
               block_len #S64.t + Seq.length vmsg < pow2 61)
ensures exists* vout'.
  S.pts_to out vout' ** S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S64.t /\
        block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
        vout' == hmac sha2_512 vkey vmsg)
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv512 ivt;
  max_input_bound ();
  hmac_impl sha2_512 kt ivt out key msg;
  S.to_array ivt;
  S.to_array kt;
}
