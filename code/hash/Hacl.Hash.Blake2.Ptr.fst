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

(** The flat C interface to BLAKE2.

      void Hacl_Hash_Blake2_Ptr_blake2b_512(uint8_t *out,
                                            uint8_t *key, size_t key_len,
                                            uint8_t *msg, size_t msg_len);

    An empty key -- [key_len] zero, [key] anything -- is an unkeyed hash.

    The message length is bounded by two blocks below [SIZE_MAX] and below
    2^64.  Both bounds are vacuous on any real platform; they are written down
    because [FStar.SizeT.fits] is abstract, so F* will not assume a [size_t] is
    sixty-four bits and no wider, and the block counter is computed in
    [size_t]. *)
module Hacl.Hash.Blake2.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.Blake2
open Spec.Blake2.Constants
open Hacl.Hash.Blake2.Named

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** BLAKE2B with a 512-bit digest.  [out] must have room for 64 bytes. *)
fn blake2b_512 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 64 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 64 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_512_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2b_512 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** BLAKE2B with a 384-bit digest.  [out] must have room for 48 bytes. *)
fn blake2b_384 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 48 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 64 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_384_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 48sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2b_384 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** BLAKE2B with a 256-bit digest.  [out] must have room for 32 bytes. *)
fn blake2b_256 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 32 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 64 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_256_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2b_256 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** BLAKE2B with a 160-bit digest.  [out] must have room for 20 bytes. *)
fn blake2b_160 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 20 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 64 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_160_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 20sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2b_160 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** BLAKE2S with a 256-bit digest.  [out] must have room for 32 bytes. *)
fn blake2s_256 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 32 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 32 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_256_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2s_256 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** BLAKE2S with a 224-bit digest.  [out] must have room for 28 bytes. *)
fn blake2s_224 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 28 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 32 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_224_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 28sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2s_224 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** BLAKE2S with a 160-bit digest.  [out] must have room for 20 bytes. *)
fn blake2s_160 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 20 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 32 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_160_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 20sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2s_160 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}


(** BLAKE2S with a 128-bit digest.  [out] must have room for 16 bytes. *)
fn blake2s_128 (out: AP.ptr S8.t)
            (key: AP.ptr S8.t) (key_len: SZ.t)
            (msg: AP.ptr S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
         pure (Seq.length vout == 16 /\
               Seq.length vkey == SZ.v key_len /\ Seq.length vkey <= 32 /\
               Seq.length vmsg == SZ.v msg_len /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to key #pk vkey ** AP.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_128_p (reveal vkey) (reveal vmsg))
{
  let so = S.arrayptr_to_slice_intro out 16sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Hash.Blake2.Named.blake2s_128 so sk sm;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
}
