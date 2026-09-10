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

(** The flat C interface to the incremental BLAKE2 hashes.

    A state is three pointers:

      uint64_t *acc;   // eight words
      uint8_t  *buf;   // one block, 64 or 128 bytes
      size_t   *total; // one element

    and the C header this extracts to reads

      void Hacl_Streaming_Blake2_Ptr_blake2b_512_init(uint64_t *acc, uint8_t *buf,
                                                      size_t *total,
                                                      uint8_t *key, size_t key_len);
      void Hacl_Streaming_Blake2_Ptr_blake2b_512_update(uint64_t *acc, uint8_t *buf,
                                                        size_t *total,
                                                        uint8_t *data, size_t data_len);
      void Hacl_Streaming_Blake2_Ptr_blake2b_512_digest(uint64_t *acc, uint8_t *buf,
                                                        size_t *total, uint8_t *out);

    The key is given once, to [init], and copied into the buffer; the later
    calls do not see it.  [total] counts the *combined* stream, so it starts
    at one block for a keyed hash and at zero for an unkeyed one.

    As in [Hacl.Streaming.SHA2.Ptr], [total] is a [size_t] rather than a
    [uint64_t]: on a thirty-two bit target one state can absorb four
    gigabytes. *)
module Hacl.Streaming.Blake2.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.Blake2
open Spec.Blake2.Streaming
open Hacl.Hash.Blake2.Named

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

(** {2 BLAKE2B-512} *)

fn blake2b_512_init (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 64)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2b_512_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2b_512_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_512_update (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2b_512_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2b_512_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2b_512_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_512_digest (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2b_512_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vout == 64)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_512_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 64sz;
  Hacl.Streaming.Blake2.blake2b_512_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

(** {2 BLAKE2B-384} *)

fn blake2b_384_init (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 64)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2b_384_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2b_384_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_384_update (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2b_384_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2b_384_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2b_384_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_384_digest (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2b_384_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vout == 48)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_384_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 48sz;
  Hacl.Streaming.Blake2.blake2b_384_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

(** {2 BLAKE2B-256} *)

fn blake2b_256_init (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 64)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2b_256_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2b_256_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_256_update (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2b_256_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2b_256_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2b_256_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_256_digest (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2b_256_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_256_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 32sz;
  Hacl.Streaming.Blake2.blake2b_256_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

(** {2 BLAKE2B-160} *)

fn blake2b_160_init (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 64)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2b_160_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2b_160_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_160_update (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2b_160_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2b_160_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2b_160_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2b_160_digest (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2b_160_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 128 /\ Seq.length vout == 20)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_160_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 20sz;
  Hacl.Streaming.Blake2.blake2b_160_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

(** {2 BLAKE2S-256} *)

fn blake2s_256_init (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 32)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2s_256_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2s_256_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_256_update (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2s_256_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2s_256_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2s_256_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_256_digest (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2s_256_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_256_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 32sz;
  Hacl.Streaming.Blake2.blake2s_256_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

(** {2 BLAKE2S-224} *)

fn blake2s_224_init (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 32)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2s_224_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2s_224_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_224_update (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2s_224_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2s_224_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2s_224_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_224_digest (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2s_224_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vout == 28)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_224_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 28sz;
  Hacl.Streaming.Blake2.blake2s_224_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

(** {2 BLAKE2S-160} *)

fn blake2s_160_init (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 32)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2s_160_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2s_160_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_160_update (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2s_160_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2s_160_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2s_160_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_160_digest (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2s_160_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vout == 20)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_160_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 20sz;
  Hacl.Streaming.Blake2.blake2s_160_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

(** {2 BLAKE2S-128} *)

fn blake2s_128_init (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
               (key: AP.ptr S8.t) (key_len: SZ.t)
               (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey == SZ.v key_len /\
               Seq.length vkey <= 32)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to key #pk vkey **
  pure (stream_ok blake2s_128_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sk = S.arrayptr_to_slice_intro key key_len;
  Hacl.Streaming.Blake2.blake2s_128_init sa sb st sk;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_128_update (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (data: AP.ptr S8.t) (data_len: SZ.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok blake2s_128_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok blake2s_128_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.Blake2.blake2s_128_update sa sb st sd key seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn blake2s_128_digest (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                 (out: AP.ptr S8.t)
                 (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                 (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                 (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
         AP.pts_to out vout **
         pure (stream_ok blake2s_128_p key seen vacc vbuf vtot /\
               Seq.length vbuf == 64 /\ Seq.length vout == 16)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot #pt vtot **
  AP.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_128_p key seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 16sz;
  Hacl.Streaming.Blake2.blake2s_128_digest sa sb st so key seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}
