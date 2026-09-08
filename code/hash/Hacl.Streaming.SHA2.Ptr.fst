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

(** The flat C interface to the incremental hash.

    A state is three pointers:

      uint32_t *acc;   // eight words
      uint8_t  *buf;   // one block, 64 or 128 bytes
      size_t   *total; // one element

    and the C header this extracts to reads

      void Hacl_Streaming_SHA2_Ptr_sha256_init(uint32_t *acc, uint8_t *buf, size_t *total);
      void Hacl_Streaming_SHA2_Ptr_sha256_update(uint32_t *acc, uint8_t *buf, size_t *total,
                                                 uint8_t *data, size_t data_len);
      void Hacl_Streaming_SHA2_Ptr_sha256_digest(uint32_t *acc, uint8_t *buf, size_t *total,
                                                 uint8_t *out);

    Note [total] is a [size_t], not a [uint64_t]: on a thirty-two bit target a
    single state can therefore only absorb four gigabytes.  That is a
    deliberate consequence of using [FStar.SizeT] for every length in the
    library (see design/changes.md); a caller that needs more can hash on a
    sixty-four bit host or use the one-shot interface. *)
module Hacl.Streaming.SHA2.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.SHA2.Streaming
open Hacl.Hash.SHA2.Streaming

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** {2 SHA224} *)

fn sha224_init (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
              (#vacc: erased (Seq.seq S32.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to acc vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S32.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok sha2_224 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA2.sha224_init sa sb st;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha224_update (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok sha2_224 vacc vbuf vtot seen /\
               Seq.length vbuf == 64 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok sha2_224 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA2.sha224_update sa sb st sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha224_digest (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout **
         pure (stream_ok sha2_224 vacc vbuf vtot seen /\
               Seq.length vbuf == 64 /\ Seq.length vout == 28)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout' **
  pure (Seq.length seen < max_input #S32.t /\ vout' == hash sha2_224 seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 28sz;
  Hacl.Streaming.SHA2.sha224_digest sa sb st so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}


(** {2 SHA256} *)

fn sha256_init (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
              (#vacc: erased (Seq.seq S32.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to acc vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S32.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok sha2_256 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA2.sha256_init sa sb st;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha256_update (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok sha2_256 vacc vbuf vtot seen /\
               Seq.length vbuf == 64 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok sha2_256 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA2.sha256_update sa sb st sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha256_digest (acc: AP.ptr S32.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout **
         pure (stream_ok sha2_256 vacc vbuf vtot seen /\
               Seq.length vbuf == 64 /\ Seq.length vout == 32)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout' **
  pure (Seq.length seen < max_input #S32.t /\ vout' == hash sha2_256 seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 64sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 32sz;
  Hacl.Streaming.SHA2.sha256_digest sa sb st so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}


(** {2 SHA384} *)

fn sha384_init (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
              (#vacc: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to acc vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok sha2_384 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA2.sha384_init sa sb st;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha384_update (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok sha2_384 vacc vbuf vtot seen /\
               Seq.length vbuf == 128 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok sha2_384 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA2.sha384_update sa sb st sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha384_digest (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout **
         pure (stream_ok sha2_384 vacc vbuf vtot seen /\
               Seq.length vbuf == 128 /\ Seq.length vout == 48)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout' **
  pure (Seq.length seen < max_input #S64.t /\ vout' == hash sha2_384 seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 48sz;
  Hacl.Streaming.SHA2.sha384_digest sa sb st so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}


(** {2 SHA512} *)

fn sha512_init (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
              (#vacc: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to acc vacc ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok sha2_512 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA2.sha512_init sa sb st;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha512_update (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to acc vacc ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok sha2_512 vacc vbuf vtot seen /\
               Seq.length vbuf == 128 /\ Seq.length vdata == SZ.v data_len /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to acc vacc' ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok sha2_512 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA2.sha512_update sa sb st sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

fn sha512_digest (acc: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
                (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout **
         pure (stream_ok sha2_512 vacc vbuf vtot seen /\
               Seq.length vbuf == 128 /\ Seq.length vout == 64)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  AP.pts_to acc #pa vacc ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout' **
  pure (Seq.length seen < max_input #S64.t /\ vout' == hash sha2_512 seen)
{
  let sa = S.arrayptr_to_slice_intro acc 8sz;
  let sb = S.arrayptr_to_slice_intro buf 128sz;
  let st = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 64sz;
  Hacl.Streaming.SHA2.sha512_digest sa sb st so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sa;
}

