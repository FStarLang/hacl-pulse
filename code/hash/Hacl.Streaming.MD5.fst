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

(** The incremental interface to MD5.

    The same shape as [Hacl.Streaming.SHA2]: the state a caller keeps is three
    flat pieces of memory -- a four-word accumulator, one block of buffered
    bytes, and a single [size_t] byte count -- with no allocation, no
    destructor and no error code.  The ghost [seen] argument costs nothing at
    runtime and is what lets [digest] promise [Spec.MD5.hash seen].

    [init] writes four literals; [update] allocates nothing but the sixteen
    words of the current block, since MD5 has no schedule to expand.

      void Hacl_Streaming_MD5_md5_init(uint32_t *acc, uint8_t *buf, size_t *tot); *)
module Hacl.Streaming.MD5

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MD5
open Spec.MD5.Streaming
open Hacl.Hash.MD5.Streaming

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32

(** Reset the state to the empty message. *)
fn md5_init (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
             (#vacc: erased (Seq.seq S32.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
             (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to acc vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vacc == 4 /\ Seq.length vbuf == 64 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S32.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok vacc' vbuf vtot' (Seq.empty #S8.t))
{
  init_impl acc buf tot;
}

(** Absorb [data]. *)
fn md5_update (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
               (data: A.array S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
               (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
               (#vtot: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok vacc vbuf vtot seen /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok vacc' vbuf' vtot' (Seq.append seen vdata))
{
  let z = S32.classify 0ul;
  let mut warr = [| z; 16sz |];
  A.pts_to_len warr;
  update_impl warr acc buf tot data data_len seen;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn md5_digest (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
               (out: A.array S8.t) (seen: erased (Seq.seq S8.t))
               (#pa: perm) (#vacc: erased (Seq.seq S32.t))
               (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
               (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
               (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout **
         pure (stream_ok vacc vbuf vtot seen /\ Seq.length vout == 16)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout' **
  pure (Seq.length seen < max_input /\ vout' == hash seen)
{
  let z = S32.classify 0ul;
  let mut warr = [| z; 16sz |];
  A.pts_to_len warr;
  digest_impl warr acc buf tot out seen;
}
