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

(** The flat C interface to the incremental sponge.

    A state is three pointers:

      uint64_t *st;    // twenty-five lanes
      uint8_t  *buf;   // one rate: 144, 136, 104, 72 or 168 bytes
      size_t   *total; // one element

    and the generated header reads, for each algorithm,

      void Hacl_Streaming_SHA3_Ptr_sha3_256_init(uint64_t *st, uint8_t *buf, size_t *total);
      void Hacl_Streaming_SHA3_Ptr_sha3_256_update(uint64_t *st, uint8_t *buf, size_t *total,
                                                   uint8_t *data, size_t data_len);
      void Hacl_Streaming_SHA3_Ptr_sha3_256_digest(uint64_t *st, uint8_t *buf, size_t *total,
                                                   uint8_t *out);

    with the two SHAKE [digest]s taking an extra output length. *)
module Hacl.Streaming.SHA3.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Streaming
open Hacl.Hash.SHA3.Streaming

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64


(** {2 SHA3-224} *)

fn sha3_224_init (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to st vst0 ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 144 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok 144sz vst vbuf vtot' (Seq.empty #S8.t))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 144sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA3.sha3_224_init ss sb stt;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_224_update (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to st vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok 144sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 144 /\ Seq.length vdata == SZ.v data_len /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok 144sz vst vbuf' vtot' (Seq.append seen vdata))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 144sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA3.sha3_224_update ss sb stt sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_224_digest (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout0 **
         pure (stream_ok 144sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 144 /\ Seq.length vout0 == 28)
ensures exists* (vbuf': Seq.seq S8.t) (vout: Seq.seq S8.t).
  AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout **
  pure (vout == sha3_224 seen)
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 144sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 28sz;
  Hacl.Streaming.SHA3.sha3_224_digest ss sb stt so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}


(** {2 SHA3-256} *)

fn sha3_256_init (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to st vst0 ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 136 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok 136sz vst vbuf vtot' (Seq.empty #S8.t))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 136sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA3.sha3_256_init ss sb stt;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_256_update (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to st vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok 136sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 136 /\ Seq.length vdata == SZ.v data_len /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok 136sz vst vbuf' vtot' (Seq.append seen vdata))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 136sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA3.sha3_256_update ss sb stt sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_256_digest (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout0 **
         pure (stream_ok 136sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 136 /\ Seq.length vout0 == 32)
ensures exists* (vbuf': Seq.seq S8.t) (vout: Seq.seq S8.t).
  AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout **
  pure (vout == sha3_256 seen)
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 136sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 32sz;
  Hacl.Streaming.SHA3.sha3_256_digest ss sb stt so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}


(** {2 SHA3-384} *)

fn sha3_384_init (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to st vst0 ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 104 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok 104sz vst vbuf vtot' (Seq.empty #S8.t))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 104sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA3.sha3_384_init ss sb stt;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_384_update (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to st vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok 104sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 104 /\ Seq.length vdata == SZ.v data_len /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok 104sz vst vbuf' vtot' (Seq.append seen vdata))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 104sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA3.sha3_384_update ss sb stt sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_384_digest (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout0 **
         pure (stream_ok 104sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 104 /\ Seq.length vout0 == 48)
ensures exists* (vbuf': Seq.seq S8.t) (vout: Seq.seq S8.t).
  AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout **
  pure (vout == sha3_384 seen)
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 104sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 48sz;
  Hacl.Streaming.SHA3.sha3_384_digest ss sb stt so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}


(** {2 SHA3-512} *)

fn sha3_512_init (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to st vst0 ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 72 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok 72sz vst vbuf vtot' (Seq.empty #S8.t))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 72sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA3.sha3_512_init ss sb stt;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_512_update (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to st vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok 72sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 72 /\ Seq.length vdata == SZ.v data_len /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok 72sz vst vbuf' vtot' (Seq.append seen vdata))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 72sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA3.sha3_512_update ss sb stt sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn sha3_512_digest (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (out: AP.ptr S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout0 **
         pure (stream_ok 72sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 72 /\ Seq.length vout0 == 64)
ensures exists* (vbuf': Seq.seq S8.t) (vout: Seq.seq S8.t).
  AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout **
  pure (vout == sha3_512 seen)
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 72sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out 64sz;
  Hacl.Streaming.SHA3.sha3_512_digest ss sb stt so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}


(** {2 SHAKE128} *)

fn shake128_init (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to st vst0 ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 168 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok 168sz vst vbuf vtot' (Seq.empty #S8.t))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 168sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA3.shake128_init ss sb stt;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn shake128_update (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to st vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok 168sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 168 /\ Seq.length vdata == SZ.v data_len /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok 168sz vst vbuf' vtot' (Seq.append seen vdata))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 168sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA3.shake128_update ss sb stt sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn shake128_digest (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (out: AP.ptr S8.t) (out_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout0 **
         pure (stream_ok 168sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 168 /\ Seq.length vout0 == SZ.v out_len)
ensures exists* (vbuf': Seq.seq S8.t) (vout: Seq.seq S8.t).
  AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout **
  pure (Seq.length vout == Seq.length vout0 /\
        vout == shake128 seen (Seq.length vout0))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 168sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out out_len;
  Hacl.Streaming.SHA3.shake128_digest ss sb stt so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}


(** {2 SHAKE256} *)

fn shake256_init (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires AP.pts_to st vst0 ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 136 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf #pb vbuf ** AP.pts_to tot vtot' **
  pure (stream_ok 136sz vst vbuf vtot' (Seq.empty #S8.t))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 136sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  Hacl.Streaming.SHA3.shake256_init ss sb stt;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn shake256_update (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (data: AP.ptr S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires AP.pts_to st vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot vtot **
         AP.pts_to data #pd vdata **
         pure (stream_ok 136sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 136 /\ Seq.length vdata == SZ.v data_len /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  AP.pts_to st vst ** AP.pts_to buf vbuf' ** AP.pts_to tot vtot' **
  AP.pts_to data #pd vdata **
  pure (stream_ok 136sz vst vbuf' vtot' (Seq.append seen vdata))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 136sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let sd = S.arrayptr_to_slice_intro data data_len;
  Hacl.Streaming.SHA3.shake256_update ss sb stt sd seen;
  S.arrayptr_to_slice_elim sd;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}

fn shake256_digest (st: AP.ptr S64.t) (buf: AP.ptr S8.t) (tot: AP.ptr SZ.t)
          (out: AP.ptr S8.t) (out_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf ** AP.pts_to tot #ptot vtot **
         AP.pts_to out vout0 **
         pure (stream_ok 136sz vst0 vbuf vtot seen /\
               Seq.length vbuf == 136 /\ Seq.length vout0 == SZ.v out_len)
ensures exists* (vbuf': Seq.seq S8.t) (vout: Seq.seq S8.t).
  AP.pts_to st #pst vst0 ** AP.pts_to buf vbuf' ** AP.pts_to tot #ptot vtot **
  AP.pts_to out vout **
  pure (Seq.length vout == Seq.length vout0 /\
        vout == shake256 seen (Seq.length vout0))
{
  let ss = S.arrayptr_to_slice_intro st 25sz;
  let sb = S.arrayptr_to_slice_intro buf 136sz;
  let stt = S.arrayptr_to_slice_intro tot 1sz;
  let so = S.arrayptr_to_slice_intro out out_len;
  Hacl.Streaming.SHA3.shake256_digest ss sb stt so seen;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim stt;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim ss;
}
