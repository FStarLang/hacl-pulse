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

(** The incremental interface to the six SHA-3 algorithms.

    A state is three flat pieces of memory the caller owns:

    - twenty-five [uint64_t] of Keccak state,
    - one rate's worth of buffered bytes (144, 136, 104, 72 or 168, depending
      on the algorithm),
    - one [size_t] holding the number of bytes seen.

    There is no allocation, no destructor and no error code.  Ghostly the state
    also carries [seen], the message absorbed so far; it is [erased], so it
    costs nothing at runtime, and it is what lets [digest] promise the one-shot
    hash of exactly those bytes.

    The two constant tables are [static const] arrays in the program image,
    so [update] does no work proportional to them whatever the call absorbs --
    which matters here, since a caller may feed the sponge a byte at a
    time. *)
module Hacl.Streaming.SHA3

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3.Constants
open Spec.SHA3
open Spec.SHA3.Streaming
open Hacl.Hash.SHA3
open Hacl.Impl.Table
open Hacl.Hash.SHA3.Streaming

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32

(** {2 The two operations that need the round constants}

    [init] does not: it only zeroes the state.  These two allocate the scratch
    lanes and both tables, and are shared by all six algorithms -- the rate and
    the domain-separation byte are runtime arguments. *)

fn keccak_update (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                 (data: A.array S8.t) (data_len: SZ.t) (r: SZ.t) (seen: erased (Seq.seq S8.t))
                 (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vtot: erased (Seq.seq SZ.t))
                 (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok r vst0 vbuf vtot seen /\ SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok r vst vbuf' vtot' (Seq.append seen vdata))
{
  let z64 = S64.classify 0uL;

  let mut barr = [| z64; 25sz |];
  A.pts_to_len barr;
  A.pts_to_len barr;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;

  update_impl st barr rc_tbl buf tot data data_len r seen;

  drop_table rc_tbl;
  ()
}

fn keccak_digest (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                 (out: A.array S8.t) (out_len: SZ.t) (r: SZ.t) (suffix: U8.t)
                 (seen: erased (Seq.seq S8.t))
                 (#pst: perm) (#vst0: erased (Seq.seq S64.t))
                 (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
                 (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                 (#vout0: erased (Seq.seq S8.t))
requires A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout0 **
         pure (stream_ok r vst0 vbuf vtot seen)
         ** pure (SZ.v out_len == Seq.length vout0)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout **
  pure (rate_ok r /\ Seq.length vout == Seq.length vout0 /\ vout == keccak (SZ.v r) suffix seen (Seq.length vout0))
{
  let z64 = S64.classify 0uL;

  let mut barr = [| z64; 25sz |];
  A.pts_to_len barr;
  A.pts_to_len barr;

  table_lens ();
  let rc_tbl = table rc_arr 24sz;

  digest_impl st barr rc_tbl buf tot out out_len r suffix seen;

  drop_table rc_tbl;
  ()
}

(** {2 SHA3-224} *)

(** Reset the state to the empty message. *)
fn sha3_224_init (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to st vst0 ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 144 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok 144sz vst vbuf vtot' (Seq.empty #S8.t))
{
  init_impl st tot 144sz;
}

(** Absorb [data]. *)
fn sha3_224_update (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (data: A.array S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok 144sz vst0 vbuf vtot seen /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok 144sz vst vbuf' vtot' (Seq.append seen vdata))
{
  keccak_update st buf tot data data_len 144sz seen;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha3_224_digest (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (out: A.array S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t))
          (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout0 **
         pure (stream_ok 144sz vst0 vbuf vtot seen /\ Seq.length vout0 == 28)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout **
  pure (vout == sha3_224 seen)
{
  keccak_digest st buf tot out 28sz 144sz sha3_suffix seen;
}

(** {2 SHA3-256} *)

(** Reset the state to the empty message. *)
fn sha3_256_init (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to st vst0 ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 136 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok 136sz vst vbuf vtot' (Seq.empty #S8.t))
{
  init_impl st tot 136sz;
}

(** Absorb [data]. *)
fn sha3_256_update (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (data: A.array S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok 136sz vst0 vbuf vtot seen /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok 136sz vst vbuf' vtot' (Seq.append seen vdata))
{
  keccak_update st buf tot data data_len 136sz seen;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha3_256_digest (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (out: A.array S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t))
          (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout0 **
         pure (stream_ok 136sz vst0 vbuf vtot seen /\ Seq.length vout0 == 32)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout **
  pure (vout == sha3_256 seen)
{
  keccak_digest st buf tot out 32sz 136sz sha3_suffix seen;
}

(** {2 SHA3-384} *)

(** Reset the state to the empty message. *)
fn sha3_384_init (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to st vst0 ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 104 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok 104sz vst vbuf vtot' (Seq.empty #S8.t))
{
  init_impl st tot 104sz;
}

(** Absorb [data]. *)
fn sha3_384_update (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (data: A.array S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok 104sz vst0 vbuf vtot seen /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok 104sz vst vbuf' vtot' (Seq.append seen vdata))
{
  keccak_update st buf tot data data_len 104sz seen;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha3_384_digest (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (out: A.array S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t))
          (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout0 **
         pure (stream_ok 104sz vst0 vbuf vtot seen /\ Seq.length vout0 == 48)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout **
  pure (vout == sha3_384 seen)
{
  keccak_digest st buf tot out 48sz 104sz sha3_suffix seen;
}

(** {2 SHA3-512} *)

(** Reset the state to the empty message. *)
fn sha3_512_init (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to st vst0 ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 72 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok 72sz vst vbuf vtot' (Seq.empty #S8.t))
{
  init_impl st tot 72sz;
}

(** Absorb [data]. *)
fn sha3_512_update (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (data: A.array S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok 72sz vst0 vbuf vtot seen /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok 72sz vst vbuf' vtot' (Seq.append seen vdata))
{
  keccak_update st buf tot data data_len 72sz seen;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha3_512_digest (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (out: A.array S8.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t))
          (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout0 **
         pure (stream_ok 72sz vst0 vbuf vtot seen /\ Seq.length vout0 == 64)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout **
  pure (vout == sha3_512 seen)
{
  keccak_digest st buf tot out 64sz 72sz sha3_suffix seen;
}

(** {2 SHAKE128} *)

(** Reset the state to the empty message. *)
fn shake128_init (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to st vst0 ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 168 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok 168sz vst vbuf vtot' (Seq.empty #S8.t))
{
  init_impl st tot 168sz;
}

(** Absorb [data]. *)
fn shake128_update (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (data: A.array S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok 168sz vst0 vbuf vtot seen /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok 168sz vst vbuf' vtot' (Seq.append seen vdata))
{
  keccak_update st buf tot data data_len 168sz seen;
}

(** Squeeze [len out] bytes.  The state is left usable: a further [update]
    continues the same message, and a further [digest] at another length is
    the same output stream. *)
fn shake128_digest (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (out: A.array S8.t) (out_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t))
          (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout0 **
         pure (stream_ok 168sz vst0 vbuf vtot seen)
         ** pure (SZ.v out_len == Seq.length vout0)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout **
  pure (Seq.length vout == Seq.length vout0 /\
        vout == shake128 seen (Seq.length vout0))
{
  keccak_digest st buf tot out out_len 168sz shake_suffix seen;
}

(** {2 SHAKE256} *)

(** Reset the state to the empty message. *)
fn shake256_init (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
        (#vst0: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
        (#vtot: erased (Seq.seq SZ.t))
requires A.pts_to st vst0 ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot **
         pure (Seq.length vst0 == 25 /\ Seq.length vbuf == 136 /\ Seq.length vtot == 1)
ensures exists* (vst: Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf #pb vbuf ** A.pts_to tot vtot' **
  pure (stream_ok 136sz vst vbuf vtot' (Seq.empty #S8.t))
{
  init_impl st tot 136sz;
}

(** Absorb [data]. *)
fn shake256_update (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (data: A.array S8.t) (data_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#vst0: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
          (#vtot: erased (Seq.seq SZ.t))
          (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to st vst0 ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok 136sz vst0 vbuf vtot seen /\
               SZ.fits (Seq.length seen + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vst: Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to st vst ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok 136sz vst vbuf' vtot' (Seq.append seen vdata))
{
  keccak_update st buf tot data data_len 136sz seen;
}

(** Squeeze [len out] bytes.  The state is left usable: a further [update]
    continues the same message, and a further [digest] at another length is
    the same output stream. *)
fn shake256_digest (st: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
          (out: A.array S8.t) (out_len: SZ.t) (seen: erased (Seq.seq S8.t))
          (#pst: perm) (#vst0: erased (Seq.seq S64.t))
          (#pbuf: perm) (#vbuf: erased (Seq.seq S8.t))
          (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
          (#vout0: erased (Seq.seq S8.t))
requires A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to out vout0 **
         pure (stream_ok 136sz vst0 vbuf vtot seen)
         ** pure (SZ.v out_len == Seq.length vout0)
ensures exists* (vout: Seq.seq S8.t).
  A.pts_to st #pst vst0 ** A.pts_to buf #pbuf vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to out vout **
  pure (Seq.length vout == Seq.length vout0 /\
        vout == shake256 seen (Seq.length vout0))
{
  keccak_digest st buf tot out out_len 136sz shake_suffix seen;
}
