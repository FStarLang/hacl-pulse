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

(** The incremental interface to the four SHA-2 algorithms.

    The state a caller has to keep is three flat pieces of memory and nothing
    else: the eight-word accumulator, one block of buffered bytes, and a single
    [size_t] holding the number of bytes seen.  There is no allocation, no
    destructor and no error code; a caller that can declare three arrays can
    use this interface, and a caller that wants a struct can put the three
    arrays in one.

    Ghostly, the state also carries [seen], the message absorbed so far.  It is
    an [erased] argument, so it costs nothing at runtime, and it is what lets
    [digest] promise [Spec.SHA2.hash p seen].

    As in [Hacl.Hash.SHA2], the round constants and the initial state are
    written into stack arrays on entry, since the direct-to-C backend cannot
    emit a constant global.  For [update] that is sixty-four stores per call
    regardless of how much data the call absorbs, so callers that feed the hash
    in very small pieces pay for it; the fix is a backend change, not an
    interface change. *)
module Hacl.Streaming.SHA2

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.SHA2.Streaming
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Streaming

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** The two block lengths, as literals.  [block_len] is [16 * (bits / 8)] and
    the type class does not reduce on its own inside a Pulse context. *)
let block_len_32 (_: unit) : Lemma (block_len #S32.t == 64) =
  assert_norm (bits #S32.t == 32)

let block_len_64 (_: unit) : Lemma (block_len #S64.t == 128) =
  assert_norm (bits #S64.t == 64)


(** {2 SHA224} *)

(** Reset the state to the empty message. *)
fn sha224_init (acc: S.slice S32.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
              (#vacc: erased (Seq.seq S32.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires S.pts_to acc vacc ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S32.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot' **
  pure (stream_ok sha2_224 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  block_len_32 ();
  let z = S32.classify 0ul;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv224 ivt;
  init_impl sha2_224 ivt acc buf tot;
  S.to_array ivt;
}

(** Absorb [data]. *)
fn sha224_update (acc: S.slice S32.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (data: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to buf vbuf ** S.pts_to tot vtot **
         S.pts_to data #pd vdata **
         pure (stream_ok sha2_224 vacc vbuf vtot seen /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf vbuf' ** S.pts_to tot vtot' **
  S.pts_to data #pd vdata **
  pure (stream_ok sha2_224 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut wsarr = [| z; 64sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 64sz;
  update_impl sha2_224 kt wsb acc buf tot data seen;
  S.to_array wsb;
  S.to_array kt;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha224_digest (acc: S.slice S32.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (out: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires S.pts_to acc #pa vacc ** S.pts_to buf vbuf ** S.pts_to tot #ptot vtot **
         S.pts_to out vout **
         pure (stream_ok sha2_224 vacc vbuf vtot seen /\ Seq.length vout == 28)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  S.pts_to acc #pa vacc ** S.pts_to buf vbuf' ** S.pts_to tot #ptot vtot **
  S.pts_to out vout' **
  pure (Seq.length seen < max_input #S32.t /\ vout' == hash sha2_224 seen)
{
  block_len_32 ();
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut wsarr = [| z; 64sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 64sz;
  digest_impl sha2_224 kt wsb acc buf tot out seen;
  S.to_array wsb;
  S.to_array kt;
}


(** {2 SHA256} *)

(** Reset the state to the empty message. *)
fn sha256_init (acc: S.slice S32.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
              (#vacc: erased (Seq.seq S32.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires S.pts_to acc vacc ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S32.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot' **
  pure (stream_ok sha2_256 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  block_len_32 ();
  let z = S32.classify 0ul;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv256 ivt;
  init_impl sha2_256 ivt acc buf tot;
  S.to_array ivt;
}

(** Absorb [data]. *)
fn sha256_update (acc: S.slice S32.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (data: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to buf vbuf ** S.pts_to tot vtot **
         S.pts_to data #pd vdata **
         pure (stream_ok sha2_256 vacc vbuf vtot seen /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf vbuf' ** S.pts_to tot vtot' **
  S.pts_to data #pd vdata **
  pure (stream_ok sha2_256 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut wsarr = [| z; 64sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 64sz;
  update_impl sha2_256 kt wsb acc buf tot data seen;
  S.to_array wsb;
  S.to_array kt;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha256_digest (acc: S.slice S32.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (out: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires S.pts_to acc #pa vacc ** S.pts_to buf vbuf ** S.pts_to tot #ptot vtot **
         S.pts_to out vout **
         pure (stream_ok sha2_256 vacc vbuf vtot seen /\ Seq.length vout == 32)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  S.pts_to acc #pa vacc ** S.pts_to buf vbuf' ** S.pts_to tot #ptot vtot **
  S.pts_to out vout' **
  pure (Seq.length seen < max_input #S32.t /\ vout' == hash sha2_256 seen)
{
  block_len_32 ();
  let z = S32.classify 0ul;
  let mut karr = [| z; 64sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 64sz;
  fill_k256 kt;
  let mut wsarr = [| z; 64sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 64sz;
  digest_impl sha2_256 kt wsb acc buf tot out seen;
  S.to_array wsb;
  S.to_array kt;
}


(** {2 SHA384} *)

(** Reset the state to the empty message. *)
fn sha384_init (acc: S.slice S64.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
              (#vacc: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires S.pts_to acc vacc ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot' **
  pure (stream_ok sha2_384 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  block_len_64 ();
  let z = S64.classify 0uL;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv384 ivt;
  init_impl sha2_384 ivt acc buf tot;
  S.to_array ivt;
}

(** Absorb [data]. *)
fn sha384_update (acc: S.slice S64.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (data: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to buf vbuf ** S.pts_to tot vtot **
         S.pts_to data #pd vdata **
         pure (stream_ok sha2_384 vacc vbuf vtot seen /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf vbuf' ** S.pts_to tot vtot' **
  S.pts_to data #pd vdata **
  pure (stream_ok sha2_384 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut wsarr = [| z; 80sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 80sz;
  update_impl sha2_384 kt wsb acc buf tot data seen;
  S.to_array wsb;
  S.to_array kt;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha384_digest (acc: S.slice S64.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (out: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires S.pts_to acc #pa vacc ** S.pts_to buf vbuf ** S.pts_to tot #ptot vtot **
         S.pts_to out vout **
         pure (stream_ok sha2_384 vacc vbuf vtot seen /\ Seq.length vout == 48)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  S.pts_to acc #pa vacc ** S.pts_to buf vbuf' ** S.pts_to tot #ptot vtot **
  S.pts_to out vout' **
  pure (Seq.length seen < max_input #S64.t /\ vout' == hash sha2_384 seen)
{
  block_len_64 ();
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut wsarr = [| z; 80sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 80sz;
  digest_impl sha2_384 kt wsb acc buf tot out seen;
  S.to_array wsb;
  S.to_array kt;
}


(** {2 SHA512} *)

(** Reset the state to the empty message. *)
fn sha512_init (acc: S.slice S64.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
              (#vacc: erased (Seq.seq S64.t)) (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
requires S.pts_to acc vacc ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\ Seq.length vtot == 1)
ensures exists* (vacc': Seq.seq S64.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf #pb vbuf ** S.pts_to tot vtot' **
  pure (stream_ok sha2_512 vacc' vbuf vtot' (Seq.empty #S8.t))
{
  block_len_64 ();
  let z = S64.classify 0uL;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv512 ivt;
  init_impl sha2_512 ivt acc buf tot;
  S.to_array ivt;
}

(** Absorb [data]. *)
fn sha512_update (acc: S.slice S64.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (data: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#vtot: erased (Seq.seq SZ.t))
                (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires S.pts_to acc vacc ** S.pts_to buf vbuf ** S.pts_to tot vtot **
         S.pts_to data #pd vdata **
         pure (stream_ok sha2_512 vacc vbuf vtot seen /\
               Seq.length seen + Seq.length vdata < pow2 61 /\
               SZ.fits (Seq.length seen + Seq.length vdata))
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  S.pts_to acc vacc' ** S.pts_to buf vbuf' ** S.pts_to tot vtot' **
  S.pts_to data #pd vdata **
  pure (stream_ok sha2_512 vacc' vbuf' vtot' (Seq.append seen vdata))
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut wsarr = [| z; 80sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 80sz;
  update_impl sha2_512 kt wsb acc buf tot data seen;
  S.to_array wsb;
  S.to_array kt;
}

(** The digest of everything seen so far.  The state is left usable. *)
fn sha512_digest (acc: S.slice S64.t) (buf: S.slice S8.t) (tot: S.slice SZ.t)
                (out: S.slice S8.t) (seen: erased (Seq.seq S8.t))
                (#pa: perm) (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
                (#vout: erased (Seq.seq S8.t))
requires S.pts_to acc #pa vacc ** S.pts_to buf vbuf ** S.pts_to tot #ptot vtot **
         S.pts_to out vout **
         pure (stream_ok sha2_512 vacc vbuf vtot seen /\ Seq.length vout == 64)
ensures exists* (vbuf': Seq.seq S8.t) (vout': Seq.seq S8.t).
  S.pts_to acc #pa vacc ** S.pts_to buf vbuf' ** S.pts_to tot #ptot vtot **
  S.pts_to out vout' **
  pure (Seq.length seen < max_input #S64.t /\ vout' == hash sha2_512 seen)
{
  block_len_64 ();
  let z = S64.classify 0uL;
  let mut karr = [| z; 80sz |];
  A.pts_to_len karr;
  let kt = S.from_array karr 80sz;
  fill_k512 kt;
  let mut wsarr = [| z; 80sz |];
  A.pts_to_len wsarr;
  let wsb = S.from_array wsarr 80sz;
  digest_impl sha2_512 kt wsb acc buf tot out seen;
  S.to_array wsb;
  S.to_array kt;
}

