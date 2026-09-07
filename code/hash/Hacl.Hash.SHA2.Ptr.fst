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

(** The flat C interface to SHA-2.

    Everything inside the library passes [Pulse.Lib.Slice.slice], which is a
    pointer and a length travelling together and which the verifier can reason
    about.  A slice extracts to a two-field struct, and a C caller should not
    have to know about it, so the functions that appear in the generated header
    take a bare pointer and a [size_t] instead:

      void Hacl_Hash_SHA2_Ptr_sha256(uint8_t *out, uint8_t *input, size_t len);

    The conversion is [Pulse.Lib.Slice.arrayptr_to_slice_intro], which is free
    at runtime: it pairs the pointer with the length the caller supplied and
    hands back the permission when the slice is dropped.  Because the length is
    a proof-irrelevant witness on the way in, the precondition that says
    "[input] really has [input_len] bytes" is the caller's obligation, exactly
    as in C.

    These are the only entry points that should be passed to
    [--custard_entry]. *)
module Hacl.Hash.SHA2.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** SHA-224.  [out] must have room for twenty-eight bytes. *)
fn sha224 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 28 /\ Seq.length vin == SZ.v input_len /\
               Seq.length vin < pow2 61)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_224 vin)
{
  let so = S.arrayptr_to_slice_intro out 28sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA2.sha224 so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}


(** SHA-256.  [out] must have room for thirty-two bytes. *)
fn sha256 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 32 /\ Seq.length vin == SZ.v input_len /\
               Seq.length vin < pow2 61)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_256 vin)
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA2.sha256 so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}


(** SHA-384.  [out] must have room for forty-eight bytes. *)
fn sha384 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 48 /\ Seq.length vin == SZ.v input_len /\
               Seq.length vin < pow2 61)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_384 vin)
{
  let so = S.arrayptr_to_slice_intro out 48sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA2.sha384 so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}


(** SHA-512.  [out] must have room for sixty-four bytes. *)
fn sha512 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 64 /\ Seq.length vin == SZ.v input_len /\
               Seq.length vin < pow2 61)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_512 vin)
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA2.sha512 so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}
