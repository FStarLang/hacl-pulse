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

(** The flat C interface to SHA-3 and SHAKE.

      void Hacl_Hash_SHA3_Ptr_sha3_256(uint8_t *out, uint8_t *input, size_t len);
      void Hacl_Hash_SHA3_Ptr_shake128(uint8_t *out, size_t out_len,
                                       uint8_t *input, size_t input_len);

    The SHA-3 digests have a fixed length, so their [out] length is implicit;
    the SHAKEs are extendable, so theirs is an argument.

    These are the only entry points that should be passed to
    [--custard_entry]. *)
module Hacl.Hash.SHA3.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8


(** SHA3-224.  [out] must have room for 28 bytes. *)
fn sha3_224 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
          (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 28 /\ Seq.length vin == SZ.v input_len)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (vout' == Spec.SHA3.sha3_224 vin)
{
  let so = S.arrayptr_to_slice_intro out 28sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA3.sha3_224_impl so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}

(** SHA3-256.  [out] must have room for 32 bytes. *)
fn sha3_256 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
          (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 32 /\ Seq.length vin == SZ.v input_len)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (vout' == Spec.SHA3.sha3_256 vin)
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA3.sha3_256_impl so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}

(** SHA3-384.  [out] must have room for 48 bytes. *)
fn sha3_384 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
          (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 48 /\ Seq.length vin == SZ.v input_len)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (vout' == Spec.SHA3.sha3_384 vin)
{
  let so = S.arrayptr_to_slice_intro out 48sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA3.sha3_384_impl so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}

(** SHA3-512.  [out] must have room for 64 bytes. *)
fn sha3_512 (out: AP.ptr S8.t) (input: AP.ptr S8.t) (input_len: SZ.t)
          (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == 64 /\ Seq.length vin == SZ.v input_len)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (vout' == Spec.SHA3.sha3_512 vin)
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA3.sha3_512_impl so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}

(** SHAKE128.  [out] may be any length. *)
fn shake128 (out: AP.ptr S8.t) (out_len: SZ.t) (input: AP.ptr S8.t) (input_len: SZ.t)
          (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == SZ.v out_len /\ Seq.length vin == SZ.v input_len)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (vout' == Spec.SHA3.shake128 vin (SZ.v out_len))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA3.shake128_impl so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}

(** SHAKE256.  [out] may be any length. *)
fn shake256 (out: AP.ptr S8.t) (out_len: SZ.t) (input: AP.ptr S8.t) (input_len: SZ.t)
          (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to input #pin vin **
         pure (Seq.length vout == SZ.v out_len /\ Seq.length vin == SZ.v input_len)
ensures exists* vout'. AP.pts_to out vout' ** AP.pts_to input #pin vin **
        pure (vout' == Spec.SHA3.shake256 vin (SZ.v out_len))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let si = S.arrayptr_to_slice_intro input input_len;
  Hacl.Hash.SHA3.shake256_impl so si;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim so;
}
