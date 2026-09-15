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

(** The MD5 entry point.

    MD5 is thoroughly broken -- collisions are minutes of laptop time -- and
    is here only because protocols that predate its break still specify it;
    see the header of [Spec.MD5].  The C signature is

      void Hacl_Hash_MD5_md5(uint8_t *out, uint8_t *input, size_t len); *)
module Hacl.Hash.MD5

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MD5
open Hacl.Hash.MD5.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

fn md5 (out: A.array S8.t) (input: A.array S8.t) (input_len: SZ.t)
       (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vout == 16 /\ Seq.length vin < pow2 61)
         ** pure (SZ.v input_len == Seq.length vin)
ensures exists* vout'. A.pts_to out vout' ** A.pts_to input #pin vin **
        pure (Seq.length vin < max_input /\ vout' == hash vin)
{
  A.pts_to_len out;
  A.pts_to_len input;
  hash_impl out input input_len;
}
