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

(** The SHA-1 entry point.

    SHA-1 is broken; see the header of [Spec.SHA1] for why the library has one
    anyway.  Unlike SHA-2 there are no constant tables to load and no family
    to choose from, so this is a thin name over [Hacl.Hash.SHA1.Core.hash_impl]
    and the C signature is

      void Hacl_Hash_SHA1_sha1(uint8_t *out, uint8_t *input, size_t len); *)
module Hacl.Hash.SHA1

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA1
open Hacl.Hash.SHA1.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

fn sha1 (out: A.array S8.t) (input: A.array S8.t) (input_len: SZ.t)
        (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vout == 20 /\ Seq.length vin < pow2 61)
         ** pure (SZ.v input_len == Seq.length vin)
ensures exists* vout'. A.pts_to out vout' ** A.pts_to input #pin vin **
        pure (Seq.length vin < max_input /\ vout' == hash vin)
{
  A.pts_to_len out;
  A.pts_to_len input;
  hash_impl out input input_len;
}
