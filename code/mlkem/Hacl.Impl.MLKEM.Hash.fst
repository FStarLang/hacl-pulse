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


(** See {!Hacl.Impl.MLKEM.Hash} (the interface) for why this module
    exists.  It forwards three calls. *)
module Hacl.Impl.MLKEM.Hash

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Hash.SHA3

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module Seq = FStar.Seq

fn hash_g_impl' (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#v0: erased (Seq.seq S8.t)) (#p: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out v0 ** A.pts_to msg #p vm **
         pure (Seq.length v0 == 64 /\ SZ.v msg_len == Seq.length vm)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to out v ** A.pts_to msg #p vm **
  pure (Seq.length v == 64 /\ v == Spec.MLKEM.hash_g vm)
{
  sha3_512 out msg msg_len;
}

let hash_g_impl = hash_g_impl'

fn hash_h_impl' (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#v0: erased (Seq.seq S8.t)) (#p: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out v0 ** A.pts_to msg #p vm **
         pure (Seq.length v0 == 32 /\ SZ.v msg_len == Seq.length vm)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to out v ** A.pts_to msg #p vm **
  pure (Seq.length v == 32 /\ v == Spec.MLKEM.hash_h vm)
{
  sha3_256 out msg msg_len;
}

let hash_h_impl = hash_h_impl'

fn hash_j_impl' (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#v0: erased (Seq.seq S8.t)) (#p: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out v0 ** A.pts_to msg #p vm **
         pure (Seq.length v0 == 32 /\ SZ.v msg_len == Seq.length vm)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to out v ** A.pts_to msg #p vm **
  pure (Seq.length v == 32 /\ v == Spec.MLKEM.hash_j vm)
{
  shake256 out 32sz msg msg_len;
}

let hash_j_impl = hash_j_impl'
