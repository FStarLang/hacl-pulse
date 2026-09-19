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


(** The three hashes ML-KEM uses, as seen by their callers.

    [Hacl.Hash.SHA3] is a large Pulse module and everything in it lands in
    the solver's context of whoever opens it; K-PKE and ML-KEM need three
    fixed-output calls out of it, so they go through this interface
    instead.  The names are FIPS 203's: [G] is SHA3-512, [H] is SHA3-256
    and [J] is SHAKE256 truncated to 32 bytes. *)
module Hacl.Impl.MLKEM.Hash

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module Seq = FStar.Seq

(** [G(s)]: 64 bytes, the pair (rho, sigma) at key generation and the pair
    (shared secret, randomness) at encapsulation. *)
val hash_g_impl (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#v0: erased (Seq.seq S8.t)) (#p: perm) (#vm: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to out v0 ** A.pts_to msg #p vm **
              pure (Seq.length v0 == 64 /\ SZ.v msg_len == Seq.length vm))
    (ensures fun _ -> exists* (v: Seq.seq S8.t).
       A.pts_to out v ** A.pts_to msg #p vm **
       pure (Seq.length v == 64 /\ v == Spec.MLKEM.hash_g vm))

(** [H(s)]: 32 bytes, the hash of the encapsulation key. *)
val hash_h_impl (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#v0: erased (Seq.seq S8.t)) (#p: perm) (#vm: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to out v0 ** A.pts_to msg #p vm **
              pure (Seq.length v0 == 32 /\ SZ.v msg_len == Seq.length vm))
    (ensures fun _ -> exists* (v: Seq.seq S8.t).
       A.pts_to out v ** A.pts_to msg #p vm **
       pure (Seq.length v == 32 /\ v == Spec.MLKEM.hash_h vm))

(** [J(s)]: 32 bytes, the implicit-rejection key. *)
val hash_j_impl (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#v0: erased (Seq.seq S8.t)) (#p: perm) (#vm: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to out v0 ** A.pts_to msg #p vm **
              pure (Seq.length v0 == 32 /\ SZ.v msg_len == Seq.length vm))
    (ensures fun _ -> exists* (v: Seq.seq S8.t).
       A.pts_to out v ** A.pts_to msg #p vm **
       pure (Seq.length v == 32 /\ v == Spec.MLKEM.hash_j vm))
