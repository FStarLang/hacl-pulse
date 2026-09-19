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

(** The samplers, as seen by their callers.

    {!Hacl.Impl.MLKEM.Sample} carries all of rejection sampling and the
    incremental SHAKE128 with it, and every definition in it lands in the
    solver's context of any module that opens it.  The matrix and noise
    loops need only these two operations, so they go through this interface
    instead.  See {!Hacl.Impl.MLKEM.Poly} for the same argument about the
    transform, where it was worth eight minutes a module. *)
module Hacl.Impl.MLKEM.Sampler

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Sample
open Hacl.Impl.MLKEM.Zq

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module U8 = FStar.UInt8
module Seq = FStar.Seq
module S = Hacl.Impl.MLKEM.Sample

(** Algorithm 7, [SampleNTT]. *)
fn sample_ntt_impl (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                   (#vd: erased (Seq.seq zqt))
                   (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to seed #ps vs **
         pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs)
ensures exists* v. A.pts_to dst v ** A.pts_to seed #ps vs **
  pure (Seq.length v == n /\ as_poly v == sample_ntt vs)
{
  S.sample_ntt_impl dst seed slen;
}

(** Algorithm 8, [SamplePolyCBD]. *)
fn sample_poly_cbd_impl (dst: A.array zqt) (s: A.array S8.t) (byte: U8.t) (eta: SZ.t)
                        (#vd: erased (Seq.seq zqt)) (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to s #p vs **
         pure (Seq.length vd == n /\ Seq.length vs == 32 /\
               1 <= SZ.v eta /\ SZ.v eta <= 3)
ensures exists* v. A.pts_to dst v ** A.pts_to s #p vs **
  pure (Seq.length v == n /\ Seq.length vs == 32 /\
        1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        as_poly v == sample_poly_cbd (SZ.v eta) vs byte)
{
  S.sample_poly_cbd_impl dst s byte eta;
}
