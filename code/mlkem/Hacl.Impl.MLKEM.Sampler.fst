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
module S4 = Hacl.Impl.MLKEM.Sample4
module P4 = Hacl.Impl.MLKEM.PRF4

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

(** [SampleNTT] of four seeds at once. *)
[@@CPrologue "__attribute__((target(\"avx2\")))"]
fn sample_ntt4_impl (d0 d1 d2 d3: A.array zqt) (s0 s1 s2 s3: A.array S8.t) (slen: SZ.t)
                    (#vd0 #vd1 #vd2 #vd3: erased (Seq.seq zqt))
                    (#p0 #p1 #p2 #p3: perm)
                    (#vs0 #vs1 #vs2 #vs3: erased (Seq.seq S8.t))
requires A.pts_to d0 vd0 ** A.pts_to d1 vd1 ** A.pts_to d2 vd2 ** A.pts_to d3 vd3 **
         A.pts_to s0 #p0 vs0 ** A.pts_to s1 #p1 vs1 **
         A.pts_to s2 #p2 vs2 ** A.pts_to s3 #p3 vs3 **
         pure (Seq.length vd0 == n /\ Seq.length vd1 == n /\
               Seq.length vd2 == n /\ Seq.length vd3 == n /\
               SZ.v slen == Seq.length vs0 /\ SZ.v slen == Seq.length vs1 /\
               SZ.v slen == Seq.length vs2 /\ SZ.v slen == Seq.length vs3)
ensures exists* (w0 w1 w2 w3: Seq.seq zqt).
  A.pts_to d0 w0 ** A.pts_to d1 w1 ** A.pts_to d2 w2 ** A.pts_to d3 w3 **
  A.pts_to s0 #p0 vs0 ** A.pts_to s1 #p1 vs1 **
  A.pts_to s2 #p2 vs2 ** A.pts_to s3 #p3 vs3 **
  pure (Seq.length w0 == n /\ Seq.length w1 == n /\
        Seq.length w2 == n /\ Seq.length w3 == n /\
        as_poly w0 == sample_ntt vs0 /\ as_poly w1 == sample_ntt vs1 /\
        as_poly w2 == sample_ntt vs2 /\ as_poly w3 == sample_ntt vs3)
{
  S4.sample_ntt4_impl d0 d1 d2 d3 s0 s1 s2 s3 slen;
}

(** Algorithm 8, [SamplePolyCBD]. *)
fn sample_poly_cbd_impl (dst: A.array zqt) (s: A.array S8.t) (byte: U8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
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

(** Algorithm 8 proper. *)
fn cbd_impl (dst: A.array zqt) (b: A.array S8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
            (#vd: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to b #p vb **
         pure (Seq.length vd == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               Seq.length vb == 64 * SZ.v eta)
ensures exists* v. A.pts_to dst v ** A.pts_to b #p vb **
  pure (Seq.length v == n /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        Seq.length vb == 64 * SZ.v eta /\
        as_poly v == sample_cbd (SZ.v eta) vb)
{
  S.cbd_impl dst b eta;
}

(** Four PRFs at once. *)
fn prf4_impl (o0 o1 o2 o3: A.array S8.t) (s: A.array S8.t)
             (b0 b1 b2 b3: U8.t) (eta: SZ.t)
             (#vo0 #vo1 #vo2 #vo3: erased (Seq.seq S8.t))
             (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to o0 vo0 ** A.pts_to o1 vo1 ** A.pts_to o2 vo2 ** A.pts_to o3 vo3 **
         A.pts_to s #p vs **
         pure (Seq.length vs == 32 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               Seq.length vo0 == 192 /\ Seq.length vo1 == 192 /\
               Seq.length vo2 == 192 /\ Seq.length vo3 == 192)
ensures exists* (w0 w1 w2 w3: Seq.seq S8.t).
  A.pts_to o0 w0 ** A.pts_to o1 w1 ** A.pts_to o2 w2 ** A.pts_to o3 w3 **
  A.pts_to s #p vs **
  pure (Seq.length vs == 32 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        Seq.length w0 == 192 /\ Seq.length w1 == 192 /\
        Seq.length w2 == 192 /\ Seq.length w3 == 192 /\
        Seq.slice w0 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b0 /\
        Seq.slice w1 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b1 /\
        Seq.slice w2 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b2 /\
        Seq.slice w3 0 (64 * SZ.v eta) == prf (SZ.v eta) vs b3)
{
  P4.prf4_impl o0 o1 o2 o3 s b0 b1 b2 b3 eta;
}
