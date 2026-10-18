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


(** The ML-DSA samplers, as seen by their callers.

    {!Hacl.Impl.MLDSA.Sample} carries the rejection loops, the incremental
    SHAKE and their lemmas, all of which would land in the solver context
    of any module that opened it; key generation and signing need only
    these five operations, so they go through this interface instead (as
    ML-KEM does with {!Hacl.Impl.MLKEM.Sampler}).

    Parameters are passed as in ML-KEM: the parameter set [p] is erased,
    and the sizes the code needs are runtime arguments tied to it by the
    precondition and specialised by [monomorphize]. *)
module Hacl.Impl.MLDSA.Sampler

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Sample
open Hacl.Impl.MLDSA.Zq

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module Seq = FStar.Seq

(** Algorithm 30, [RejNTTPoly]: a polynomial in the NTT domain from a
    SHAKE128 seed (thirty-four bytes in ExpandA). *)
val rej_ntt_poly_impl (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                      (#vd: erased (Seq.seq zqt))
                      (#ps: perm) (#vs: erased (Seq.seq S8.t))
  : stt unit
      (A.pts_to dst vd ** A.pts_to seed #ps vs **
       pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to seed #ps vs **
        pure (Seq.length v == n /\ as_poly v == rej_ntt_poly vs))

(** Algorithm 31, [RejBoundedPoly]: a polynomial with coefficients in
    [[-eta, eta]] from a SHAKE256 seed (sixty-six bytes in ExpandS). *)
val rej_bounded_poly_impl (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                          ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                          (#vd: erased (Seq.seq zqt))
                          (#ps: perm) (#vs: erased (Seq.seq S8.t))
  : stt unit
      (A.pts_to dst vd ** A.pts_to seed #ps vs **
       pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs /\
             (SZ.v eta == 2 \/ SZ.v eta == 4)))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to seed #ps vs **
        pure (Seq.length v == n /\ (SZ.v eta == 2 \/ SZ.v eta == 4) /\
              as_poly v == rej_bounded_poly (SZ.v eta) vs))

(** Algorithm 29, [SampleInBall]: the challenge polynomial from the
    commitment hash [c~] ([slen] is its length, [lambda / 4]). *)
val sample_in_ball_impl (p: erased params) (dst: A.array zqt) (seed: A.array S8.t) (slen: SZ.t)
                        ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                        (#vd: erased (Seq.seq zqt))
                        (#ps: perm) (#vs: erased (Seq.seq S8.t))
  : stt unit
      (A.pts_to dst vd ** A.pts_to seed #ps vs **
       pure (Seq.length vd == n /\ SZ.v slen == Seq.length vs /\ SZ.v tau == p.tau))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to seed #ps vs **
        pure (Seq.length v == n /\ as_poly v == sample_in_ball p vs))

(** Algorithm 32, [ExpandA]: [A-hat] as [k * l] polynomials, row major,
    from the thirty-two byte [rho]. *)
val expand_a_impl (p: erased params) (dst: A.array zqt) (rho: A.array S8.t)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                  (#vd: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
  : stt unit
      (A.pts_to dst vd ** A.pts_to rho #pr vr **
       pure (Seq.length vr == 32 /\ SZ.v k == p.k /\ SZ.v l == p.l /\
             Seq.length vd == p.k * p.l * n))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to rho #pr vr **
        pure (Seq.length vr == 32 /\ Seq.length v == p.k * p.l * n /\
              as_zqs v == expand_a p vr))

(** Algorithm 33, [ExpandS]: [s1] ([l] polynomials) and [s2] ([k]
    polynomials) from the sixty-four byte [rho']. *)
val expand_s_impl (p: erased params) (s1: A.array zqt) (s2: A.array zqt) (rho: A.array S8.t)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                  (#v1: erased (Seq.seq zqt)) (#v2: erased (Seq.seq zqt))
                  (#pr: perm) (#vr: erased (Seq.seq S8.t))
  : stt unit
      (A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to rho #pr vr **
       pure (Seq.length vr == 64 /\ SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
             Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n))
      (fun _ -> exists* (w1: Seq.seq zqt) (w2: Seq.seq zqt).
        A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to rho #pr vr **
        pure (Seq.length vr == 64 /\ Seq.length w1 == p.l * n /\ Seq.length w2 == p.k * n /\
              as_zqs w1 == expand_s1 p vr /\ as_zqs w2 == expand_s2 p vr))
