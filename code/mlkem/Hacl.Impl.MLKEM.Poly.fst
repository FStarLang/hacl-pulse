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

(** Polynomial operations, as seen by their callers.

    {!Hacl.Impl.MLKEM.NTT} is large -- eight layers, two butterflies, a
    table of twiddle factors -- and every definition in it lands in the
    solver's context of every module that opens it.  That is expensive
    enough to matter: the vector loops below took eight minutes to verify
    with the transform's implementation in scope and seconds with only this
    interface.  So this module re-exports the three operations a caller
    actually needs, and nothing else, and the callers open it instead. *)
module Hacl.Impl.MLKEM.Poly

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq
module N = Hacl.Impl.MLKEM.NTT

module A = Pulse.Lib.Array
module Seq = FStar.Seq

(** [f <- NTT(f)], in place up to the scratch buffer. *)
fn ntt_inplace (f tmp: A.array zqt) (#vf #vt: erased (Seq.seq zqt))
requires A.pts_to f vf ** A.pts_to tmp vt **
         pure (Seq.length vf == n /\ Seq.length vt == n)
ensures exists* v w. A.pts_to f v ** A.pts_to tmp w **
        pure (Seq.length vf == n /\ Seq.length v == n /\ Seq.length w == n /\
              as_poly v == ntt (as_poly vf))
{
  N.ntt_inplace f tmp;
}

(** [f <- NTT^-1(f)]. *)
fn intt_inplace (f tmp: A.array zqt) (#vf #vt: erased (Seq.seq zqt))
requires A.pts_to f vf ** A.pts_to tmp vt **
         pure (Seq.length vf == n /\ Seq.length vt == n)
ensures exists* v w. A.pts_to f v ** A.pts_to tmp w **
        pure (Seq.length vf == n /\ Seq.length v == n /\ Seq.length w == n /\
              as_poly v == intt (as_poly vf))
{
  N.intt_inplace f tmp;
}

(** [dst <- a * b], both arguments in the NTT domain. *)
fn multiply (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n)
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == multiply_ntts (as_poly va) (as_poly vb))
{
  N.multiply dst a b;
}
