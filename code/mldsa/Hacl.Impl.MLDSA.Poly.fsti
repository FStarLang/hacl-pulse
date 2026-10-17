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


(** The polynomial operations the rest of ML-DSA needs from
    {!Hacl.Impl.MLDSA.NTT}, behind an interface so that the transform's
    implementation (eight layers, tables, butterfly lemmas) stays out of
    the solver's context of every module that opens this one; see
    {!Hacl.Impl.MLKEM.Poly} for the measurements that motivated this. *)
module Hacl.Impl.MLDSA.Poly
#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.NTT
open Hacl.Impl.MLDSA.Zq

module A = Pulse.Lib.Array
module Seq = FStar.Seq

(** [f <- NTT(f)], in place. *)
val ntt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
  : stt unit
      (A.pts_to f vf ** pure (Seq.length vf == n))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == ntt (as_poly vf)))

(** [f <- NTT^-1(f)], in place. *)
val intt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
  : stt unit
      (A.pts_to f vf ** pure (Seq.length vf == n))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == intt (as_poly vf)))

(** [dst <- a * b] in the NTT domain (pointwise). *)
val multiply (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
  : stt unit
      (A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
       pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == poly_mul (as_poly va) (as_poly vb)))
