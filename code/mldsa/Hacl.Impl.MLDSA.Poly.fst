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


module Hacl.Impl.MLDSA.Poly
#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.NTT
open Hacl.Impl.MLDSA.Zq

module N = Hacl.Impl.MLDSA.NTT
module NV = Hacl.Impl.MLDSA.NTT.Vec256
module V = Hacl.Vec256
module A = Pulse.Lib.Array
module Seq = FStar.Seq

fn ntt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
requires A.pts_to f vf ** pure (Seq.length vf == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == ntt (as_poly vf))
{
  if (Hacl.X64.x86_64) {
    if (V.supported ()) { NV.ntt_inplace f } else { N.ntt_inplace f }
  } else { N.ntt_inplace f }
}

fn intt_inplace (f: A.array zqt) (#vf: erased (Seq.seq zqt))
requires A.pts_to f vf ** pure (Seq.length vf == n)
ensures exists* v. A.pts_to f v **
        pure (Seq.length vf == n /\ Seq.length v == n /\ as_poly v == intt (as_poly vf))
{
  if (Hacl.X64.x86_64) {
    if (V.supported ()) { NV.intt_inplace f } else { N.intt_inplace f }
  } else { N.intt_inplace f }
}

fn multiply (dst a b: A.array zqt) (#pa #pb: perm) (#vd #va #vb: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vd == n /\ Seq.length va == n /\ Seq.length vb == n)
ensures exists* v. A.pts_to dst v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length v == n /\ Seq.length va == n /\ Seq.length vb == n /\
              as_poly v == poly_mul (as_poly va) (as_poly vb))
{
  if (Hacl.X64.x86_64) {
    if (V.supported ()) { NV.multiply dst a b } else { N.multiply dst a b }
  } else { N.multiply dst a b }
}
