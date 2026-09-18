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

(** The error matrices.

    Frodo's secrets and errors are sampled from a discrete distribution
    given by its inverse CDF table: two bytes of randomness per entry, a
    comparison against each table row, and a sign bit.  The whole matrix is
    one call.

    What the KEM needs is only that the result is the matrix the
    specification samples from the same bytes, which is the statement
    below; the flat traversal and the constant-time table walk that get
    there are [Hacl.Frodo.Sample]'s business. *)
module Hacl.Frodo.Sample

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Frodo.Params

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U16 = FStar.UInt16
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module F = Spec.Frodo

(** [m <- sample_matrix p r c (b[base .. base + 2rc])].  [cdf] is the
    parameter set's inverse CDF table. *)
val sample_matrix ([@@@FStar.Attributes.monomorphize] p: params)
                  (cdf: A.array U16.t) (m: A.array S16.t) (b: A.array S8.t)
                  (r: SZ.t) (c: SZ.t { 0 < SZ.v c }) (blen: SZ.t)
                  (base: SZ.t { SZ.v base + 2 * (SZ.v r * SZ.v c) <= SZ.v blen })
                  (#pc: perm) (#pb: perm)
                  (#vcdf: erased (Seq.lseq U16.t (cdf_len p)))
                  (#vm: erased (Seq.seq S16.t))
                  (#vb: erased (Seq.lseq S8.t (SZ.v blen)))
  : stt unit
    (requires A.pts_to cdf #pc vcdf ** A.pts_to m vm ** A.pts_to b #pb vb **
              pure (reveal vcdf == reveal p.cdf /\
                    Seq.length vm == SZ.v r * SZ.v c /\ SZ.v blen < pow2 32))
    (ensures fun _ -> exists* v.
             A.pts_to cdf #pc vcdf ** A.pts_to m v ** A.pts_to b #pb vb **
             pure (v == F.sample_matrix p (SZ.v r) (SZ.v c)
                          (Seq.slice vb (SZ.v base) (SZ.v base + 2 * (SZ.v r * SZ.v c)))))
