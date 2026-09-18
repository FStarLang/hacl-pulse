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

(** A, and the two products that are taken against it.

    A is [n] by [n] -- one and three quarter megabytes at the largest
    parameter set -- and it is used exactly twice, each time against a
    matrix that is only eight wide.  Neither product materializes it:
    both expand one row at a time, use it and throw it away, so the
    working set is a single row rather than the whole matrix.  What the
    caller sees is only the two products, each equal to the one the
    specification names; how A is streamed is [Hacl.Frodo.Gen]'s business
    and is not visible here.

    Keeping the row expansion behind this interface is also what lets
    [Hacl.Frodo.KEM] be checked without waiting for it: the two products
    are the only thing the KEM needs, and their statements are short. *)
module Hacl.Frodo.Gen

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Frodo.Params

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module M = Spec.Frodo.Matrix
module F = Spec.Frodo

(** [b <- A S^T], with A given by its seed and S stored transposed.  The
    result is [n] by [nbar]. *)
val mul_t_as ([@@@FStar.Attributes.monomorphize] p: params)
             (seed: A.array S8.t) (st: A.array S16.t) (b: A.array S16.t)
             (#ps: perm) (#pt: perm)
             (#vseed: erased (Seq.lseq S8.t 16))
             (#vst: erased (Seq.lseq S16.t (nbar * n p)))
             (#vb0: erased (Seq.lseq S16.t (n p * nbar)))
  : stt unit
    (requires A.pts_to seed #ps vseed ** A.pts_to st #pt vst ** A.pts_to b vb0)
    (ensures fun _ -> exists* vb.
             A.pts_to seed #ps vseed ** A.pts_to st #pt vst ** A.pts_to b vb **
             pure (vb == M.mul_t (n p) (n p) nbar (F.gen_matrix p vseed) vst))

(** [b <- S' A].  The result is [nbar] by [n]. *)
val mul_sa ([@@@FStar.Attributes.monomorphize] p: params)
           (seed: A.array S8.t) (sp: A.array S16.t) (b: A.array S16.t)
           (#ps: perm) (#pt: perm)
           (#vseed: erased (Seq.lseq S8.t 16))
           (#vsp: erased (Seq.lseq S16.t (nbar * n p)))
           (#vb0: erased (Seq.lseq S16.t (nbar * n p)))
  : stt unit
    (requires A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp ** A.pts_to b vb0)
    (ensures fun _ -> exists* vb.
             A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp ** A.pts_to b vb **
             pure (vb == M.mul nbar (n p) (n p) vsp (F.gen_matrix p vseed)))
