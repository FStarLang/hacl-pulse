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

(** The Keccak-f[1600] permutation.

    Everything the sponge needs from the permutation is this one function:
    twenty-four rounds applied in place to a twenty-five lane state.  How a
    round is written -- and it is written carefully, twenty-five unrolled
    lane functions so that the extracted C has immediate rotate counts --
    is [Hacl.Hash.SHA3.Core]'s business and is deliberately not visible
    here, so the sponge, the streaming layer and the named hashes can all
    be checked without waiting for it. *)
module Hacl.Hash.SHA3.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3
open Spec.SHA3.Constants

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module S64 = Hacl.Secret.UInt64

(** Twenty-four rounds, in place.  [b] is scratch the caller owns and its
    contents on exit are unspecified; [rc_tbl] is the round constant table. *)
val permute_impl (st: A.array S64.t) (b: A.array S64.t)
                 (rc_tbl: A.array S64.t)
                 (#vst0: erased (Seq.seq S64.t)) (#vb0: erased (Seq.seq S64.t))
                 (#prc: perm) (#vrc: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to st vst0 ** A.pts_to b vb0 ** A.pts_to rc_tbl #prc vrc **
              pure (Seq.length vst0 == 25 /\ Seq.length vb0 == 25 /\
                    reveal vrc == (rc <: Seq.seq S64.t)))
    (ensures fun _ -> exists* (vst: Seq.seq S64.t) (vb: Seq.seq S64.t).
             A.pts_to st vst ** A.pts_to b vb ** A.pts_to rc_tbl #prc vrc **
             pure (Seq.length vst0 == 25 /\ Seq.length vst == 25 /\
                   Seq.length vb == 25 /\ vst == permute (reveal vst0)))
