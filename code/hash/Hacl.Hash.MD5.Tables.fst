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

(** MD5's two constant tables, as [static const] arrays in the program image.

    The lists are the ones in [Spec.MD5], so the table the compiler lays out
    and the table the specification talks about are the same literals, and the
    relation is in the type rather than in a lemma -- see the header of
    [Hacl.Hash.SHA2.Tables] for why.

    [s_arr]'s element type is the {i refined} [Spec.MD5.rot], so reading the
    rotation out of the array hands the caller its bound rather than leaving
    it to be recovered.  The refinement erases, so the C is still a
    [uint32_t] array. *)
module Hacl.Hash.MD5.Tables

open Spec.MD5

module G = Pulse.Lib.GlobalArray
module Seq = FStar.Seq
module S32 = Hacl.Secret.UInt32

let k_arr : (a: G.static_array S32.t
               { G.static_array_elems a == (k_table <: Seq.seq S32.t) })
  = G.mk_static_array k_list

let s_arr : (a: G.static_array rot
               { G.static_array_elems a == (s_table <: Seq.seq rot) })
  = G.mk_static_array s_list
