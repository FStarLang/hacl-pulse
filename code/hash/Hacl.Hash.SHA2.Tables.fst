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

(** The SHA-2 tables, in the program image.

    Their own module because four entry-point modules need them -- the
    one-shot hashes, HMAC, HKDF and the streaming interface -- and a
    [static_array] is a definition, so two copies would be two arrays.  Custard
    emits only what an entry point reaches, so a unit that uses SHA-256 and
    nothing else gets [k256] and one initial state, not all six tables. *)
module Hacl.Hash.SHA2.Tables

open Spec.SHA2.Constants

module G = Pulse.Lib.GlobalArray
module Seq = FStar.Seq
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

(** One [static const] array per table, in the program image.  The list is the
    one in [Spec.SHA2.Constants], so the table the compiler lays out and the
    table the specification talks about are the same literals.

    The relation to the specification is in the *type* rather than in a lemma.
    It is true by unfolding either way -- [static_array_elems (mk_static_array
    l)] is [Seq.seq_of_list l] by the refinement on [mk_static_array], and that
    is how [Spec.SHA2.Constants] defines the sequences -- but a lemma would put
    six sixty-four-element lists in scope at once, and the two facts a caller
    actually needs would then be found, if at all, inside a query that also
    carries a heap and the whole of [Spec.SHA2].  In the type, each fact
    arrives on its own and needs no unfolding at all.  The length comes with
    it, since [k256] is an [lseq]. *)

let k256_arr : (a: G.static_array S32.t
                  { G.static_array_elems a == (k256 <: Seq.seq S32.t) })
  = G.mk_static_array k256_list

let k512_arr : (a: G.static_array S64.t
                  { G.static_array_elems a == (k512 <: Seq.seq S64.t) })
  = G.mk_static_array k512_list

let iv224_arr : (a: G.static_array S32.t
                   { G.static_array_elems a == (iv224 <: Seq.seq S32.t) })
  = G.mk_static_array iv224_list

let iv256_arr : (a: G.static_array S32.t
                   { G.static_array_elems a == (iv256 <: Seq.seq S32.t) })
  = G.mk_static_array iv256_list

let iv384_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == (iv384 <: Seq.seq S64.t) })
  = G.mk_static_array iv384_list

let iv512_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == (iv512 <: Seq.seq S64.t) })
  = G.mk_static_array iv512_list
