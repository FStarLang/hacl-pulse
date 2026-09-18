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

(** The five FFDHE moduli, in the program image.

    Their own module for the same reason the SHA-2 tables have one: a
    [static_array] is a definition, so naming it once means one C array
    however many entry points reach it.  Custard emits only what an entry
    point reaches, so a unit that uses FFDHE-2048 and nothing else gets two
    hundred and fifty-six bytes of table, not the three kilobytes that all
    five groups come to. *)
module Hacl.FFDHE.Tables

open Spec.FFDHE

module G = Pulse.Lib.GlobalArray
module Seq = FStar.Seq
module S64 = Hacl.Secret.UInt64

let ffdhe2048_arr : (a: G.static_array S64.t
                       { G.static_array_elems a == (ffdhe2048 <: Seq.seq S64.t) })
  = G.mk_static_array ffdhe2048_list

let ffdhe3072_arr : (a: G.static_array S64.t
                       { G.static_array_elems a == (ffdhe3072 <: Seq.seq S64.t) })
  = G.mk_static_array ffdhe3072_list

let ffdhe4096_arr : (a: G.static_array S64.t
                       { G.static_array_elems a == (ffdhe4096 <: Seq.seq S64.t) })
  = G.mk_static_array ffdhe4096_list

let ffdhe6144_arr : (a: G.static_array S64.t
                       { G.static_array_elems a == (ffdhe6144 <: Seq.seq S64.t) })
  = G.mk_static_array ffdhe6144_list

let ffdhe8192_arr : (a: G.static_array S64.t
                       { G.static_array_elems a == (ffdhe8192 <: Seq.seq S64.t) })
  = G.mk_static_array ffdhe8192_list
