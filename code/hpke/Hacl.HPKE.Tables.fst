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

(** HPKE's string constants, in the program image.

    RFC 9180 labels every KDF input.  The labels are ASCII strings, and a
    string constant in C is a [static const] array, so here they are: the
    version prefix, the two suite-identifier prefixes, and the nine labels.

    The lists are the ones in [Spec.HPKE], so the bytes the compiler lays out
    and the bytes the specification talks about are the same literals, and
    the relation is in the type rather than in a lemma -- the same
    arrangement, and for the same reasons, as [Hacl.Hash.SHA2.Tables]. *)
module Hacl.HPKE.Tables

open Spec.HPKE

module G = Pulse.Lib.GlobalArray
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8

let version_arr : (a: G.static_array S8.t
                     { G.static_array_elems a == (version <: Seq.seq S8.t) })
  = G.mk_static_array version_list

let hpke_prefix_arr : (a: G.static_array S8.t
                         { G.static_array_elems a == (hpke_prefix <: Seq.seq S8.t) })
  = G.mk_static_array hpke_prefix_list

let kem_prefix_arr : (a: G.static_array S8.t
                        { G.static_array_elems a == (kem_prefix <: Seq.seq S8.t) })
  = G.mk_static_array kem_prefix_list

let label_eae_prk_arr : (a: G.static_array S8.t
                           { G.static_array_elems a == (label_eae_prk <: Seq.seq S8.t) })
  = G.mk_static_array label_eae_prk_list

let label_shared_secret_arr : (a: G.static_array S8.t
                                 { G.static_array_elems a == (label_shared_secret <: Seq.seq S8.t) })
  = G.mk_static_array label_shared_secret_list

let label_psk_id_hash_arr : (a: G.static_array S8.t
                               { G.static_array_elems a == (label_psk_id_hash <: Seq.seq S8.t) })
  = G.mk_static_array label_psk_id_hash_list

let label_info_hash_arr : (a: G.static_array S8.t
                             { G.static_array_elems a == (label_info_hash <: Seq.seq S8.t) })
  = G.mk_static_array label_info_hash_list

let label_secret_arr : (a: G.static_array S8.t
                          { G.static_array_elems a == (label_secret <: Seq.seq S8.t) })
  = G.mk_static_array label_secret_list

let label_key_arr : (a: G.static_array S8.t
                       { G.static_array_elems a == (label_key <: Seq.seq S8.t) })
  = G.mk_static_array label_key_list

let label_base_nonce_arr : (a: G.static_array S8.t
                              { G.static_array_elems a == (label_base_nonce <: Seq.seq S8.t) })
  = G.mk_static_array label_base_nonce_list

let label_exp_arr : (a: G.static_array S8.t
                       { G.static_array_elems a == (label_exp <: Seq.seq S8.t) })
  = G.mk_static_array label_exp_list

let label_sec_arr : (a: G.static_array S8.t
                       { G.static_array_elems a == (label_sec <: Seq.seq S8.t) })
  = G.mk_static_array label_sec_list
