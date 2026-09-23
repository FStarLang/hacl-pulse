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

(** The secp256k1 curve constants, in five fifty-two-bit limbs.

    [Hacl.K256.Tables] holds the four-limb tables the scalar field still
    uses -- the modulus, its negation, the Montgomery factors and the two
    exponents -- and this module holds the four curve constants, which
    moved to the new field representation and are no longer in Montgomery
    form.  They are therefore the numbers themselves, and for [b] and [3b]
    that means a single nonzero limb.

    They live apart from the rest because [Hacl.K256.Tables] opens
    [Spec.Bignum4], where [nl] is four and [base] is [2^64]; opening
    [Spec.Bignum52] in the same file would shadow both. *)
module Hacl.K256.Tables52

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum52
open Spec.K256.Freeze
open Hacl.Impl.Limb4
open Hacl.Impl.Lit52

module Seq = FStar.Seq
module L = FStar.List.Tot
module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module U64 = FStar.UInt64

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** The curve coefficient [b = 7], needed only by the on-curve test. *)
let b_list : list S64.t = [
  S64.classify 7uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL
]

let b_arr : (a: G.static_array S64.t
                 { Seq.length (G.static_array_elems a) == nl /\
                   vals (G.static_array_elems a) == limbs_of K.b_coeff })
  = assert_norm (L.length b_list == nl);
    assert_norm (lbnd b_list);
    assert_norm (leval b_list == 7);
    assert_norm (K.b_coeff == 7);
    assert_norm (7 < pow2 256);
    lit_limbs b_list K.b_coeff;
    G.mk_static_array b_list

(** [3b = 21], which is what the complete addition formulas multiply by. *)
let b3_list : list S64.t = [
  S64.classify 21uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL
]

let b3_arr : (a: G.static_array S64.t
                  { Seq.length (G.static_array_elems a) == nl /\
                    vals (G.static_array_elems a) == limbs_of K.b3 })
  = assert_norm (L.length b3_list == nl);
    assert_norm (lbnd b3_list);
    assert_norm (leval b3_list == 21);
    assert_norm (K.b3 == 21);
    assert_norm (21 < pow2 256);
    lit_limbs b3_list K.b3;
    G.mk_static_array b3_list

(** The base point. *)
let gx_list : list S64.t = [
  S64.classify 705178180786072uL; S64.classify 3855836460717471uL;
  S64.classify 4089131105950716uL; S64.classify 3301581525494108uL;
  S64.classify 133858670344668uL
]

let gx_arr : (a: G.static_array S64.t
                  { Seq.length (G.static_array_elems a) == nl /\
                    vals (G.static_array_elems a) == limbs_of K.g_x })
  = assert_norm (L.length gx_list == nl);
    assert_norm (lbnd gx_list);
    assert_norm (leval gx_list ==
      55066263022277343669578718895168534326250603453777594175500187360389116729240);
    assert_norm (K.g_x ==
      55066263022277343669578718895168534326250603453777594175500187360389116729240);
    assert_norm (
      55066263022277343669578718895168534326250603453777594175500187360389116729240
        < pow2 256);
    lit_limbs gx_list K.g_x;
    G.mk_static_array gx_list

let gy_list : list S64.t = [
  S64.classify 2199641648059576uL; S64.classify 1278080618437060uL;
  S64.classify 3959378566518708uL; S64.classify 3455034269351872uL;
  S64.classify 79417610544803uL
]

let gy_arr : (a: G.static_array S64.t
                  { Seq.length (G.static_array_elems a) == nl /\
                    vals (G.static_array_elems a) == limbs_of K.g_y })
  = assert_norm (L.length gy_list == nl);
    assert_norm (lbnd gy_list);
    assert_norm (leval gy_list ==
      32670510020758816978083085130507043184471273380659243275938904335757337482424);
    assert_norm (K.g_y ==
      32670510020758816978083085130507043184471273380659243275938904335757337482424);
    assert_norm (
      32670510020758816978083085130507043184471273380659243275938904335757337482424
        < pow2 256);
    lit_limbs gy_list K.g_y;
    G.mk_static_array gy_list

#pop-options
