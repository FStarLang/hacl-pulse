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

(** The P-384 constants, as compile-time arrays of six 64-bit limbs.

    Both moduli, the Montgomery radix constant [R^2] for each (with
    [R = 2^384]), and the curve constants the field code needs, the latter
    in Montgomery form.  They are the only place in the implementation where
    P-384's actual numbers appear.

    A table is written as a list of literals, and what it has to prove is
    the number they evaluate to.  [leval] is that evaluation written as a
    recursion on the {i list}, which the normaliser computes in one step;
    [lit_ok] relates it to [Hacl.Bignum.Base.num] by one induction, as in
    [Hacl.Impl.Lit4].  Each table then needs one [assert_norm] on concrete
    arithmetic. *)
module Hacl.P384.Tables

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Bignum.Base
open Hacl.Impl.Table

module Seq = FStar.Seq
module L = FStar.List.Tot
module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P384

(** {2 Literals} *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let rec leval (l: list S64.t) : GTot nat =
  match l with
  | [] -> 0
  | h :: t -> S64.v h + base * leval t

let rec lit_ok (l: list S64.t)
  : Lemma (ensures num (Seq.seq_of_list l) == leval l /\
                   Seq.length (Seq.seq_of_list l) == L.length l)
          (decreases l)
  = match l with
    | [] -> Seq.lemma_eq_intro (Seq.seq_of_list l) Seq.empty
    | h :: t ->
      lit_ok t;
      let s = vals (Seq.seq_of_list l) in
      let n = Seq.length s in
      Classical.forall_intro (Seq.lemma_seq_of_list_index l);
      Classical.forall_intro (Seq.lemma_seq_of_list_index t);
      Seq.lemma_eq_intro (Seq.slice s 1 n) (vals (Seq.seq_of_list t))

(** The bottom limb, which is what the Montgomery constant is checked
    against. *)
let lit_low (l: list S64.t)
  : Lemma (requires Cons? l)
          (ensures Seq.length (Seq.seq_of_list l) > 0 /\
                   Seq.index (Seq.seq_of_list l) 0 == L.hd l)
  = Seq.lemma_seq_of_list_index l 0

#pop-options

(** What a table promises: six limbs evaluating to [x]. *)
let tbl (v: Seq.seq S64.t) (x: nat) : prop = Seq.length v == 6 /\ num v == x

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** The field prime. *)
let pms_list : list S64.t = [
  S64.classify 4294967295uL;
  S64.classify 18446744069414584320uL;
  S64.classify 18446744073709551614uL;
  S64.classify 18446744073709551615uL;
  S64.classify 18446744073709551615uL;
  S64.classify 18446744073709551615uL
]

(** The group order. *)
let qms_list : list S64.t = [
  S64.classify 17072048233947408755uL;
  S64.classify 6348401684107011962uL;
  S64.classify 14367412456785391071uL;
  S64.classify 18446744073709551615uL;
  S64.classify 18446744073709551615uL;
  S64.classify 18446744073709551615uL
]

(** [R^2 mod p], for entering Montgomery form and for reduction. *)
let pr2_list : list S64.t = [
  S64.classify 18446744065119617025uL;
  S64.classify 8589934592uL;
  S64.classify 18446744065119617024uL;
  S64.classify 8589934592uL;
  S64.classify 1uL;
  S64.classify 0uL
]

(** [R^2 mod n]. *)
let qr2_list : list S64.t = [
  S64.classify 3256554584917936553uL;
  S64.classify 18391999277541532697uL;
  S64.classify 13564358545871743303uL;
  S64.classify 15279949475123764421uL;
  S64.classify 4589268600508278933uL;
  S64.classify 902107514168524577uL
]

(** [R mod p]: one, in Montgomery form. *)
let pr1_list : list S64.t = [
  S64.classify 18446744069414584321uL;
  S64.classify 4294967295uL;
  S64.classify 1uL;
  S64.classify 0uL;
  S64.classify 0uL;
  S64.classify 0uL
]

(** [b R mod p]. *)
let bm_list : list S64.t = [
  S64.classify 581395848458481100uL;
  S64.classify 17809957346689692396uL;
  S64.classify 8643006485390950958uL;
  S64.classify 16372638458395724514uL;
  S64.classify 13126622871277412500uL;
  S64.classify 14774077593024970745uL
]

(** [3 R mod p]. *)
let threem_list : list S64.t = [
  S64.classify 18446744060824649731uL;
  S64.classify 12884901887uL;
  S64.classify 3uL;
  S64.classify 0uL;
  S64.classify 0uL;
  S64.classify 0uL
]

(** The base point's [x], in Montgomery form. *)
let gxm_list : list S64.t = [
  S64.classify 4454189113653900584uL;
  S64.classify 2369870743683386936uL;
  S64.classify 9771750146904378734uL;
  S64.classify 7229551204834152191uL;
  S64.classify 9308930686126579243uL;
  S64.classify 5564951339003155731uL
]

(** The base point's [y], in Montgomery form. *)
let gym_list : list S64.t = [
  S64.classify 2523209505731486974uL;
  S64.classify 11655219901025790380uL;
  S64.classify 10064955099576512592uL;
  S64.classify 14322381509056856025uL;
  S64.classify 15960759442596276288uL;
  S64.classify 3132442392059561449uL
]

let pms_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (P.prime) /\ Seq.length (G.static_array_elems a) > 0 /\ S64.v (Seq.index (G.static_array_elems a) 0) == 4294967295 })
  = assert_norm (L.length pms_list == 6);
    assert_norm (leval pms_list == 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319);
    assert_norm (P.prime == 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319);
    lit_ok pms_list;
    lit_low pms_list;
    assert_norm (S64.v (L.hd pms_list) == 4294967295);
    G.mk_static_array pms_list


let qms_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (P.order) /\ Seq.length (G.static_array_elems a) > 0 /\ S64.v (Seq.index (G.static_array_elems a) 0) == 17072048233947408755 })
  = assert_norm (L.length qms_list == 6);
    assert_norm (leval qms_list == 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643);
    assert_norm (P.order == 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643);
    lit_ok qms_list;
    lit_low qms_list;
    assert_norm (S64.v (L.hd qms_list) == 17072048233947408755);
    G.mk_static_array qms_list


let pr2_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (pow2 384 * pow2 384 % P.prime) })
  = assert_norm (L.length pr2_list == 6);
    assert_norm (leval pr2_list == 115792089291236088764149366330485615516483229599873605960255493794524727083009);
    assert_norm (pow2 384 * pow2 384 % P.prime == 115792089291236088764149366330485615516483229599873605960255493794524727083009);
    lit_ok pr2_list;
    G.mk_static_array pr2_list


let qr2_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (pow2 384 * pow2 384 % P.order) })
  = assert_norm (L.length qr2_list == 6);
    assert_norm (leval qr2_list == 1926889955270807207284364373743377144127886613064468223890781010531391223293594548775097723903321707631980877973929);
    assert_norm (pow2 384 * pow2 384 % P.order == 1926889955270807207284364373743377144127886613064468223890781010531391223293594548775097723903321707631980877973929);
    lit_ok qr2_list;
    G.mk_static_array qr2_list


let pr1_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (pow2 384 % P.prime) })
  = assert_norm (L.length pr1_list == 6);
    assert_norm (leval pr1_list == 340282367000166625977638945021017194497);
    assert_norm (pow2 384 % P.prime == 340282367000166625977638945021017194497);
    lit_ok pr1_list;
    G.mk_static_array pr1_list


let bm_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (P.b_coeff * pow2 384 % P.prime) })
  = assert_norm (L.length bm_list == 6);
    assert_norm (leval bm_list == 31557238206390940957597319936599174722055881914217182876712135092282706590848110034779859449912744153716396065369548);
    assert_norm (P.b_coeff * pow2 384 % P.prime == 31557238206390940957597319936599174722055881914217182876712135092282706590848110034779859449912744153716396065369548);
    lit_ok bm_list;
    G.mk_static_array bm_list


let threem_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (3 * pow2 384 % P.prime) })
  = assert_norm (L.length threem_list == 6);
    assert_norm (leval threem_list == 1020847101000499877932916835063051583491);
    assert_norm (3 * pow2 384 % P.prime == 1020847101000499877932916835063051583491);
    lit_ok threem_list;
    G.mk_static_array threem_list


let gxm_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (P.g_x * pow2 384 % P.prime) })
  = assert_norm (L.length gxm_list == 6);
    assert_norm (leval gxm_list == 11886663915641450262705530632889500068342115401403085422162279173580545128391329974348679073644930512304398693086504);
    assert_norm (P.g_x * pow2 384 % P.prime == 11886663915641450262705530632889500068342115401403085422162279173580545128391329974348679073644930512304398693086504);
    lit_ok gxm_list;
    G.mk_static_array gxm_list


let gym_arr : (a: G.static_array S64.t { tbl (G.static_array_elems a) (P.g_y * pow2 384 % P.prime) })
  = assert_norm (L.length gym_list == 6);
    assert_norm (leval gym_list == 6690856340208307986067173017744274988727037133556318391016008114468400829859944973987663397697166869847345570489598);
    assert_norm (P.g_y * pow2 384 % P.prime == 6690856340208307986067173017744274988727037133556318391016008114468400829859944973987663397697166869847345570489598);
    lit_ok gym_list;
    G.mk_static_array gym_list

(** {2 Reading a table}

    The permission never comes back: these are [static const] arrays in the
    emitted C. *)

inline_for_extraction
fn pms () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (P.prime) /\ S64.v (Seq.index v 0) == 4294967295)
{ table pms_arr 6sz }

inline_for_extraction
fn qms () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (P.order) /\ S64.v (Seq.index v 0) == 17072048233947408755)
{ table qms_arr 6sz }

inline_for_extraction
fn pr2 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (pow2 384 * pow2 384 % P.prime))
{ table pr2_arr 6sz }

inline_for_extraction
fn qr2 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (pow2 384 * pow2 384 % P.order))
{ table qr2_arr 6sz }

inline_for_extraction
fn pr1 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (pow2 384 % P.prime))
{ table pr1_arr 6sz }

inline_for_extraction
fn bm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (P.b_coeff * pow2 384 % P.prime))
{ table bm_arr 6sz }

inline_for_extraction
fn threem () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (3 * pow2 384 % P.prime))
{ table threem_arr 6sz }

inline_for_extraction
fn gxm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (P.g_x * pow2 384 % P.prime))
{ table gxm_arr 6sz }

inline_for_extraction
fn gym () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (tbl v (P.g_y * pow2 384 % P.prime))
{ table gym_arr 6sz }

(** {2 The Montgomery constants}

    [-m^-1 mod 2^64] for each modulus. *)

let mu_ok (mu m0: nat) : prop = (mu * m0 + 1) % base == 0

inline_for_extraction
let pmu : (w: S64.t { mu_ok (S64.v w) 4294967295 }) =
  assert_norm ((4294967297 * 4294967295 + 1) % pow2 64 == 0);
  S64.classify 4294967297uL

inline_for_extraction
let qmu : (w: S64.t { mu_ok (S64.v w) 17072048233947408755 }) =
  assert_norm ((7986114184663260229 * 17072048233947408755 + 1) % pow2 64 == 0);
  S64.classify 7986114184663260229uL

#pop-options
