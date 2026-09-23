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

(** The P-256 constants, as compile-time arrays.

    Eight tables of four limbs: for each of the two moduli, the modulus
    itself, its two's complement, and the two Montgomery radix constants.
    They are the only place in the implementation where P-256's actual
    numbers appear.

    {b Connecting a literal to the specification.}  [Spec.P256.Field] reads
    the limbs off the number -- [limbs x] is [Seq.init nl (fun i -> x / 2^32i
    mod 2^32)] -- so what a table has to prove is that its eight literals
    are that sequence.  Proving it index by index means four case splits
    inside a query that also carries [Seq.init], which is slow enough to be
    unusable.

    Going through the value instead costs nothing.  [leval] and [lbnd] are
    the evaluation and the bound written as recursions on the {i list},
    which the normaliser computes in one step and with no sequence axioms at
    all; [lit_ok] relates them to their sequence counterparts by one generic
    induction; and [lit_limbs] closes the loop with [eval_digit], which says
    that a bounded sequence is determined by the number it evaluates to.
    Each table then needs three [assert_norm]s on concrete arithmetic and
    one generic lemma call. *)
module Hacl.P256.Tables

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Lit4
open Hacl.Impl.Table

module Seq = FStar.Seq
module L = FStar.List.Tot
module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module U64 = FStar.UInt64

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

#push-options "--fuel 0 --ifuel 0"

(** {2 The tables} *)

(** The field prime, as four limbs. *)
let fms_list : list S64.t = [
  S64.classify 18446744073709551615uL; S64.classify 4294967295uL;
  S64.classify 0uL; S64.classify 18446744069414584321uL
]

(** [2^256] less the field prime: subtraction without borrows. *)
let fnm_list : list S64.t = [
  S64.classify 1uL; S64.classify 18446744069414584320uL;
  S64.classify 18446744073709551615uL; S64.classify 4294967294uL
]

(** [R mod p] -- the Montgomery form of one. *)
let fr1_list : list S64.t = [
  S64.classify 1uL; S64.classify 18446744069414584320uL;
  S64.classify 18446744073709551615uL; S64.classify 4294967294uL
]

(** [R^2 mod p] -- the Montgomery form of [R]. *)
let fr2_list : list S64.t = [
  S64.classify 3uL; S64.classify 18446744056529682431uL;
  S64.classify 18446744073709551614uL; S64.classify 21474836477uL
]

(** The group order, as four limbs. *)
let qms_list : list S64.t = [
  S64.classify 17562291160714782033uL; S64.classify 13611842547513532036uL;
  S64.classify 18446744073709551615uL; S64.classify 18446744069414584320uL
]

(** [2^256] less the group order. *)
let qnm_list : list S64.t = [
  S64.classify 884452912994769583uL; S64.classify 4834901526196019579uL;
  S64.classify 0uL; S64.classify 4294967295uL
]

(** [R mod n]. *)
let qr1_list : list S64.t = [
  S64.classify 884452912994769583uL; S64.classify 4834901526196019579uL;
  S64.classify 0uL; S64.classify 4294967295uL
]

(** [R^2 mod n]. *)
let qr2_list : list S64.t = [
  S64.classify 9449762124159643298uL; S64.classify 5087230966250696614uL;
  S64.classify 2901921493521525849uL; S64.classify 7413256579398063648uL
]

let fms_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.ms })
  = assert_norm (L.length fms_list == nl);
    assert_norm (lbnd fms_list);
    assert_norm (leval fms_list == 115792089210356248762697446949407573530086143415290314195533631308867097853951);
    assert_norm (P.prime == 115792089210356248762697446949407573530086143415290314195533631308867097853951);
    assert_norm (115792089210356248762697446949407573530086143415290314195533631308867097853951 < pow2 256);
    lit_limbs fms_list P.prime;
    G.mk_static_array fms_list

let fnm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.nm })
  = assert_norm (L.length fnm_list == nl);
    assert_norm (lbnd fnm_list);
    assert_norm (leval fnm_list == 26959946660873538059280334323183841250350249843923952699046031785985);
    assert_norm ((pow2 256 - P.prime) == 26959946660873538059280334323183841250350249843923952699046031785985);
    assert_norm (26959946660873538059280334323183841250350249843923952699046031785985 < pow2 256);
    lit_limbs fnm_list (pow2 256 - P.prime);
    G.mk_static_array fnm_list

let fr1_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.r1 })
  = assert_norm (L.length fr1_list == nl);
    assert_norm (lbnd fr1_list);
    assert_norm (leval fr1_list == 26959946660873538059280334323183841250350249843923952699046031785985);
    assert_norm ((pow2 256 % P.prime) == 26959946660873538059280334323183841250350249843923952699046031785985);
    assert_norm (26959946660873538059280334323183841250350249843923952699046031785985 < pow2 256);
    lit_limbs fr1_list (pow2 256 % P.prime);
    G.mk_static_array fr1_list

let fr2_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.r2 })
  = assert_norm (L.length fr2_list == nl);
    assert_norm (lbnd fr2_list);
    assert_norm (leval fr2_list == 134799733323198995502561713907086292154532538166959272814710328655875);
    assert_norm ((pow2 256 * pow2 256 % P.prime) == 134799733323198995502561713907086292154532538166959272814710328655875);
    assert_norm (134799733323198995502561713907086292154532538166959272814710328655875 < pow2 256);
    lit_limbs fr2_list (pow2 256 * pow2 256 % P.prime);
    G.mk_static_array fr2_list

let qms_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.ms })
  = assert_norm (L.length qms_list == nl);
    assert_norm (lbnd qms_list);
    assert_norm (leval qms_list == 115792089210356248762697446949407573529996955224135760342422259061068512044369);
    assert_norm (P.order == 115792089210356248762697446949407573529996955224135760342422259061068512044369);
    assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044369 < pow2 256);
    lit_limbs qms_list P.order;
    G.mk_static_array qms_list

let qnm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.nm })
  = assert_norm (L.length qnm_list == nl);
    assert_norm (lbnd qnm_list);
    assert_norm (leval qnm_list == 26959946660873538059280334323273029441504803697035324946844617595567);
    assert_norm ((pow2 256 - P.order) == 26959946660873538059280334323273029441504803697035324946844617595567);
    assert_norm (26959946660873538059280334323273029441504803697035324946844617595567 < pow2 256);
    lit_limbs qnm_list (pow2 256 - P.order);
    G.mk_static_array qnm_list

let qr1_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.r1 })
  = assert_norm (L.length qr1_list == nl);
    assert_norm (lbnd qr1_list);
    assert_norm (leval qr1_list == 26959946660873538059280334323273029441504803697035324946844617595567);
    assert_norm ((pow2 256 % P.order) == 26959946660873538059280334323273029441504803697035324946844617595567);
    assert_norm (26959946660873538059280334323273029441504803697035324946844617595567 < pow2 256);
    lit_limbs qr1_list (pow2 256 % P.order);
    G.mk_static_array qr1_list

let qr2_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.r2 })
  = assert_norm (L.length qr2_list == nl);
    assert_norm (lbnd qr2_list);
    assert_norm (leval qr2_list == 46533765739406314298121036767150998762426774378559716911348521029833835802274);
    assert_norm ((pow2 256 * pow2 256 % P.order) == 46533765739406314298121036767150998762426774378559716911348521029833835802274);
    assert_norm (46533765739406314298121036767150998762426774378559716911348521029833835802274 < pow2 256);
    lit_limbs qr2_list (pow2 256 * pow2 256 % P.order);
    G.mk_static_array qr2_list

(** One, for leaving Montgomery form. *)
let one_list : list S64.t = [
  S64.classify 1uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL
]

let one_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs 1 })
  = assert_norm (L.length one_list == nl);
    assert_norm (lbnd one_list);
    assert_norm (leval one_list == 1);
    assert_norm (1 < pow2 256);
    lit_limbs one_list 1;
    G.mk_static_array one_list

(** {2 The exponents} *)

(** [p - 2], the inversion exponent. *)
let finv_e_list : list U64.t = [
  18446744073709551613uL; 4294967295uL;
  0uL; 18446744069414584321uL
]

let finv_e_arr : (a: G.static_array U64.t
                  { pvals (G.static_array_elems a) == limbs (P.prime - 2) })
  = assert_norm (L.length finv_e_list == nl);
    assert_norm (ulbnd finv_e_list);
    assert_norm (uleval finv_e_list == 115792089210356248762697446949407573530086143415290314195533631308867097853949);
    assert_norm (P.prime - 2 == 115792089210356248762697446949407573530086143415290314195533631308867097853949);
    assert_norm (115792089210356248762697446949407573530086143415290314195533631308867097853949 < pow2 256);
    ulit_limbs finv_e_list (P.prime - 2);
    G.mk_static_array finv_e_list

(** [(p + 1) / 4], the square-root exponent; [p] is [3 mod 4]. *)
let fsqrt_e_list : list U64.t = [
  0uL; 1073741824uL;
  4611686018427387904uL; 4611686017353646080uL
]

let fsqrt_e_arr : (a: G.static_array U64.t
                  { pvals (G.static_array_elems a) == limbs ((P.prime + 1) / 4) })
  = assert_norm (L.length fsqrt_e_list == nl);
    assert_norm (ulbnd fsqrt_e_list);
    assert_norm (uleval fsqrt_e_list == 28948022302589062190674361737351893382521535853822578548883407827216774463488);
    assert_norm ((P.prime + 1) / 4 == 28948022302589062190674361737351893382521535853822578548883407827216774463488);
    assert_norm (28948022302589062190674361737351893382521535853822578548883407827216774463488 < pow2 256);
    ulit_limbs fsqrt_e_list ((P.prime + 1) / 4);
    G.mk_static_array fsqrt_e_list

(** [n - 2], for inverting a scalar. *)
let qinv_e_list : list U64.t = [
  17562291160714782031uL; 13611842547513532036uL;
  18446744073709551615uL; 18446744069414584320uL
]

let qinv_e_arr : (a: G.static_array U64.t
                  { pvals (G.static_array_elems a) == limbs (P.order - 2) })
  = assert_norm (L.length qinv_e_list == nl);
    assert_norm (ulbnd qinv_e_list);
    assert_norm (uleval qinv_e_list == 115792089210356248762697446949407573529996955224135760342422259061068512044367);
    assert_norm (P.order - 2 == 115792089210356248762697446949407573529996955224135760342422259061068512044367);
    assert_norm (115792089210356248762697446949407573529996955224135760342422259061068512044367 < pow2 256);
    ulit_limbs qinv_e_list (P.order - 2);
    G.mk_static_array qinv_e_list

(** {2 Curve constants}

    The coefficient [b] and the base point, already multiplied by [R]: they
    are only ever used as field elements, so storing them in Montgomery
    form saves two conversions per call and costs nothing. *)

(** The curve coefficient [b] in Montgomery form. *)
let bm_list : list S64.t = [
  S64.classify 15608596021259845087uL; S64.classify 12461466548982526096uL;
  S64.classify 16546823903870267094uL; S64.classify 15866188208926050356uL
]

let bm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs (P.b_coeff * pow2 256 % P.prime) })
  = assert_norm (L.length bm_list == nl);
    assert_norm (lbnd bm_list);
    assert_norm (leval bm_list == 99593677540221402957765480916910020772520766868399186769503856397241456836063);
    assert_norm (P.b_coeff * pow2 256 % P.prime == 99593677540221402957765480916910020772520766868399186769503856397241456836063);
    assert_norm (99593677540221402957765480916910020772520766868399186769503856397241456836063 < pow2 256);
    lit_limbs bm_list (P.b_coeff * pow2 256 % P.prime);
    G.mk_static_array bm_list

(** Three, in Montgomery form.  The curve equation names [-3] as the
    coefficient [a]; the addition formulas fold it away, but the on-curve
    test cannot. *)
let threem_list : list S64.t = [
  S64.classify 3uL; S64.classify 18446744060824649728uL;
  S64.classify 18446744073709551615uL; S64.classify 12884901884uL
]

let threem_arr : (a: G.static_array S64.t
                     { vals (G.static_array_elems a) == limbs (3 * pow2 256 % P.prime) })
  = assert_norm (L.length threem_list == nl);
    assert_norm (lbnd threem_list);
    assert_norm (leval threem_list == 80879839982620614177841002969551523751050749531771858097138095357955);
    assert_norm (3 * pow2 256 % P.prime == 80879839982620614177841002969551523751050749531771858097138095357955);
    assert_norm (80879839982620614177841002969551523751050749531771858097138095357955 < pow2 256);
    lit_limbs threem_list (3 * pow2 256 % P.prime);
    G.mk_static_array threem_list

(** The base point, in Montgomery form. *)
let gxm_list : list S64.t = [
  S64.classify 8784043285714375740uL; S64.classify 8483257759279461889uL;
  S64.classify 8789745728267363600uL; S64.classify 1770019616739251654uL
]

let gxm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs (P.g_x * pow2 256 % P.prime) })
  = assert_norm (L.length gxm_list == nl);
    assert_norm (lbnd gxm_list);
    assert_norm (leval gxm_list == 11110593207902424140321080247206512405358633331993495164878354046817554469948);
    assert_norm (P.g_x * pow2 256 % P.prime == 11110593207902424140321080247206512405358633331993495164878354046817554469948);
    assert_norm (11110593207902424140321080247206512405358633331993495164878354046817554469948 < pow2 256);
    lit_limbs gxm_list (P.g_x * pow2 256 % P.prime);
    G.mk_static_array gxm_list

(** The base point, in Montgomery form. *)
let gym_list : list S64.t = [
  S64.classify 15992936863339206154uL; S64.classify 10037038012062884956uL;
  S64.classify 15197544864945402661uL; S64.classify 9615747158586711429uL
]

let gym_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs (P.g_y * pow2 256 % P.prime) })
  = assert_norm (L.length gym_list == nl);
    assert_norm (lbnd gym_list);
    assert_norm (leval gym_list == 60359023176204190920225817201443260813112970217682417638161152432929735267850);
    assert_norm (P.g_y * pow2 256 % P.prime == 60359023176204190920225817201443260813112970217682417638161152432929735267850);
    assert_norm (60359023176204190920225817201443260813112970217682417638161152432929735267850 < pow2 256);
    lit_limbs gym_list (P.g_y * pow2 256 % P.prime);
    G.mk_static_array gym_list

(** {2 Reading a table}

    Each is four limbs, and the permission never comes back: these are
    [static const] arrays in the emitted C. *)

inline_for_extraction
fn finv_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs (P.prime - 2))
{ table finv_e_arr 4sz }

inline_for_extraction
fn fsqrt_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs ((P.prime + 1) / 4))
{ table fsqrt_e_arr 4sz }

inline_for_extraction
fn qinv_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs (P.order - 2))
{ table qinv_e_arr 4sz }

inline_for_extraction
fn mone () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == limbs 1)
{ table one_arr 4sz }

inline_for_extraction
fn fms () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.ms)
{ table fms_arr 4sz }

inline_for_extraction
fn fnm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.nm)
{ table fnm_arr 4sz }

inline_for_extraction
fn fr1 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.r1)
{ table fr1_arr 4sz }

inline_for_extraction
fn fr2 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.r2)
{ table fr2_arr 4sz }

inline_for_extraction
fn qms () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.ms)
{ table qms_arr 4sz }

inline_for_extraction
fn qnm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.nm)
{ table qnm_arr 4sz }

inline_for_extraction
fn qr1 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.r1)
{ table qr1_arr 4sz }

inline_for_extraction
fn qr2 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.r2)
{ table qr2_arr 4sz }

(** The Montgomery constants.  The field prime's is [1], a gift from its
    Solinas shape. *)

inline_for_extraction
let fmu : (w: S64.t { S64.v w == fmod.mu }) = S64.classify 1uL

inline_for_extraction
let qmu : (w: S64.t { S64.v w == qmod.mu }) = S64.classify 14758798090332847183uL

#pop-options
#pop-options
