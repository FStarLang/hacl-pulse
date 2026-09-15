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

(** The secp256k1 constants, as compile-time arrays.

    Eight tables of sixteen limbs -- for each of the two moduli, the modulus
    itself, its two's complement, and the two Montgomery radix constants --
    three exponents, and the curve constants in Montgomery form.  They are
    the only place in the implementation where secp256k1's actual numbers
    appear.

    {!Hacl.Impl.Lit256} explains why each one goes through its value rather
    than through its sixteen indices. *)
module Hacl.K256.Tables

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.K256.Field
open Hacl.Impl.Limb
open Hacl.Impl.Lit256
open Hacl.Impl.Table

module Seq = FStar.Seq
module L = FStar.List.Tot
module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module U64 = FStar.UInt64

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
#push-options "--fuel 0 --ifuel 0"

(** The field prime, as sixteen limbs. *)
let fms_list : list S64.t = [
  S64.classify 64559uL; S64.classify 65535uL; S64.classify 65534uL; S64.classify 65535uL;
  S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL;
  S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL;
  S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL
]

let fms_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.ms })
  = assert_norm (L.length fms_list == nl);
    assert_norm (lbnd fms_list);
    assert_norm (leval fms_list == 115792089237316195423570985008687907853269984665640564039457584007908834671663);
    assert_norm (K.prime == 115792089237316195423570985008687907853269984665640564039457584007908834671663);
    assert_norm (115792089237316195423570985008687907853269984665640564039457584007908834671663 < pow2 256);
    lit_limbs fms_list (K.prime);
    G.mk_static_array fms_list

(** [2^256] less the field prime: subtraction without borrows. *)
let fnm_list : list S64.t = [
  S64.classify 977uL; S64.classify 0uL; S64.classify 1uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let fnm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.nm })
  = assert_norm (L.length fnm_list == nl);
    assert_norm (lbnd fnm_list);
    assert_norm (leval fnm_list == 4294968273);
    assert_norm (pow2 256 - K.prime == 4294968273);
    assert_norm (4294968273 < pow2 256);
    lit_limbs fnm_list (pow2 256 - K.prime);
    G.mk_static_array fnm_list

(** [R mod p] -- the Montgomery form of one. *)
let fr1_list : list S64.t = [
  S64.classify 977uL; S64.classify 0uL; S64.classify 1uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let fr1_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.r1 })
  = assert_norm (L.length fr1_list == nl);
    assert_norm (lbnd fr1_list);
    assert_norm (leval fr1_list == 4294968273);
    assert_norm (pow2 256 % K.prime == 4294968273);
    assert_norm (4294968273 < pow2 256);
    lit_limbs fr1_list (pow2 256 % K.prime);
    G.mk_static_array fr1_list

(** [R^2 mod p] -- the Montgomery form of [R]. *)
let fr2_list : list S64.t = [
  S64.classify 37025uL; S64.classify 14uL; S64.classify 1954uL; S64.classify 0uL;
  S64.classify 1uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let fr2_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == fmod.r2 })
  = assert_norm (L.length fr2_list == nl);
    assert_norm (lbnd fr2_list);
    assert_norm (leval fr2_list == 18446752466076602529);
    assert_norm (pow2 256 * pow2 256 % K.prime == 18446752466076602529);
    assert_norm (18446752466076602529 < pow2 256);
    lit_limbs fr2_list (pow2 256 * pow2 256 % K.prime);
    G.mk_static_array fr2_list

(** The group order, as sixteen limbs. *)
let qms_list : list S64.t = [
  S64.classify 16705uL; S64.classify 53302uL; S64.classify 24204uL; S64.classify 49106uL;
  S64.classify 41019uL; S64.classify 44872uL; S64.classify 56550uL; S64.classify 47790uL;
  S64.classify 65534uL; S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL;
  S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL
]

let qms_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.ms })
  = assert_norm (L.length qms_list == nl);
    assert_norm (lbnd qms_list);
    assert_norm (leval qms_list == 115792089237316195423570985008687907852837564279074904382605163141518161494337);
    assert_norm (K.order == 115792089237316195423570985008687907852837564279074904382605163141518161494337);
    assert_norm (115792089237316195423570985008687907852837564279074904382605163141518161494337 < pow2 256);
    lit_limbs qms_list (K.order);
    G.mk_static_array qms_list

(** [2^256] less the group order. *)
let qnm_list : list S64.t = [
  S64.classify 48831uL; S64.classify 12233uL; S64.classify 41331uL; S64.classify 16429uL;
  S64.classify 24516uL; S64.classify 20663uL; S64.classify 8985uL; S64.classify 17745uL;
  S64.classify 1uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let qnm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.nm })
  = assert_norm (L.length qnm_list == nl);
    assert_norm (lbnd qnm_list);
    assert_norm (leval qnm_list == 432420386565659656852420866394968145599);
    assert_norm (pow2 256 - K.order == 432420386565659656852420866394968145599);
    assert_norm (432420386565659656852420866394968145599 < pow2 256);
    lit_limbs qnm_list (pow2 256 - K.order);
    G.mk_static_array qnm_list

(** [R mod n]. *)
let qr1_list : list S64.t = [
  S64.classify 48831uL; S64.classify 12233uL; S64.classify 41331uL; S64.classify 16429uL;
  S64.classify 24516uL; S64.classify 20663uL; S64.classify 8985uL; S64.classify 17745uL;
  S64.classify 1uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let qr1_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.r1 })
  = assert_norm (L.length qr1_list == nl);
    assert_norm (lbnd qr1_list);
    assert_norm (leval qr1_list == 432420386565659656852420866394968145599);
    assert_norm (pow2 256 % K.order == 432420386565659656852420866394968145599);
    assert_norm (432420386565659656852420866394968145599 < pow2 256);
    lit_limbs qr1_list (pow2 256 % K.order);
    G.mk_static_array qr1_list

(** [R^2 mod n]. *)
let qr2_list : list S64.t = [
  S64.classify 53568uL; S64.classify 26583uL; S64.classify 61972uL; S64.classify 35180uL;
  S64.classify 63608uL; S64.classify 3708uL; S64.classify 38594uL; S64.classify 29716uL;
  S64.classify 1990uL; S64.classify 23501uL; S64.classify 62948uL; S64.classify 59031uL;
  S64.classify 39877uL; S64.classify 33222uL; S64.classify 7381uL; S64.classify 40295uL
]

let qr2_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == qmod.r2 })
  = assert_norm (L.length qr2_list == nl);
    assert_norm (lbnd qr2_list);
    assert_norm (leval qr2_list == 71195301480278335217902614543643724933430614355449737089222010364394701574464);
    assert_norm (pow2 256 * pow2 256 % K.order == 71195301480278335217902614543643724933430614355449737089222010364394701574464);
    assert_norm (71195301480278335217902614543643724933430614355449737089222010364394701574464 < pow2 256);
    lit_limbs qr2_list (pow2 256 * pow2 256 % K.order);
    G.mk_static_array qr2_list

(** One, for leaving Montgomery form. *)
let one_list : list S64.t = [
  S64.classify 1uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let one_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs 1 })
  = assert_norm (L.length one_list == nl);
    assert_norm (lbnd one_list);
    assert_norm (leval one_list == 1);
    assert_norm (1 == 1);
    assert_norm (1 < pow2 256);
    lit_limbs one_list (1);
    G.mk_static_array one_list

(** Half the group order, rounded down: the low-S boundary. *)
let qhalf_list : list S64.t = [
  S64.classify 8352uL; S64.classify 26651uL; S64.classify 12102uL; S64.classify 57321uL;
  S64.classify 20509uL; S64.classify 22436uL; S64.classify 28275uL; S64.classify 23895uL;
  S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL;
  S64.classify 65535uL; S64.classify 65535uL; S64.classify 65535uL; S64.classify 32767uL
]

let qhalf_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs K.q_half })
  = assert_norm (L.length qhalf_list == nl);
    assert_norm (lbnd qhalf_list);
    assert_norm (leval qhalf_list == 57896044618658097711785492504343953926418782139537452191302581570759080747168);
    assert_norm (K.q_half == 57896044618658097711785492504343953926418782139537452191302581570759080747168);
    assert_norm (57896044618658097711785492504343953926418782139537452191302581570759080747168 < pow2 256);
    lit_limbs qhalf_list (K.q_half);
    G.mk_static_array qhalf_list

(** {2 The exponents} *)

(** [p - 2], the inversion exponent. *)
let finv_e_list : list U64.t = [
  64557uL; 65535uL; 65534uL; 65535uL;
  65535uL; 65535uL; 65535uL; 65535uL;
  65535uL; 65535uL; 65535uL; 65535uL;
  65535uL; 65535uL; 65535uL; 65535uL
]

let finv_e_arr : (a: G.static_array U64.t
                  { pvals (G.static_array_elems a) == limbs (K.prime - 2) })
  = assert_norm (L.length finv_e_list == nl);
    assert_norm (ulbnd finv_e_list);
    assert_norm (uleval finv_e_list == 115792089237316195423570985008687907853269984665640564039457584007908834671661);
    assert_norm (K.prime - 2 == 115792089237316195423570985008687907853269984665640564039457584007908834671661);
    assert_norm (115792089237316195423570985008687907853269984665640564039457584007908834671661 < pow2 256);
    ulit_limbs finv_e_list (K.prime - 2);
    G.mk_static_array finv_e_list

(** [(p + 1) / 4], the square-root exponent; [p] is [3 mod 4]. *)
let fsqrt_e_list : list U64.t = [
  65292uL; 49151uL; 65535uL; 65535uL;
  65535uL; 65535uL; 65535uL; 65535uL;
  65535uL; 65535uL; 65535uL; 65535uL;
  65535uL; 65535uL; 65535uL; 16383uL
]

let fsqrt_e_arr : (a: G.static_array U64.t
                  { pvals (G.static_array_elems a) == limbs ((K.prime + 1) / 4) })
  = assert_norm (L.length fsqrt_e_list == nl);
    assert_norm (ulbnd fsqrt_e_list);
    assert_norm (uleval fsqrt_e_list == 28948022309329048855892746252171976963317496166410141009864396001977208667916);
    assert_norm ((K.prime + 1) / 4 == 28948022309329048855892746252171976963317496166410141009864396001977208667916);
    assert_norm (28948022309329048855892746252171976963317496166410141009864396001977208667916 < pow2 256);
    ulit_limbs fsqrt_e_list ((K.prime + 1) / 4);
    G.mk_static_array fsqrt_e_list

(** [n - 2], for inverting a scalar. *)
let qinv_e_list : list U64.t = [
  16703uL; 53302uL; 24204uL; 49106uL;
  41019uL; 44872uL; 56550uL; 47790uL;
  65534uL; 65535uL; 65535uL; 65535uL;
  65535uL; 65535uL; 65535uL; 65535uL
]

let qinv_e_arr : (a: G.static_array U64.t
                  { pvals (G.static_array_elems a) == limbs (K.order - 2) })
  = assert_norm (L.length qinv_e_list == nl);
    assert_norm (ulbnd qinv_e_list);
    assert_norm (uleval qinv_e_list == 115792089237316195423570985008687907852837564279074904382605163141518161494335);
    assert_norm (K.order - 2 == 115792089237316195423570985008687907852837564279074904382605163141518161494335);
    assert_norm (115792089237316195423570985008687907852837564279074904382605163141518161494335 < pow2 256);
    ulit_limbs qinv_e_list (K.order - 2);
    G.mk_static_array qinv_e_list

(** {2 Curve constants}

    The coefficient [3b] and the base point, already multiplied by [R]: they
    are only ever used as field elements, so storing them in Montgomery form
    saves two conversions per call and costs nothing.  [b] itself is needed
    only by the on-curve test, and [3b] only by the addition formulas. *)


(** The curve coefficient [b] in Montgomery form. *)
let bm_list : list S64.t = [
  S64.classify 6839uL; S64.classify 0uL; S64.classify 7uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let bm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs (K.b_coeff * pow2 256 % K.prime) })
  = assert_norm (L.length bm_list == nl);
    assert_norm (lbnd bm_list);
    assert_norm (leval bm_list == 30064777911);
    assert_norm (K.b_coeff * pow2 256 % K.prime == 30064777911);
    assert_norm (30064777911 < pow2 256);
    lit_limbs bm_list (K.b_coeff * pow2 256 % K.prime);
    G.mk_static_array bm_list

(** [3b = 21] in Montgomery form, which is what the complete formulas multiply by. *)
let b3m_list : list S64.t = [
  S64.classify 20517uL; S64.classify 0uL; S64.classify 21uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL; S64.classify 0uL; S64.classify 0uL
]

let b3m_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs (K.b3 * pow2 256 % K.prime) })
  = assert_norm (L.length b3m_list == nl);
    assert_norm (lbnd b3m_list);
    assert_norm (leval b3m_list == 90194333733);
    assert_norm (K.b3 * pow2 256 % K.prime == 90194333733);
    assert_norm (90194333733 < pow2 256);
    lit_limbs b3m_list (K.b3 * pow2 256 % K.prime);
    G.mk_static_array b3m_list

(** The base point's [x], in Montgomery form. *)
let gxm_list : list S64.t = [
  S64.classify 8343uL; S64.classify 18558uL; S64.classify 11866uL; S64.classify 55094uL;
  S64.classify 26331uL; S64.classify 10684uL; S64.classify 10579uL; S64.classify 8990uL;
  S64.classify 4764uL; S64.classify 13309uL; S64.classify 18624uL; S64.classify 38815uL;
  S64.classify 40776uL; S64.classify 59656uL; S64.classify 58947uL; S64.classify 39297uL
]

let gxm_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs (K.g_x * pow2 256 % K.prime) })
  = assert_norm (L.length gxm_list == nl);
    assert_norm (lbnd gxm_list);
    assert_norm (leval gxm_list == 69433378337113668455105412783699478161510570509662971881309371014080806920343);
    assert_norm (K.g_x * pow2 256 % K.prime == 69433378337113668455105412783699478161510570509662971881309371014080806920343);
    assert_norm (69433378337113668455105412783699478161510570509662971881309371014080806920343 < pow2 256);
    lit_limbs gxm_list (K.g_x * pow2 256 % K.prime);
    G.mk_static_array gxm_list

(** The base point's [y], in Montgomery form. *)
let gym_list : list S64.t = [
  S64.classify 44002uL; S64.classify 54235uL; S64.classify 42706uL; S64.classify 45406uL;
  S64.classify 50765uL; S64.classify 7965uL; S64.classify 23901uL; S64.classify 36348uL;
  S64.classify 49462uL; S64.classify 44057uL; S64.classify 46490uL; S64.classify 28854uL;
  S64.classify 33494uL; S64.classify 54437uL; S64.classify 34079uL; S64.classify 53055uL
]

let gym_arr : (a: G.static_array S64.t
                  { vals (G.static_array_elems a) == limbs (K.g_y * pow2 256 % K.prime) })
  = assert_norm (L.length gym_list == nl);
    assert_norm (lbnd gym_list);
    assert_norm (leval gym_list == 93740989812233943577428291822008373258935927472951925563046116858250011585506);
    assert_norm (K.g_y * pow2 256 % K.prime == 93740989812233943577428291822008373258935927472951925563046116858250011585506);
    assert_norm (93740989812233943577428291822008373258935927472951925563046116858250011585506 < pow2 256);
    lit_limbs gym_list (K.g_y * pow2 256 % K.prime);
    G.mk_static_array gym_list


(** {2 Reading a table}

    Each is sixteen limbs, and the permission never comes back: these are
    [static const] arrays in the emitted C. *)

inline_for_extraction
fn finv_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs (K.prime - 2))
{ table finv_e_arr 16sz }

inline_for_extraction
fn fsqrt_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs ((K.prime + 1) / 4))
{ table fsqrt_e_arr 16sz }

inline_for_extraction
fn qinv_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs (K.order - 2))
{ table qinv_e_arr 16sz }

inline_for_extraction
fn mone () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == limbs 1)
{ table one_arr 16sz }

inline_for_extraction
fn fms () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.ms)
{ table fms_arr 16sz }

inline_for_extraction
fn fnm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.nm)
{ table fnm_arr 16sz }

inline_for_extraction
fn fr1 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.r1)
{ table fr1_arr 16sz }

inline_for_extraction
fn fr2 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.r2)
{ table fr2_arr 16sz }

inline_for_extraction
fn qms () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.ms)
{ table qms_arr 16sz }

inline_for_extraction
fn qnm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.nm)
{ table qnm_arr 16sz }

inline_for_extraction
fn qr1 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.r1)
{ table qr1_arr 16sz }

inline_for_extraction
fn qr2 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.r2)
{ table qr2_arr 16sz }

inline_for_extraction
fn qhalf () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == limbs K.q_half)
{ table qhalf_arr 16sz }

(** The Montgomery constants; neither of K-256's moduli has one as
    convenient as P-256's prime. *)

inline_for_extraction
let fmu : (w: S64.t { S64.v w == fmod.mu }) = S64.classify 13617uL

inline_for_extraction
let qmu : (w: S64.t { S64.v w == qmod.mu }) = S64.classify 45375uL

#pop-options
#pop-options
