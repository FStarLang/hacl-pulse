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

    Eight tables of four limbs -- for each of the two moduli, the modulus
    itself, its two's complement, and the two Montgomery radix constants --
    three exponents, and the curve constants in Montgomery form.  They are
    the only place in the implementation where secp256k1's actual numbers
    appear.

    {!Hacl.Impl.Lit4} explains why each one goes through its value rather
    than through its eight indices. *)
module Hacl.K256.Tables

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.K256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Lit4
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

(** The field prime, as four limbs. *)
(** [2^256] less the field prime: subtraction without borrows. *)
let fnm_list : list S64.t = [
  S64.classify 4294968273uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL
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
(** [R^2 mod p] -- the Montgomery form of [R]. *)
(** The group order, as four limbs. *)
let qms_list : list S64.t = [
  S64.classify 13822214165235122497uL; S64.classify 13451932020343611451uL;
  S64.classify 18446744073709551614uL; S64.classify 18446744073709551615uL
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
  S64.classify 4624529908474429119uL; S64.classify 4994812053365940164uL;
  S64.classify 1uL; S64.classify 0uL
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
  S64.classify 4624529908474429119uL; S64.classify 4994812053365940164uL;
  S64.classify 1uL; S64.classify 0uL
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
  S64.classify 9902555850136342848uL; S64.classify 8364476168144746616uL;
  S64.classify 16616019711348246470uL; S64.classify 11342065889886772165uL
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
  S64.classify 1uL; S64.classify 0uL;
  S64.classify 0uL; S64.classify 0uL
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
  S64.classify 16134479119472337056uL; S64.classify 6725966010171805725uL;
  S64.classify 18446744073709551615uL; S64.classify 9223372036854775807uL
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
  18446744069414583341uL; 18446744073709551615uL;
  18446744073709551615uL; 18446744073709551615uL
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
  18446744072635809548uL; 18446744073709551615uL;
  18446744073709551615uL; 4611686018427387903uL
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
  13822214165235122495uL; 13451932020343611451uL;
  18446744073709551614uL; 18446744073709551615uL
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
(** [3b = 21] in Montgomery form, which is what the complete formulas multiply by. *)
(** The base point's [x], in Montgomery form. *)
(** The base point's [y], in Montgomery form. *)
(** {2 Reading a table}

    Each is four limbs, and the permission never comes back: these are
    [static const] arrays in the emitted C. *)

inline_for_extraction
fn finv_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs (K.prime - 2))
{ table finv_e_arr 4sz }

inline_for_extraction
fn fsqrt_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs ((K.prime + 1) / 4))
{ table fsqrt_e_arr 4sz }

inline_for_extraction
fn qinv_e () requires emp returns s: A.array U64.t
ensures exists* (p: perm) (v: Seq.seq U64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ pvals v == limbs (K.order - 2))
{ table qinv_e_arr 4sz }

inline_for_extraction
fn mone () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == limbs 1)
{ table one_arr 4sz }

inline_for_extraction
fn fnm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == fmod.nm)
{ table fnm_arr 4sz }

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

inline_for_extraction
fn qhalf () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == limbs K.q_half)
{ table qhalf_arr 4sz }

(** The Montgomery constants; neither of K-256's moduli has one as
    convenient as P-256's prime. *)

inline_for_extraction
let fmu : (w: S64.t { S64.v w == fmod.mu }) = S64.classify 15580212934572586289uL

inline_for_extraction
let qmu : (w: S64.t { S64.v w == qmod.mu }) = S64.classify 5408259542528602431uL

#pop-options
#pop-options
