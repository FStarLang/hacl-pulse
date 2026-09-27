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

(** The fixed-base window's extra base points, as limbs.

    [2^64 G], [2^128 G] and [2^192 G] for secp256k1, affine, radix 52.
    They live in a module of their own rather than beside the generator in
    {!Hacl.K256.Tables52} because six two-hundred-and-fifty-six-bit
    literals sharing one solver context with the ones already there is
    enough to make the whole file stop terminating; the numbers themselves
    are settled by the normaliser, but they are still in scope for every
    query the file asks afterwards. *)
module Hacl.K256.Tables52G

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
module KB = Spec.K256.Base
module KB = Spec.K256.Base
module U64 = FStar.UInt64

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 The fixed-base window's extra base points}

    [2^64 G], [2^128 G] and [2^192 G], affine, from {!Spec.K256.Base}. *)

let q1x_list : list S64.t = [
  S64.classify 2217608700028605uL; S64.classify 1756680109240635uL;
  S64.classify 85138263733457uL; S64.classify 1374768198666177uL;
  S64.classify 56224678749244uL
]

let q1x_arr : (a: G.static_array S64.t
                   { Seq.length (G.static_array_elems a) == nl /\
                     vals (G.static_array_elems a) == limbs_of KB.q1x })
  = assert_norm (L.length q1x_list == nl);
    assert_norm (lbnd q1x_list);
    assert_norm (leval q1x_list ==
      23129491278950567785970148376500648032717531886785241126168611397589814798013);
    assert_norm (KB.q1x ==
      23129491278950567785970148376500648032717531886785241126168611397589814798013);
    assert_norm (
      23129491278950567785970148376500648032717531886785241126168611397589814798013
        < pow2 256);
    lit_limbs q1x_list KB.q1x;
    G.mk_static_array q1x_list

let q1y_list : list S64.t = [
  S64.classify 1023548355818144uL; S64.classify 1101884390597199uL;
  S64.classify 3899940751803894uL; S64.classify 1389078239091652uL;
  S64.classify 95550264830310uL
]

let q1y_arr : (a: G.static_array S64.t
                   { Seq.length (G.static_array_elems a) == nl /\
                     vals (G.static_array_elems a) == limbs_of KB.q1y })
  = assert_norm (L.length q1y_list == nl);
    assert_norm (lbnd q1y_list);
    assert_norm (leval q1y_list ==
      39307099057880941662675806615359097347682728603444928455093651353540932186784);
    assert_norm (KB.q1y ==
      39307099057880941662675806615359097347682728603444928455093651353540932186784);
    assert_norm (
      39307099057880941662675806615359097347682728603444928455093651353540932186784
        < pow2 256);
    lit_limbs q1y_list KB.q1y;
    G.mk_static_array q1y_list

let q2x_list : list S64.t = [
  S64.classify 3171320615715034uL; S64.classify 2118913159811511uL;
  S64.classify 2285979950419030uL; S64.classify 1674801619671769uL;
  S64.classify 157679956981307uL
]

let q2x_arr : (a: G.static_array S64.t
                   { Seq.length (G.static_array_elems a) == nl /\
                     vals (G.static_array_elems a) == limbs_of KB.q2x })
  = assert_norm (L.length q2x_list == nl);
    assert_norm (lbnd q2x_list);
    assert_norm (leval q2x_list ==
      64865771952738249789114440545196421582918768733599534045195125031385885360346);
    assert_norm (KB.q2x ==
      64865771952738249789114440545196421582918768733599534045195125031385885360346);
    assert_norm (
      64865771952738249789114440545196421582918768733599534045195125031385885360346
        < pow2 256);
    lit_limbs q2x_list KB.q2x;
    G.mk_static_array q2x_list

let q2y_list : list S64.t = [
  S64.classify 3588227476750210uL; S64.classify 4478676213161763uL;
  S64.classify 1897900376058412uL; S64.classify 1012022638087211uL;
  S64.classify 112333245233670uL
]

let q2y_arr : (a: G.static_array S64.t
                   { Seq.length (G.static_array_elems a) == nl /\
                     vals (G.static_array_elems a) == limbs_of KB.q2y })
  = assert_norm (L.length q2y_list == nl);
    assert_norm (lbnd q2y_list);
    assert_norm (leval q2y_list ==
      46211216742671250426576585530459394900178019437443360579906162037052661563266);
    assert_norm (KB.q2y ==
      46211216742671250426576585530459394900178019437443360579906162037052661563266);
    assert_norm (
      46211216742671250426576585530459394900178019437443360579906162037052661563266
        < pow2 256);
    lit_limbs q2y_list KB.q2y;
    G.mk_static_array q2y_list

let q3x_list : list S64.t = [
  S64.classify 3194056064688819uL; S64.classify 3632737019406323uL;
  S64.classify 3631571504093437uL; S64.classify 3337767193194036uL;
  S64.classify 257999926075217uL
]

let q3x_arr : (a: G.static_array S64.t
                   { Seq.length (G.static_array_elems a) == nl /\
                     vals (G.static_array_elems a) == limbs_of KB.q3x })
  = assert_norm (L.length q3x_list == nl);
    assert_norm (lbnd q3x_list);
    assert_norm (leval q3x_list ==
      106135013536326263233204638779771538367307463662639765758785315935371743257267);
    assert_norm (KB.q3x ==
      106135013536326263233204638779771538367307463662639765758785315935371743257267);
    assert_norm (
      106135013536326263233204638779771538367307463662639765758785315935371743257267
        < pow2 256);
    lit_limbs q3x_list KB.q3x;
    G.mk_static_array q3x_list

let q3y_list : list S64.t = [
  S64.classify 2906033833564477uL; S64.classify 1793389228301639uL;
  S64.classify 2385572375144121uL; S64.classify 3100263785697161uL;
  S64.classify 209124003240891uL
]

let q3y_arr : (a: G.static_array S64.t
                   { Seq.length (G.static_array_elems a) == nl /\
                     vals (G.static_array_elems a) == limbs_of KB.q3y })
  = assert_norm (L.length q3y_list == nl);
    assert_norm (lbnd q3y_list);
    assert_norm (leval q3y_list ==
      86028625094535483850261571256264386723357163272666519397289099603747119225149);
    assert_norm (KB.q3y ==
      86028625094535483850261571256264386723357163272666519397289099603747119225149);
    assert_norm (
      86028625094535483850261571256264386723357163272666519397289099603747119225149
        < pow2 256);
    lit_limbs q3y_list KB.q3y;
    G.mk_static_array q3y_list

#pop-options
