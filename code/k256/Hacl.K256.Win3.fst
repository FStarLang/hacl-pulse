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

(** The fixed-base window's fourth table, compiled in.

    Sixteen multiples of [2^192 G], three arrays of eighty limbs, laid
    out the way {!Hacl.K256.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.K256.Win3} says what the sixteen
    points are and {!Hacl.K256.WinTable} turns a list of limbs into one of
    them, so what is left here is sixteen entries of three [assert_norm]s
    each, every one of them arithmetic on a literal list that the
    normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried two hundred and forty fifty-two-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.K256.Win3

open Spec.Bignum52
open Spec.K256.Freeze
open Hacl.Impl.Limb4
open Hacl.Impl.Lit52
open Hacl.K256.PointWin
open Hacl.K256.WinTable

module Seq = FStar.Seq
module L = FStar.List.Tot
module G = Pulse.Lib.GlobalArray
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module W = Spec.K256.Win3

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The three arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0xb58fa2120e2b3uL; S64.classify 0xce7f47f9aa7f3uL; S64.classify 0xce6e5217a58fduL; S64.classify 0xbdbae7be4ae34uL; S64.classify 0xeaa649f21f51uL;
  S64.classify 0xbc1cc1fc9b0a8uL; S64.classify 0x5c705f3db453duL; S64.classify 0x2279ea9e337buL; S64.classify 0x97eec2623ea50uL; S64.classify 0x3adb9db3beb9uL;
  S64.classify 0x3fd3a3f2e070duL; S64.classify 0x1cc52a6a98f58uL; S64.classify 0x85047e229aab7uL; S64.classify 0x4abff48731c3buL; S64.classify 0x4b72a5e9042fuL;
  S64.classify 0xe9e0c90ae86f9uL; S64.classify 0x56963e7caf054uL; S64.classify 0x6c5fc69fefdffuL; S64.classify 0x9cbb7e10955e5uL; S64.classify 0x129e53ac428euL;
  S64.classify 0xe7fd84a02591cuL; S64.classify 0x96585125a1e9cuL; S64.classify 0x5e1fd613ef549uL; S64.classify 0xc8e285a6bfbebuL; S64.classify 0xa9fc93fc6539uL;
  S64.classify 0x700a0f85912ecuL; S64.classify 0x4e4609113428uL; S64.classify 0xaaf054327f9cauL; S64.classify 0x5b786ab499694uL; S64.classify 0xaa7121d4e3fbuL;
  S64.classify 0x6e0e2d968b59uL; S64.classify 0xae13cbbc2e110uL; S64.classify 0x9b027709a28buL; S64.classify 0x9f0a6a7d7ac12uL; S64.classify 0xc940017c1a6fuL;
  S64.classify 0x243d5e855b8dauL; S64.classify 0x7d12894711922uL; S64.classify 0xee10956c75626uL; S64.classify 0x94485b85ecb6auL; S64.classify 0x60144494c8f6uL;
  S64.classify 0x73335726b3332uL; S64.classify 0xd073ee5de6a28uL; S64.classify 0x70bf8e0310388uL; S64.classify 0x24ec6793a5fuL; S64.classify 0x1f84bb9d7eeduL;
  S64.classify 0x95979b1972bcbuL; S64.classify 0x3e241ecceb9dduL; S64.classify 0xeda1776c2f22euL; S64.classify 0x9f028f68e0213uL; S64.classify 0x3df2d057c8bbuL;
  S64.classify 0xaa54acdefa98euL; S64.classify 0x6811ac27995cduL; S64.classify 0x991e9c7724844uL; S64.classify 0xfcd06ca8157b3uL; S64.classify 0xf13e0890945uL;
  S64.classify 0x6a24ffd292dcuL; S64.classify 0x80b17714ce1b8uL; S64.classify 0x7bd79d9775e26uL; S64.classify 0xf934ba48070d3uL; S64.classify 0x4b9915533720uL;
  S64.classify 0x1c03be9f59b6buL; S64.classify 0x63c1888e2fa5euL; S64.classify 0xd5826d3e9b38cuL; S64.classify 0xec7db3728a1d2uL; S64.classify 0xdde191a551dduL;
  S64.classify 0xd1b3423b43eebuL; S64.classify 0x1bf81184feeeuL; S64.classify 0xf359c5c181c94uL; S64.classify 0x5e937ea4825ffuL; S64.classify 0x83c403979eb9uL;
  S64.classify 0xc55fdc9c6b699uL; S64.classify 0x356be46871b68uL; S64.classify 0x7b41682a86f57uL; S64.classify 0x6f7a5a16d7bf9uL; S64.classify 0x5fab012eed83uL
]
[@@"opaque_to_smt"; FStar.Custard.no_specialize]
let tx_seq : Seq.seq S64.t = Seq.seq_of_list tx_list

let tx_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == tx_seq /\
                     Seq.length (G.static_array_elems a) == 80 })
  = reveal_opaque (`%tx_seq) tx_seq;
    assert_norm (L.length tx_list == 80);
    G.mk_static_array tx_list

(** The [y] coordinates. *)
let ty_list : list S64.t = [
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0xa5305ba5ad93duL; S64.classify 0x65f13f7e59d47uL; S64.classify 0x879aa5a01a6b9uL; S64.classify 0xb03ac69a80f89uL; S64.classify 0xbe3279ed5bbbuL;
  S64.classify 0xe7975f05bbddauL; S64.classify 0xf9870266cc61auL; S64.classify 0xc095ff6aad9c8uL; S64.classify 0x4e713c774de07uL; S64.classify 0x374e2d6daee7uL;
  S64.classify 0xba82ee96dd780uL; S64.classify 0xddd2948c3de44uL; S64.classify 0xd0f3c10b0b465uL; S64.classify 0xe1cf60277bb36uL; S64.classify 0x599e1d4e1d6auL;
  S64.classify 0xefdcd1e89c85duL; S64.classify 0xfd16b3e01b822uL; S64.classify 0x712183fb2a232uL; S64.classify 0x9a29b2da2115buL; S64.classify 0x415ecb958aeeuL;
  S64.classify 0xaddef69bec2dcuL; S64.classify 0x415fcf7253790uL; S64.classify 0xa9165e5ca888cuL; S64.classify 0x87173e84c17a1uL; S64.classify 0x9c2ce739dc53uL;
  S64.classify 0x4cb264ae35978uL; S64.classify 0xa8ce056cbdb11uL; S64.classify 0x6a2edebfee134uL; S64.classify 0x9509c505266b9uL; S64.classify 0xc690f077dad0uL;
  S64.classify 0xd76408de572fbuL; S64.classify 0xb64390c9c8fefuL; S64.classify 0x5b5742ce2842cuL; S64.classify 0x862013b8a1bfauL; S64.classify 0x39d922500c9buL;
  S64.classify 0x590f34e4bbduL; S64.classify 0xc27e3f2a4bad5uL; S64.classify 0x132e65b543955uL; S64.classify 0xe6469e8be1fd9uL; S64.classify 0x8bb5d669f681uL;
  S64.classify 0x428a314e8d52euL; S64.classify 0x2d436dc3a2554uL; S64.classify 0x5b9edf0c2bcceuL; S64.classify 0x9ecc2547c27f7uL; S64.classify 0xee726d072bcauL;
  S64.classify 0x22cd3d65d09dfuL; S64.classify 0x9680194771b28uL; S64.classify 0x46a684b1b9144uL; S64.classify 0x6eead6e6b23b0uL; S64.classify 0xdc7eb1c640c8uL;
  S64.classify 0xa7769be286767uL; S64.classify 0x5e16ceaccdc08uL; S64.classify 0x7b362db287e70uL; S64.classify 0x7c5035e3f8b0auL; S64.classify 0xadd521f1764euL;
  S64.classify 0xa5ffe57095ca6uL; S64.classify 0xc45b376afd433uL; S64.classify 0x5f01f57938323uL; S64.classify 0x3a226dfc0a74buL; S64.classify 0xe32775496110uL;
  S64.classify 0xd962926cb1410uL; S64.classify 0xbbe7154fecf6auL; S64.classify 0xc52e14e8b5738uL; S64.classify 0x75cbe0a757d61uL; S64.classify 0x5b2bfb780282uL;
  S64.classify 0x34086d484fb51uL; S64.classify 0xcab553fb40affuL; S64.classify 0xd61b295b6bfuL; S64.classify 0xee3d0bfc1e46duL; S64.classify 0x29575ff2437cuL;
  S64.classify 0x32152c1c6c3aauL; S64.classify 0x7fea883519b17uL; S64.classify 0xd62f7b90ab11uL; S64.classify 0xd144e9ebb4113uL; S64.classify 0x2d9bfa70a3c3uL
]
[@@"opaque_to_smt"; FStar.Custard.no_specialize]
let ty_seq : Seq.seq S64.t = Seq.seq_of_list ty_list

let ty_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == ty_seq /\
                     Seq.length (G.static_array_elems a) == 80 })
  = reveal_opaque (`%ty_seq) ty_seq;
    assert_norm (L.length ty_list == 80);
    G.mk_static_array ty_list

(** The [z] coordinates, which are all one: the entries are stored affine. *)
let tz_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL
]
[@@"opaque_to_smt"; FStar.Custard.no_specialize]
let tz_seq : Seq.seq S64.t = Seq.seq_of_list tz_list

let tz_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == tz_seq /\
                     Seq.length (G.static_array_elems a) == 80 })
  = reveal_opaque (`%tz_seq) tz_seq;
    assert_norm (L.length tz_list == 80);
    G.mk_static_array tz_list

(** {2 The shape}

    Three lengths, which every entry below needs and none of them should
    reprove. *)

let shape (_: unit)
  : Lemma (L.length tx_list == 80 /\ L.length ty_list == 80 /\
           L.length tz_list == 80)
  = assert_norm (L.length tx_list == 80);
    assert_norm (L.length ty_list == 80);
    assert_norm (L.length tz_list == 80)

(** {2 The sixteen entries} *)

let ent_0 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 0)
  = shape ();
    assert_norm (L.length (chunk tx_list 0) == nl /\
                 lbnd (chunk tx_list 0) /\
                 leval (chunk tx_list 0) == qx W.e0);
    assert_norm (L.length (chunk ty_list 0) == nl /\
                 lbnd (chunk ty_list 0) /\
                 leval (chunk ty_list 0) == qy W.e0);
    assert_norm (L.length (chunk tz_list 0) == nl /\
                 lbnd (chunk tz_list 0) /\
                 leval (chunk tz_list 0) == qz W.e0);
    W.e0_ok ();
    ent_lit tx_list ty_list tz_list 0 K.g W.n W.e0

let ent_1 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 1)
  = shape ();
    assert_norm (L.length (chunk tx_list 1) == nl /\
                 lbnd (chunk tx_list 1) /\
                 leval (chunk tx_list 1) == qx W.e1);
    assert_norm (L.length (chunk ty_list 1) == nl /\
                 lbnd (chunk ty_list 1) /\
                 leval (chunk ty_list 1) == qy W.e1);
    assert_norm (L.length (chunk tz_list 1) == nl /\
                 lbnd (chunk tz_list 1) /\
                 leval (chunk tz_list 1) == qz W.e1);
    W.e1_ok ();
    ent_lit tx_list ty_list tz_list 1 K.g W.n W.e1

let ent_2 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 2)
  = shape ();
    assert_norm (L.length (chunk tx_list 2) == nl /\
                 lbnd (chunk tx_list 2) /\
                 leval (chunk tx_list 2) == qx W.e2);
    assert_norm (L.length (chunk ty_list 2) == nl /\
                 lbnd (chunk ty_list 2) /\
                 leval (chunk ty_list 2) == qy W.e2);
    assert_norm (L.length (chunk tz_list 2) == nl /\
                 lbnd (chunk tz_list 2) /\
                 leval (chunk tz_list 2) == qz W.e2);
    W.e2_ok ();
    ent_lit tx_list ty_list tz_list 2 K.g W.n W.e2

let ent_3 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 3)
  = shape ();
    assert_norm (L.length (chunk tx_list 3) == nl /\
                 lbnd (chunk tx_list 3) /\
                 leval (chunk tx_list 3) == qx W.e3);
    assert_norm (L.length (chunk ty_list 3) == nl /\
                 lbnd (chunk ty_list 3) /\
                 leval (chunk ty_list 3) == qy W.e3);
    assert_norm (L.length (chunk tz_list 3) == nl /\
                 lbnd (chunk tz_list 3) /\
                 leval (chunk tz_list 3) == qz W.e3);
    W.e3_ok ();
    ent_lit tx_list ty_list tz_list 3 K.g W.n W.e3

let ent_4 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 4)
  = shape ();
    assert_norm (L.length (chunk tx_list 4) == nl /\
                 lbnd (chunk tx_list 4) /\
                 leval (chunk tx_list 4) == qx W.e4);
    assert_norm (L.length (chunk ty_list 4) == nl /\
                 lbnd (chunk ty_list 4) /\
                 leval (chunk ty_list 4) == qy W.e4);
    assert_norm (L.length (chunk tz_list 4) == nl /\
                 lbnd (chunk tz_list 4) /\
                 leval (chunk tz_list 4) == qz W.e4);
    W.e4_ok ();
    ent_lit tx_list ty_list tz_list 4 K.g W.n W.e4

let ent_5 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 5)
  = shape ();
    assert_norm (L.length (chunk tx_list 5) == nl /\
                 lbnd (chunk tx_list 5) /\
                 leval (chunk tx_list 5) == qx W.e5);
    assert_norm (L.length (chunk ty_list 5) == nl /\
                 lbnd (chunk ty_list 5) /\
                 leval (chunk ty_list 5) == qy W.e5);
    assert_norm (L.length (chunk tz_list 5) == nl /\
                 lbnd (chunk tz_list 5) /\
                 leval (chunk tz_list 5) == qz W.e5);
    W.e5_ok ();
    ent_lit tx_list ty_list tz_list 5 K.g W.n W.e5

let ent_6 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 6)
  = shape ();
    assert_norm (L.length (chunk tx_list 6) == nl /\
                 lbnd (chunk tx_list 6) /\
                 leval (chunk tx_list 6) == qx W.e6);
    assert_norm (L.length (chunk ty_list 6) == nl /\
                 lbnd (chunk ty_list 6) /\
                 leval (chunk ty_list 6) == qy W.e6);
    assert_norm (L.length (chunk tz_list 6) == nl /\
                 lbnd (chunk tz_list 6) /\
                 leval (chunk tz_list 6) == qz W.e6);
    W.e6_ok ();
    ent_lit tx_list ty_list tz_list 6 K.g W.n W.e6

let ent_7 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 7)
  = shape ();
    assert_norm (L.length (chunk tx_list 7) == nl /\
                 lbnd (chunk tx_list 7) /\
                 leval (chunk tx_list 7) == qx W.e7);
    assert_norm (L.length (chunk ty_list 7) == nl /\
                 lbnd (chunk ty_list 7) /\
                 leval (chunk ty_list 7) == qy W.e7);
    assert_norm (L.length (chunk tz_list 7) == nl /\
                 lbnd (chunk tz_list 7) /\
                 leval (chunk tz_list 7) == qz W.e7);
    W.e7_ok ();
    ent_lit tx_list ty_list tz_list 7 K.g W.n W.e7

let ent_8 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 8)
  = shape ();
    assert_norm (L.length (chunk tx_list 8) == nl /\
                 lbnd (chunk tx_list 8) /\
                 leval (chunk tx_list 8) == qx W.e8);
    assert_norm (L.length (chunk ty_list 8) == nl /\
                 lbnd (chunk ty_list 8) /\
                 leval (chunk ty_list 8) == qy W.e8);
    assert_norm (L.length (chunk tz_list 8) == nl /\
                 lbnd (chunk tz_list 8) /\
                 leval (chunk tz_list 8) == qz W.e8);
    W.e8_ok ();
    ent_lit tx_list ty_list tz_list 8 K.g W.n W.e8

let ent_9 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 9)
  = shape ();
    assert_norm (L.length (chunk tx_list 9) == nl /\
                 lbnd (chunk tx_list 9) /\
                 leval (chunk tx_list 9) == qx W.e9);
    assert_norm (L.length (chunk ty_list 9) == nl /\
                 lbnd (chunk ty_list 9) /\
                 leval (chunk ty_list 9) == qy W.e9);
    assert_norm (L.length (chunk tz_list 9) == nl /\
                 lbnd (chunk tz_list 9) /\
                 leval (chunk tz_list 9) == qz W.e9);
    W.e9_ok ();
    ent_lit tx_list ty_list tz_list 9 K.g W.n W.e9

let ent_10 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 10)
  = shape ();
    assert_norm (L.length (chunk tx_list 10) == nl /\
                 lbnd (chunk tx_list 10) /\
                 leval (chunk tx_list 10) == qx W.e10);
    assert_norm (L.length (chunk ty_list 10) == nl /\
                 lbnd (chunk ty_list 10) /\
                 leval (chunk ty_list 10) == qy W.e10);
    assert_norm (L.length (chunk tz_list 10) == nl /\
                 lbnd (chunk tz_list 10) /\
                 leval (chunk tz_list 10) == qz W.e10);
    W.e10_ok ();
    ent_lit tx_list ty_list tz_list 10 K.g W.n W.e10

let ent_11 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 11)
  = shape ();
    assert_norm (L.length (chunk tx_list 11) == nl /\
                 lbnd (chunk tx_list 11) /\
                 leval (chunk tx_list 11) == qx W.e11);
    assert_norm (L.length (chunk ty_list 11) == nl /\
                 lbnd (chunk ty_list 11) /\
                 leval (chunk ty_list 11) == qy W.e11);
    assert_norm (L.length (chunk tz_list 11) == nl /\
                 lbnd (chunk tz_list 11) /\
                 leval (chunk tz_list 11) == qz W.e11);
    W.e11_ok ();
    ent_lit tx_list ty_list tz_list 11 K.g W.n W.e11

let ent_12 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 12)
  = shape ();
    assert_norm (L.length (chunk tx_list 12) == nl /\
                 lbnd (chunk tx_list 12) /\
                 leval (chunk tx_list 12) == qx W.e12);
    assert_norm (L.length (chunk ty_list 12) == nl /\
                 lbnd (chunk ty_list 12) /\
                 leval (chunk ty_list 12) == qy W.e12);
    assert_norm (L.length (chunk tz_list 12) == nl /\
                 lbnd (chunk tz_list 12) /\
                 leval (chunk tz_list 12) == qz W.e12);
    W.e12_ok ();
    ent_lit tx_list ty_list tz_list 12 K.g W.n W.e12

let ent_13 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 13)
  = shape ();
    assert_norm (L.length (chunk tx_list 13) == nl /\
                 lbnd (chunk tx_list 13) /\
                 leval (chunk tx_list 13) == qx W.e13);
    assert_norm (L.length (chunk ty_list 13) == nl /\
                 lbnd (chunk ty_list 13) /\
                 leval (chunk ty_list 13) == qy W.e13);
    assert_norm (L.length (chunk tz_list 13) == nl /\
                 lbnd (chunk tz_list 13) /\
                 leval (chunk tz_list 13) == qz W.e13);
    W.e13_ok ();
    ent_lit tx_list ty_list tz_list 13 K.g W.n W.e13

let ent_14 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 14)
  = shape ();
    assert_norm (L.length (chunk tx_list 14) == nl /\
                 lbnd (chunk tx_list 14) /\
                 leval (chunk tx_list 14) == qx W.e14);
    assert_norm (L.length (chunk ty_list 14) == nl /\
                 lbnd (chunk ty_list 14) /\
                 leval (chunk ty_list 14) == qy W.e14);
    assert_norm (L.length (chunk tz_list 14) == nl /\
                 lbnd (chunk tz_list 14) /\
                 leval (chunk tz_list 14) == qz W.e14);
    W.e14_ok ();
    ent_lit tx_list ty_list tz_list 14 K.g W.n W.e14

let ent_15 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) K.g W.n 15)
  = shape ();
    assert_norm (L.length (chunk tx_list 15) == nl /\
                 lbnd (chunk tx_list 15) /\
                 leval (chunk tx_list 15) == qx W.e15);
    assert_norm (L.length (chunk ty_list 15) == nl /\
                 lbnd (chunk ty_list 15) /\
                 leval (chunk ty_list 15) == qy W.e15);
    assert_norm (L.length (chunk tz_list 15) == nl /\
                 lbnd (chunk tz_list 15) /\
                 leval (chunk tz_list 15) == qz W.e15);
    W.e15_ok ();
    ent_lit tx_list ty_list tz_list 15 K.g W.n W.e15

(** {2 The table}

    What {!Hacl.K256.PointMulG} asks for. *)

let reveal_seqs (_: unit)
  : Lemma (tx_seq == Seq.seq_of_list tx_list /\
           ty_seq == Seq.seq_of_list ty_list /\
           tz_seq == Seq.seq_of_list tz_list)
  = reveal_opaque (`%tx_seq) tx_seq;
    reveal_opaque (`%ty_seq) ty_seq;
    reveal_opaque (`%tz_seq) tz_seq

let tbl_ok (_: unit)
  : Lemma (tok tx_seq ty_seq tz_seq K.g (pow2 192) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) K.g W.n

#pop-options
