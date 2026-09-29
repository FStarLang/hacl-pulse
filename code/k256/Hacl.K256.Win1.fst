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

(** The fixed-base window's second table, compiled in.

    Sixteen multiples of [2^64 G], three arrays of eighty limbs, laid
    out the way {!Hacl.K256.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.K256.Win1} says what the sixteen
    points are and {!Hacl.K256.WinTable} turns a list of limbs into one of
    them, so what is left here is sixteen entries of three [assert_norm]s
    each, every one of them arithmetic on a literal list that the
    normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried two hundred and forty fifty-two-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.K256.Win1

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
module W = Spec.K256.Win1

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The three arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x7e0e742d0e6bduL; S64.classify 0x63db0f5e5313buL; S64.classify 0x4d6ecbf774d1uL; S64.classify 0x4e2582a2147c1uL; S64.classify 0x3322d401243cuL;
  S64.classify 0x96d32c0ade462uL; S64.classify 0xc8eadbcf29fc6uL; S64.classify 0x4c80cd50d4cdduL; S64.classify 0xbdae120ef31b0uL; S64.classify 0x8d26200250ceuL;
  S64.classify 0x9d3f2059ab499uL; S64.classify 0x9c6e73c330abduL; S64.classify 0x67f01bc0b1329uL; S64.classify 0x5ba5d2196b3cuL; S64.classify 0x78baaff3015cuL;
  S64.classify 0x4643e1516e633uL; S64.classify 0xd072d9c8b916uL; S64.classify 0x594d03b8ed493uL; S64.classify 0xbea9ce4068a1fuL; S64.classify 0x1238c0766eaeuL;
  S64.classify 0x3e16cfd06ace6uL; S64.classify 0x36f83a20ca449uL; S64.classify 0x929ab1a23709buL; S64.classify 0xe3d4c20b84984uL; S64.classify 0x6f70f211a14auL;
  S64.classify 0x63330a5cd5379uL; S64.classify 0x385870bcadc30uL; S64.classify 0xaa4d2232db794uL; S64.classify 0x1382a782481b8uL; S64.classify 0x17c072d56bdduL;
  S64.classify 0xee3ee60ee1b40uL; S64.classify 0x5b71e96247dc8uL; S64.classify 0x103ccd48ced48uL; S64.classify 0xa415f80949f19uL; S64.classify 0xe1599db29d6auL;
  S64.classify 0x1552788e7a66uL; S64.classify 0x282b0ec21619buL; S64.classify 0xa6a11b9cddcd7uL; S64.classify 0x9c15e7b2ea758uL; S64.classify 0x271d5b0770cbuL;
  S64.classify 0xdfa2849c00c3euL; S64.classify 0x3c91208e2f81uL; S64.classify 0xd451859f00e8fuL; S64.classify 0x6956436562d33uL; S64.classify 0xbb0b04970440uL;
  S64.classify 0xe87d8a8a923b7uL; S64.classify 0xeed81c5b30da1uL; S64.classify 0x8338266aef650uL; S64.classify 0x9a70540708ab6uL; S64.classify 0xac2acb9b2199uL;
  S64.classify 0x75b9c05dd32e6uL; S64.classify 0x51b53e5ee7e0euL; S64.classify 0x75a5fbfc663b5uL; S64.classify 0x789e9b649dbe0uL; S64.classify 0xdc5a41554195uL;
  S64.classify 0x3c018ca2d8daeuL; S64.classify 0xf91fd25ea9579uL; S64.classify 0xcb2256eac32a5uL; S64.classify 0x92f9ba6b25ef9uL; S64.classify 0x88271c026211uL;
  S64.classify 0x45bac4544e7cbuL; S64.classify 0x25b52960359eduL; S64.classify 0x1014e99a10642uL; S64.classify 0x3b9dbe3354a57uL; S64.classify 0x156e19703987uL;
  S64.classify 0xbadc99c89240fuL; S64.classify 0xbafa2e7b858f5uL; S64.classify 0x7e0e17674f8c4uL; S64.classify 0x7338e18ee0919uL; S64.classify 0x15b8390d652duL;
  S64.classify 0xbc29cc59853cauL; S64.classify 0x6b9f19bf54dbfuL; S64.classify 0x8e7161348e962uL; S64.classify 0x43826bca76a22uL; S64.classify 0x4269bccecb68uL
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
  S64.classify 0x3a2e96c28b2a0uL; S64.classify 0x3ea2873af624fuL; S64.classify 0xddaf9b72805f6uL; S64.classify 0x4ef5bfb019bc4uL; S64.classify 0x56e70797e966uL;
  S64.classify 0xa8b90f26470cuL; S64.classify 0x4e72678b3ad8euL; S64.classify 0x3ee36ba1d4afbuL; S64.classify 0xf437d31f6f2dcuL; S64.classify 0xebed3bb4715buL;
  S64.classify 0xd2318fee097fduL; S64.classify 0xee8d125199681uL; S64.classify 0xd82082e91632euL; S64.classify 0xc0afafca84e0euL; S64.classify 0xad4bdcdbdb06uL;
  S64.classify 0xdb728c77b7805uL; S64.classify 0x2dcc74022805cuL; S64.classify 0x1c3dc17094625uL; S64.classify 0x1359d6c979e2duL; S64.classify 0x8a9db02dbb27uL;
  S64.classify 0xbed34b602d5deuL; S64.classify 0x66be5ac5ee048uL; S64.classify 0x7b99f50753295uL; S64.classify 0x7b736f95d8f34uL; S64.classify 0x791e8a309402uL;
  S64.classify 0xae051b108cd25uL; S64.classify 0x76265bad0df7cuL; S64.classify 0xf1d034f8959acuL; S64.classify 0xa064e77c1247auL; S64.classify 0xd901bdf4283duL;
  S64.classify 0x6265ed78f93a6uL; S64.classify 0x74bc32999de1duL; S64.classify 0xa2fc7cfa6363auL; S64.classify 0xd4a0efaf894aauL; S64.classify 0x793362232a81uL;
  S64.classify 0xd7258e03c9727uL; S64.classify 0xe3508a824e7a8uL; S64.classify 0x9ac877fe2a065uL; S64.classify 0xf491e457d0994uL; S64.classify 0x5d3aa45834e7uL;
  S64.classify 0xa982d11955a35uL; S64.classify 0x4e905dc90a799uL; S64.classify 0xab1b052fe6704uL; S64.classify 0x9f63655d2fa17uL; S64.classify 0x4067e45853afuL;
  S64.classify 0xc124ad7cd20a6uL; S64.classify 0xbf12d27a4fa2duL; S64.classify 0x13d9eb360b0d0uL; S64.classify 0x724d1c9afa0dfuL; S64.classify 0x7684428511c1uL;
  S64.classify 0x7db7a754a99b9uL; S64.classify 0x9076e49bcf80euL; S64.classify 0x1bf59442ff2eeuL; S64.classify 0x67a76dcea5e20uL; S64.classify 0x4af3a8a63f9fuL;
  S64.classify 0x26c0f3e1e77d9uL; S64.classify 0x6dc717d099fb4uL; S64.classify 0x5abf5acc30087uL; S64.classify 0x76aa401c8b3aeuL; S64.classify 0xd719dd535071uL;
  S64.classify 0x392c0ad250a37uL; S64.classify 0x8d5eb439cd6d5uL; S64.classify 0x3834be89496d5uL; S64.classify 0x907da939572a6uL; S64.classify 0x6bc08d9f8f31uL;
  S64.classify 0xf9ef8e326f04auL; S64.classify 0xab5c1a33352e2uL; S64.classify 0x7a59f99b30367uL; S64.classify 0x8d083abdd7cccuL; S64.classify 0x786cf20c8efeuL;
  S64.classify 0x58ef535b8d367uL; S64.classify 0xa5f9e5a8a3da9uL; S64.classify 0x431a409fd3940uL; S64.classify 0x16b723c84ca9cuL; S64.classify 0xed2b1c1a82c0uL
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
  : Lemma (tok tx_seq ty_seq tz_seq K.g (pow2 64) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) K.g W.n

#pop-options
