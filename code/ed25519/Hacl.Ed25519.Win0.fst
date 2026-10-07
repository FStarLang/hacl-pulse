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

(** The fixed-base window's first table, compiled in.

    Sixteen multiples of the generator, four arrays of eighty limbs, laid out
    the way {!Hacl.Ed25519.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.Ed25519.Win0} says what the sixteen
    points are and {!Hacl.Ed25519.WinTable} turns a list of limbs into one
    of them, so what is left here is sixteen entries of four
    [assert_norm]s each, every one of them arithmetic on a literal list
    that the normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried three hundred and twenty fifty-one-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.Ed25519.Win0

open Hacl.Impl.Limb
open Hacl.Impl.Lit51
open Hacl.Ed25519.PointWin
open Hacl.Ed25519.WinTable

module Seq = FStar.Seq
module L = FStar.List.Tot
module G = Pulse.Lib.GlobalArray
module S64 = Hacl.Secret.UInt64
module F = Spec.Curve25519.Field
module E = Spec.Ed25519
module W = Spec.Ed25519.Win0

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The four arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x62d608f25d51auL; S64.classify 0x412a4b4f6592auL; S64.classify 0x75b7171a4b31duL; S64.classify 0x1ff60527118feuL; S64.classify 0x216936d3cd6e5uL;
  S64.classify 0x5a14e2843ce0euL; S64.classify 0xa2baf48bf078uL; S64.classify 0xcf9eb0203639uL; S64.classify 0x2361e821dbe8cuL; S64.classify 0x36ab384c9f5a0uL;
  S64.classify 0x2485fd3f8e25cuL; S64.classify 0x3302c4910d58cuL; S64.classify 0x36b20e98d0e60uL; S64.classify 0x7a48ffa573a1fuL; S64.classify 0x67ae9c4a22928uL;
  S64.classify 0x2a657c4c9f870uL; S64.classify 0x3279c2a8e927uL; S64.classify 0xd483e469ce7buL; S64.classify 0xa34192ea5c3duL; S64.classify 0x203da8db56cffuL;
  S64.classify 0x9cc0322ef233uL; S64.classify 0x727c37c34b228uL; S64.classify 0x4b6977970a067uL; S64.classify 0x43dfe77be7be8uL; S64.classify 0x49fda73eade35uL;
  S64.classify 0x2741a7dcbf23duL; S64.classify 0x4d8f6884ef07uL; S64.classify 0x428a6fa879666uL; S64.classify 0xe315756606euL; S64.classify 0x4c9797ba7a456uL;
  S64.classify 0x5981af50e4107uL; S64.classify 0x6777e39d2ab0auL; S64.classify 0x476041e0fa027uL; S64.classify 0x6a774f1f70ca5uL; S64.classify 0x14568685fcf4buL;
  S64.classify 0x7fdbc08a584c8uL; S64.classify 0x7700d31732770uL; S64.classify 0x13b3e4faceb19uL; S64.classify 0xdb214316ae7cuL; S64.classify 0x6742e15f97d77uL;
  S64.classify 0x23065185715cuL; S64.classify 0x385c9c0529a7cuL; S64.classify 0x6508ae21b6039uL; S64.classify 0xb28df99b7037uL; S64.classify 0x357cc970c8007uL;
  S64.classify 0x51f224877f94fuL; S64.classify 0x1db06df028892uL; S64.classify 0x2f219dc81fa39uL; S64.classify 0x6baa2385b0769uL; S64.classify 0x602c797e30ca6uL;
  S64.classify 0x7d2c1207cf3cbuL; S64.classify 0x658b27aaa5fe5uL; S64.classify 0x1c490e34e0696uL; S64.classify 0x20bdb6783c6ebuL; S64.classify 0x14e528b1154beuL;
  S64.classify 0x2fe6678f0902duL; S64.classify 0x470b8276855ccuL; S64.classify 0x289276cca56fcuL; S64.classify 0x69aaf67b87006uL; S64.classify 0x4719e17e016e5uL;
  S64.classify 0xe073b7c05feduL; S64.classify 0x511a456f706f0uL; S64.classify 0xb4c13e210f8fuL; S64.classify 0x3666d99d6f814uL; S64.classify 0x107427e0d5f36uL;
  S64.classify 0x67353b58515b9uL; S64.classify 0x307c730655471uL; S64.classify 0x32aec57637b9buL; S64.classify 0x55782463d44aeuL; S64.classify 0x205f3b42f5884uL;
  S64.classify 0x17f3e66a18dc1uL; S64.classify 0x68ee03139720cuL; S64.classify 0x481067b658c4duL; S64.classify 0x21aee2d637caeuL; S64.classify 0x4f162deaec2ecuL
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
  S64.classify 0x6666666666658uL; S64.classify 0x4ccccccccccccuL; S64.classify 0x1999999999999uL; S64.classify 0x3333333333333uL; S64.classify 0x6666666666666uL;
  S64.classify 0x746ae6af8a3c9uL; S64.classify 0x22c870a2ac1cbuL; S64.classify 0x6887d5a5ce43duL; S64.classify 0x4e10ed12f7464uL; S64.classify 0x2260cdf309232uL;
  S64.classify 0x3684878f5b4d4uL; S64.classify 0x2ece480608058uL; S64.classify 0x9a7bde7c5bb0uL; S64.classify 0x4d5d09350c730uL; S64.classify 0x1267b1d177ee6uL;
  S64.classify 0xab61ca32112fuL; S64.classify 0x65d45e1fe1be7uL; S64.classify 0x355c5b133c8a0uL; S64.classify 0x2f0a3875c42c0uL; S64.classify 0x47d0e827cb159uL;
  S64.classify 0x21f83d676c8eduL; S64.classify 0x15128616ba21auL; S64.classify 0x6491998c4a0bbuL; S64.classify 0x737f016370a44uL; S64.classify 0x5f4825b298feauL;
  S64.classify 0x27ad0f9497ef4uL; S64.classify 0xd289ad6c183auL; S64.classify 0x53df5dfe505f0uL; S64.classify 0x4508edb84d3feuL; S64.classify 0x54de3fc2886duL;
  S64.classify 0x4c4b59f4062b8uL; S64.classify 0xdef57e47a258uL; S64.classify 0x4dab507c220aduL; S64.classify 0x297c3e732346euL; S64.classify 0x31c563e32b47duL;
  S64.classify 0x75ba9fc37b9b4uL; S64.classify 0x78c43dc9263c5uL; S64.classify 0x22bce3e05e0f3uL; S64.classify 0x1bcb756b784b3uL; S64.classify 0x21d30600c9e57uL;
  S64.classify 0x644845522f1c0uL; S64.classify 0x2646dc88618e9uL; S64.classify 0x3cb4bf47de240uL; S64.classify 0x6fa595f7e74abuL; S64.classify 0x7f3d23c2c2dd0uL;
  S64.classify 0x74b06ae87b2cuL; S64.classify 0xa7bc1d087751uL; S64.classify 0x262ff3c95da9auL; S64.classify 0x23be47226aa64uL; S64.classify 0x637ffcaa7a1b2uL;
  S64.classify 0x72dc36a033713uL; S64.classify 0x387938b1a8611uL; S64.classify 0x3fc3f38496164uL; S64.classify 0x5cbad37be71a0uL; S64.classify 0x2d9082313f21auL;
  S64.classify 0x281dc2e2de4f9uL; S64.classify 0x68a4e72cce67auL; S64.classify 0x5e096e15921fauL; S64.classify 0x11738eb62731uL; S64.classify 0x4070ce608bce8uL;
  S64.classify 0x7e1aeea401f80uL; S64.classify 0x6451344e470fduL; S64.classify 0x36a26e0dd033euL; S64.classify 0x5ba3c23301169uL; S64.classify 0x12dbb00ded538uL;
  S64.classify 0x1fd98899c2839uL; S64.classify 0x50336c4cb906duL; S64.classify 0x6dc0afe9d2263uL; S64.classify 0x5c08add68bd65uL; S64.classify 0x4e50256f50c4cuL;
  S64.classify 0x54cc4ad2e5cdfuL; S64.classify 0x314335354328duL; S64.classify 0x34a4cc6b396bcuL; S64.classify 0x17aa8b17b80b2uL; S64.classify 0x12cbfb2d04ff2uL
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

(** The [t] coordinates. *)
let tt_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x68ab3a5b7dda3uL; S64.classify 0xeea2a5eadbbuL; S64.classify 0x2af8df483c27euL; S64.classify 0x332b375274732uL; S64.classify 0x67875f0fd78b7uL;
  S64.classify 0x23f556d69b401uL; S64.classify 0x1383ee48056e3uL; S64.classify 0x40ed04d75e6b3uL; S64.classify 0x46e0ef2af8439uL; S64.classify 0x2498a7850b2f6uL;
  S64.classify 0x108fa78b3a41auL; S64.classify 0x17f62df8959bfuL; S64.classify 0x6e4549d709cd6uL; S64.classify 0x28875f79bc1d6uL; S64.classify 0x2a4d025cb1dd9uL;
  S64.classify 0x722f6728a1358uL; S64.classify 0x3d6dba0f94bf1uL; S64.classify 0x1f0a581c6578cuL; S64.classify 0x306390a5d3563uL; S64.classify 0x22783cd8d8732uL;
  S64.classify 0x150bcf3e801d0uL; S64.classify 0xa00124d7ec83uL; S64.classify 0x4db1fe6bee53auL; S64.classify 0x6a618b0752843uL; S64.classify 0x745c562c9c593uL;
  S64.classify 0x6d6c8b44ef1d2uL; S64.classify 0x28f8fb91378f9uL; S64.classify 0x79f73102ebe48uL; S64.classify 0x27c142ad4ca7uL; S64.classify 0x3c32efd109aa6uL;
  S64.classify 0x545565587ed1buL; S64.classify 0x543d3549c8217uL; S64.classify 0x756ead14a518cuL; S64.classify 0x70dcdf416e2c4uL; S64.classify 0x119e77b11d165uL;
  S64.classify 0x6f41ad41a51bfuL; S64.classify 0x5a689857eadf7uL; S64.classify 0x2cf664d17c339uL; S64.classify 0x5708b04614d9cuL; S64.classify 0x2c4f59ecedf7euL;
  S64.classify 0x3386f88b2f465uL; S64.classify 0x41eee064fcb87uL; S64.classify 0x51f35d05ecf52uL; S64.classify 0x5fcedb33b56fbuL; S64.classify 0x5c70fc48ea87cuL;
  S64.classify 0x74c95035bc63euL; S64.classify 0x6967724a4a87cuL; S64.classify 0x6d15dfdd3d6a7uL; S64.classify 0x149445fe88184uL; S64.classify 0x36e05f3266735uL;
  S64.classify 0x5cf2edb5beed4uL; S64.classify 0x3bc31f906fd70uL; S64.classify 0x5ab6fd640007uL; S64.classify 0x4511ce5535f79uL; S64.classify 0x5ae6a565800f2uL;
  S64.classify 0x4c3128e4b1ccbuL; S64.classify 0x918b62757abduL; S64.classify 0x73401bc3c7bc3uL; S64.classify 0x4509033e9d418uL; S64.classify 0x2b344e203a485uL;
  S64.classify 0x4dccde8de2f53uL; S64.classify 0x23d65d1df8a45uL; S64.classify 0x5588ce16c52a9uL; S64.classify 0x23062e06eb0e6uL; S64.classify 0x412806b917be6uL;
  S64.classify 0x33d2ca271c2e0uL; S64.classify 0x7fccc88bc1122uL; S64.classify 0x2ff91e5c79d0duL; S64.classify 0x707c753055f9euL; S64.classify 0x66432d1463a87uL;
  S64.classify 0x57f335c92bf29uL; S64.classify 0x1fc815cbea281uL; S64.classify 0x5d8378be98edauL; S64.classify 0x248d5927e9120uL; S64.classify 0x5e33f00e36b77uL
]
[@@"opaque_to_smt"; FStar.Custard.no_specialize]
let tt_seq : Seq.seq S64.t = Seq.seq_of_list tt_list

let tt_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == tt_seq /\
                     Seq.length (G.static_array_elems a) == 80 })
  = reveal_opaque (`%tt_seq) tt_seq;
    assert_norm (L.length tt_list == 80);
    G.mk_static_array tt_list

(** {2 The shape}

    Four lengths, which every entry below needs and none of them should
    reprove. *)

let shape (_: unit)
  : Lemma (L.length tx_list == 80 /\ L.length ty_list == 80 /\
           L.length tz_list == 80 /\ L.length tt_list == 80)
  = assert_norm (L.length tx_list == 80);
    assert_norm (L.length ty_list == 80);
    assert_norm (L.length tz_list == 80);
    assert_norm (L.length tt_list == 80)

(** {2 The sixteen entries} *)

let ent_0 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 0)
  = shape ();
    assert_norm (L.length (chunk tx_list 0) == F.nl /\
                 lbnd (chunk tx_list 0) /\
                 leval (chunk tx_list 0) == px W.e0);
    assert_norm (L.length (chunk ty_list 0) == F.nl /\
                 lbnd (chunk ty_list 0) /\
                 leval (chunk ty_list 0) == py W.e0);
    assert_norm (L.length (chunk tz_list 0) == F.nl /\
                 lbnd (chunk tz_list 0) /\
                 leval (chunk tz_list 0) == pz W.e0);
    assert_norm (L.length (chunk tt_list 0) == F.nl /\
                 lbnd (chunk tt_list 0) /\
                 leval (chunk tt_list 0) == pw W.e0);
    W.e0_ok ();
    ent_lit tx_list ty_list tz_list tt_list 0 E.g W.n W.e0

let ent_1 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 1)
  = shape ();
    assert_norm (L.length (chunk tx_list 1) == F.nl /\
                 lbnd (chunk tx_list 1) /\
                 leval (chunk tx_list 1) == px W.e1);
    assert_norm (L.length (chunk ty_list 1) == F.nl /\
                 lbnd (chunk ty_list 1) /\
                 leval (chunk ty_list 1) == py W.e1);
    assert_norm (L.length (chunk tz_list 1) == F.nl /\
                 lbnd (chunk tz_list 1) /\
                 leval (chunk tz_list 1) == pz W.e1);
    assert_norm (L.length (chunk tt_list 1) == F.nl /\
                 lbnd (chunk tt_list 1) /\
                 leval (chunk tt_list 1) == pw W.e1);
    W.e1_ok ();
    ent_lit tx_list ty_list tz_list tt_list 1 E.g W.n W.e1

let ent_2 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 2)
  = shape ();
    assert_norm (L.length (chunk tx_list 2) == F.nl /\
                 lbnd (chunk tx_list 2) /\
                 leval (chunk tx_list 2) == px W.e2);
    assert_norm (L.length (chunk ty_list 2) == F.nl /\
                 lbnd (chunk ty_list 2) /\
                 leval (chunk ty_list 2) == py W.e2);
    assert_norm (L.length (chunk tz_list 2) == F.nl /\
                 lbnd (chunk tz_list 2) /\
                 leval (chunk tz_list 2) == pz W.e2);
    assert_norm (L.length (chunk tt_list 2) == F.nl /\
                 lbnd (chunk tt_list 2) /\
                 leval (chunk tt_list 2) == pw W.e2);
    W.e2_ok ();
    ent_lit tx_list ty_list tz_list tt_list 2 E.g W.n W.e2

let ent_3 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 3)
  = shape ();
    assert_norm (L.length (chunk tx_list 3) == F.nl /\
                 lbnd (chunk tx_list 3) /\
                 leval (chunk tx_list 3) == px W.e3);
    assert_norm (L.length (chunk ty_list 3) == F.nl /\
                 lbnd (chunk ty_list 3) /\
                 leval (chunk ty_list 3) == py W.e3);
    assert_norm (L.length (chunk tz_list 3) == F.nl /\
                 lbnd (chunk tz_list 3) /\
                 leval (chunk tz_list 3) == pz W.e3);
    assert_norm (L.length (chunk tt_list 3) == F.nl /\
                 lbnd (chunk tt_list 3) /\
                 leval (chunk tt_list 3) == pw W.e3);
    W.e3_ok ();
    ent_lit tx_list ty_list tz_list tt_list 3 E.g W.n W.e3

let ent_4 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 4)
  = shape ();
    assert_norm (L.length (chunk tx_list 4) == F.nl /\
                 lbnd (chunk tx_list 4) /\
                 leval (chunk tx_list 4) == px W.e4);
    assert_norm (L.length (chunk ty_list 4) == F.nl /\
                 lbnd (chunk ty_list 4) /\
                 leval (chunk ty_list 4) == py W.e4);
    assert_norm (L.length (chunk tz_list 4) == F.nl /\
                 lbnd (chunk tz_list 4) /\
                 leval (chunk tz_list 4) == pz W.e4);
    assert_norm (L.length (chunk tt_list 4) == F.nl /\
                 lbnd (chunk tt_list 4) /\
                 leval (chunk tt_list 4) == pw W.e4);
    W.e4_ok ();
    ent_lit tx_list ty_list tz_list tt_list 4 E.g W.n W.e4

let ent_5 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 5)
  = shape ();
    assert_norm (L.length (chunk tx_list 5) == F.nl /\
                 lbnd (chunk tx_list 5) /\
                 leval (chunk tx_list 5) == px W.e5);
    assert_norm (L.length (chunk ty_list 5) == F.nl /\
                 lbnd (chunk ty_list 5) /\
                 leval (chunk ty_list 5) == py W.e5);
    assert_norm (L.length (chunk tz_list 5) == F.nl /\
                 lbnd (chunk tz_list 5) /\
                 leval (chunk tz_list 5) == pz W.e5);
    assert_norm (L.length (chunk tt_list 5) == F.nl /\
                 lbnd (chunk tt_list 5) /\
                 leval (chunk tt_list 5) == pw W.e5);
    W.e5_ok ();
    ent_lit tx_list ty_list tz_list tt_list 5 E.g W.n W.e5

let ent_6 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 6)
  = shape ();
    assert_norm (L.length (chunk tx_list 6) == F.nl /\
                 lbnd (chunk tx_list 6) /\
                 leval (chunk tx_list 6) == px W.e6);
    assert_norm (L.length (chunk ty_list 6) == F.nl /\
                 lbnd (chunk ty_list 6) /\
                 leval (chunk ty_list 6) == py W.e6);
    assert_norm (L.length (chunk tz_list 6) == F.nl /\
                 lbnd (chunk tz_list 6) /\
                 leval (chunk tz_list 6) == pz W.e6);
    assert_norm (L.length (chunk tt_list 6) == F.nl /\
                 lbnd (chunk tt_list 6) /\
                 leval (chunk tt_list 6) == pw W.e6);
    W.e6_ok ();
    ent_lit tx_list ty_list tz_list tt_list 6 E.g W.n W.e6

let ent_7 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 7)
  = shape ();
    assert_norm (L.length (chunk tx_list 7) == F.nl /\
                 lbnd (chunk tx_list 7) /\
                 leval (chunk tx_list 7) == px W.e7);
    assert_norm (L.length (chunk ty_list 7) == F.nl /\
                 lbnd (chunk ty_list 7) /\
                 leval (chunk ty_list 7) == py W.e7);
    assert_norm (L.length (chunk tz_list 7) == F.nl /\
                 lbnd (chunk tz_list 7) /\
                 leval (chunk tz_list 7) == pz W.e7);
    assert_norm (L.length (chunk tt_list 7) == F.nl /\
                 lbnd (chunk tt_list 7) /\
                 leval (chunk tt_list 7) == pw W.e7);
    W.e7_ok ();
    ent_lit tx_list ty_list tz_list tt_list 7 E.g W.n W.e7

let ent_8 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 8)
  = shape ();
    assert_norm (L.length (chunk tx_list 8) == F.nl /\
                 lbnd (chunk tx_list 8) /\
                 leval (chunk tx_list 8) == px W.e8);
    assert_norm (L.length (chunk ty_list 8) == F.nl /\
                 lbnd (chunk ty_list 8) /\
                 leval (chunk ty_list 8) == py W.e8);
    assert_norm (L.length (chunk tz_list 8) == F.nl /\
                 lbnd (chunk tz_list 8) /\
                 leval (chunk tz_list 8) == pz W.e8);
    assert_norm (L.length (chunk tt_list 8) == F.nl /\
                 lbnd (chunk tt_list 8) /\
                 leval (chunk tt_list 8) == pw W.e8);
    W.e8_ok ();
    ent_lit tx_list ty_list tz_list tt_list 8 E.g W.n W.e8

let ent_9 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 9)
  = shape ();
    assert_norm (L.length (chunk tx_list 9) == F.nl /\
                 lbnd (chunk tx_list 9) /\
                 leval (chunk tx_list 9) == px W.e9);
    assert_norm (L.length (chunk ty_list 9) == F.nl /\
                 lbnd (chunk ty_list 9) /\
                 leval (chunk ty_list 9) == py W.e9);
    assert_norm (L.length (chunk tz_list 9) == F.nl /\
                 lbnd (chunk tz_list 9) /\
                 leval (chunk tz_list 9) == pz W.e9);
    assert_norm (L.length (chunk tt_list 9) == F.nl /\
                 lbnd (chunk tt_list 9) /\
                 leval (chunk tt_list 9) == pw W.e9);
    W.e9_ok ();
    ent_lit tx_list ty_list tz_list tt_list 9 E.g W.n W.e9

let ent_10 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 10)
  = shape ();
    assert_norm (L.length (chunk tx_list 10) == F.nl /\
                 lbnd (chunk tx_list 10) /\
                 leval (chunk tx_list 10) == px W.e10);
    assert_norm (L.length (chunk ty_list 10) == F.nl /\
                 lbnd (chunk ty_list 10) /\
                 leval (chunk ty_list 10) == py W.e10);
    assert_norm (L.length (chunk tz_list 10) == F.nl /\
                 lbnd (chunk tz_list 10) /\
                 leval (chunk tz_list 10) == pz W.e10);
    assert_norm (L.length (chunk tt_list 10) == F.nl /\
                 lbnd (chunk tt_list 10) /\
                 leval (chunk tt_list 10) == pw W.e10);
    W.e10_ok ();
    ent_lit tx_list ty_list tz_list tt_list 10 E.g W.n W.e10

let ent_11 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 11)
  = shape ();
    assert_norm (L.length (chunk tx_list 11) == F.nl /\
                 lbnd (chunk tx_list 11) /\
                 leval (chunk tx_list 11) == px W.e11);
    assert_norm (L.length (chunk ty_list 11) == F.nl /\
                 lbnd (chunk ty_list 11) /\
                 leval (chunk ty_list 11) == py W.e11);
    assert_norm (L.length (chunk tz_list 11) == F.nl /\
                 lbnd (chunk tz_list 11) /\
                 leval (chunk tz_list 11) == pz W.e11);
    assert_norm (L.length (chunk tt_list 11) == F.nl /\
                 lbnd (chunk tt_list 11) /\
                 leval (chunk tt_list 11) == pw W.e11);
    W.e11_ok ();
    ent_lit tx_list ty_list tz_list tt_list 11 E.g W.n W.e11

let ent_12 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 12)
  = shape ();
    assert_norm (L.length (chunk tx_list 12) == F.nl /\
                 lbnd (chunk tx_list 12) /\
                 leval (chunk tx_list 12) == px W.e12);
    assert_norm (L.length (chunk ty_list 12) == F.nl /\
                 lbnd (chunk ty_list 12) /\
                 leval (chunk ty_list 12) == py W.e12);
    assert_norm (L.length (chunk tz_list 12) == F.nl /\
                 lbnd (chunk tz_list 12) /\
                 leval (chunk tz_list 12) == pz W.e12);
    assert_norm (L.length (chunk tt_list 12) == F.nl /\
                 lbnd (chunk tt_list 12) /\
                 leval (chunk tt_list 12) == pw W.e12);
    W.e12_ok ();
    ent_lit tx_list ty_list tz_list tt_list 12 E.g W.n W.e12

let ent_13 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 13)
  = shape ();
    assert_norm (L.length (chunk tx_list 13) == F.nl /\
                 lbnd (chunk tx_list 13) /\
                 leval (chunk tx_list 13) == px W.e13);
    assert_norm (L.length (chunk ty_list 13) == F.nl /\
                 lbnd (chunk ty_list 13) /\
                 leval (chunk ty_list 13) == py W.e13);
    assert_norm (L.length (chunk tz_list 13) == F.nl /\
                 lbnd (chunk tz_list 13) /\
                 leval (chunk tz_list 13) == pz W.e13);
    assert_norm (L.length (chunk tt_list 13) == F.nl /\
                 lbnd (chunk tt_list 13) /\
                 leval (chunk tt_list 13) == pw W.e13);
    W.e13_ok ();
    ent_lit tx_list ty_list tz_list tt_list 13 E.g W.n W.e13

let ent_14 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 14)
  = shape ();
    assert_norm (L.length (chunk tx_list 14) == F.nl /\
                 lbnd (chunk tx_list 14) /\
                 leval (chunk tx_list 14) == px W.e14);
    assert_norm (L.length (chunk ty_list 14) == F.nl /\
                 lbnd (chunk ty_list 14) /\
                 leval (chunk ty_list 14) == py W.e14);
    assert_norm (L.length (chunk tz_list 14) == F.nl /\
                 lbnd (chunk tz_list 14) /\
                 leval (chunk tz_list 14) == pz W.e14);
    assert_norm (L.length (chunk tt_list 14) == F.nl /\
                 lbnd (chunk tt_list 14) /\
                 leval (chunk tt_list 14) == pw W.e14);
    W.e14_ok ();
    ent_lit tx_list ty_list tz_list tt_list 14 E.g W.n W.e14

let ent_15 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list)
               E.g W.n 15)
  = shape ();
    assert_norm (L.length (chunk tx_list 15) == F.nl /\
                 lbnd (chunk tx_list 15) /\
                 leval (chunk tx_list 15) == px W.e15);
    assert_norm (L.length (chunk ty_list 15) == F.nl /\
                 lbnd (chunk ty_list 15) /\
                 leval (chunk ty_list 15) == py W.e15);
    assert_norm (L.length (chunk tz_list 15) == F.nl /\
                 lbnd (chunk tz_list 15) /\
                 leval (chunk tz_list 15) == pz W.e15);
    assert_norm (L.length (chunk tt_list 15) == F.nl /\
                 lbnd (chunk tt_list 15) /\
                 leval (chunk tt_list 15) == pw W.e15);
    W.e15_ok ();
    ent_lit tx_list ty_list tz_list tt_list 15 E.g W.n W.e15

(** {2 The table}

    What {!Hacl.Ed25519.PointMulG} asks for. *)

let reveal_seqs (_: unit)
  : Lemma (tx_seq == Seq.seq_of_list tx_list /\
           ty_seq == Seq.seq_of_list ty_list /\
           tz_seq == Seq.seq_of_list tz_list /\
           tt_seq == Seq.seq_of_list tt_list)
  = reveal_opaque (`%tx_seq) tx_seq;
    reveal_opaque (`%ty_seq) ty_seq;
    reveal_opaque (`%tz_seq) tz_seq;
    reveal_opaque (`%tt_seq) tt_seq

let tbl_ok (_: unit)
  : Lemma (tok tx_seq ty_seq tz_seq tt_seq E.g 1 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list) E.g W.n

#pop-options
