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

    Sixteen multiples of [2^192 g], four arrays of eighty limbs, laid out
    the way {!Hacl.Ed25519.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.Ed25519.Win3} says what the sixteen
    points are and {!Hacl.Ed25519.WinTable} turns a list of limbs into one
    of them, so what is left here is sixteen entries of four
    [assert_norm]s each, every one of them arithmetic on a literal list
    that the normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried three hundred and twenty fifty-one-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.Ed25519.Win3

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
module W = Spec.Ed25519.Win3

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The four arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x2d644c7dad28duL; S64.classify 0x43703afa4db6fuL; S64.classify 0x1f85df5ea777buL; S64.classify 0x73e16c6821b8euL; S64.classify 0x1bc7af1e38185uL;
  S64.classify 0x1938218028354uL; S64.classify 0x6bb1b54fa00f3uL; S64.classify 0x6e28f67cbea25uL; S64.classify 0x4b5e9141aad35uL; S64.classify 0x6bce245f8c25uL;
  S64.classify 0x589041b29662fuL; S64.classify 0x1d6fbadddcfd7uL; S64.classify 0x1fff2d032c3bcuL; S64.classify 0x2f7b21e1d64e1uL; S64.classify 0x7665908aaf444uL;
  S64.classify 0x5954e6c16d4f7uL; S64.classify 0x7ca457221ebb3uL; S64.classify 0x69398c394d173uL; S64.classify 0x554841a79f99duL; S64.classify 0xa09b36eb5a04uL;
  S64.classify 0x4d5451113735euL; S64.classify 0x2574dcfa41233uL; S64.classify 0x55926182e858buL; S64.classify 0x6b540645ad45fuL; S64.classify 0x1c71ce37638e6uL;
  S64.classify 0x39e7f74cbc8d6uL; S64.classify 0x8d90a5963263uL; S64.classify 0x70b3f944839e5uL; S64.classify 0x7bec4bd417c4auL; S64.classify 0x3c607a84c1df2uL;
  S64.classify 0x2f417ffbe2da0uL; S64.classify 0x4d4c71c738621uL; S64.classify 0x5bbdfc4e85ff1uL; S64.classify 0x6331ffc9c6eb0uL; S64.classify 0x89b6cd02000buL;
  S64.classify 0x6b2d6fc2c9fdbuL; S64.classify 0x5b0e0cf4a45c3uL; S64.classify 0x1de41b4adca18uL; S64.classify 0x6b07c3d5aa1a3uL; S64.classify 0x79e9d5b60917uL;
  S64.classify 0x54ba615e7bacfuL; S64.classify 0x4e5177009b7b9uL; S64.classify 0x735e62946071duL; S64.classify 0x6115696f90eauL; S64.classify 0x14445439305d0uL;
  S64.classify 0x87787e2dd7b8uL; S64.classify 0x7bb442643ef2uL; S64.classify 0x70221dc40c4e7uL; S64.classify 0x10e30d662465auL; S64.classify 0x7b23a7dce9a09uL;
  S64.classify 0x13e2d3b4b1d5cuL; S64.classify 0x8985fcb81ee5uL; S64.classify 0x1988a1a828025uL; S64.classify 0xa01a7d870114uL; S64.classify 0x488953fd41867uL;
  S64.classify 0x3403b4621d719uL; S64.classify 0x3015b2e7b4c3euL; S64.classify 0x5115565bbd38buL; S64.classify 0x3f631614c3f31uL; S64.classify 0x2396f9d65dc6buL;
  S64.classify 0x657b3ace3c6f8uL; S64.classify 0x366a7ba42314duL; S64.classify 0x29eb30543f7f7uL; S64.classify 0x1b6c2a1d320d3uL; S64.classify 0x229f80407ae62uL;
  S64.classify 0xcc1a47ce93c4uL; S64.classify 0x3393627feb977uL; S64.classify 0x1eb4e9e334c2cuL; S64.classify 0x496d2855b1681uL; S64.classify 0x4c7cb3e8f525auL;
  S64.classify 0xdc27e0016faauL; S64.classify 0x5c13389191daduL; S64.classify 0x440264d63e1c5uL; S64.classify 0xe2d56486f232uL; S64.classify 0x2a4b994aa61f7uL
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
  S64.classify 0x2f65900314833uL; S64.classify 0x24c6364e1f95euL; S64.classify 0x57701247409f8uL; S64.classify 0x797bd2f77c3bcuL; S64.classify 0x61d909d855661uL;
  S64.classify 0x4955188a3c065uL; S64.classify 0x161bd0f1292dfuL; S64.classify 0x1d521630b2506uL; S64.classify 0x6d06495669788uL; S64.classify 0x3d26989cdd0f6uL;
  S64.classify 0x3a00e4b704ca1uL; S64.classify 0x71715f4826e10uL; S64.classify 0x40ad025948864uL; S64.classify 0x2a3670bfc0327uL; S64.classify 0x4ed18a7c50da4uL;
  S64.classify 0x2eb0fa35ed926uL; S64.classify 0x49a86e7641e74uL; S64.classify 0x3b54cf41b3a7buL; S64.classify 0x85125b7595d7uL; S64.classify 0x3aa47fd60fa31uL;
  S64.classify 0xfee129e406cbuL; S64.classify 0x7e88f52e59c7duL; S64.classify 0x2833edf503460uL; S64.classify 0x166921edd6bcduL; S64.classify 0x7880cc1c2003buL;
  S64.classify 0x79a86ba3cea68uL; S64.classify 0x42e6340c19d4euL; S64.classify 0x76fb861261f82uL; S64.classify 0x51d11c25d5a44uL; S64.classify 0x34518ad109941uL;
  S64.classify 0x16f13e8ceb88uL; S64.classify 0x4f9b762547cf1uL; S64.classify 0x72995f90f2f92uL; S64.classify 0x7ec5a1c6f7e88uL; S64.classify 0x66ef7206aa36duL;
  S64.classify 0x1381c04c78797uL; S64.classify 0x79470b8eb0720uL; S64.classify 0x2fe8895900193uL; S64.classify 0x5229893654a28uL; S64.classify 0x16512951d2240uL;
  S64.classify 0x200515d0477bcuL; S64.classify 0x157fafd10b1dduL; S64.classify 0x2e35626b9af26uL; S64.classify 0x6a69f71b080cfuL; S64.classify 0x2ab36d724a6ecuL;
  S64.classify 0x2040bc9616570uL; S64.classify 0x39cf90f92e9c2uL; S64.classify 0x2edbe7e0547abuL; S64.classify 0x30189d6ee99fbuL; S64.classify 0x77a7fbafce1bcuL;
  S64.classify 0x399223384410uL; S64.classify 0x14223f9006beuL; S64.classify 0x50f09050a657duL; S64.classify 0x292378430245duL; S64.classify 0x7bd340fdf6e04uL;
  S64.classify 0x6d8b42d583ddeuL; S64.classify 0x777423d7bfc3buL; S64.classify 0x48c1559a710a7uL; S64.classify 0x698034ab91fabuL; S64.classify 0x675952b2e020euL;
  S64.classify 0x3f16fe3db85b0uL; S64.classify 0x7cd85cb93b208uL; S64.classify 0x7a019da637748uL; S64.classify 0x4f4880eb525e0uL; S64.classify 0x1d44ec76d45e6uL;
  S64.classify 0x18cd592e65741uL; S64.classify 0x296915f5154fduL; S64.classify 0xe85466180265uL; S64.classify 0x2ee9f744c36abuL; S64.classify 0x4c957905c63cbuL;
  S64.classify 0x57486d74dda9auL; S64.classify 0x7984da5d06098uL; S64.classify 0x5f05e86ec0601uL; S64.classify 0x61bbb3c0adce8uL; S64.classify 0x13a4a860954e7uL
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
  S64.classify 0x45216636c2c7uL; S64.classify 0x6cadbcfdf0a37uL; S64.classify 0x47c3ef66ee3c8uL; S64.classify 0x522665b326f25uL; S64.classify 0x1a340b8054b8fuL;
  S64.classify 0x365eb8eb94b17uL; S64.classify 0x18452cd8dbe9uL; S64.classify 0xd790b46bf270uL; S64.classify 0x78813093349c2uL; S64.classify 0x7a9f6260e653auL;
  S64.classify 0x54343b9ec13bbuL; S64.classify 0x15437f0d48d06uL; S64.classify 0x366c6c241874buL; S64.classify 0x6e66e4600d1c1uL; S64.classify 0x6bb9cf0f2d4dbuL;
  S64.classify 0x3b1cc6b04c053uL; S64.classify 0x13e65c5705fc4uL; S64.classify 0x7f81640bc9a65uL; S64.classify 0x6ac534fc04217uL; S64.classify 0x3bd5dfb4b4648uL;
  S64.classify 0x30eaefc5832acuL; S64.classify 0x7bb8bc02f05uL; S64.classify 0x10ee994d38e57uL; S64.classify 0xc32dd003212euL; S64.classify 0x79030a4774645uL;
  S64.classify 0x3c6c9e37345duL; S64.classify 0x7081214e622b1uL; S64.classify 0x60ece5ba974a8uL; S64.classify 0x179f8768deed4uL; S64.classify 0x727055e32e57uL;
  S64.classify 0x478374da76d28uL; S64.classify 0x5344ef62175f4uL; S64.classify 0x78f681d66e834uL; S64.classify 0x1fda3b879848duL; S64.classify 0xd2c585f51161uL;
  S64.classify 0x1b9bb33b94e2auL; S64.classify 0x471701c32b888uL; S64.classify 0x7201f9f3e4791uL; S64.classify 0x9c9665f45f28uL; S64.classify 0x18a2cd789580buL;
  S64.classify 0x46e2ce7ceecabuL; S64.classify 0x5b697fb2f2e3auL; S64.classify 0x43723380b355buL; S64.classify 0x1594187a6aa3auL; S64.classify 0x3768f1d146014uL;
  S64.classify 0x25b1a1380ed31uL; S64.classify 0x70dbb6d788f3duL; S64.classify 0x510ca8a63cb2duL; S64.classify 0xfec9668bc1dduL; S64.classify 0x678006f65af05uL;
  S64.classify 0xec1fcde050f2uL; S64.classify 0x4898e6bcf3408uL; S64.classify 0x4c6e0a7708771uL; S64.classify 0x68b1dcb7e3c7fuL; S64.classify 0x602833b0f078buL;
  S64.classify 0x72ab1e3bcf96buL; S64.classify 0x6f4bde8068edbuL; S64.classify 0x4f5b5bada9c40uL; S64.classify 0x485bc50a03394uL; S64.classify 0x415d255a9d532uL;
  S64.classify 0x5f8864731bfcbuL; S64.classify 0x7ab32c19376cduL; S64.classify 0x339acb66b1bdeuL; S64.classify 0x28a92de1eb77auL; S64.classify 0x76a4d6aa450ebuL;
  S64.classify 0x3578a80d634dbuL; S64.classify 0x6b064354f9c85uL; S64.classify 0xfb9d2c116f8fuL; S64.classify 0x5c1966ac524c7uL; S64.classify 0x7ed22b364f0d8uL;
  S64.classify 0x3af37d41878buL; S64.classify 0x21320c8533a02uL; S64.classify 0x4f99d4d5b0067uL; S64.classify 0x6dc96bcafbb01uL; S64.classify 0x55f69782ed38buL
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
  : Lemma (tok tx_seq ty_seq tz_seq tt_seq E.g (pow2 192) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list) E.g W.n

#pop-options
