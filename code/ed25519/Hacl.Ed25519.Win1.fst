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

    Sixteen multiples of [2^64 g], four arrays of eighty limbs, laid out
    the way {!Hacl.Ed25519.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.Ed25519.Win1} says what the sixteen
    points are and {!Hacl.Ed25519.WinTable} turns a list of limbs into one
    of them, so what is left here is sixteen entries of four
    [assert_norm]s each, every one of them arithmetic on a literal list
    that the normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried three hundred and twenty fifty-one-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.Ed25519.Win1

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
module W = Spec.Ed25519.Win1

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The four arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x36b8ff4eda202uL; S64.classify 0x7daa346bd67c1uL; S64.classify 0x2822a5801e36duL; S64.classify 0x4eaea25b067dauL; S64.classify 0x6222bd88bf2dfuL;
  S64.classify 0x2aa2d8bdba597uL; S64.classify 0x337727e412228uL; S64.classify 0x682a0453a101buL; S64.classify 0x262572fd31592uL; S64.classify 0x23bc7abc84cbuL;
  S64.classify 0x7640e33263467uL; S64.classify 0x4d99d421b1000uL; S64.classify 0x229877cb2a32auL; S64.classify 0x20e2cd45a4e5uL; S64.classify 0x132a065edb5c4uL;
  S64.classify 0x633fbbd39d169uL; S64.classify 0x2de1deb9e1897uL; S64.classify 0x1cb211e5ff1a1uL; S64.classify 0x252cc055229dbuL; S64.classify 0x6d5066cf7137buL;
  S64.classify 0x2429c7b04c2cduL; S64.classify 0x1f7334164ea0euL; S64.classify 0x2e82a3d8f00c4uL; S64.classify 0x49a3fac10ad3auL; S64.classify 0x35ff8f7cdb086uL;
  S64.classify 0x2120a622e0213uL; S64.classify 0x4928e70b4255euL; S64.classify 0x20ca395004af1uL; S64.classify 0x137b5a74383cduL; S64.classify 0x6c6365c17f4bbuL;
  S64.classify 0x44c675bd887d1uL; S64.classify 0x309183c31e772uL; S64.classify 0x1f3aa0d1e7794uL; S64.classify 0x2965c1800a0dfuL; S64.classify 0x68b818a50b31duL;
  S64.classify 0x3e8be859362a9uL; S64.classify 0x285b6b601c94euL; S64.classify 0x277aacb4ea942uL; S64.classify 0x6a71a039dbb31uL; S64.classify 0x6b66159ac8702uL;
  S64.classify 0x50334a9d159auL; S64.classify 0x5ce33ce0e9334uL; S64.classify 0x334c4d2f28074uL; S64.classify 0x352820028e76fuL; S64.classify 0x1d3b69c19baa7uL;
  S64.classify 0x2e27609a42401uL; S64.classify 0x2309b257e2d42uL; S64.classify 0x3da7c8d0cb2c7uL; S64.classify 0x67eb1a5a486fbuL; S64.classify 0x1a12237794fd0uL;
  S64.classify 0x673b0f96c0677uL; S64.classify 0x2b01cac525d87uL; S64.classify 0xb716b8b91d3auL; S64.classify 0xe236c66fa7c8uL; S64.classify 0x17ffc4a242bfcuL;
  S64.classify 0x568a17517c24duL; S64.classify 0x71c688078d879uL; S64.classify 0x3903cfd1e4425uL; S64.classify 0x2100fbefd2c49uL; S64.classify 0x6f0219bc5e589uL;
  S64.classify 0x4b72109a85cc5uL; S64.classify 0x761ee0187ec1cuL; S64.classify 0x1c9a0cbd9bb4auL; S64.classify 0x116b7bdb3030buL; S64.classify 0x4a52307dc395euL;
  S64.classify 0x8dc7b4d7e206uL; S64.classify 0x422442e9ca98duL; S64.classify 0x681e8c56e3a74uL; S64.classify 0x4c8fb148d15euL; S64.classify 0x7d664177da027uL;
  S64.classify 0x61c7c797779d5uL; S64.classify 0x4bfbfd0827c0buL; S64.classify 0x1ba5951da73d0uL; S64.classify 0x6b19d7cc847c7uL; S64.classify 0x2ae19cea663d4uL
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
  S64.classify 0x6fa5782e45313uL; S64.classify 0x117520560d1e3uL; S64.classify 0x6df13d5042d8uL; S64.classify 0x12eeb5ed7693uL; S64.classify 0x325bb42ea4eduL;
  S64.classify 0x511df0f29c9eeuL; S64.classify 0x1e58c41b9ddb0uL; S64.classify 0x5c81ba413e52euL; S64.classify 0x58a64a8101b8euL; S64.classify 0x4d2b97a739eceuL;
  S64.classify 0x5fa3e1dd7de2fuL; S64.classify 0x3863fd1d4b30cuL; S64.classify 0x7973f46ce42c3uL; S64.classify 0x3c03b16b5bdc2uL; S64.classify 0x534ef70a3532fuL;
  S64.classify 0x347115219a417uL; S64.classify 0x68445d52b6b96uL; S64.classify 0x2e0615fe54802uL; S64.classify 0x3e441d5f1ad5fuL; S64.classify 0x54bb8cd82a0a8uL;
  S64.classify 0x49cbaa6ce8b8auL; S64.classify 0x2fbfc351521f8uL; S64.classify 0x6ed81ad386d5cuL; S64.classify 0x782aa34f434a9uL; S64.classify 0x50e1cc6871155uL;
  S64.classify 0x1499e5494c782uL; S64.classify 0x54c171a7d6061uL; S64.classify 0x2a7b2382370ccuL; S64.classify 0x4b4641905002buL; S64.classify 0x1c5703a9d3d1auL;
  S64.classify 0xe4dfed398826uL; S64.classify 0x2a6b5bb8ee8e5uL; S64.classify 0x5b63d0e5a1659uL; S64.classify 0x35914773a6ba9uL; S64.classify 0x1e8b233ec0076uL;
  S64.classify 0x61a22c8ca96c5uL; S64.classify 0x644c063cebfduL; S64.classify 0x110cae7398c22uL; S64.classify 0x282724d9d2eacuL; S64.classify 0x19dd4bef38efduL;
  S64.classify 0x7fbf1373fd0b9uL; S64.classify 0x7c4663d51a8e7uL; S64.classify 0x3b378c1ccc439uL; S64.classify 0x281e507cf1be7uL; S64.classify 0x68d73077fa5e3uL;
  S64.classify 0x684b7d2ba4f29uL; S64.classify 0x23e115d6e7ea6uL; S64.classify 0x55638174762b3uL; S64.classify 0x7797572f6eab2uL; S64.classify 0x1d079c642f577uL;
  S64.classify 0x555f000269875uL; S64.classify 0x33d877c0c651duL; S64.classify 0x608cf36b7dccbuL; S64.classify 0x5244ca9423174uL; S64.classify 0x69b87fc7d5aefuL;
  S64.classify 0x3a75491d8d620uL; S64.classify 0x61f40c689641euL; S64.classify 0x5d1944051bf20uL; S64.classify 0x7e71334f82709uL; S64.classify 0x64c8c5d0f490cuL;
  S64.classify 0x3da3eb734947duL; S64.classify 0x12913b4a5f390uL; S64.classify 0x18967261e0095uL; S64.classify 0x6aaa501f214deuL; S64.classify 0x6a83e11cb340fuL;
  S64.classify 0x35d0e82761ae9uL; S64.classify 0x3b0bd222bd613uL; S64.classify 0xb8cac3dfeabuL; S64.classify 0x5cf0f8a5d92b9uL; S64.classify 0x2e680498e9582uL;
  S64.classify 0x377e5bfcf9334uL; S64.classify 0x5a6a3140242bauL; S64.classify 0x77e504b59af89uL; S64.classify 0x763f53b5953d0uL; S64.classify 0x6fc4bdd1912e5uL
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
  S64.classify 0x592e9b6740859uL; S64.classify 0x1d39897f0c5bfuL; S64.classify 0x251580ec2af8uL; S64.classify 0x70563ccc07320uL; S64.classify 0x628b09e2c7d3auL;
  S64.classify 0x320ab2c14539auL; S64.classify 0x137b00f01661fuL; S64.classify 0x5b6edcf358ad2uL; S64.classify 0x4243cb28d0446uL; S64.classify 0x2be24dbdd7a46uL;
  S64.classify 0x25b0e72ecf407uL; S64.classify 0x5e9b86d31f29euL; S64.classify 0x717e3d7ee0972uL; S64.classify 0x2d2ea94ab733auL; S64.classify 0x13de9f98824e0uL;
  S64.classify 0xead868ab7c70uL; S64.classify 0x37519f2944719uL; S64.classify 0x239bc7c2a540buL; S64.classify 0x7330e4f203f15uL; S64.classify 0x609142e130e7fuL;
  S64.classify 0x289b38c30e3d7uL; S64.classify 0xa98bfd31710buL; S64.classify 0x6dec6dcfff0eduL; S64.classify 0x4a8cc50bd6ec3uL; S64.classify 0x330c0a7ed1b12uL;
  S64.classify 0x2125c8b8f0450uL; S64.classify 0x68a693333f97euL; S64.classify 0x4db1dc8b06120uL; S64.classify 0x1547ff45b5efeuL; S64.classify 0x397f5db80e233uL;
  S64.classify 0x795099c995b42uL; S64.classify 0x350ab19851e94uL; S64.classify 0x4657c36d323bfuL; S64.classify 0x14e89c4af4304uL; S64.classify 0x76724d74dba8euL;
  S64.classify 0x356e7c4fdc3uL; S64.classify 0x6cce9df96746auL; S64.classify 0x231226afcf26fuL; S64.classify 0xe6a709a55008uL; S64.classify 0x667fbacce0dc3uL;
  S64.classify 0x375c055e14773uL; S64.classify 0x5bff2ad6e8f26uL; S64.classify 0x1d069a22c054fuL; S64.classify 0x7b510676d36c9uL; S64.classify 0x492034611c74uL;
  S64.classify 0x536d1e398a5dduL; S64.classify 0x4b74cc9f3766auL; S64.classify 0x578e721630175uL; S64.classify 0x18a9e40238faduL; S64.classify 0x533594b8b7e22uL;
  S64.classify 0x4c59dd4aa431buL; S64.classify 0x7464e76380fc5uL; S64.classify 0x714b55fc458fduL; S64.classify 0xb6246313a047uL; S64.classify 0x573e2870fd086uL;
  S64.classify 0x42f04bce66fc8uL; S64.classify 0x5dec0dc5fbd5fuL; S64.classify 0x1226e1387aaa0uL; S64.classify 0x5e9ec008c01beuL; S64.classify 0xc8e43546e18cuL;
  S64.classify 0x256370cb5a454uL; S64.classify 0x3a5a52e73f7abuL; S64.classify 0x60902a84204b9uL; S64.classify 0x349e23f6ad1e9uL; S64.classify 0x38ca9f6f16e0cuL;
  S64.classify 0xbd35dde74c3duL; S64.classify 0x314202fcaf86euL; S64.classify 0x1f392acaa2ee8uL; S64.classify 0x257d726bfdd59uL; S64.classify 0x419480e62aa87uL;
  S64.classify 0x4d5bc000fc6b3uL; S64.classify 0x2cce6c31c323buL; S64.classify 0x17384421af80cuL; S64.classify 0x3f52db867971euL; S64.classify 0x3e305c53bc3beuL
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
  : Lemma (tok tx_seq ty_seq tz_seq tt_seq E.g (pow2 64) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list) E.g W.n

#pop-options
