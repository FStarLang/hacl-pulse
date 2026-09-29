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

    Sixteen multiples of the generator, three arrays of eighty limbs, laid
    out the way {!Hacl.K256.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.K256.Win0} says what the sixteen
    points are and {!Hacl.K256.WinTable} turns a list of limbs into one of
    them, so what is left here is sixteen entries of three [assert_norm]s
    each, every one of them arithmetic on a literal list that the
    normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried two hundred and forty fifty-two-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.K256.Win0

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
module W = Spec.K256.Win0

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The three arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x2815b16f81798uL; S64.classify 0xdb2dce28d959fuL; S64.classify 0xe870b07029bfcuL; S64.classify 0xbbac55a06295cuL; S64.classify 0x79be667ef9dcuL;
  S64.classify 0xc09b95c709ee5uL; S64.classify 0x4b8cef3ca7abauL; S64.classify 0x5c07cd85c778euL; S64.classify 0x7d6d3045406e9uL; S64.classify 0xc6047f9441eduL;
  S64.classify 0x1f113bce036f9uL; S64.classify 0x45836f99b0860uL; S64.classify 0x89d5229b531c8uL; S64.classify 0xc31049344f85fuL; S64.classify 0xf9308a019258uL;
  S64.classify 0xa94abe8c4cd13uL; S64.classify 0x900ee0758474fuL; S64.classify 0x30b1404cc6c13uL; S64.classify 0x80f3581e49049uL; S64.classify 0xe493dbf1c10duL;
  S64.classify 0x8d569b240efe4uL; S64.classify 0xbddc619ab7cbauL; S64.classify 0xa5c5128e88b84uL; S64.classify 0x209355b4a7250uL; S64.classify 0x2f8bde4d1a07uL;
  S64.classify 0x57a1460297556uL; S64.classify 0x2f8568a18b2f0uL; S64.classify 0x55235d382f647uL; S64.classify 0xeea420453a143uL; S64.classify 0xfff97bd5755euL;
  S64.classify 0xbddedcac4f9bcuL; S64.classify 0x7e0330e39ce92uL; S64.classify 0x2ea7a0e3d419buL; S64.classify 0xb4eaa398f365fuL; S64.classify 0x5cbdf0646e5duL;
  S64.classify 0x84ef3e10a2a01uL; S64.classify 0x5e5af888a677uL; S64.classify 0x70f3c2f0a1bdduL; S64.classify 0x351daff3843fbuL; S64.classify 0x2f01e5e15ccauL;
  S64.classify 0xf110dfc27ccbeuL; S64.classify 0x974c57e714c35uL; S64.classify 0xf559abde09796uL; S64.classify 0xf65309ad178a9uL; S64.classify 0xacd484e2f0c7uL;
  S64.classify 0x68e2a47e247c7uL; S64.classify 0x9b1943c2b752auL; S64.classify 0xae6ae5d3442d4uL; S64.classify 0xc86235477c7b1uL; S64.classify 0xa0434d9e47f3uL;
  S64.classify 0xc17895da008cbuL; S64.classify 0xbe5c17891bbeuL; S64.classify 0xc65aac564998uL; S64.classify 0x411e5ef4246b7uL; S64.classify 0x774ae7f858a9uL;
  S64.classify 0xf47070afe85auL; S64.classify 0x419620095bc5buL; S64.classify 0xd734633687cf4uL; S64.classify 0x561b15c38f004uL; S64.classify 0xd01115d548e7uL;
  S64.classify 0xddf8f19405aa8uL; S64.classify 0xc6610e58cddeeuL; S64.classify 0x3748651b075fbuL; S64.classify 0x288bc7d1d205cuL; S64.classify 0xf28773c2d975uL;
  S64.classify 0xb241a60e823e4uL; S64.classify 0x63678949e6e49uL; S64.classify 0x7d38e3226aa7buL; S64.classify 0x719cfd64e67f0uL; S64.classify 0x499fdf9e895euL;
  S64.classify 0xdbcf8e27e080euL; S64.classify 0x6f3c85f79e44auL; S64.classify 0x95ff41131e594uL; S64.classify 0xea965a465ae30uL; S64.classify 0xd7924d4f7d43uL
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
  S64.classify 0x7d08ffb10d4b8uL; S64.classify 0x48a68554199c4uL; S64.classify 0xe1108a8fd17b4uL; S64.classify 0xc4655da4fbfc0uL; S64.classify 0x483ada7726a3uL;
  S64.classify 0x431a950cfe52auL; S64.classify 0x653266d0e1236uL; S64.classify 0x66ceaeef7f632uL; S64.classify 0xc339a3c584194uL; S64.classify 0x1ae168fea63duL;
  S64.classify 0x9fd7584b8e672uL; S64.classify 0x9934c2231b6cbuL; S64.classify 0xa37f3566500a9uL; S64.classify 0xe8140fe337e62uL; S64.classify 0x388f7b0f632duL;
  S64.classify 0x97bdc47739922uL; S64.classify 0x33bfbdfe40cfeuL; S64.classify 0xea51448d967aeuL; S64.classify 0x55b75642e2098uL; S64.classify 0x51ed993ea0d4uL;
  S64.classify 0x87d3aa6ac62d6uL; S64.classify 0x1bab0d6840dcauL; S64.classify 0x6c9c426f78827uL; S64.classify 0xe3d6d4dba9ddauL; S64.classify 0xd8ac222636e5uL;
  S64.classify 0x70c36b075f297uL; S64.classify 0xf6518fe4a03c8uL; S64.classify 0xf45c560de80f0uL; S64.classify 0xb620f3be96017uL; S64.classify 0xae12777aacfbuL;
  S64.classify 0x82628087264dauL; S64.classify 0xb813fde7b5a50uL; S64.classify 0x61a54dba813d0uL; S64.classify 0x5960a3178d6d8uL; S64.classify 0x6aebca40ba25uL;
  S64.classify 0xa2cb76cbde904uL; S64.classify 0xd6ba5b7617b5duL; S64.classify 0x32d13b4c2e213uL; S64.classify 0x9949293d082a1uL; S64.classify 0x5c4da8a74153uL;
  S64.classify 0xc262ac64f9c37uL; S64.classify 0xa4375f8e0f05cuL; S64.classify 0x63b61e9add888uL; S64.classify 0xd9fd643809717uL; S64.classify 0xcc338921b0a7uL;
  S64.classify 0xee53b037368d7uL; S64.classify 0x2ed877a1593cbuL; S64.classify 0x3a24c696f794cuL; S64.classify 0xbc27a3b6c7e69uL; S64.classify 0x893aba425419uL;
  S64.classify 0xd74c9c953c61buL; S64.classify 0xe2dff9d6a8301uL; S64.classify 0x7b7b365372db1uL; S64.classify 0x5e190243dd56duL; S64.classify 0xd984a032eb6buL;
  S64.classify 0x51b13f4062327uL; S64.classify 0x5dd9a86d526b0uL; S64.classify 0x17bd81579238cuL; S64.classify 0xe0d7a8b64537euL; S64.classify 0xa9f34ffdc815uL;
  S64.classify 0x5cb52db03ed81uL; S64.classify 0xda521fa91f29buL; S64.classify 0x5cdaf473a1a06uL; S64.classify 0xa89758212eb6uL; S64.classify 0xab0902e8d88uL;
  S64.classify 0xf40d403a13f5buL; S64.classify 0xc27a3f95bcc65uL; S64.classify 0x7b3d464464279uL; S64.classify 0x855190f044e4auL; S64.classify 0xcac2f6c4b54euL;
  S64.classify 0x4dc9ff6a26b58uL; S64.classify 0x2bd896d3a5c50uL; S64.classify 0x8cc6defea40afuL; S64.classify 0x72a683842ec22uL; S64.classify 0x581e2872a86cuL
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
  : Lemma (tok tx_seq ty_seq tz_seq K.g 1 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) K.g W.n

#pop-options
