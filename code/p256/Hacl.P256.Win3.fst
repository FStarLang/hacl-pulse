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

    Sixteen multiples of [2^192 G], three arrays of sixty-four limbs laid
    out the way {!Hacl.P256.PointWin.entry} reads them: entry [d] is limbs
    [4d] through [4d + 3], in Montgomery form.  {!Spec.P256.Win3} says what
    the sixteen points are and {!Hacl.P256.WinTable} turns a list of limbs
    into one of them, so what is left here is three [assert_norm]s per
    entry, each arithmetic on a literal list.  Nothing below mentions the
    curve. *)
module Hacl.P256.Win3

open Spec.Bignum4
open Hacl.Impl.Limb4
open Hacl.Impl.Lit4
open Hacl.P256.PointWin
open Hacl.P256.WinTable

module Seq = FStar.Seq
module L = FStar.List.Tot
module G = Pulse.Lib.GlobalArray
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module W = Spec.P256.Win3

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The three arrays} *)

let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x56f8410ef4f8b16auL; S64.classify 0x97241afec47b266auL; S64.classify 0xa406b8e6d9c87c1uL; S64.classify 0x803f3e02cd42ab1buL;
  S64.classify 0x3f747fa0b311898cuL; S64.classify 0xe2a272e4cd0eac65uL; S64.classify 0x4bba5851f914d0bcuL; S64.classify 0x7a1a9660c4a43ee3uL;
  S64.classify 0x266344a43794f8dcuL; S64.classify 0xdcca923a483c5c36uL; S64.classify 0x2d6b6bbf3f9d10a0uL; S64.classify 0xb320c5ca81d9bdf3uL;
  S64.classify 0xb6c185c341dca566uL; S64.classify 0x7de7fedad8622aa3uL; S64.classify 0x99e84d92901b6dfbuL; S64.classify 0x30a02b0e7c4ad288uL;
  S64.classify 0x25470fabe085116buL; S64.classify 0x4a4337587285310uL; S64.classify 0x4e39187ee2bfd52fuL; S64.classify 0x36166b447d9ebc74uL;
  S64.classify 0xd74e9bdac97e6516uL; S64.classify 0x88779360c230f49euL; S64.classify 0xa6ec1de31e74ea49uL; S64.classify 0x581dcee53fb645a2uL;
  S64.classify 0x72cfd2e949dee168uL; S64.classify 0x1ae052233e2af239uL; S64.classify 0x9e75be1d94066auL; S64.classify 0x6cca31c738abf413uL;
  S64.classify 0xc492ec644cd8f64cuL; S64.classify 0x58a2d790279d7b51uL; S64.classify 0xced1fc51fc75256uL; S64.classify 0x3e658aed8f433017uL;
  S64.classify 0x3ce519ef76257c51uL; S64.classify 0x6f5818d318d477e7uL; S64.classify 0xab022e037963edc0uL; S64.classify 0xf0403a898bd1f5f3uL;
  S64.classify 0xf1ff42a12c84bd9duL; S64.classify 0x751f3ec4390c674auL; S64.classify 0x27bb36f701e5e0cauL; S64.classify 0x65dfff515caf6692uL;
  S64.classify 0xbdec338e3318d2d4uL; S64.classify 0x733dd7bbbe8de963uL; S64.classify 0x61bcc3baa2c47ebduL; S64.classify 0xa821ad1935efcbdeuL;
  S64.classify 0x7b2a0bcb81f41c78uL; S64.classify 0x5c522c851fd240e1uL; S64.classify 0xce512e68df5ce3f6uL; S64.classify 0xa7d4b952b6d5ee13uL;
  S64.classify 0xed1b5ec279f464bauL; S64.classify 0x2d65e42c47d72e26uL; S64.classify 0x8198e5749e67f926uL; S64.classify 0x4106673834747e44uL;
  S64.classify 0x197cfdb332a92318uL; S64.classify 0x9ebea84125ac87b6uL; S64.classify 0x4cd805f7a3510c7auL; S64.classify 0x24df999ae06e428euL;
  S64.classify 0x468ff80338330507uL; S64.classify 0x6f34ddf4037a53euL; S64.classify 0x70cd1a408d6993a4uL; S64.classify 0xf85a159743e5c022uL
]

[@@"opaque_to_smt"; FStar.Custard.no_specialize]
let tx_seq : Seq.seq S64.t = Seq.seq_of_list tx_list

let tx_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == tx_seq /\
                     Seq.length (G.static_array_elems a) == 64 })
  = reveal_opaque (`%tx_seq) tx_seq;
    assert_norm (L.length tx_list == 64);
    G.mk_static_array tx_list

let ty_list : list S64.t = [
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x7f0309a804dbec69uL; S64.classify 0xa83b85f73bbad05fuL; S64.classify 0xc6097273ad8e197fuL; S64.classify 0xc097440e5067adc1uL;
  S64.classify 0xe5a367cea1c8cde9uL; S64.classify 0x9d958ba97271abe3uL; S64.classify 0xf3ff7eb63d1615cduL; S64.classify 0xa2280dcef5ae20b0uL;
  S64.classify 0x620e28ff47b50a95uL; S64.classify 0x933e3b01cef03371uL; S64.classify 0xf081bf8599100153uL; S64.classify 0x183be9a0c3a8c8d6uL;
  S64.classify 0xc7c81daa2fd3cf36uL; S64.classify 0xd1319547df89e59fuL; S64.classify 0xb2be8184cd496733uL; S64.classify 0xd5f449eb93d3412buL;
  S64.classify 0x92ad433cfd4b322cuL; S64.classify 0x726aa817ba79ab51uL; S64.classify 0xf96eacd8c1db15ebuL; S64.classify 0xfaf71e910476be63uL;
  S64.classify 0xbaef23918f483f14uL; S64.classify 0x6d2dddfcd137d13buL; S64.classify 0x54cde50ed2743a42uL; S64.classify 0x89a34fc5e4d97e67uL;
  S64.classify 0xb50bd61d9bc49908uL; S64.classify 0x4a9b4a8cf5e2bc1euL; S64.classify 0xeb6cc5f7946f83acuL; S64.classify 0x27da93fcebffab28uL;
  S64.classify 0xb61942e05da59ebuL; S64.classify 0xba3d60a30ddc3722uL; S64.classify 0x7c311cd1742e7f87uL; S64.classify 0x6473ffeef6b01b6euL;
  S64.classify 0xe43b8da0496033cauL; S64.classify 0x994e10ea1cfdd72uL; S64.classify 0xb1ec6d20ba73c0e2uL; S64.classify 0x329c9ecb6bcfad1uL;
  S64.classify 0x5df579c4cd7bbd3fuL; S64.classify 0xef8fb29785591205uL; S64.classify 0x1ded7203e47ac732uL; S64.classify 0xa93dc45ccd1c331auL;
  S64.classify 0x91ac668c024cdd5cuL; S64.classify 0x7ba558e4c1cdfa49uL; S64.classify 0x491d4ce0908fb4dauL; S64.classify 0x7ba869f9f685bde8uL;
  S64.classify 0x8cdc0a8b31ad7eafuL; S64.classify 0x165e86751b915e20uL; S64.classify 0x8e8c269b5d6477f4uL; S64.classify 0xd28d5ade44421b91uL;
  S64.classify 0x4637acc1e37e5447uL; S64.classify 0x2cbc9ecf3e15822uL; S64.classify 0x58a8e98e805aa83cuL; S64.classify 0x73facd6e5595e800uL;
  S64.classify 0xd54dd5dc4d71459cuL; S64.classify 0x1484324f20b8a03cuL; S64.classify 0x7924f2d93174b927uL; S64.classify 0x42b8acbff93ade50uL;
  S64.classify 0x396fc9c2c125a67duL; S64.classify 0x3b7bebf1064bfcbuL; S64.classify 0x7c444592a9806dcbuL; S64.classify 0x1b02614b4487cd54uL
]

[@@"opaque_to_smt"; FStar.Custard.no_specialize]
let ty_seq : Seq.seq S64.t = Seq.seq_of_list ty_list

let ty_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == ty_seq /\
                     Seq.length (G.static_array_elems a) == 64 })
  = reveal_opaque (`%ty_seq) ty_seq;
    assert_norm (L.length ty_list == 64);
    G.mk_static_array ty_list

let tz_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL;
  S64.classify 0x1uL; S64.classify 0xffffffff00000000uL; S64.classify 0xffffffffffffffffuL; S64.classify 0xfffffffeuL
]

[@@"opaque_to_smt"; FStar.Custard.no_specialize]
let tz_seq : Seq.seq S64.t = Seq.seq_of_list tz_list

let tz_arr : (a: G.static_array S64.t
                   { G.static_array_elems a == tz_seq /\
                     Seq.length (G.static_array_elems a) == 64 })
  = reveal_opaque (`%tz_seq) tz_seq;
    assert_norm (L.length tz_list == 64);
    G.mk_static_array tz_list

let shape (_: unit)
  : Lemma (L.length tx_list == 64 /\ L.length ty_list == 64 /\
           L.length tz_list == 64)
  = assert_norm (L.length tx_list == 64);
    assert_norm (L.length ty_list == 64);
    assert_norm (L.length tz_list == 64)

(** {2 The sixteen entries} *)

let ent_0 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 0)
  = shape ();
    assert_norm (L.length (chunk tx_list 0) == nl /\
                 lbnd (chunk tx_list 0) /\
                 leval (chunk tx_list 0) == qx W.e0 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 0) == nl /\
                 lbnd (chunk ty_list 0) /\
                 leval (chunk ty_list 0) == qy W.e0 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 0) == nl /\
                 lbnd (chunk tz_list 0) /\
                 leval (chunk tz_list 0) == qz W.e0 * pow2 256 % P.prime);
    W.e0_ok ();
    ent_lit tx_list ty_list tz_list 0 P.g W.n W.e0

let ent_1 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 1)
  = shape ();
    assert_norm (L.length (chunk tx_list 1) == nl /\
                 lbnd (chunk tx_list 1) /\
                 leval (chunk tx_list 1) == qx W.e1 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 1) == nl /\
                 lbnd (chunk ty_list 1) /\
                 leval (chunk ty_list 1) == qy W.e1 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 1) == nl /\
                 lbnd (chunk tz_list 1) /\
                 leval (chunk tz_list 1) == qz W.e1 * pow2 256 % P.prime);
    W.e1_ok ();
    ent_lit tx_list ty_list tz_list 1 P.g W.n W.e1

let ent_2 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 2)
  = shape ();
    assert_norm (L.length (chunk tx_list 2) == nl /\
                 lbnd (chunk tx_list 2) /\
                 leval (chunk tx_list 2) == qx W.e2 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 2) == nl /\
                 lbnd (chunk ty_list 2) /\
                 leval (chunk ty_list 2) == qy W.e2 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 2) == nl /\
                 lbnd (chunk tz_list 2) /\
                 leval (chunk tz_list 2) == qz W.e2 * pow2 256 % P.prime);
    W.e2_ok ();
    ent_lit tx_list ty_list tz_list 2 P.g W.n W.e2

let ent_3 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 3)
  = shape ();
    assert_norm (L.length (chunk tx_list 3) == nl /\
                 lbnd (chunk tx_list 3) /\
                 leval (chunk tx_list 3) == qx W.e3 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 3) == nl /\
                 lbnd (chunk ty_list 3) /\
                 leval (chunk ty_list 3) == qy W.e3 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 3) == nl /\
                 lbnd (chunk tz_list 3) /\
                 leval (chunk tz_list 3) == qz W.e3 * pow2 256 % P.prime);
    W.e3_ok ();
    ent_lit tx_list ty_list tz_list 3 P.g W.n W.e3

let ent_4 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 4)
  = shape ();
    assert_norm (L.length (chunk tx_list 4) == nl /\
                 lbnd (chunk tx_list 4) /\
                 leval (chunk tx_list 4) == qx W.e4 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 4) == nl /\
                 lbnd (chunk ty_list 4) /\
                 leval (chunk ty_list 4) == qy W.e4 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 4) == nl /\
                 lbnd (chunk tz_list 4) /\
                 leval (chunk tz_list 4) == qz W.e4 * pow2 256 % P.prime);
    W.e4_ok ();
    ent_lit tx_list ty_list tz_list 4 P.g W.n W.e4

let ent_5 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 5)
  = shape ();
    assert_norm (L.length (chunk tx_list 5) == nl /\
                 lbnd (chunk tx_list 5) /\
                 leval (chunk tx_list 5) == qx W.e5 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 5) == nl /\
                 lbnd (chunk ty_list 5) /\
                 leval (chunk ty_list 5) == qy W.e5 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 5) == nl /\
                 lbnd (chunk tz_list 5) /\
                 leval (chunk tz_list 5) == qz W.e5 * pow2 256 % P.prime);
    W.e5_ok ();
    ent_lit tx_list ty_list tz_list 5 P.g W.n W.e5

let ent_6 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 6)
  = shape ();
    assert_norm (L.length (chunk tx_list 6) == nl /\
                 lbnd (chunk tx_list 6) /\
                 leval (chunk tx_list 6) == qx W.e6 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 6) == nl /\
                 lbnd (chunk ty_list 6) /\
                 leval (chunk ty_list 6) == qy W.e6 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 6) == nl /\
                 lbnd (chunk tz_list 6) /\
                 leval (chunk tz_list 6) == qz W.e6 * pow2 256 % P.prime);
    W.e6_ok ();
    ent_lit tx_list ty_list tz_list 6 P.g W.n W.e6

let ent_7 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 7)
  = shape ();
    assert_norm (L.length (chunk tx_list 7) == nl /\
                 lbnd (chunk tx_list 7) /\
                 leval (chunk tx_list 7) == qx W.e7 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 7) == nl /\
                 lbnd (chunk ty_list 7) /\
                 leval (chunk ty_list 7) == qy W.e7 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 7) == nl /\
                 lbnd (chunk tz_list 7) /\
                 leval (chunk tz_list 7) == qz W.e7 * pow2 256 % P.prime);
    W.e7_ok ();
    ent_lit tx_list ty_list tz_list 7 P.g W.n W.e7

let ent_8 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 8)
  = shape ();
    assert_norm (L.length (chunk tx_list 8) == nl /\
                 lbnd (chunk tx_list 8) /\
                 leval (chunk tx_list 8) == qx W.e8 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 8) == nl /\
                 lbnd (chunk ty_list 8) /\
                 leval (chunk ty_list 8) == qy W.e8 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 8) == nl /\
                 lbnd (chunk tz_list 8) /\
                 leval (chunk tz_list 8) == qz W.e8 * pow2 256 % P.prime);
    W.e8_ok ();
    ent_lit tx_list ty_list tz_list 8 P.g W.n W.e8

let ent_9 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 9)
  = shape ();
    assert_norm (L.length (chunk tx_list 9) == nl /\
                 lbnd (chunk tx_list 9) /\
                 leval (chunk tx_list 9) == qx W.e9 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 9) == nl /\
                 lbnd (chunk ty_list 9) /\
                 leval (chunk ty_list 9) == qy W.e9 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 9) == nl /\
                 lbnd (chunk tz_list 9) /\
                 leval (chunk tz_list 9) == qz W.e9 * pow2 256 % P.prime);
    W.e9_ok ();
    ent_lit tx_list ty_list tz_list 9 P.g W.n W.e9

let ent_10 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 10)
  = shape ();
    assert_norm (L.length (chunk tx_list 10) == nl /\
                 lbnd (chunk tx_list 10) /\
                 leval (chunk tx_list 10) == qx W.e10 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 10) == nl /\
                 lbnd (chunk ty_list 10) /\
                 leval (chunk ty_list 10) == qy W.e10 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 10) == nl /\
                 lbnd (chunk tz_list 10) /\
                 leval (chunk tz_list 10) == qz W.e10 * pow2 256 % P.prime);
    W.e10_ok ();
    ent_lit tx_list ty_list tz_list 10 P.g W.n W.e10

let ent_11 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 11)
  = shape ();
    assert_norm (L.length (chunk tx_list 11) == nl /\
                 lbnd (chunk tx_list 11) /\
                 leval (chunk tx_list 11) == qx W.e11 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 11) == nl /\
                 lbnd (chunk ty_list 11) /\
                 leval (chunk ty_list 11) == qy W.e11 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 11) == nl /\
                 lbnd (chunk tz_list 11) /\
                 leval (chunk tz_list 11) == qz W.e11 * pow2 256 % P.prime);
    W.e11_ok ();
    ent_lit tx_list ty_list tz_list 11 P.g W.n W.e11

let ent_12 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 12)
  = shape ();
    assert_norm (L.length (chunk tx_list 12) == nl /\
                 lbnd (chunk tx_list 12) /\
                 leval (chunk tx_list 12) == qx W.e12 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 12) == nl /\
                 lbnd (chunk ty_list 12) /\
                 leval (chunk ty_list 12) == qy W.e12 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 12) == nl /\
                 lbnd (chunk tz_list 12) /\
                 leval (chunk tz_list 12) == qz W.e12 * pow2 256 % P.prime);
    W.e12_ok ();
    ent_lit tx_list ty_list tz_list 12 P.g W.n W.e12

let ent_13 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 13)
  = shape ();
    assert_norm (L.length (chunk tx_list 13) == nl /\
                 lbnd (chunk tx_list 13) /\
                 leval (chunk tx_list 13) == qx W.e13 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 13) == nl /\
                 lbnd (chunk ty_list 13) /\
                 leval (chunk ty_list 13) == qy W.e13 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 13) == nl /\
                 lbnd (chunk tz_list 13) /\
                 leval (chunk tz_list 13) == qz W.e13 * pow2 256 % P.prime);
    W.e13_ok ();
    ent_lit tx_list ty_list tz_list 13 P.g W.n W.e13

let ent_14 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 14)
  = shape ();
    assert_norm (L.length (chunk tx_list 14) == nl /\
                 lbnd (chunk tx_list 14) /\
                 leval (chunk tx_list 14) == qx W.e14 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 14) == nl /\
                 lbnd (chunk ty_list 14) /\
                 leval (chunk ty_list 14) == qy W.e14 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 14) == nl /\
                 lbnd (chunk tz_list 14) /\
                 leval (chunk tz_list 14) == qz W.e14 * pow2 256 % P.prime);
    W.e14_ok ();
    ent_lit tx_list ty_list tz_list 14 P.g W.n W.e14

let ent_15 (_: unit)
  : Lemma (ent (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
               (Seq.seq_of_list tz_list) P.g W.n 15)
  = shape ();
    assert_norm (L.length (chunk tx_list 15) == nl /\
                 lbnd (chunk tx_list 15) /\
                 leval (chunk tx_list 15) == qx W.e15 * pow2 256 % P.prime);
    assert_norm (L.length (chunk ty_list 15) == nl /\
                 lbnd (chunk ty_list 15) /\
                 leval (chunk ty_list 15) == qy W.e15 * pow2 256 % P.prime);
    assert_norm (L.length (chunk tz_list 15) == nl /\
                 lbnd (chunk tz_list 15) /\
                 leval (chunk tz_list 15) == qz W.e15 * pow2 256 % P.prime);
    W.e15_ok ();
    ent_lit tx_list ty_list tz_list 15 P.g W.n W.e15

(** {2 The table} *)

let reveal_seqs (_: unit)
  : Lemma (tx_seq == Seq.seq_of_list tx_list /\
           ty_seq == Seq.seq_of_list ty_list /\
           tz_seq == Seq.seq_of_list tz_list)
  = reveal_opaque (`%tx_seq) tx_seq;
    reveal_opaque (`%ty_seq) ty_seq;
    reveal_opaque (`%tz_seq) tz_seq

let tbl_ok (_: unit)
  : Lemma (tok tx_seq ty_seq tz_seq P.g (pow2 192) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) P.g W.n

#pop-options
