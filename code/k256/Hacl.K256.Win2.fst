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

(** The fixed-base window's third table, compiled in.

    Sixteen multiples of [2^128 G], three arrays of eighty limbs, laid
    out the way {!Hacl.K256.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.K256.Win2} says what the sixteen
    points are and {!Hacl.K256.WinTable} turns a list of limbs into one of
    them, so what is left here is sixteen entries of three [assert_norm]s
    each, every one of them arithmetic on a literal list that the
    normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried two hundred and forty fifty-two-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.K256.Win2

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
module W = Spec.K256.Win2

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The three arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0xb444c9ec4c0dauL; S64.classify 0x78723ea3351b7uL; S64.classify 0x81f162ee88c56uL; S64.classify 0x5f339239c1ad9uL; S64.classify 0x8f68b9d2f63buL;
  S64.classify 0x47df84cf27076uL; S64.classify 0xade7627eaee68uL; S64.classify 0xfd9af59d89858uL; S64.classify 0x8158fcafebe77uL; S64.classify 0x4d49aefd784euL;
  S64.classify 0x2b8edd23809fauL; S64.classify 0xb351d954be18euL; S64.classify 0x2451f08fd845cuL; S64.classify 0x9f228ba93363fuL; S64.classify 0x38381dbe2e50uL;
  S64.classify 0xbcb5729b62026uL; S64.classify 0xe0889d1d4ee8duL; S64.classify 0xf5c5aa78d2a3duL; S64.classify 0x6f8537d6619e1uL; S64.classify 0x7564539e85d5uL;
  S64.classify 0x4264897c2a310uL; S64.classify 0xa5401226303eauL; S64.classify 0xa4699a1f186aeuL; S64.classify 0x2ae6f6921b82auL; S64.classify 0x49262724e437uL;
  S64.classify 0x66c1903663da4uL; S64.classify 0x919f5d0b81f81uL; S64.classify 0xc44aa2ba5a362uL; S64.classify 0x705e6808a6ed7uL; S64.classify 0x6a664a356aa5uL;
  S64.classify 0x4b079cebd2d31uL; S64.classify 0x56ff06db8d138uL; S64.classify 0x477e2f84dcc1auL; S64.classify 0xc90d5e253b3euL; S64.classify 0xe306568c1a24uL;
  S64.classify 0x4dacd57b4a278uL; S64.classify 0x5f1ff4082b536uL; S64.classify 0xad9ccc878f61auL; S64.classify 0x27796746ff301uL; S64.classify 0x210a917ad9dfuL;
  S64.classify 0xc39e363136b0uL; S64.classify 0xd9aab41dd9c53uL; S64.classify 0x3fbd63374ebf8uL; S64.classify 0xcefc271b0e762uL; S64.classify 0x3b9e100e2428uL;
  S64.classify 0x8eb53dd90124euL; S64.classify 0x685281c85dea9uL; S64.classify 0xdb38156c1e802uL; S64.classify 0x554177e9a1946uL; S64.classify 0x7aeaca93c06cuL;
  S64.classify 0x8f0472f485d3fuL; S64.classify 0x688107beee960uL; S64.classify 0x5dedef717ca07uL; S64.classify 0xc9a92b76ca80fuL; S64.classify 0xbb0aad49712auL;
  S64.classify 0x702d505ed815euL; S64.classify 0xabc1c017b470fuL; S64.classify 0x9547ad166f440uL; S64.classify 0x4a32ebb5fad21uL; S64.classify 0x5568dac679f7uL;
  S64.classify 0xed33a36718dc9uL; S64.classify 0x4db01123de4aeuL; S64.classify 0xafe0113e1e58buL; S64.classify 0xfcc0d4e8eb197uL; S64.classify 0x79090ac8e4eeuL;
  S64.classify 0xc1bdc2e44a0c8uL; S64.classify 0x402ee29932abeuL; S64.classify 0xc7436c32c9be7uL; S64.classify 0x943cbc9bae600uL; S64.classify 0x601e9e884807uL;
  S64.classify 0x9694c7f60c7d1uL; S64.classify 0xe7cd775ad2a26uL; S64.classify 0x549ba668dd71duL; S64.classify 0x7b551c03dbbceuL; S64.classify 0xe77c81ade9f9uL
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
  S64.classify 0xcbf79501fff82uL; S64.classify 0xfe95510bfdf23uL; S64.classify 0x6be215dbbea2cuL; S64.classify 0x3986de1d90c2buL; S64.classify 0x662a9f2dba06uL;
  S64.classify 0xb66203aa781euL; S64.classify 0x1a7df4d8466b9uL; S64.classify 0x59ca6f06e0f2duL; S64.classify 0xd135e723f2103uL; S64.classify 0xcd32fc59a10duL;
  S64.classify 0x7518331fed52uL; S64.classify 0xcb32d8f24dbd7uL; S64.classify 0x20eb1cc3681fcuL; S64.classify 0x17dcb09405a55uL; S64.classify 0xe4a32d0a0fb9uL;
  S64.classify 0x2c8fadace0cf3uL; S64.classify 0xd954b79f33417uL; S64.classify 0xa722925684aacuL; S64.classify 0xb3c65231df524uL; S64.classify 0xc1d685413749uL;
  S64.classify 0x1b6815e27ded0uL; S64.classify 0x12a75ff8ce0c4uL; S64.classify 0x714303b6d1636uL; S64.classify 0xabf95a2cfa569uL; S64.classify 0x1337e773bca7uL;
  S64.classify 0x313fb33fc22c4uL; S64.classify 0x127e6c04c9c28uL; S64.classify 0x6bf0cd5089916uL; S64.classify 0xe98b29f86ec19uL; S64.classify 0x449a125954fduL;
  S64.classify 0xb408392546e44uL; S64.classify 0x42be373826692uL; S64.classify 0xf7d0db6ffbc80uL; S64.classify 0x4260888f2b107uL; S64.classify 0xeac6fe37893uL;
  S64.classify 0x713fd0c7b2231uL; S64.classify 0x1aaff20bfc7f2uL; S64.classify 0x8d6737d3789e6uL; S64.classify 0xe57b7a39be81fuL; S64.classify 0x670e1b5450b5uL;
  S64.classify 0xec16f6cdbbc8auL; S64.classify 0xa33ad31f81953uL; S64.classify 0xf475b26a2ae28uL; S64.classify 0xbb71df1533eb8uL; S64.classify 0xfafb98152d16uL;
  S64.classify 0x781022021e31uL; S64.classify 0xf9b90a904b3f5uL; S64.classify 0x6c1d95159bc1buL; S64.classify 0x90f04facaff04uL; S64.classify 0xdfb29b190c13uL;
  S64.classify 0x392503ca2f975uL; S64.classify 0xfa31670bffe79uL; S64.classify 0x297da34895a5auL; S64.classify 0x54798ecd201f7uL; S64.classify 0xea699c53c583uL;
  S64.classify 0xbf64c00602df0uL; S64.classify 0xeee2582151d9buL; S64.classify 0xd073f2beb05f7uL; S64.classify 0xba64580d6fe01uL; S64.classify 0x7a85f8742788uL;
  S64.classify 0x322b11cfae7c5uL; S64.classify 0xb70ba9008b963uL; S64.classify 0xd9aaa56dd36afuL; S64.classify 0x5b8f13d816cbcuL; S64.classify 0xeaab722b9190uL;
  S64.classify 0x93412ba00e557uL; S64.classify 0x5a6b46e659547uL; S64.classify 0xffabbb1424e0cuL; S64.classify 0x8ecc714b8cfa9uL; S64.classify 0x5a7a22aa6fdcuL;
  S64.classify 0x581f282d72449uL; S64.classify 0xf71c2986d34ecuL; S64.classify 0xea81543631470uL; S64.classify 0x1321c5fc3b323uL; S64.classify 0x3acf1478eef8uL
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
  : Lemma (tok tx_seq ty_seq tz_seq K.g (pow2 128) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) K.g W.n

#pop-options
