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

    Sixteen multiples of [G], three arrays of sixty-four limbs laid
    out the way {!Hacl.P256.PointWin.entry} reads them: entry [d] is limbs
    [4d] through [4d + 3], in Montgomery form.  {!Spec.P256.Win0} says what
    the sixteen points are and {!Hacl.P256.WinTable} turns a list of limbs
    into one of them, so what is left here is three [assert_norm]s per
    entry, each arithmetic on a literal list.  Nothing below mentions the
    curve. *)
module Hacl.P256.Win0

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
module W = Spec.P256.Win0

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The three arrays} *)

let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x79e730d418a9143cuL; S64.classify 0x75ba95fc5fedb601uL; S64.classify 0x79fb732b77622510uL; S64.classify 0x18905f76a53755c6uL;
  S64.classify 0x850046d410ddd64duL; S64.classify 0xaa6ae3c1a433827duL; S64.classify 0x732205038d1490d9uL; S64.classify 0xf6bb32e43dcf3a3buL;
  S64.classify 0xffac3f904eebc127uL; S64.classify 0xb027f84a087d81fbuL; S64.classify 0x66ad77dd87cbbc98uL; S64.classify 0x26936a3fb6ff747euL;
  S64.classify 0x74b0b50d46918dccuL; S64.classify 0x4650a6edc623c173uL; S64.classify 0xcdaacace8100af2uL; S64.classify 0x577362f541b0176buL;
  S64.classify 0xbe1b8aaec45c61f5uL; S64.classify 0x90ec649a94b9537duL; S64.classify 0x941cb5aad076c20cuL; S64.classify 0xc9079605890523c8uL;
  S64.classify 0x403947373e77664auL; S64.classify 0x55ae744f346cee3euL; S64.classify 0xd50a961a5b17a3aduL; S64.classify 0x13074b5954213673uL;
  S64.classify 0x746354ea0173b4fuL; S64.classify 0x2bd20213d23c00f7uL; S64.classify 0xf43eaab50c23bb08uL; S64.classify 0x13ba5119c3123e03uL;
  S64.classify 0x27f14cd19499a78fuL; S64.classify 0x462ab5c56f9b3455uL; S64.classify 0x8f90f02af02cfc6buL; S64.classify 0xb763891eb265230duL;
  S64.classify 0x75c96e8f264e20e8uL; S64.classify 0xabe6bfed59a7a841uL; S64.classify 0x2cc09c0444c8eb00uL; S64.classify 0xe05b3080f0c4e16buL;
  S64.classify 0x2c18dbd19dc21ec8uL; S64.classify 0x98f9868a0fcf8139uL; S64.classify 0x737d2cd648250b49uL; S64.classify 0xcc61c94724b3428fuL;
  S64.classify 0xea7d260a6245e404uL; S64.classify 0x9de407956e7fdfe0uL; S64.classify 0x1ff3a4158dac1ab5uL; S64.classify 0x3e7090f1649c9073uL;
  S64.classify 0x4b71aa7d2697768uL; S64.classify 0xabdedef5ca345a33uL; S64.classify 0x2409d29dee37385euL; S64.classify 0x4ee1df77cb83e156uL;
  S64.classify 0xccc425634b2ed709uL; S64.classify 0xe356769856fd30duL; S64.classify 0xbcbcd43f559e9811uL; S64.classify 0x738477ac5395b759uL;
  S64.classify 0xa242a35bb0cf664auL; S64.classify 0x126e48f77f9707e3uL; S64.classify 0x1717bf54c6832660uL; S64.classify 0xfaae7332fd12c72euL;
  S64.classify 0x72bcd8b7bc60055buL; S64.classify 0x3cc23ee56e27e4buL; S64.classify 0xee337424e4819370uL; S64.classify 0xe2aa0e430ad3da09uL
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
  S64.classify 0xddf25357ce95560auL; S64.classify 0x8b4ab8e4ba19e45cuL; S64.classify 0xd2e88688dd21f325uL; S64.classify 0x8571ff1825885d85uL;
  S64.classify 0x2f3648d361bee1a5uL; S64.classify 0x152cd7cbeb236ff8uL; S64.classify 0x19a8fb0e92042dbeuL; S64.classify 0x78c577510a5b8a3buL;
  S64.classify 0xb04c5c1fc983a7ebuL; S64.classify 0x583e47ad0861fe1auL; S64.classify 0x788208311a2ee98euL; S64.classify 0xd5f06a29e587cc07uL;
  S64.classify 0x2d96f24ce4cbaba6uL; S64.classify 0x17628471fad6f447uL; S64.classify 0x6b6c36dee5ddd22euL; S64.classify 0x84b14c394c5ab863uL;
  S64.classify 0xeb309b4ae7ba4f10uL; S64.classify 0x73c568efe5eb882buL; S64.classify 0x3540a9877e7a1f68uL; S64.classify 0x73a076bb2dd1e916uL;
  S64.classify 0x93d36220d377e44buL; S64.classify 0x299c2b53adff14b5uL; S64.classify 0xf424d44cef639f11uL; S64.classify 0xa4c9916d4a07f75fuL;
  S64.classify 0x2847d0303f5b9d4duL; S64.classify 0x6742f2f25da67bdduL; S64.classify 0xef933bdc77c94195uL; S64.classify 0xeaedd9156e240867uL;
  S64.classify 0xf59da3a9532d4977uL; S64.classify 0x21e3327dcf9eba15uL; S64.classify 0x123c7b84be60bbf0uL; S64.classify 0x56ec12f27706df76uL;
  S64.classify 0x1eb7777aa45f3314uL; S64.classify 0x56af7bedce5d45e3uL; S64.classify 0x2b6e019a88b12f1auL; S64.classify 0x86659cdfd835f9buL;
  S64.classify 0xc2b407880dd9e76uL; S64.classify 0xc43a8991383fbe08uL; S64.classify 0x5f7d2d65779be5d2uL; S64.classify 0x78719a54eb3b4ab5uL;
  S64.classify 0x1a7685612b944e88uL; S64.classify 0x250f939ee57f61c8uL; S64.classify 0xc0daa891ead643duL; S64.classify 0x68930023e125b88euL;
  S64.classify 0xcac12d91cbb5b43uL; S64.classify 0x170ed2f6ca895637uL; S64.classify 0x28228cfa8ade6d66uL; S64.classify 0x7ff57c9553238acauL;
  S64.classify 0x35752b90c00ee17fuL; S64.classify 0x68748390742ed2e3uL; S64.classify 0x7cd06422bd1f5bc1uL; S64.classify 0xfbc08769c9e7b797uL;
  S64.classify 0x27b52db7995d586buL; S64.classify 0xbe29569e832237c2uL; S64.classify 0xe8e4193e2a65e7dbuL; S64.classify 0x152706dc2eaa1bbbuL;
  S64.classify 0x40b8524f6383c45duL; S64.classify 0xd766355442a41b25uL; S64.classify 0x64efa6de778a4797uL; S64.classify 0x2042170a7079adf4uL
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
  : Lemma (tok tx_seq ty_seq tz_seq P.g (1) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) P.g W.n

#pop-options
