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

    Sixteen multiples of [2^128 g], four arrays of eighty limbs, laid out
    the way {!Hacl.Ed25519.PointWin.entry} reads them: entry [d] is limbs
    [5d] through [5d + 4].  {!Spec.Ed25519.Win2} says what the sixteen
    points are and {!Hacl.Ed25519.WinTable} turns a list of limbs into one
    of them, so what is left here is sixteen entries of four
    [assert_norm]s each, every one of them arithmetic on a literal list
    that the normaliser does in a step.

    Nothing below mentions the field or the curve, which is the point of
    the split: a file that carried three hundred and twenty fifty-one-bit
    literals {i and} the addition law in one solver context would not
    terminate. *)
module Hacl.Ed25519.Win2

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
module W = Spec.Ed25519.Win2

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The four arrays} *)

(** The [x] coordinates. *)
let tx_list : list S64.t = [
  S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL; S64.classify 0x0uL;
  S64.classify 0x47ae60b7e824uL; S64.classify 0x1385ce47cbf90uL; S64.classify 0x538a682639a17uL; S64.classify 0x1964a969cc270uL; S64.classify 0x4c27afff3c45fuL;
  S64.classify 0x7d1b43224e085uL; S64.classify 0x651f7f44d3f9duL; S64.classify 0x1f5bb93da54b1uL; S64.classify 0x57bd040abfbc8uL; S64.classify 0x786be30733efduL;
  S64.classify 0x5ca89f193c7c7uL; S64.classify 0x190eadb296624uL; S64.classify 0x613c26eba92ebuL; S64.classify 0x28e517e9d52c5uL; S64.classify 0x9c186afb8339uL;
  S64.classify 0x22f04c2eaa13uL; S64.classify 0x57d69a3366d97uL; S64.classify 0x72376731a9341uL; S64.classify 0x499efc4abc0aduL; S64.classify 0x21fee4804968auL;
  S64.classify 0x1e3a2b12d4f17uL; S64.classify 0x4b2e7932aa923uL; S64.classify 0x22727a3b68433uL; S64.classify 0x415c09f01b2euL; S64.classify 0x4a2e1f96eee4euL;
  S64.classify 0x1449ec0ec3464uL; S64.classify 0x54da0a6d415e8uL; S64.classify 0x27490d51894c3uL; S64.classify 0x3a33578cadec3uL; S64.classify 0x5dbd3bf95494duL;
  S64.classify 0xbadc76ed5685uL; S64.classify 0x35fa4ebc2326euL; S64.classify 0x5dc73aed63804uL; S64.classify 0x1e078f96abefcuL; S64.classify 0x4b3702044575duL;
  S64.classify 0x7136e1146b3dfuL; S64.classify 0x59e3baac9c516uL; S64.classify 0x25223e30d62b6uL; S64.classify 0x5b57250cc032fuL; S64.classify 0x77fe8a5d490afuL;
  S64.classify 0x35c8de42dce20uL; S64.classify 0x4f3903f2d597fuL; S64.classify 0x3dd85b13817fduL; S64.classify 0x19ccf62218b91uL; S64.classify 0x3df71993fb635uL;
  S64.classify 0xcddd479736b0uL; S64.classify 0x216ab397f0497uL; S64.classify 0x1e1f35503332auL; S64.classify 0x6f3f6da3a0cf9uL; S64.classify 0x8f8726bcbbdeuL;
  S64.classify 0x2e9ccb983430cuL; S64.classify 0x4c8d99999422duL; S64.classify 0x7549b92767f0cuL; S64.classify 0x68f157021163buL; S64.classify 0x4cf0cb74c7099uL;
  S64.classify 0x5f4ed0d8b6abuL; S64.classify 0x371a4b0a6056cuL; S64.classify 0x570359ac26890uL; S64.classify 0x61f05be0bd307uL; S64.classify 0x54d6778da5f0fuL;
  S64.classify 0x14382c7d59993uL; S64.classify 0x7ae9d998c6fb0uL; S64.classify 0x2599ebd8e7a64uL; S64.classify 0x6a67d4c5972uL; S64.classify 0x390414491821buL;
  S64.classify 0x682e2c99e70f0uL; S64.classify 0x404469b48712cuL; S64.classify 0x64667988eeefuL; S64.classify 0x40539d99c51bduL; S64.classify 0x1432670aad334uL;
  S64.classify 0x7d1ff333057e4uL; S64.classify 0x5576fdf5ab79fuL; S64.classify 0x6b385a10d53e8uL; S64.classify 0x40892bfbfb2d6uL; S64.classify 0x29b0c323e8469uL
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
  S64.classify 0x2bd114bf5a66buL; S64.classify 0x3ca349893cb77uL; S64.classify 0x30a70ea4342f8uL; S64.classify 0x43ecaf88f5b13uL; S64.classify 0x5f2c99e6526dcuL;
  S64.classify 0x30712c63e2736uL; S64.classify 0x7d673ad37c9d5uL; S64.classify 0x3f4211ca9f022uL; S64.classify 0x42d9a138766eauL; S64.classify 0x653a5f772f349uL;
  S64.classify 0x49a357f7b062fuL; S64.classify 0x577daa9fe2346uL; S64.classify 0x61928780aa0a9uL; S64.classify 0x1a9c9a34ad8a4uL; S64.classify 0x6137b0746027buL;
  S64.classify 0xd3e930901700uL; S64.classify 0x7512e5846260cuL; S64.classify 0x2160ce6f694d9uL; S64.classify 0x28ea0b62ed0a8uL; S64.classify 0x500b7740072cbuL;
  S64.classify 0x4b832ac846fc4uL; S64.classify 0x22e66b4cc889auL; S64.classify 0x77c36a3708a79uL; S64.classify 0x62dc64a88c45fuL; S64.classify 0x6c3f24822e185uL;
  S64.classify 0x4e1c737e25b77uL; S64.classify 0x54f6f73f1826fuL; S64.classify 0x264aae68d0b38uL; S64.classify 0x5d8431e6c6054uL; S64.classify 0x56f5f77776e9fuL;
  S64.classify 0x27acd289b820uL; S64.classify 0x1f5f99c524904uL; S64.classify 0x581aabf8db72cuL; S64.classify 0x17a97a13d4072uL; S64.classify 0x54333c50acf33uL;
  S64.classify 0x5c5afa5f50246uL; S64.classify 0x7c146a8b74daeuL; S64.classify 0x48636448ab327uL; S64.classify 0x18b45600199cauL; S64.classify 0x3c530f01e039fuL;
  S64.classify 0x722692a09fa98uL; S64.classify 0x5439e0021cf78uL; S64.classify 0x51c729edb2aauL; S64.classify 0x69ce48b27d832uL; S64.classify 0x7dcf8776aa205uL;
  S64.classify 0x2aefea8b4c884uL; S64.classify 0x5d470b1df666fuL; S64.classify 0x25d20223888c0uL; S64.classify 0x3dc111cc068uL; S64.classify 0x11f808ca3d11fuL;
  S64.classify 0x507c5e74f9735uL; S64.classify 0x1c5016a149617uL; S64.classify 0x7ca26a562ea69uL; S64.classify 0x30dc2fa516024uL; S64.classify 0x5df4e013e64uL;
  S64.classify 0x2806f9009c619uL; S64.classify 0x675cf4e8fcfd1uL; S64.classify 0x48df9ce5e08e4uL; S64.classify 0x4ecc62b32ac58uL; S64.classify 0x5f988a1f2c959uL;
  S64.classify 0x3facbdff0df5auL; S64.classify 0x2b4be0de64279uL; S64.classify 0x6de9ff12603a1uL; S64.classify 0x78ebbb820348buL; S64.classify 0x69710b1edcd36uL;
  S64.classify 0x2cfced8a71cd3uL; S64.classify 0x3a90088ba560buL; S64.classify 0x321b83e07eceauL; S64.classify 0x597b7bd55183euL; S64.classify 0x6ef2e391ba981uL;
  S64.classify 0x60930c75ce1cuL; S64.classify 0x5cd42b095b8efuL; S64.classify 0x66c89b07042b5uL; S64.classify 0x2e5c6e0a952e8uL; S64.classify 0x39a797181bd8auL
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
  S64.classify 0x731c946f1338auL; S64.classify 0x4ccc75b53d3cuL; S64.classify 0x6492da851e192uL; S64.classify 0x17ea70ab0003uL; S64.classify 0x5a164fd0bf46uL;
  S64.classify 0x4e817719f64c8uL; S64.classify 0x2aaf757adc018uL; S64.classify 0x74f63b25b13b9uL; S64.classify 0x74586c8334d2duL; S64.classify 0x12c73ed34d313uL;
  S64.classify 0x562410e8ef362uL; S64.classify 0x7e7115a47163uL; S64.classify 0x63082b8bba0eduL; S64.classify 0x6c576f02a36f1uL; S64.classify 0x572c78d37f263uL;
  S64.classify 0xa584e1b381f8uL; S64.classify 0x2dc40f2fe1bb0uL; S64.classify 0x7a252afa919c4uL; S64.classify 0x7f8344713f782uL; S64.classify 0x198588f68c188uL;
  S64.classify 0xb2d34c797678uL; S64.classify 0x6b7b48f082a56uL; S64.classify 0x320892791968auL; S64.classify 0x130d94db67890uL; S64.classify 0x2ddebaccef8dduL;
  S64.classify 0x4643a2e2f2569uL; S64.classify 0x611669774e72uL; S64.classify 0x6e17d81aef50euL; S64.classify 0x60a92020f5168uL; S64.classify 0x5844f533bb02buL;
  S64.classify 0x271da3c1535e8uL; S64.classify 0x50808b29d87a9uL; S64.classify 0x11653cf3c08euL; S64.classify 0xee45253cfdc0uL; S64.classify 0x1d1cecdf260f8uL;
  S64.classify 0x566861b52ad2cuL; S64.classify 0x752b00120dfc5uL; S64.classify 0x73bad60eb6373uL; S64.classify 0x40fc2927931ffuL; S64.classify 0x25a2c58c77260uL;
  S64.classify 0xcb8d6970e9b5uL; S64.classify 0x1e291b140584auL; S64.classify 0x607784546a446uL; S64.classify 0xf74fa2c522beuL; S64.classify 0x46c49dfefb5beuL;
  S64.classify 0x181684b2460b6uL; S64.classify 0x4e00bfc81618cuL; S64.classify 0x615fe58d16190uL; S64.classify 0x3d554d029d535uL; S64.classify 0x308a2fc2d525buL;
  S64.classify 0x68bbe81be9cc8uL; S64.classify 0x6d87286f756c8uL; S64.classify 0x3f807a456a8fuL; S64.classify 0x701ac2b9e248euL; S64.classify 0x25e0b22e23b82uL;
  S64.classify 0x47545bc03c212uL; S64.classify 0x63a742f44ee6buL; S64.classify 0x5735298f03895uL; S64.classify 0x25e3cda9e8ca9uL; S64.classify 0x28ae8803cb684uL;
  S64.classify 0x4e273fb7ae6buL; S64.classify 0x349abbea2b788uL; S64.classify 0x24a4e6a4b330duL; S64.classify 0xc75513396fe7uL; S64.classify 0x7eb4c6c7e9177uL;
  S64.classify 0x7120e749c98bauL; S64.classify 0x2064fa141e024uL; S64.classify 0x34fe13bbecea0uL; S64.classify 0x169b35efc6bauL; S64.classify 0x4a7b37baf1f65uL;
  S64.classify 0x25af544a9a94buL; S64.classify 0x7578b03b6c66cuL; S64.classify 0x52bd498306d8uL; S64.classify 0x154bac09b10d1uL; S64.classify 0x4446f2c6af923uL
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
  : Lemma (tok tx_seq ty_seq tz_seq tt_seq E.g (pow2 128) 16)
  = reveal_seqs ();
    ent_0 (); ent_1 (); ent_2 (); ent_3 ();
    ent_4 (); ent_5 (); ent_6 (); ent_7 ();
    ent_8 (); ent_9 (); ent_10 (); ent_11 ();
    ent_12 (); ent_13 (); ent_14 (); ent_15 ();
    tok_all (Seq.seq_of_list tx_list) (Seq.seq_of_list ty_list)
            (Seq.seq_of_list tz_list) (Seq.seq_of_list tt_list) E.g W.n

#pop-options
