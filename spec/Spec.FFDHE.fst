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

(** The five RFC 7919 finite-field Diffie-Hellman groups.

    Each modulus is a safe prime of the shape

      p = 2^b - 2^(b-64) + (floor(2^(b-130) * e) + X) * 2^64 - 1

    with [X] the per-group offset the RFC publishes.  The limbs below were
    generated from that formula -- not transcribed from the RFC's hex dump --
    and checked three ways: the top hundred and twenty-eight bits against the
    published value, the bit length, and a Miller-Rabin test on both [p] and
    [(p-1)/2].  The generator is two for every group.

    Limbs are thirty-two bits, least significant first, which is the
    representation [Hacl.Bignum.Base] uses.  Each group appears once as a
    [list] -- that is the spine [Pulse.Lib.GlobalArray.mk_static_array] turns
    into a C array initializer -- and once as the [Seq.lseq] the specification
    talks about, the second being [Seq.seq_of_list] of the first, so the two
    cannot drift. *)
module Spec.FFDHE

module Seq = FStar.Seq
module List = FStar.List.Tot
module U32 = FStar.UInt32
module S32 = Hacl.Secret.UInt32

(** {2 FFDHE-2048} *)

(** The FFDHE-2048 modulus: 2048 bits, 64 limbs. *)
let ffdhe2048_list : list S32.t = [
  S32.classify 0xfffffffful; S32.classify 0xfffffffful; S32.classify 0x61285c97ul; S32.classify 0x886b4238ul;
  S32.classify 0xc1b2effaul; S32.classify 0xc6f34a26ul; S32.classify 0x7d1683b2ul; S32.classify 0xc58ef183ul;
  S32.classify 0x2ec22005ul; S32.classify 0x3bb5fcbcul; S32.classify 0x4c6fad73ul; S32.classify 0xc3fe3b1bul;
  S32.classify 0xeef28183ul; S32.classify 0x8e4f1232ul; S32.classify 0xe98583fful; S32.classify 0x9172fe9cul;
  S32.classify 0x28342f61ul; S32.classify 0xc03404cdul; S32.classify 0xcdf7e2ecul; S32.classify 0x9e02fce1ul;
  S32.classify 0xee0a6d70ul; S32.classify 0x0b07a7c8ul; S32.classify 0x6372bb19ul; S32.classify 0xae56ede7ul;
  S32.classify 0xde394df4ul; S32.classify 0x1d4f42a3ul; S32.classify 0x60d7f468ul; S32.classify 0xb96adab7ul;
  S32.classify 0xb2c8e3fbul; S32.classify 0xd108a94bul; S32.classify 0xb324fb61ul; S32.classify 0xbc0ab182ul;
  S32.classify 0x483a797aul; S32.classify 0x30acca4ful; S32.classify 0x36ade735ul; S32.classify 0x1df158a1ul;
  S32.classify 0xf3efe872ul; S32.classify 0xe2a689daul; S32.classify 0xe0e68b77ul; S32.classify 0x984f0c70ul;
  S32.classify 0x7f57c935ul; S32.classify 0xb557135eul; S32.classify 0x3ded1af3ul; S32.classify 0x85636555ul;
  S32.classify 0x5f066ed0ul; S32.classify 0x2433f51ful; S32.classify 0xd5fd6561ul; S32.classify 0xd3df1ed5ul;
  S32.classify 0xaec4617aul; S32.classify 0xf681b202ul; S32.classify 0x630c75d8ul; S32.classify 0x7d2fe363ul;
  S32.classify 0x249b3ef9ul; S32.classify 0xcc939dceul; S32.classify 0x146433fbul; S32.classify 0xa9e13641ul;
  S32.classify 0xce2d3695ul; S32.classify 0xd8b9c583ul; S32.classify 0x273d3cf1ul; S32.classify 0xafdc5620ul;
  S32.classify 0xa2bb4a9aul; S32.classify 0xadf85458ul; S32.classify 0xfffffffful; S32.classify 0xfffffffful;
]

[@@FStar.Custard.no_specialize]
let ffdhe2048 : Seq.lseq S32.t 64 =
  assert_norm (List.length ffdhe2048_list == 64);
  Seq.seq_of_list ffdhe2048_list

(** {2 FFDHE-3072} *)

(** The FFDHE-3072 modulus: 3072 bits, 96 limbs. *)
let ffdhe3072_list : list S32.t = [
  S32.classify 0xfffffffful; S32.classify 0xfffffffful; S32.classify 0x66c62e37ul; S32.classify 0x25e41d2bul;
  S32.classify 0x3fd59d7cul; S32.classify 0x3c1b20eeul; S32.classify 0xfa53ddeful; S32.classify 0x0abcd06bul;
  S32.classify 0xd5c4484eul; S32.classify 0x1dbf9a42ul; S32.classify 0x9b0deadaul; S32.classify 0xabc52197ul;
  S32.classify 0x22363a0dul; S32.classify 0xe86d2bc5ul; S32.classify 0x9c9df69eul; S32.classify 0x5cae82abul;
  S32.classify 0x71f54bfful; S32.classify 0x64f2e21eul; S32.classify 0xe2d74dd3ul; S32.classify 0xf4fd4452ul;
  S32.classify 0xbc437944ul; S32.classify 0xb4130c93ul; S32.classify 0x85139270ul; S32.classify 0xaefe1309ul;
  S32.classify 0xc186d91cul; S32.classify 0x598cb0faul; S32.classify 0x91f7f7eeul; S32.classify 0x7ad91d26ul;
  S32.classify 0xd6e6c907ul; S32.classify 0x61b46fc9ul; S32.classify 0xf99c0238ul; S32.classify 0xbc34f4deul;
  S32.classify 0x6519035bul; S32.classify 0xde355b3bul; S32.classify 0x611fcfdcul; S32.classify 0x886b4238ul;
  S32.classify 0xc1b2effaul; S32.classify 0xc6f34a26ul; S32.classify 0x7d1683b2ul; S32.classify 0xc58ef183ul;
  S32.classify 0x2ec22005ul; S32.classify 0x3bb5fcbcul; S32.classify 0x4c6fad73ul; S32.classify 0xc3fe3b1bul;
  S32.classify 0xeef28183ul; S32.classify 0x8e4f1232ul; S32.classify 0xe98583fful; S32.classify 0x9172fe9cul;
  S32.classify 0x28342f61ul; S32.classify 0xc03404cdul; S32.classify 0xcdf7e2ecul; S32.classify 0x9e02fce1ul;
  S32.classify 0xee0a6d70ul; S32.classify 0x0b07a7c8ul; S32.classify 0x6372bb19ul; S32.classify 0xae56ede7ul;
  S32.classify 0xde394df4ul; S32.classify 0x1d4f42a3ul; S32.classify 0x60d7f468ul; S32.classify 0xb96adab7ul;
  S32.classify 0xb2c8e3fbul; S32.classify 0xd108a94bul; S32.classify 0xb324fb61ul; S32.classify 0xbc0ab182ul;
  S32.classify 0x483a797aul; S32.classify 0x30acca4ful; S32.classify 0x36ade735ul; S32.classify 0x1df158a1ul;
  S32.classify 0xf3efe872ul; S32.classify 0xe2a689daul; S32.classify 0xe0e68b77ul; S32.classify 0x984f0c70ul;
  S32.classify 0x7f57c935ul; S32.classify 0xb557135eul; S32.classify 0x3ded1af3ul; S32.classify 0x85636555ul;
  S32.classify 0x5f066ed0ul; S32.classify 0x2433f51ful; S32.classify 0xd5fd6561ul; S32.classify 0xd3df1ed5ul;
  S32.classify 0xaec4617aul; S32.classify 0xf681b202ul; S32.classify 0x630c75d8ul; S32.classify 0x7d2fe363ul;
  S32.classify 0x249b3ef9ul; S32.classify 0xcc939dceul; S32.classify 0x146433fbul; S32.classify 0xa9e13641ul;
  S32.classify 0xce2d3695ul; S32.classify 0xd8b9c583ul; S32.classify 0x273d3cf1ul; S32.classify 0xafdc5620ul;
  S32.classify 0xa2bb4a9aul; S32.classify 0xadf85458ul; S32.classify 0xfffffffful; S32.classify 0xfffffffful;
]

[@@FStar.Custard.no_specialize]
let ffdhe3072 : Seq.lseq S32.t 96 =
  assert_norm (List.length ffdhe3072_list == 96);
  Seq.seq_of_list ffdhe3072_list

(** {2 FFDHE-4096} *)

(** The FFDHE-4096 modulus: 4096 bits, 128 limbs. *)
let ffdhe4096_list : list S32.t = [
  S32.classify 0xfffffffful; S32.classify 0xfffffffful; S32.classify 0x5e655f6aul; S32.classify 0xc68a007eul;
  S32.classify 0xf44182e1ul; S32.classify 0x4db5a851ul; S32.classify 0x7f88a46bul; S32.classify 0x8ec9b55aul;
  S32.classify 0xcec97dcful; S32.classify 0x0a8291cdul; S32.classify 0xf98d0accul; S32.classify 0x2a4ecea9ul;
  S32.classify 0x7140003cul; S32.classify 0x1a1db93dul; S32.classify 0x33cb8b7aul; S32.classify 0x092999a3ul;
  S32.classify 0x71ad0038ul; S32.classify 0x6dc778f9ul; S32.classify 0x918130c4ul; S32.classify 0xa907600aul;
  S32.classify 0x2d9e6832ul; S32.classify 0xed6a1e01ul; S32.classify 0xefb4318aul; S32.classify 0x7135c886ul;
  S32.classify 0x7e31cc7aul; S32.classify 0x87f55ba5ul; S32.classify 0x55034004ul; S32.classify 0x7763cf1dul;
  S32.classify 0xd69f6d18ul; S32.classify 0xac7d5f42ul; S32.classify 0xe58857b6ul; S32.classify 0x7930e9e4ul;
  S32.classify 0x164df4fbul; S32.classify 0x6e6f52c3ul; S32.classify 0x669e1ef1ul; S32.classify 0x25e41d2bul;
  S32.classify 0x3fd59d7cul; S32.classify 0x3c1b20eeul; S32.classify 0xfa53ddeful; S32.classify 0x0abcd06bul;
  S32.classify 0xd5c4484eul; S32.classify 0x1dbf9a42ul; S32.classify 0x9b0deadaul; S32.classify 0xabc52197ul;
  S32.classify 0x22363a0dul; S32.classify 0xe86d2bc5ul; S32.classify 0x9c9df69eul; S32.classify 0x5cae82abul;
  S32.classify 0x71f54bfful; S32.classify 0x64f2e21eul; S32.classify 0xe2d74dd3ul; S32.classify 0xf4fd4452ul;
  S32.classify 0xbc437944ul; S32.classify 0xb4130c93ul; S32.classify 0x85139270ul; S32.classify 0xaefe1309ul;
  S32.classify 0xc186d91cul; S32.classify 0x598cb0faul; S32.classify 0x91f7f7eeul; S32.classify 0x7ad91d26ul;
  S32.classify 0xd6e6c907ul; S32.classify 0x61b46fc9ul; S32.classify 0xf99c0238ul; S32.classify 0xbc34f4deul;
  S32.classify 0x6519035bul; S32.classify 0xde355b3bul; S32.classify 0x611fcfdcul; S32.classify 0x886b4238ul;
  S32.classify 0xc1b2effaul; S32.classify 0xc6f34a26ul; S32.classify 0x7d1683b2ul; S32.classify 0xc58ef183ul;
  S32.classify 0x2ec22005ul; S32.classify 0x3bb5fcbcul; S32.classify 0x4c6fad73ul; S32.classify 0xc3fe3b1bul;
  S32.classify 0xeef28183ul; S32.classify 0x8e4f1232ul; S32.classify 0xe98583fful; S32.classify 0x9172fe9cul;
  S32.classify 0x28342f61ul; S32.classify 0xc03404cdul; S32.classify 0xcdf7e2ecul; S32.classify 0x9e02fce1ul;
  S32.classify 0xee0a6d70ul; S32.classify 0x0b07a7c8ul; S32.classify 0x6372bb19ul; S32.classify 0xae56ede7ul;
  S32.classify 0xde394df4ul; S32.classify 0x1d4f42a3ul; S32.classify 0x60d7f468ul; S32.classify 0xb96adab7ul;
  S32.classify 0xb2c8e3fbul; S32.classify 0xd108a94bul; S32.classify 0xb324fb61ul; S32.classify 0xbc0ab182ul;
  S32.classify 0x483a797aul; S32.classify 0x30acca4ful; S32.classify 0x36ade735ul; S32.classify 0x1df158a1ul;
  S32.classify 0xf3efe872ul; S32.classify 0xe2a689daul; S32.classify 0xe0e68b77ul; S32.classify 0x984f0c70ul;
  S32.classify 0x7f57c935ul; S32.classify 0xb557135eul; S32.classify 0x3ded1af3ul; S32.classify 0x85636555ul;
  S32.classify 0x5f066ed0ul; S32.classify 0x2433f51ful; S32.classify 0xd5fd6561ul; S32.classify 0xd3df1ed5ul;
  S32.classify 0xaec4617aul; S32.classify 0xf681b202ul; S32.classify 0x630c75d8ul; S32.classify 0x7d2fe363ul;
  S32.classify 0x249b3ef9ul; S32.classify 0xcc939dceul; S32.classify 0x146433fbul; S32.classify 0xa9e13641ul;
  S32.classify 0xce2d3695ul; S32.classify 0xd8b9c583ul; S32.classify 0x273d3cf1ul; S32.classify 0xafdc5620ul;
  S32.classify 0xa2bb4a9aul; S32.classify 0xadf85458ul; S32.classify 0xfffffffful; S32.classify 0xfffffffful;
]

[@@FStar.Custard.no_specialize]
let ffdhe4096 : Seq.lseq S32.t 128 =
  assert_norm (List.length ffdhe4096_list == 128);
  Seq.seq_of_list ffdhe4096_list

(** {2 FFDHE-6144} *)

(** The FFDHE-6144 modulus: 6144 bits, 192 limbs. *)
let ffdhe6144_list : list S32.t = [
  S32.classify 0xfffffffful; S32.classify 0xfffffffful; S32.classify 0xd0e40e65ul; S32.classify 0xa40e329cul;
  S32.classify 0x7938dad4ul; S32.classify 0xa41d570dul; S32.classify 0xd43161c1ul; S32.classify 0x62a69526ul;
  S32.classify 0x9adb1e69ul; S32.classify 0x3fdd4a8eul; S32.classify 0xdc6b80d6ul; S32.classify 0x5b3b71f9ul;
  S32.classify 0xc6272b04ul; S32.classify 0xec9d1810ul; S32.classify 0xcacef403ul; S32.classify 0x8ccf2dd5ul;
  S32.classify 0xc95b9117ul; S32.classify 0xe49f5235ul; S32.classify 0xb854338aul; S32.classify 0x505dc82dul;
  S32.classify 0x1562a846ul; S32.classify 0x62292c31ul; S32.classify 0x6ae77f5eul; S32.classify 0xd72b0374ul;
  S32.classify 0x462d538cul; S32.classify 0xf9c9091bul; S32.classify 0x47a67cbeul; S32.classify 0x0ae8db58ul;
  S32.classify 0x22611682ul; S32.classify 0xb3a739c1ul; S32.classify 0x2a281bf6ul; S32.classify 0xeeaac023ul;
  S32.classify 0x77caf992ul; S32.classify 0x94c6651eul; S32.classify 0x94b2bbc1ul; S32.classify 0x763e4e4bul;
  S32.classify 0x0077d9b4ul; S32.classify 0x587e38daul; S32.classify 0x183023c3ul; S32.classify 0x7fb29f8cul;
  S32.classify 0xf9e3a26eul; S32.classify 0x0abec1fful; S32.classify 0x350511e3ul; S32.classify 0xa00ef092ul;
  S32.classify 0xdb6340d8ul; S32.classify 0xb855322eul; S32.classify 0xa9a96910ul; S32.classify 0xa52471f7ul;
  S32.classify 0x4cfdb477ul; S32.classify 0x388147fbul; S32.classify 0x4e46041ful; S32.classify 0x9b1f5c3eul;
  S32.classify 0xfccfec71ul; S32.classify 0xcdad0657ul; S32.classify 0x4c701c3aul; S32.classify 0xb38e8c33ul;
  S32.classify 0xb1c0fd4cul; S32.classify 0x917bdd64ul; S32.classify 0x9b7624c8ul; S32.classify 0x3bb45432ul;
  S32.classify 0xcaf53ea6ul; S32.classify 0x23ba4442ul; S32.classify 0x38532a3aul; S32.classify 0x4e677d2cul;
  S32.classify 0x45036c7aul; S32.classify 0x0bfd64b6ul; S32.classify 0x5e0dd902ul; S32.classify 0xc68a007eul;
  S32.classify 0xf44182e1ul; S32.classify 0x4db5a851ul; S32.classify 0x7f88a46bul; S32.classify 0x8ec9b55aul;
  S32.classify 0xcec97dcful; S32.classify 0x0a8291cdul; S32.classify 0xf98d0accul; S32.classify 0x2a4ecea9ul;
  S32.classify 0x7140003cul; S32.classify 0x1a1db93dul; S32.classify 0x33cb8b7aul; S32.classify 0x092999a3ul;
  S32.classify 0x71ad0038ul; S32.classify 0x6dc778f9ul; S32.classify 0x918130c4ul; S32.classify 0xa907600aul;
  S32.classify 0x2d9e6832ul; S32.classify 0xed6a1e01ul; S32.classify 0xefb4318aul; S32.classify 0x7135c886ul;
  S32.classify 0x7e31cc7aul; S32.classify 0x87f55ba5ul; S32.classify 0x55034004ul; S32.classify 0x7763cf1dul;
  S32.classify 0xd69f6d18ul; S32.classify 0xac7d5f42ul; S32.classify 0xe58857b6ul; S32.classify 0x7930e9e4ul;
  S32.classify 0x164df4fbul; S32.classify 0x6e6f52c3ul; S32.classify 0x669e1ef1ul; S32.classify 0x25e41d2bul;
  S32.classify 0x3fd59d7cul; S32.classify 0x3c1b20eeul; S32.classify 0xfa53ddeful; S32.classify 0x0abcd06bul;
  S32.classify 0xd5c4484eul; S32.classify 0x1dbf9a42ul; S32.classify 0x9b0deadaul; S32.classify 0xabc52197ul;
  S32.classify 0x22363a0dul; S32.classify 0xe86d2bc5ul; S32.classify 0x9c9df69eul; S32.classify 0x5cae82abul;
  S32.classify 0x71f54bfful; S32.classify 0x64f2e21eul; S32.classify 0xe2d74dd3ul; S32.classify 0xf4fd4452ul;
  S32.classify 0xbc437944ul; S32.classify 0xb4130c93ul; S32.classify 0x85139270ul; S32.classify 0xaefe1309ul;
  S32.classify 0xc186d91cul; S32.classify 0x598cb0faul; S32.classify 0x91f7f7eeul; S32.classify 0x7ad91d26ul;
  S32.classify 0xd6e6c907ul; S32.classify 0x61b46fc9ul; S32.classify 0xf99c0238ul; S32.classify 0xbc34f4deul;
  S32.classify 0x6519035bul; S32.classify 0xde355b3bul; S32.classify 0x611fcfdcul; S32.classify 0x886b4238ul;
  S32.classify 0xc1b2effaul; S32.classify 0xc6f34a26ul; S32.classify 0x7d1683b2ul; S32.classify 0xc58ef183ul;
  S32.classify 0x2ec22005ul; S32.classify 0x3bb5fcbcul; S32.classify 0x4c6fad73ul; S32.classify 0xc3fe3b1bul;
  S32.classify 0xeef28183ul; S32.classify 0x8e4f1232ul; S32.classify 0xe98583fful; S32.classify 0x9172fe9cul;
  S32.classify 0x28342f61ul; S32.classify 0xc03404cdul; S32.classify 0xcdf7e2ecul; S32.classify 0x9e02fce1ul;
  S32.classify 0xee0a6d70ul; S32.classify 0x0b07a7c8ul; S32.classify 0x6372bb19ul; S32.classify 0xae56ede7ul;
  S32.classify 0xde394df4ul; S32.classify 0x1d4f42a3ul; S32.classify 0x60d7f468ul; S32.classify 0xb96adab7ul;
  S32.classify 0xb2c8e3fbul; S32.classify 0xd108a94bul; S32.classify 0xb324fb61ul; S32.classify 0xbc0ab182ul;
  S32.classify 0x483a797aul; S32.classify 0x30acca4ful; S32.classify 0x36ade735ul; S32.classify 0x1df158a1ul;
  S32.classify 0xf3efe872ul; S32.classify 0xe2a689daul; S32.classify 0xe0e68b77ul; S32.classify 0x984f0c70ul;
  S32.classify 0x7f57c935ul; S32.classify 0xb557135eul; S32.classify 0x3ded1af3ul; S32.classify 0x85636555ul;
  S32.classify 0x5f066ed0ul; S32.classify 0x2433f51ful; S32.classify 0xd5fd6561ul; S32.classify 0xd3df1ed5ul;
  S32.classify 0xaec4617aul; S32.classify 0xf681b202ul; S32.classify 0x630c75d8ul; S32.classify 0x7d2fe363ul;
  S32.classify 0x249b3ef9ul; S32.classify 0xcc939dceul; S32.classify 0x146433fbul; S32.classify 0xa9e13641ul;
  S32.classify 0xce2d3695ul; S32.classify 0xd8b9c583ul; S32.classify 0x273d3cf1ul; S32.classify 0xafdc5620ul;
  S32.classify 0xa2bb4a9aul; S32.classify 0xadf85458ul; S32.classify 0xfffffffful; S32.classify 0xfffffffful;
]

[@@FStar.Custard.no_specialize]
let ffdhe6144 : Seq.lseq S32.t 192 =
  assert_norm (List.length ffdhe6144_list == 192);
  Seq.seq_of_list ffdhe6144_list

(** {2 FFDHE-8192} *)

(** The FFDHE-8192 modulus: 8192 bits, 256 limbs. *)
let ffdhe8192_list : list S32.t = [
  S32.classify 0xfffffffful; S32.classify 0xfffffffful; S32.classify 0xc5c6424cul; S32.classify 0xd68c8bb7ul;
  S32.classify 0x838ff88cul; S32.classify 0x011e2a94ul; S32.classify 0xa9f4614eul; S32.classify 0x0822e506ul;
  S32.classify 0xf7a8443dul; S32.classify 0x97d11d49ul; S32.classify 0x30677f0dul; S32.classify 0xa6bbfde5ul;
  S32.classify 0xc1fe86feul; S32.classify 0x2f741ef8ul; S32.classify 0x5d71a87eul; S32.classify 0xfafabe1cul;
  S32.classify 0xfbe58a30ul; S32.classify 0xded2fbabul; S32.classify 0x72b0a66eul; S32.classify 0xb6855dfeul;
  S32.classify 0xba8a4fe8ul; S32.classify 0x1efc8ce0ul; S32.classify 0x3f2fa457ul; S32.classify 0x83f81d4aul;
  S32.classify 0xa577e231ul; S32.classify 0xa1fe3075ul; S32.classify 0x88d9c0a0ul; S32.classify 0xd5b80194ul;
  S32.classify 0xad9a95f9ul; S32.classify 0x624816cdul; S32.classify 0x50c1217bul; S32.classify 0x99e9e316ul;
  S32.classify 0x0e423cfcul; S32.classify 0x51aa691eul; S32.classify 0x3826e52cul; S32.classify 0x1c217e6cul;
  S32.classify 0x09703feeul; S32.classify 0x51a8a931ul; S32.classify 0x6a460e74ul; S32.classify 0xbb709987ul;
  S32.classify 0x9c86b022ul; S32.classify 0x541fc68cul; S32.classify 0x46fd8251ul; S32.classify 0x59160cc0ul;
  S32.classify 0x35c35f5cul; S32.classify 0x2846c0baul; S32.classify 0x8b758282ul; S32.classify 0x54504ac7ul;
  S32.classify 0xd2af05e4ul; S32.classify 0x29388839ul; S32.classify 0xc01bd702ul; S32.classify 0xcb2c0f1cul;
  S32.classify 0x7c932665ul; S32.classify 0x555b2f74ul; S32.classify 0xa3ab8829ul; S32.classify 0x86b63142ul;
  S32.classify 0xf64b10eful; S32.classify 0x0b8cc3bdul; S32.classify 0xedd1cc5eul; S32.classify 0x687feb69ul;
  S32.classify 0xc9509d43ul; S32.classify 0xfdb23fceul; S32.classify 0xd951ae64ul; S32.classify 0x1e425a31ul;
  S32.classify 0xf600c838ul; S32.classify 0x36ad004cul; S32.classify 0xcff46aaaul; S32.classify 0xa40e329cul;
  S32.classify 0x7938dad4ul; S32.classify 0xa41d570dul; S32.classify 0xd43161c1ul; S32.classify 0x62a69526ul;
  S32.classify 0x9adb1e69ul; S32.classify 0x3fdd4a8eul; S32.classify 0xdc6b80d6ul; S32.classify 0x5b3b71f9ul;
  S32.classify 0xc6272b04ul; S32.classify 0xec9d1810ul; S32.classify 0xcacef403ul; S32.classify 0x8ccf2dd5ul;
  S32.classify 0xc95b9117ul; S32.classify 0xe49f5235ul; S32.classify 0xb854338aul; S32.classify 0x505dc82dul;
  S32.classify 0x1562a846ul; S32.classify 0x62292c31ul; S32.classify 0x6ae77f5eul; S32.classify 0xd72b0374ul;
  S32.classify 0x462d538cul; S32.classify 0xf9c9091bul; S32.classify 0x47a67cbeul; S32.classify 0x0ae8db58ul;
  S32.classify 0x22611682ul; S32.classify 0xb3a739c1ul; S32.classify 0x2a281bf6ul; S32.classify 0xeeaac023ul;
  S32.classify 0x77caf992ul; S32.classify 0x94c6651eul; S32.classify 0x94b2bbc1ul; S32.classify 0x763e4e4bul;
  S32.classify 0x0077d9b4ul; S32.classify 0x587e38daul; S32.classify 0x183023c3ul; S32.classify 0x7fb29f8cul;
  S32.classify 0xf9e3a26eul; S32.classify 0x0abec1fful; S32.classify 0x350511e3ul; S32.classify 0xa00ef092ul;
  S32.classify 0xdb6340d8ul; S32.classify 0xb855322eul; S32.classify 0xa9a96910ul; S32.classify 0xa52471f7ul;
  S32.classify 0x4cfdb477ul; S32.classify 0x388147fbul; S32.classify 0x4e46041ful; S32.classify 0x9b1f5c3eul;
  S32.classify 0xfccfec71ul; S32.classify 0xcdad0657ul; S32.classify 0x4c701c3aul; S32.classify 0xb38e8c33ul;
  S32.classify 0xb1c0fd4cul; S32.classify 0x917bdd64ul; S32.classify 0x9b7624c8ul; S32.classify 0x3bb45432ul;
  S32.classify 0xcaf53ea6ul; S32.classify 0x23ba4442ul; S32.classify 0x38532a3aul; S32.classify 0x4e677d2cul;
  S32.classify 0x45036c7aul; S32.classify 0x0bfd64b6ul; S32.classify 0x5e0dd902ul; S32.classify 0xc68a007eul;
  S32.classify 0xf44182e1ul; S32.classify 0x4db5a851ul; S32.classify 0x7f88a46bul; S32.classify 0x8ec9b55aul;
  S32.classify 0xcec97dcful; S32.classify 0x0a8291cdul; S32.classify 0xf98d0accul; S32.classify 0x2a4ecea9ul;
  S32.classify 0x7140003cul; S32.classify 0x1a1db93dul; S32.classify 0x33cb8b7aul; S32.classify 0x092999a3ul;
  S32.classify 0x71ad0038ul; S32.classify 0x6dc778f9ul; S32.classify 0x918130c4ul; S32.classify 0xa907600aul;
  S32.classify 0x2d9e6832ul; S32.classify 0xed6a1e01ul; S32.classify 0xefb4318aul; S32.classify 0x7135c886ul;
  S32.classify 0x7e31cc7aul; S32.classify 0x87f55ba5ul; S32.classify 0x55034004ul; S32.classify 0x7763cf1dul;
  S32.classify 0xd69f6d18ul; S32.classify 0xac7d5f42ul; S32.classify 0xe58857b6ul; S32.classify 0x7930e9e4ul;
  S32.classify 0x164df4fbul; S32.classify 0x6e6f52c3ul; S32.classify 0x669e1ef1ul; S32.classify 0x25e41d2bul;
  S32.classify 0x3fd59d7cul; S32.classify 0x3c1b20eeul; S32.classify 0xfa53ddeful; S32.classify 0x0abcd06bul;
  S32.classify 0xd5c4484eul; S32.classify 0x1dbf9a42ul; S32.classify 0x9b0deadaul; S32.classify 0xabc52197ul;
  S32.classify 0x22363a0dul; S32.classify 0xe86d2bc5ul; S32.classify 0x9c9df69eul; S32.classify 0x5cae82abul;
  S32.classify 0x71f54bfful; S32.classify 0x64f2e21eul; S32.classify 0xe2d74dd3ul; S32.classify 0xf4fd4452ul;
  S32.classify 0xbc437944ul; S32.classify 0xb4130c93ul; S32.classify 0x85139270ul; S32.classify 0xaefe1309ul;
  S32.classify 0xc186d91cul; S32.classify 0x598cb0faul; S32.classify 0x91f7f7eeul; S32.classify 0x7ad91d26ul;
  S32.classify 0xd6e6c907ul; S32.classify 0x61b46fc9ul; S32.classify 0xf99c0238ul; S32.classify 0xbc34f4deul;
  S32.classify 0x6519035bul; S32.classify 0xde355b3bul; S32.classify 0x611fcfdcul; S32.classify 0x886b4238ul;
  S32.classify 0xc1b2effaul; S32.classify 0xc6f34a26ul; S32.classify 0x7d1683b2ul; S32.classify 0xc58ef183ul;
  S32.classify 0x2ec22005ul; S32.classify 0x3bb5fcbcul; S32.classify 0x4c6fad73ul; S32.classify 0xc3fe3b1bul;
  S32.classify 0xeef28183ul; S32.classify 0x8e4f1232ul; S32.classify 0xe98583fful; S32.classify 0x9172fe9cul;
  S32.classify 0x28342f61ul; S32.classify 0xc03404cdul; S32.classify 0xcdf7e2ecul; S32.classify 0x9e02fce1ul;
  S32.classify 0xee0a6d70ul; S32.classify 0x0b07a7c8ul; S32.classify 0x6372bb19ul; S32.classify 0xae56ede7ul;
  S32.classify 0xde394df4ul; S32.classify 0x1d4f42a3ul; S32.classify 0x60d7f468ul; S32.classify 0xb96adab7ul;
  S32.classify 0xb2c8e3fbul; S32.classify 0xd108a94bul; S32.classify 0xb324fb61ul; S32.classify 0xbc0ab182ul;
  S32.classify 0x483a797aul; S32.classify 0x30acca4ful; S32.classify 0x36ade735ul; S32.classify 0x1df158a1ul;
  S32.classify 0xf3efe872ul; S32.classify 0xe2a689daul; S32.classify 0xe0e68b77ul; S32.classify 0x984f0c70ul;
  S32.classify 0x7f57c935ul; S32.classify 0xb557135eul; S32.classify 0x3ded1af3ul; S32.classify 0x85636555ul;
  S32.classify 0x5f066ed0ul; S32.classify 0x2433f51ful; S32.classify 0xd5fd6561ul; S32.classify 0xd3df1ed5ul;
  S32.classify 0xaec4617aul; S32.classify 0xf681b202ul; S32.classify 0x630c75d8ul; S32.classify 0x7d2fe363ul;
  S32.classify 0x249b3ef9ul; S32.classify 0xcc939dceul; S32.classify 0x146433fbul; S32.classify 0xa9e13641ul;
  S32.classify 0xce2d3695ul; S32.classify 0xd8b9c583ul; S32.classify 0x273d3cf1ul; S32.classify 0xafdc5620ul;
  S32.classify 0xa2bb4a9aul; S32.classify 0xadf85458ul; S32.classify 0xfffffffful; S32.classify 0xfffffffful;
]

[@@FStar.Custard.no_specialize]
let ffdhe8192 : Seq.lseq S32.t 256 =
  assert_norm (List.length ffdhe8192_list == 256);
  Seq.seq_of_list ffdhe8192_list


(** {2 The ends of every modulus}

    Each prime is [-1] modulo [2^64] and has its top bit set, so its lowest
    and highest limbs are both [2^32 - 1].  Those are the only two limbs the
    implementation looks at: the first says the modulus is odd, which is what
    Montgomery arithmetic needs, and the second says it is large, which is
    what makes the generator smaller than it.

    Proved by evaluating [List.index] rather than [Seq.index], because
    [FStar.Seq.Base] is an interface and its operations do not reduce. *)

let ffdhe2048_ends () : Lemma
  (S32.v (Seq.index ffdhe2048 0) == pow2 32 - 1 /\
   S32.v (Seq.index ffdhe2048 63) == pow2 32 - 1)
  = assert_norm (List.length ffdhe2048_list == 64);
    Seq.lemma_seq_of_list_index ffdhe2048_list 0;
    Seq.lemma_seq_of_list_index ffdhe2048_list 63;
    assert_norm (List.index ffdhe2048_list 0 == S32.classify 0xfffffffful);
    assert_norm (List.index ffdhe2048_list 63 == S32.classify 0xfffffffful);
    assert_norm (U32.v 0xfffffffful == pow2 32 - 1)

let ffdhe3072_ends () : Lemma
  (S32.v (Seq.index ffdhe3072 0) == pow2 32 - 1 /\
   S32.v (Seq.index ffdhe3072 95) == pow2 32 - 1)
  = assert_norm (List.length ffdhe3072_list == 96);
    Seq.lemma_seq_of_list_index ffdhe3072_list 0;
    Seq.lemma_seq_of_list_index ffdhe3072_list 95;
    assert_norm (List.index ffdhe3072_list 0 == S32.classify 0xfffffffful);
    assert_norm (List.index ffdhe3072_list 95 == S32.classify 0xfffffffful);
    assert_norm (U32.v 0xfffffffful == pow2 32 - 1)

let ffdhe4096_ends () : Lemma
  (S32.v (Seq.index ffdhe4096 0) == pow2 32 - 1 /\
   S32.v (Seq.index ffdhe4096 127) == pow2 32 - 1)
  = assert_norm (List.length ffdhe4096_list == 128);
    Seq.lemma_seq_of_list_index ffdhe4096_list 0;
    Seq.lemma_seq_of_list_index ffdhe4096_list 127;
    assert_norm (List.index ffdhe4096_list 0 == S32.classify 0xfffffffful);
    assert_norm (List.index ffdhe4096_list 127 == S32.classify 0xfffffffful);
    assert_norm (U32.v 0xfffffffful == pow2 32 - 1)

let ffdhe6144_ends () : Lemma
  (S32.v (Seq.index ffdhe6144 0) == pow2 32 - 1 /\
   S32.v (Seq.index ffdhe6144 191) == pow2 32 - 1)
  = assert_norm (List.length ffdhe6144_list == 192);
    Seq.lemma_seq_of_list_index ffdhe6144_list 0;
    Seq.lemma_seq_of_list_index ffdhe6144_list 191;
    assert_norm (List.index ffdhe6144_list 0 == S32.classify 0xfffffffful);
    assert_norm (List.index ffdhe6144_list 191 == S32.classify 0xfffffffful);
    assert_norm (U32.v 0xfffffffful == pow2 32 - 1)

let ffdhe8192_ends () : Lemma
  (S32.v (Seq.index ffdhe8192 0) == pow2 32 - 1 /\
   S32.v (Seq.index ffdhe8192 255) == pow2 32 - 1)
  = assert_norm (List.length ffdhe8192_list == 256);
    Seq.lemma_seq_of_list_index ffdhe8192_list 0;
    Seq.lemma_seq_of_list_index ffdhe8192_list 255;
    assert_norm (List.index ffdhe8192_list 0 == S32.classify 0xfffffffful);
    assert_norm (List.index ffdhe8192_list 255 == S32.classify 0xfffffffful);
    assert_norm (U32.v 0xfffffffful == pow2 32 - 1)

