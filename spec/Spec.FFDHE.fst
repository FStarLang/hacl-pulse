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

    Limbs are sixty-four bits, least significant first, which is the
    representation [Hacl.Bignum.Base] uses.  Each group appears once as a
    [list] -- that is the spine [Pulse.Lib.GlobalArray.mk_static_array] turns
    into a C array initializer -- and once as the [Seq.lseq] the specification
    talks about, the second being [Seq.seq_of_list] of the first, so the two
    cannot drift. *)
module Spec.FFDHE

module Seq = FStar.Seq
module List = FStar.List.Tot
module U64 = FStar.UInt64
module S64 = Hacl.Secret.UInt64

(** {2 FFDHE-2048} *)

(** The FFDHE-2048 modulus: 2048 bits, 32 limbs. *)
let ffdhe2048_list : list S64.t = [
  S64.classify 0xffffffffffffffffuL; S64.classify 0x886b423861285c97uL;
  S64.classify 0xc6f34a26c1b2effauL; S64.classify 0xc58ef1837d1683b2uL;
  S64.classify 0x3bb5fcbc2ec22005uL; S64.classify 0xc3fe3b1b4c6fad73uL;
  S64.classify 0x8e4f1232eef28183uL; S64.classify 0x9172fe9ce98583ffuL;
  S64.classify 0xc03404cd28342f61uL; S64.classify 0x9e02fce1cdf7e2ecuL;
  S64.classify 0x0b07a7c8ee0a6d70uL; S64.classify 0xae56ede76372bb19uL;
  S64.classify 0x1d4f42a3de394df4uL; S64.classify 0xb96adab760d7f468uL;
  S64.classify 0xd108a94bb2c8e3fbuL; S64.classify 0xbc0ab182b324fb61uL;
  S64.classify 0x30acca4f483a797auL; S64.classify 0x1df158a136ade735uL;
  S64.classify 0xe2a689daf3efe872uL; S64.classify 0x984f0c70e0e68b77uL;
  S64.classify 0xb557135e7f57c935uL; S64.classify 0x856365553ded1af3uL;
  S64.classify 0x2433f51f5f066ed0uL; S64.classify 0xd3df1ed5d5fd6561uL;
  S64.classify 0xf681b202aec4617auL; S64.classify 0x7d2fe363630c75d8uL;
  S64.classify 0xcc939dce249b3ef9uL; S64.classify 0xa9e13641146433fbuL;
  S64.classify 0xd8b9c583ce2d3695uL; S64.classify 0xafdc5620273d3cf1uL;
  S64.classify 0xadf85458a2bb4a9auL; S64.classify 0xffffffffffffffffuL
]

[@@FStar.Custard.no_specialize]
let ffdhe2048 : Seq.lseq S64.t 32 =
  assert_norm (List.length ffdhe2048_list == 32);
  Seq.seq_of_list ffdhe2048_list

(** {2 FFDHE-3072} *)

(** The FFDHE-3072 modulus: 3072 bits, 48 limbs. *)
let ffdhe3072_list : list S64.t = [
  S64.classify 0xffffffffffffffffuL; S64.classify 0x25e41d2b66c62e37uL;
  S64.classify 0x3c1b20ee3fd59d7cuL; S64.classify 0x0abcd06bfa53ddefuL;
  S64.classify 0x1dbf9a42d5c4484euL; S64.classify 0xabc521979b0deadauL;
  S64.classify 0xe86d2bc522363a0duL; S64.classify 0x5cae82ab9c9df69euL;
  S64.classify 0x64f2e21e71f54bffuL; S64.classify 0xf4fd4452e2d74dd3uL;
  S64.classify 0xb4130c93bc437944uL; S64.classify 0xaefe130985139270uL;
  S64.classify 0x598cb0fac186d91cuL; S64.classify 0x7ad91d2691f7f7eeuL;
  S64.classify 0x61b46fc9d6e6c907uL; S64.classify 0xbc34f4def99c0238uL;
  S64.classify 0xde355b3b6519035buL; S64.classify 0x886b4238611fcfdcuL;
  S64.classify 0xc6f34a26c1b2effauL; S64.classify 0xc58ef1837d1683b2uL;
  S64.classify 0x3bb5fcbc2ec22005uL; S64.classify 0xc3fe3b1b4c6fad73uL;
  S64.classify 0x8e4f1232eef28183uL; S64.classify 0x9172fe9ce98583ffuL;
  S64.classify 0xc03404cd28342f61uL; S64.classify 0x9e02fce1cdf7e2ecuL;
  S64.classify 0x0b07a7c8ee0a6d70uL; S64.classify 0xae56ede76372bb19uL;
  S64.classify 0x1d4f42a3de394df4uL; S64.classify 0xb96adab760d7f468uL;
  S64.classify 0xd108a94bb2c8e3fbuL; S64.classify 0xbc0ab182b324fb61uL;
  S64.classify 0x30acca4f483a797auL; S64.classify 0x1df158a136ade735uL;
  S64.classify 0xe2a689daf3efe872uL; S64.classify 0x984f0c70e0e68b77uL;
  S64.classify 0xb557135e7f57c935uL; S64.classify 0x856365553ded1af3uL;
  S64.classify 0x2433f51f5f066ed0uL; S64.classify 0xd3df1ed5d5fd6561uL;
  S64.classify 0xf681b202aec4617auL; S64.classify 0x7d2fe363630c75d8uL;
  S64.classify 0xcc939dce249b3ef9uL; S64.classify 0xa9e13641146433fbuL;
  S64.classify 0xd8b9c583ce2d3695uL; S64.classify 0xafdc5620273d3cf1uL;
  S64.classify 0xadf85458a2bb4a9auL; S64.classify 0xffffffffffffffffuL
]

[@@FStar.Custard.no_specialize]
let ffdhe3072 : Seq.lseq S64.t 48 =
  assert_norm (List.length ffdhe3072_list == 48);
  Seq.seq_of_list ffdhe3072_list

(** {2 FFDHE-4096} *)

(** The FFDHE-4096 modulus: 4096 bits, 64 limbs. *)
let ffdhe4096_list : list S64.t = [
  S64.classify 0xffffffffffffffffuL; S64.classify 0xc68a007e5e655f6auL;
  S64.classify 0x4db5a851f44182e1uL; S64.classify 0x8ec9b55a7f88a46buL;
  S64.classify 0x0a8291cdcec97dcfuL; S64.classify 0x2a4ecea9f98d0accuL;
  S64.classify 0x1a1db93d7140003cuL; S64.classify 0x092999a333cb8b7auL;
  S64.classify 0x6dc778f971ad0038uL; S64.classify 0xa907600a918130c4uL;
  S64.classify 0xed6a1e012d9e6832uL; S64.classify 0x7135c886efb4318auL;
  S64.classify 0x87f55ba57e31cc7auL; S64.classify 0x7763cf1d55034004uL;
  S64.classify 0xac7d5f42d69f6d18uL; S64.classify 0x7930e9e4e58857b6uL;
  S64.classify 0x6e6f52c3164df4fbuL; S64.classify 0x25e41d2b669e1ef1uL;
  S64.classify 0x3c1b20ee3fd59d7cuL; S64.classify 0x0abcd06bfa53ddefuL;
  S64.classify 0x1dbf9a42d5c4484euL; S64.classify 0xabc521979b0deadauL;
  S64.classify 0xe86d2bc522363a0duL; S64.classify 0x5cae82ab9c9df69euL;
  S64.classify 0x64f2e21e71f54bffuL; S64.classify 0xf4fd4452e2d74dd3uL;
  S64.classify 0xb4130c93bc437944uL; S64.classify 0xaefe130985139270uL;
  S64.classify 0x598cb0fac186d91cuL; S64.classify 0x7ad91d2691f7f7eeuL;
  S64.classify 0x61b46fc9d6e6c907uL; S64.classify 0xbc34f4def99c0238uL;
  S64.classify 0xde355b3b6519035buL; S64.classify 0x886b4238611fcfdcuL;
  S64.classify 0xc6f34a26c1b2effauL; S64.classify 0xc58ef1837d1683b2uL;
  S64.classify 0x3bb5fcbc2ec22005uL; S64.classify 0xc3fe3b1b4c6fad73uL;
  S64.classify 0x8e4f1232eef28183uL; S64.classify 0x9172fe9ce98583ffuL;
  S64.classify 0xc03404cd28342f61uL; S64.classify 0x9e02fce1cdf7e2ecuL;
  S64.classify 0x0b07a7c8ee0a6d70uL; S64.classify 0xae56ede76372bb19uL;
  S64.classify 0x1d4f42a3de394df4uL; S64.classify 0xb96adab760d7f468uL;
  S64.classify 0xd108a94bb2c8e3fbuL; S64.classify 0xbc0ab182b324fb61uL;
  S64.classify 0x30acca4f483a797auL; S64.classify 0x1df158a136ade735uL;
  S64.classify 0xe2a689daf3efe872uL; S64.classify 0x984f0c70e0e68b77uL;
  S64.classify 0xb557135e7f57c935uL; S64.classify 0x856365553ded1af3uL;
  S64.classify 0x2433f51f5f066ed0uL; S64.classify 0xd3df1ed5d5fd6561uL;
  S64.classify 0xf681b202aec4617auL; S64.classify 0x7d2fe363630c75d8uL;
  S64.classify 0xcc939dce249b3ef9uL; S64.classify 0xa9e13641146433fbuL;
  S64.classify 0xd8b9c583ce2d3695uL; S64.classify 0xafdc5620273d3cf1uL;
  S64.classify 0xadf85458a2bb4a9auL; S64.classify 0xffffffffffffffffuL
]

[@@FStar.Custard.no_specialize]
let ffdhe4096 : Seq.lseq S64.t 64 =
  assert_norm (List.length ffdhe4096_list == 64);
  Seq.seq_of_list ffdhe4096_list

(** {2 FFDHE-6144} *)

(** The FFDHE-6144 modulus: 6144 bits, 96 limbs. *)
let ffdhe6144_list : list S64.t = [
  S64.classify 0xffffffffffffffffuL; S64.classify 0xa40e329cd0e40e65uL;
  S64.classify 0xa41d570d7938dad4uL; S64.classify 0x62a69526d43161c1uL;
  S64.classify 0x3fdd4a8e9adb1e69uL; S64.classify 0x5b3b71f9dc6b80d6uL;
  S64.classify 0xec9d1810c6272b04uL; S64.classify 0x8ccf2dd5cacef403uL;
  S64.classify 0xe49f5235c95b9117uL; S64.classify 0x505dc82db854338auL;
  S64.classify 0x62292c311562a846uL; S64.classify 0xd72b03746ae77f5euL;
  S64.classify 0xf9c9091b462d538cuL; S64.classify 0x0ae8db5847a67cbeuL;
  S64.classify 0xb3a739c122611682uL; S64.classify 0xeeaac0232a281bf6uL;
  S64.classify 0x94c6651e77caf992uL; S64.classify 0x763e4e4b94b2bbc1uL;
  S64.classify 0x587e38da0077d9b4uL; S64.classify 0x7fb29f8c183023c3uL;
  S64.classify 0x0abec1fff9e3a26euL; S64.classify 0xa00ef092350511e3uL;
  S64.classify 0xb855322edb6340d8uL; S64.classify 0xa52471f7a9a96910uL;
  S64.classify 0x388147fb4cfdb477uL; S64.classify 0x9b1f5c3e4e46041fuL;
  S64.classify 0xcdad0657fccfec71uL; S64.classify 0xb38e8c334c701c3auL;
  S64.classify 0x917bdd64b1c0fd4cuL; S64.classify 0x3bb454329b7624c8uL;
  S64.classify 0x23ba4442caf53ea6uL; S64.classify 0x4e677d2c38532a3auL;
  S64.classify 0x0bfd64b645036c7auL; S64.classify 0xc68a007e5e0dd902uL;
  S64.classify 0x4db5a851f44182e1uL; S64.classify 0x8ec9b55a7f88a46buL;
  S64.classify 0x0a8291cdcec97dcfuL; S64.classify 0x2a4ecea9f98d0accuL;
  S64.classify 0x1a1db93d7140003cuL; S64.classify 0x092999a333cb8b7auL;
  S64.classify 0x6dc778f971ad0038uL; S64.classify 0xa907600a918130c4uL;
  S64.classify 0xed6a1e012d9e6832uL; S64.classify 0x7135c886efb4318auL;
  S64.classify 0x87f55ba57e31cc7auL; S64.classify 0x7763cf1d55034004uL;
  S64.classify 0xac7d5f42d69f6d18uL; S64.classify 0x7930e9e4e58857b6uL;
  S64.classify 0x6e6f52c3164df4fbuL; S64.classify 0x25e41d2b669e1ef1uL;
  S64.classify 0x3c1b20ee3fd59d7cuL; S64.classify 0x0abcd06bfa53ddefuL;
  S64.classify 0x1dbf9a42d5c4484euL; S64.classify 0xabc521979b0deadauL;
  S64.classify 0xe86d2bc522363a0duL; S64.classify 0x5cae82ab9c9df69euL;
  S64.classify 0x64f2e21e71f54bffuL; S64.classify 0xf4fd4452e2d74dd3uL;
  S64.classify 0xb4130c93bc437944uL; S64.classify 0xaefe130985139270uL;
  S64.classify 0x598cb0fac186d91cuL; S64.classify 0x7ad91d2691f7f7eeuL;
  S64.classify 0x61b46fc9d6e6c907uL; S64.classify 0xbc34f4def99c0238uL;
  S64.classify 0xde355b3b6519035buL; S64.classify 0x886b4238611fcfdcuL;
  S64.classify 0xc6f34a26c1b2effauL; S64.classify 0xc58ef1837d1683b2uL;
  S64.classify 0x3bb5fcbc2ec22005uL; S64.classify 0xc3fe3b1b4c6fad73uL;
  S64.classify 0x8e4f1232eef28183uL; S64.classify 0x9172fe9ce98583ffuL;
  S64.classify 0xc03404cd28342f61uL; S64.classify 0x9e02fce1cdf7e2ecuL;
  S64.classify 0x0b07a7c8ee0a6d70uL; S64.classify 0xae56ede76372bb19uL;
  S64.classify 0x1d4f42a3de394df4uL; S64.classify 0xb96adab760d7f468uL;
  S64.classify 0xd108a94bb2c8e3fbuL; S64.classify 0xbc0ab182b324fb61uL;
  S64.classify 0x30acca4f483a797auL; S64.classify 0x1df158a136ade735uL;
  S64.classify 0xe2a689daf3efe872uL; S64.classify 0x984f0c70e0e68b77uL;
  S64.classify 0xb557135e7f57c935uL; S64.classify 0x856365553ded1af3uL;
  S64.classify 0x2433f51f5f066ed0uL; S64.classify 0xd3df1ed5d5fd6561uL;
  S64.classify 0xf681b202aec4617auL; S64.classify 0x7d2fe363630c75d8uL;
  S64.classify 0xcc939dce249b3ef9uL; S64.classify 0xa9e13641146433fbuL;
  S64.classify 0xd8b9c583ce2d3695uL; S64.classify 0xafdc5620273d3cf1uL;
  S64.classify 0xadf85458a2bb4a9auL; S64.classify 0xffffffffffffffffuL
]

[@@FStar.Custard.no_specialize]
let ffdhe6144 : Seq.lseq S64.t 96 =
  assert_norm (List.length ffdhe6144_list == 96);
  Seq.seq_of_list ffdhe6144_list

(** {2 FFDHE-8192} *)

(** The FFDHE-8192 modulus: 8192 bits, 128 limbs. *)
let ffdhe8192_list : list S64.t = [
  S64.classify 0xffffffffffffffffuL; S64.classify 0xd68c8bb7c5c6424cuL;
  S64.classify 0x011e2a94838ff88cuL; S64.classify 0x0822e506a9f4614euL;
  S64.classify 0x97d11d49f7a8443duL; S64.classify 0xa6bbfde530677f0duL;
  S64.classify 0x2f741ef8c1fe86feuL; S64.classify 0xfafabe1c5d71a87euL;
  S64.classify 0xded2fbabfbe58a30uL; S64.classify 0xb6855dfe72b0a66euL;
  S64.classify 0x1efc8ce0ba8a4fe8uL; S64.classify 0x83f81d4a3f2fa457uL;
  S64.classify 0xa1fe3075a577e231uL; S64.classify 0xd5b8019488d9c0a0uL;
  S64.classify 0x624816cdad9a95f9uL; S64.classify 0x99e9e31650c1217buL;
  S64.classify 0x51aa691e0e423cfcuL; S64.classify 0x1c217e6c3826e52cuL;
  S64.classify 0x51a8a93109703feeuL; S64.classify 0xbb7099876a460e74uL;
  S64.classify 0x541fc68c9c86b022uL; S64.classify 0x59160cc046fd8251uL;
  S64.classify 0x2846c0ba35c35f5cuL; S64.classify 0x54504ac78b758282uL;
  S64.classify 0x29388839d2af05e4uL; S64.classify 0xcb2c0f1cc01bd702uL;
  S64.classify 0x555b2f747c932665uL; S64.classify 0x86b63142a3ab8829uL;
  S64.classify 0x0b8cc3bdf64b10efuL; S64.classify 0x687feb69edd1cc5euL;
  S64.classify 0xfdb23fcec9509d43uL; S64.classify 0x1e425a31d951ae64uL;
  S64.classify 0x36ad004cf600c838uL; S64.classify 0xa40e329ccff46aaauL;
  S64.classify 0xa41d570d7938dad4uL; S64.classify 0x62a69526d43161c1uL;
  S64.classify 0x3fdd4a8e9adb1e69uL; S64.classify 0x5b3b71f9dc6b80d6uL;
  S64.classify 0xec9d1810c6272b04uL; S64.classify 0x8ccf2dd5cacef403uL;
  S64.classify 0xe49f5235c95b9117uL; S64.classify 0x505dc82db854338auL;
  S64.classify 0x62292c311562a846uL; S64.classify 0xd72b03746ae77f5euL;
  S64.classify 0xf9c9091b462d538cuL; S64.classify 0x0ae8db5847a67cbeuL;
  S64.classify 0xb3a739c122611682uL; S64.classify 0xeeaac0232a281bf6uL;
  S64.classify 0x94c6651e77caf992uL; S64.classify 0x763e4e4b94b2bbc1uL;
  S64.classify 0x587e38da0077d9b4uL; S64.classify 0x7fb29f8c183023c3uL;
  S64.classify 0x0abec1fff9e3a26euL; S64.classify 0xa00ef092350511e3uL;
  S64.classify 0xb855322edb6340d8uL; S64.classify 0xa52471f7a9a96910uL;
  S64.classify 0x388147fb4cfdb477uL; S64.classify 0x9b1f5c3e4e46041fuL;
  S64.classify 0xcdad0657fccfec71uL; S64.classify 0xb38e8c334c701c3auL;
  S64.classify 0x917bdd64b1c0fd4cuL; S64.classify 0x3bb454329b7624c8uL;
  S64.classify 0x23ba4442caf53ea6uL; S64.classify 0x4e677d2c38532a3auL;
  S64.classify 0x0bfd64b645036c7auL; S64.classify 0xc68a007e5e0dd902uL;
  S64.classify 0x4db5a851f44182e1uL; S64.classify 0x8ec9b55a7f88a46buL;
  S64.classify 0x0a8291cdcec97dcfuL; S64.classify 0x2a4ecea9f98d0accuL;
  S64.classify 0x1a1db93d7140003cuL; S64.classify 0x092999a333cb8b7auL;
  S64.classify 0x6dc778f971ad0038uL; S64.classify 0xa907600a918130c4uL;
  S64.classify 0xed6a1e012d9e6832uL; S64.classify 0x7135c886efb4318auL;
  S64.classify 0x87f55ba57e31cc7auL; S64.classify 0x7763cf1d55034004uL;
  S64.classify 0xac7d5f42d69f6d18uL; S64.classify 0x7930e9e4e58857b6uL;
  S64.classify 0x6e6f52c3164df4fbuL; S64.classify 0x25e41d2b669e1ef1uL;
  S64.classify 0x3c1b20ee3fd59d7cuL; S64.classify 0x0abcd06bfa53ddefuL;
  S64.classify 0x1dbf9a42d5c4484euL; S64.classify 0xabc521979b0deadauL;
  S64.classify 0xe86d2bc522363a0duL; S64.classify 0x5cae82ab9c9df69euL;
  S64.classify 0x64f2e21e71f54bffuL; S64.classify 0xf4fd4452e2d74dd3uL;
  S64.classify 0xb4130c93bc437944uL; S64.classify 0xaefe130985139270uL;
  S64.classify 0x598cb0fac186d91cuL; S64.classify 0x7ad91d2691f7f7eeuL;
  S64.classify 0x61b46fc9d6e6c907uL; S64.classify 0xbc34f4def99c0238uL;
  S64.classify 0xde355b3b6519035buL; S64.classify 0x886b4238611fcfdcuL;
  S64.classify 0xc6f34a26c1b2effauL; S64.classify 0xc58ef1837d1683b2uL;
  S64.classify 0x3bb5fcbc2ec22005uL; S64.classify 0xc3fe3b1b4c6fad73uL;
  S64.classify 0x8e4f1232eef28183uL; S64.classify 0x9172fe9ce98583ffuL;
  S64.classify 0xc03404cd28342f61uL; S64.classify 0x9e02fce1cdf7e2ecuL;
  S64.classify 0x0b07a7c8ee0a6d70uL; S64.classify 0xae56ede76372bb19uL;
  S64.classify 0x1d4f42a3de394df4uL; S64.classify 0xb96adab760d7f468uL;
  S64.classify 0xd108a94bb2c8e3fbuL; S64.classify 0xbc0ab182b324fb61uL;
  S64.classify 0x30acca4f483a797auL; S64.classify 0x1df158a136ade735uL;
  S64.classify 0xe2a689daf3efe872uL; S64.classify 0x984f0c70e0e68b77uL;
  S64.classify 0xb557135e7f57c935uL; S64.classify 0x856365553ded1af3uL;
  S64.classify 0x2433f51f5f066ed0uL; S64.classify 0xd3df1ed5d5fd6561uL;
  S64.classify 0xf681b202aec4617auL; S64.classify 0x7d2fe363630c75d8uL;
  S64.classify 0xcc939dce249b3ef9uL; S64.classify 0xa9e13641146433fbuL;
  S64.classify 0xd8b9c583ce2d3695uL; S64.classify 0xafdc5620273d3cf1uL;
  S64.classify 0xadf85458a2bb4a9auL; S64.classify 0xffffffffffffffffuL
]

[@@FStar.Custard.no_specialize]
let ffdhe8192 : Seq.lseq S64.t 128 =
  assert_norm (List.length ffdhe8192_list == 128);
  Seq.seq_of_list ffdhe8192_list


(** {2 The ends of every modulus}

    Each prime is [-1] modulo [2^64] and has its top bit set, so its lowest
    and highest limbs are both [2^64 - 1].  Those are the only two limbs the
    implementation looks at: the first says the modulus is odd, which is what
    Montgomery arithmetic needs, and the second says it is large, which is
    what makes the generator smaller than it.

    Proved by evaluating [List.index] rather than [Seq.index], because
    [FStar.Seq.Base] is an interface and its operations do not reduce. *)

let ffdhe2048_ends () : Lemma
  (S64.v (Seq.index ffdhe2048 0) == pow2 64 - 1 /\
   S64.v (Seq.index ffdhe2048 31) == pow2 64 - 1)
  = assert_norm (List.length ffdhe2048_list == 32);
    Seq.lemma_seq_of_list_index ffdhe2048_list 0;
    Seq.lemma_seq_of_list_index ffdhe2048_list 31;
    assert_norm (List.index ffdhe2048_list 0 == S64.classify 0xffffffffffffffffuL);
    assert_norm (List.index ffdhe2048_list 31 == S64.classify 0xffffffffffffffffuL);
    assert_norm (U64.v 0xffffffffffffffffuL == pow2 64 - 1)

let ffdhe3072_ends () : Lemma
  (S64.v (Seq.index ffdhe3072 0) == pow2 64 - 1 /\
   S64.v (Seq.index ffdhe3072 47) == pow2 64 - 1)
  = assert_norm (List.length ffdhe3072_list == 48);
    Seq.lemma_seq_of_list_index ffdhe3072_list 0;
    Seq.lemma_seq_of_list_index ffdhe3072_list 47;
    assert_norm (List.index ffdhe3072_list 0 == S64.classify 0xffffffffffffffffuL);
    assert_norm (List.index ffdhe3072_list 47 == S64.classify 0xffffffffffffffffuL);
    assert_norm (U64.v 0xffffffffffffffffuL == pow2 64 - 1)

let ffdhe4096_ends () : Lemma
  (S64.v (Seq.index ffdhe4096 0) == pow2 64 - 1 /\
   S64.v (Seq.index ffdhe4096 63) == pow2 64 - 1)
  = assert_norm (List.length ffdhe4096_list == 64);
    Seq.lemma_seq_of_list_index ffdhe4096_list 0;
    Seq.lemma_seq_of_list_index ffdhe4096_list 63;
    assert_norm (List.index ffdhe4096_list 0 == S64.classify 0xffffffffffffffffuL);
    assert_norm (List.index ffdhe4096_list 63 == S64.classify 0xffffffffffffffffuL);
    assert_norm (U64.v 0xffffffffffffffffuL == pow2 64 - 1)

let ffdhe6144_ends () : Lemma
  (S64.v (Seq.index ffdhe6144 0) == pow2 64 - 1 /\
   S64.v (Seq.index ffdhe6144 95) == pow2 64 - 1)
  = assert_norm (List.length ffdhe6144_list == 96);
    Seq.lemma_seq_of_list_index ffdhe6144_list 0;
    Seq.lemma_seq_of_list_index ffdhe6144_list 95;
    assert_norm (List.index ffdhe6144_list 0 == S64.classify 0xffffffffffffffffuL);
    assert_norm (List.index ffdhe6144_list 95 == S64.classify 0xffffffffffffffffuL);
    assert_norm (U64.v 0xffffffffffffffffuL == pow2 64 - 1)

let ffdhe8192_ends () : Lemma
  (S64.v (Seq.index ffdhe8192 0) == pow2 64 - 1 /\
   S64.v (Seq.index ffdhe8192 127) == pow2 64 - 1)
  = assert_norm (List.length ffdhe8192_list == 128);
    Seq.lemma_seq_of_list_index ffdhe8192_list 0;
    Seq.lemma_seq_of_list_index ffdhe8192_list 127;
    assert_norm (List.index ffdhe8192_list 0 == S64.classify 0xffffffffffffffffuL);
    assert_norm (List.index ffdhe8192_list 127 == S64.classify 0xffffffffffffffffuL);
    assert_norm (U64.v 0xffffffffffffffffuL == pow2 64 - 1)

