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
(** eFrodoKEM-640-SHAKE, NIST level 1.

    Three entry points, all of them deterministic.  HACL\* draws the coins
    inside {c crypto_kem_keypair} and {c crypto_kem_enc} from a platform
    entropy shim and throws the failure indication away; here, as for
    HMAC-DRBG, the randomness is an argument.  That is the whole of the
    difference: {c keypair pk sk coins} with [coins] uniform is
    {c Hacl_Frodo640_crypto_kem_keypair}, and {c enc ct ss pk mu} with
    [mu] uniform is {c Hacl_Frodo640_crypto_kem_enc}.  Nothing returns a
    status code, because nothing here can fail.

    Sizes, in bytes:

    - [coins]: 48, [mu]: 16
    - [pk]: 9616, [sk]: 19888, [ct]: 9720, [ss]: 16 *)
module Hacl.Frodo640

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Frodo.Params
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module GA = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U16 = FStar.UInt16
module S8 = Hacl.Secret.UInt8
module F = Spec.Frodo
module KEM = Hacl.Frodo.KEM

(** The sampler's table, as a [static const uint16_t[]] in the program
    image.  The literals are repeated here rather than taken from the
    specification because a [static const] array has to be built from a
    list; the refinement is what rules out a drift between the two, and it
    holds by unfolding [cdf_640]. *)
let cdf_arr : (a: GA.static_array U16.t
                 { GA.static_array_elems a == (cdf_640 <: Seq.seq U16.t) })
  = GA.mk_static_array
      [ 4643us; 13363us; 20579us; 25843us; 29227us; 31145us;
        32103us; 32525us; 32689us; 32745us; 32762us; 32766us;
        32767us ]

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** Key generation.  [coins] is [s || seed_se || z], 48 uniform bytes. *)
fn keypair (pk: A.array S8.t) (sk: A.array S8.t) (coins: A.array S8.t)
           (#pc: perm)
           (#vpk0: erased (Seq.lseq S8.t 9616))
           (#vsk0: erased (Seq.lseq S8.t 19888))
           (#vcoins: erased (Seq.lseq S8.t 48))
requires A.pts_to pk vpk0 ** A.pts_to sk vsk0 ** A.pts_to coins #pc vcoins
ensures exists* vpk vsk.
        A.pts_to pk vpk ** A.pts_to sk vsk ** A.pts_to coins #pc vcoins **
        pure (vpk == fst (F.keypair frodo640 vcoins) /\
              vsk == snd (F.keypair frodo640 vcoins))
{
  let cdf = table cdf_arr 13sz;
  KEM.keypair_coins frodo640 cdf pk sk coins;
  drop_table cdf;
}

(** Encapsulation.  [mu] is 16 uniform bytes. *)
fn enc (ct: A.array S8.t) (ss: A.array S8.t) (pk: A.array S8.t) (mu: A.array S8.t)
       (#pmu: perm) (#ppk: perm)
       (#vct0: erased (Seq.lseq S8.t 9720))
       (#vss0: erased (Seq.lseq S8.t 16))
       (#vpk: erased (Seq.lseq S8.t 9616))
       (#vmu: erased (Seq.lseq S8.t 16))
requires A.pts_to ct vct0 ** A.pts_to ss vss0 **
         A.pts_to pk #ppk vpk ** A.pts_to mu #pmu vmu
ensures exists* vct vss.
        A.pts_to ct vct ** A.pts_to ss vss **
        A.pts_to pk #ppk vpk ** A.pts_to mu #pmu vmu **
        pure (vct == fst (F.enc frodo640 vmu vpk) /\
              vss == snd (F.enc frodo640 vmu vpk))
{
  let cdf = table cdf_arr 13sz;
  KEM.enc_mu frodo640 cdf ct ss mu pk;
  drop_table cdf;
}

(** Decapsulation.  Always succeeds: a ciphertext that does not re-encrypt
    yields a shared secret derived from the secret key's rejection value
    instead, and which of the two happened is not observable. *)
fn dec (ss: A.array S8.t) (ct: A.array S8.t) (sk: A.array S8.t)
       (#pct: perm) (#psk: perm)
       (#vss0: erased (Seq.lseq S8.t 16))
       (#vct: erased (Seq.lseq S8.t 9720))
       (#vsk: erased (Seq.lseq S8.t 19888))
requires A.pts_to ss vss0 ** A.pts_to ct #pct vct ** A.pts_to sk #psk vsk
ensures exists* vss.
        A.pts_to ss vss ** A.pts_to ct #pct vct ** A.pts_to sk #psk vsk **
        pure (vss == F.dec frodo640 vct vsk)
{
  let cdf = table cdf_arr 13sz;
  KEM.dec frodo640 cdf ss ct sk;
  drop_table cdf;
}

#pop-options
