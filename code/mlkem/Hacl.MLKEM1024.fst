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


(** ML-KEM-1024.  A dozen lines: the parameters are arguments to the one
    implementation in {!Hacl.Impl.MLKEM.KEM}, so a parameter set is a
    choice of five numbers and the lengths they imply.

    All three entry points take their randomness as an argument, which is
    what the known-answer tests need; a caller that wants the standard's
    interface draws {i d}, {i z} and {i m} from the system generator
    and passes them in. *)
module Hacl.MLKEM1024

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Params

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module M = Spec.MLKEM
module KEM = Hacl.Impl.MLKEM.KEM

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Key generation.  [d] and [z] are 32 uniform bytes each. *)
fn keypair (ek: A.array S8.t) (dk: A.array S8.t) (d: A.array S8.t) (z: A.array S8.t)
           (#pd: perm) (#pz: perm)
           (#vek0: erased (Seq.lseq S8.t 1568))
           (#vdk0: erased (Seq.lseq S8.t 3168))
           (#vd: erased (Seq.lseq S8.t 32))
           (#vz: erased (Seq.lseq S8.t 32))
requires A.pts_to ek vek0 ** A.pts_to dk vdk0 **
         A.pts_to d #pd vd ** A.pts_to z #pz vz
ensures exists* vek vdk.
        A.pts_to ek vek ** A.pts_to dk vdk **
        A.pts_to d #pd vd ** A.pts_to z #pz vz **
        pure (vek == fst (M.keygen mlkem1024 vd vz) /\
              vdk == snd (M.keygen mlkem1024 vd vz))
{
  KEM.keygen_impl ek dk d z (hide mlkem1024) 4sz 2sz;
}

(** Encapsulation.  [m] is 32 uniform bytes. *)
fn enc (ct: A.array S8.t) (ss: A.array S8.t) (ek: A.array S8.t) (m: A.array S8.t)
       (#pek: perm) (#pm: perm)
       (#vct0: erased (Seq.lseq S8.t 1568))
       (#vss0: erased (Seq.lseq S8.t 32))
       (#vek: erased (Seq.lseq S8.t 1568))
       (#vm: erased (Seq.lseq S8.t 32))
requires A.pts_to ct vct0 ** A.pts_to ss vss0 **
         A.pts_to ek #pek vek ** A.pts_to m #pm vm
ensures exists* vct vss.
        A.pts_to ct vct ** A.pts_to ss vss **
        A.pts_to ek #pek vek ** A.pts_to m #pm vm **
        pure (vss == fst (M.encaps mlkem1024 vek vm) /\
              vct == snd (M.encaps mlkem1024 vek vm))
{
  KEM.encaps_impl ss ct ek m (hide mlkem1024) 4sz 2sz 2sz 11sz 5sz;
}

(** Decapsulation.  Always succeeds: a ciphertext that does not
    re-encrypt yields a shared secret derived from the decapsulation
    key's rejection value instead, and which of the two happened is not
    observable. *)
fn dec (ss: A.array S8.t) (ct: A.array S8.t) (dk: A.array S8.t)
       (#pct: perm) (#pdk: perm)
       (#vss0: erased (Seq.lseq S8.t 32))
       (#vct: erased (Seq.lseq S8.t 1568))
       (#vdk: erased (Seq.lseq S8.t 3168))
requires A.pts_to ss vss0 ** A.pts_to ct #pct vct ** A.pts_to dk #pdk vdk
ensures exists* vss.
        A.pts_to ss vss ** A.pts_to ct #pct vct ** A.pts_to dk #pdk vdk **
        pure (vss == M.decaps mlkem1024 vdk vct)
{
  KEM.decaps_impl ss dk ct (hide mlkem1024) 4sz 2sz 2sz 11sz 5sz;
}

#pop-options
