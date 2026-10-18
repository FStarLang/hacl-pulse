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


(** ML-DSA-87.  The parameters are arguments to the one implementation
    in {!Hacl.Impl.MLDSA.DSA}; this module fixes them and the lengths
    they imply: a 2592-byte public key, a 4896-byte private key and a
    4627-byte signature.

    Every entry point takes its randomness as an argument, which is what
    the known-answer tests need: a caller that wants the standard's
    interface draws the 32-byte key generation seed, and the 32-byte
    [rnd] for the hedged signing variant, from an approved generator.
    [sign] and [verify] are the pure ML-DSA of FIPS 204 section 5, with
    a context string of at most 255 bytes; [sign_internal] and
    [verify_internal] are Algorithms 7 and 8 on an already formatted
    message [M']; [sign_mu] and [verify_mu] take the 64-byte message
    representative [mu] directly ("external mu"). *)
module Hacl.MLDSA87

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Params

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module M = Spec.MLDSA
module KG = Hacl.Impl.MLDSA.KeyGen
module DSA = Hacl.Impl.MLDSA.DSA
module Sign = Hacl.Impl.MLDSA.Sign
module Verify = Hacl.Impl.MLDSA.Verify

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Key generation from a 32-byte seed [xi]. *)
fn keypair (pk sk xi: A.array S8.t) (#px: perm)
           (#vpk0: erased (Seq.lseq S8.t 2592))
           (#vsk0: erased (Seq.lseq S8.t 4896))
           (#vx: erased (Seq.lseq S8.t 32))
requires A.pts_to pk vpk0 ** A.pts_to sk vsk0 ** A.pts_to xi #px vx
ensures exists* vpk vsk.
        A.pts_to pk vpk ** A.pts_to sk vsk ** A.pts_to xi #px vx **
        pure (vpk == fst (M.keygen_internal mldsa87 vx) /\
              vsk == snd (M.keygen_internal mldsa87 vx))
{
  KG.keygen_impl pk sk xi (hide mldsa87) 8sz 7sz 2sz;
}

(** Algorithm 2, hedged: [rnd] is 32 fresh random bytes.  Returns
    [false], with [sg] unspecified, when [ctx_len > 255] or, with
    negligible probability, when every attempt is rejected. *)
fn sign (sg sk msg: A.array S8.t) (msg_len: SZ.t) (ctx: A.array S8.t) (ctx_len: SZ.t)
        (rnd: A.array S8.t) (#psk #pm #pc #pr: perm)
        (#vsg0: erased (Seq.lseq S8.t 4627))
        (#vsk: erased (Seq.lseq S8.t 4896))
        (#vm #vc: erased (Seq.seq S8.t))
        (#vr: erased (Seq.lseq S8.t 32))
requires A.pts_to sg vsg0 ** A.pts_to sk #psk vsk ** A.pts_to msg #pm vm **
         A.pts_to ctx #pc vc ** A.pts_to rnd #pr vr **
         pure (SZ.v msg_len == Seq.length vm /\ SZ.v ctx_len == Seq.length vc /\
               SZ.fits (66 + Seq.length vc + Seq.length vm))
returns ok: bool
ensures exists* vsg.
        A.pts_to sg vsg ** A.pts_to sk #psk vsk ** A.pts_to msg #pm vm **
        A.pts_to ctx #pc vc ** A.pts_to rnd #pr vr **
        pure (Seq.length vsg == 4627 /\
              (if ok then M.sign mldsa87 vsk vm vc vr == Some vsg
               else M.sign mldsa87 vsk vm vc vr == None))
{
  DSA.sign_impl sg sk msg msg_len ctx ctx_len rnd (hide mldsa87) 8sz 7sz 2sz 60sz 64sz 19sz 75sz 32ul
}

(** Algorithm 2, deterministic: [rnd = 0^32]. *)
fn sign_deterministic (sg sk msg: A.array S8.t) (msg_len: SZ.t) (ctx: A.array S8.t) (ctx_len: SZ.t)
                      (#psk #pm #pc: perm)
                      (#vsg0: erased (Seq.lseq S8.t 4627))
                      (#vsk: erased (Seq.lseq S8.t 4896))
                      (#vm #vc: erased (Seq.seq S8.t))
requires A.pts_to sg vsg0 ** A.pts_to sk #psk vsk ** A.pts_to msg #pm vm **
         A.pts_to ctx #pc vc **
         pure (SZ.v msg_len == Seq.length vm /\ SZ.v ctx_len == Seq.length vc /\
               SZ.fits (66 + Seq.length vc + Seq.length vm))
returns ok: bool
ensures exists* vsg.
        A.pts_to sg vsg ** A.pts_to sk #psk vsk ** A.pts_to msg #pm vm **
        A.pts_to ctx #pc vc **
        pure (Seq.length vsg == 4627 /\
              (if ok then M.sign mldsa87 vsk vm vc M.rnd_zero == Some vsg
               else M.sign mldsa87 vsk vm vc M.rnd_zero == None))
{
  DSA.sign_det_impl sg sk msg msg_len ctx ctx_len (hide mldsa87) 8sz 7sz 2sz 60sz 64sz 19sz 75sz 32ul
}

(** Algorithm 3.  [false] when [ctx_len > 255]. *)
fn verify (pk msg: A.array S8.t) (msg_len: SZ.t) (ctx: A.array S8.t) (ctx_len: SZ.t)
          (sg: A.array S8.t) (#ppk #pm #pc #psg: perm)
          (#vpk: erased (Seq.lseq S8.t 2592))
          (#vm #vc: erased (Seq.seq S8.t))
          (#vsg: erased (Seq.lseq S8.t 4627))
requires A.pts_to pk #ppk vpk ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
         A.pts_to sg #psg vsg **
         pure (SZ.v msg_len == Seq.length vm /\ SZ.v ctx_len == Seq.length vc /\
               SZ.fits (66 + Seq.length vc + Seq.length vm))
returns res: bool
ensures A.pts_to pk #ppk vpk ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
        A.pts_to sg #psg vsg **
        pure (res == M.verify mldsa87 vpk vm vc vsg)
{
  DSA.verify_impl pk msg msg_len ctx ctx_len sg (hide mldsa87) 8sz 7sz 2sz 60sz 64sz 19sz 75sz 32ul
}

(** Algorithm 7 on a formatted message [M']. *)
fn sign_internal (sg sk msg: A.array S8.t) (msg_len: SZ.t) (rnd: A.array S8.t)
                 (#psk #pm #pr: perm)
                 (#vsg0: erased (Seq.lseq S8.t 4627))
                 (#vsk: erased (Seq.lseq S8.t 4896))
                 (#vm: erased (Seq.seq S8.t))
                 (#vr: erased (Seq.lseq S8.t 32))
requires A.pts_to sg vsg0 ** A.pts_to sk #psk vsk ** A.pts_to msg #pm vm **
         A.pts_to rnd #pr vr **
         pure (SZ.v msg_len == Seq.length vm /\ SZ.fits (64 + Seq.length vm))
returns ok: bool
ensures exists* vsg.
        A.pts_to sg vsg ** A.pts_to sk #psk vsk ** A.pts_to msg #pm vm **
        A.pts_to rnd #pr vr **
        pure (Seq.length vsg == 4627 /\
              (if ok then M.sign_internal mldsa87 vsk vm vr == Some vsg
               else M.sign_internal mldsa87 vsk vm vr == None))
{
  DSA.sign_internal_impl sg sk msg msg_len rnd (hide mldsa87) 8sz 7sz 2sz 60sz 64sz 19sz 75sz 32ul
}

(** Algorithm 8 on a formatted message [M']. *)
fn verify_internal (pk msg: A.array S8.t) (msg_len: SZ.t) (sg: A.array S8.t)
                   (#ppk #pm #psg: perm)
                   (#vpk: erased (Seq.lseq S8.t 2592))
                   (#vm: erased (Seq.seq S8.t))
                   (#vsg: erased (Seq.lseq S8.t 4627))
requires A.pts_to pk #ppk vpk ** A.pts_to msg #pm vm ** A.pts_to sg #psg vsg **
         pure (SZ.v msg_len == Seq.length vm /\ SZ.fits (64 + Seq.length vm))
returns res: bool
ensures A.pts_to pk #ppk vpk ** A.pts_to msg #pm vm ** A.pts_to sg #psg vsg **
        pure (res == M.verify_internal mldsa87 vpk vm vsg)
{
  DSA.verify_internal_impl pk msg msg_len sg (hide mldsa87) 8sz 7sz 2sz 60sz 64sz 19sz 75sz 32ul
}

(** Algorithm 7 from the 64-byte message representative [mu]. *)
fn sign_mu (sg sk mu rnd: A.array S8.t) (#psk #pm #pr: perm)
           (#vsg0: erased (Seq.lseq S8.t 4627))
           (#vsk: erased (Seq.lseq S8.t 4896))
           (#vm: erased (Seq.lseq S8.t 64))
           (#vr: erased (Seq.lseq S8.t 32))
requires A.pts_to sg vsg0 ** A.pts_to sk #psk vsk ** A.pts_to mu #pm vm **
         A.pts_to rnd #pr vr
returns ok: bool
ensures exists* vsg.
        A.pts_to sg vsg ** A.pts_to sk #psk vsk ** A.pts_to mu #pm vm **
        A.pts_to rnd #pr vr **
        pure (Seq.length vsg == 4627 /\
              (if ok then M.sign_mu mldsa87 vsk vm vr == Some vsg
               else M.sign_mu mldsa87 vsk vm vr == None))
{
  Sign.sign_mu_impl sg sk mu rnd (hide mldsa87) 8sz 7sz 2sz 60sz 64sz 19sz 75sz 32ul
}

(** Algorithm 8 from the 64-byte message representative [mu]. *)
fn verify_mu (pk mu sg: A.array S8.t) (#ppk #pm #psg: perm)
             (#vpk: erased (Seq.lseq S8.t 2592))
             (#vm: erased (Seq.lseq S8.t 64))
             (#vsg: erased (Seq.lseq S8.t 4627))
requires A.pts_to pk #ppk vpk ** A.pts_to mu #pm vm ** A.pts_to sg #psg vsg
returns res: bool
ensures A.pts_to pk #ppk vpk ** A.pts_to mu #pm vm ** A.pts_to sg #psg vsg **
        pure (res == M.verify_mu mldsa87 vpk vm vsg)
{
  Verify.verify_mu_impl pk mu sg (hide mldsa87) 8sz 7sz 2sz 60sz 64sz 19sz 75sz 32ul
}

#pop-options
