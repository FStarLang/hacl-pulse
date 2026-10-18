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


(** The FIPS 204 entry points, generic in the parameter set: the pure
    variant with a context string (Algorithms 2 and 3), the internal
    variant on a formatted message (Algorithms 7 and 8), and the
    external-mu variant on a message representative. *)
module Hacl.Impl.MLDSA.DSA

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Params
open Spec.MLDSA.Encode
open Hacl.Impl.MLDSA.Mu
open Hacl.Impl.MLDSA.Sign
open Hacl.Impl.MLDSA.Verify

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module Seq = FStar.Seq
module HSZ = Hacl.SizeT
module Sub = Hacl.Impl.Sub
module M = Spec.MLDSA

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let rnd_zero_eq (v: Seq.seq S8.t)
  : Lemma (requires v == Seq.create 32 S8.zero) (ensures v == M.rnd_zero)
  = S8.v_extensional S8.zero (M.byte 0);
    Seq.lemma_eq_intro v M.rnd_zero

(** {2 Signing} *)

(** Algorithm 7 on [M'], with [mu = H(sk.tr || M')]. *)
fn sign_internal_impl (sg sk msg: A.array S8.t) (msg_len: SZ.t) (rnd: A.array S8.t)
                      (p: erased params)
                      ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                      ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                      (gd: U32.t)
                      (#vs: erased (Seq.seq S8.t)) (#pk #pm #pr: perm)
                      (#vk #vm #vr: erased (Seq.seq S8.t))
requires A.pts_to sg vs ** A.pts_to sk #pk vk ** A.pts_to msg #pm vm ** A.pts_to rnd #pr vr **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vs == sig_len p /\ Seq.length vk == sk_len p /\
               SZ.v msg_len == Seq.length vm /\ SZ.fits (64 + Seq.length vm) /\
               Seq.length vr == 32)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sg v ** A.pts_to sk #pk vk ** A.pts_to msg #pm vm ** A.pts_to rnd #pr vr **
  pure (Seq.length v == sig_len p /\ Seq.length vk == sk_len p /\ Seq.length vr == 32 /\
        (if ok then M.sign_internal p vk vm vr == Some v
         else M.sign_internal p vk vm vr == None))
{
  A.pts_to_len sk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sk_len p);
  sk_layout p;
  let mut mu = [| (S8.zero <: S8.t); 64sz |];
  let tr = Sub.sub sk 64sz 128sz;
  mu_impl mu tr msg msg_len;
  Sub.unsub_id sk 64 128 tr;
  sign_mu_impl sg sk mu rnd p k l eta tau ctl g1bits omega gd
}

(** Algorithm 2, [ML-DSA.Sign], with [rnd] supplied by the caller.
    Fails, without signing, when the context is longer than 255 bytes. *)
fn sign_impl (sg sk msg: A.array S8.t) (msg_len: SZ.t) (ctx: A.array S8.t) (ctx_len: SZ.t)
             (rnd: A.array S8.t) (p: erased params)
             ([@@@FStar.Attributes.monomorphize] k: SZ.t)
             ([@@@FStar.Attributes.monomorphize] l: SZ.t)
             ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
             ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
             ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
             ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
             ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
             (gd: U32.t)
             (#vs: erased (Seq.seq S8.t)) (#pk #pm #pc #pr: perm)
             (#vk #vm #vc #vr: erased (Seq.seq S8.t))
requires A.pts_to sg vs ** A.pts_to sk #pk vk ** A.pts_to msg #pm vm **
         A.pts_to ctx #pc vc ** A.pts_to rnd #pr vr **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vs == sig_len p /\ Seq.length vk == sk_len p /\
               SZ.v msg_len == Seq.length vm /\ SZ.v ctx_len == Seq.length vc /\
               SZ.fits (66 + Seq.length vc + Seq.length vm) /\ Seq.length vr == 32)
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sg v ** A.pts_to sk #pk vk ** A.pts_to msg #pm vm **
  A.pts_to ctx #pc vc ** A.pts_to rnd #pr vr **
  pure (Seq.length v == sig_len p /\ Seq.length vk == sk_len p /\ Seq.length vr == 32 /\
        (if ok then M.sign p vk vm vc vr == Some v else M.sign p vk vm vc vr == None))
{
  A.pts_to_len sk;
  A.pts_to_len sg;
  if (SZ.gte ctx_len 256sz) {
    false
  } else {
    HSZ.fits32 ();
    SZ.fits_u32_implies_fits (sk_len p);
    sk_layout p;
    let mut mu = [| (S8.zero <: S8.t); 64sz |];
    let tr = Sub.sub sk 64sz 128sz;
    mu_ctx_impl mu tr msg msg_len ctx ctx_len;
    Sub.unsub_id sk 64 128 tr;
    sign_mu_impl sg sk mu rnd p k l eta tau ctl g1bits omega gd
  }
}

(** The deterministic variant: [rnd = 0^32]. *)
fn sign_det_impl (sg sk msg: A.array S8.t) (msg_len: SZ.t) (ctx: A.array S8.t) (ctx_len: SZ.t)
                 (p: erased params)
                 ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                 (gd: U32.t)
                 (#vs: erased (Seq.seq S8.t)) (#pk #pm #pc: perm)
                 (#vk #vm #vc: erased (Seq.seq S8.t))
requires A.pts_to sg vs ** A.pts_to sk #pk vk ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vs == sig_len p /\ Seq.length vk == sk_len p /\
               SZ.v msg_len == Seq.length vm /\ SZ.v ctx_len == Seq.length vc /\
               SZ.fits (66 + Seq.length vc + Seq.length vm))
returns ok: bool
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sg v ** A.pts_to sk #pk vk ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
  pure (Seq.length v == sig_len p /\ Seq.length vk == sk_len p /\
        (if ok then M.sign p vk vm vc M.rnd_zero == Some v
         else M.sign p vk vm vc M.rnd_zero == None))
{
  let mut rnd = [| (S8.zero <: S8.t); 32sz |];
  with vr. assert (A.pts_to rnd vr);
  rnd_zero_eq vr;
  sign_impl sg sk msg msg_len ctx ctx_len rnd p k l eta tau ctl g1bits omega gd
}

(** {2 Verification} *)

(** Algorithm 8 on [M'], with [mu = H(H(pk, 64) || M')]. *)
fn verify_internal_impl (pk msg: A.array S8.t) (msg_len: SZ.t) (sg: A.array S8.t)
                        (p: erased params)
                        ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                        ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                        ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                        ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                        ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                        ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                        ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                        (gd: U32.t)
                        (#pp #pm #ps: perm) (#vpk #vm #vsg: erased (Seq.seq S8.t))
requires A.pts_to pk #pp vpk ** A.pts_to msg #pm vm ** A.pts_to sg #ps vsg **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vpk == pk_len p /\ Seq.length vsg == sig_len p /\
               SZ.v msg_len == Seq.length vm /\ SZ.fits (64 + Seq.length vm))
returns res: bool
ensures A.pts_to pk #pp vpk ** A.pts_to msg #pm vm ** A.pts_to sg #ps vsg **
  pure (Seq.length vpk == pk_len p /\ Seq.length vsg == sig_len p /\
        res == M.verify_internal p vpk vm vsg)
{
  A.pts_to_len pk;
  HSZ.fits32 ();
  let pkl = SZ.add 32sz (SZ.mul 320sz k);
  let mut tr = [| (S8.zero <: S8.t); 64sz |];
  Hacl.Hash.SHA3.shake256 tr 64sz pk pkl;
  let mut mu = [| (S8.zero <: S8.t); 64sz |];
  mu_impl mu tr msg msg_len;
  verify_mu_impl pk mu sg p k l eta tau ctl g1bits omega gd
}

(** Algorithm 3, [ML-DSA.Verify].  A context longer than 255 bytes is
    rejected. *)
fn verify_impl (pk msg: A.array S8.t) (msg_len: SZ.t) (ctx: A.array S8.t) (ctx_len: SZ.t)
               (sg: A.array S8.t) (p: erased params)
               ([@@@FStar.Attributes.monomorphize] k: SZ.t)
               ([@@@FStar.Attributes.monomorphize] l: SZ.t)
               ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
               ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
               ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
               ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
               ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
               (gd: U32.t)
               (#pp #pm #pc #ps: perm) (#vpk #vm #vc #vsg: erased (Seq.seq S8.t))
requires A.pts_to pk #pp vpk ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
         A.pts_to sg #ps vsg **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vpk == pk_len p /\ Seq.length vsg == sig_len p /\
               SZ.v msg_len == Seq.length vm /\ SZ.v ctx_len == Seq.length vc /\
               SZ.fits (66 + Seq.length vc + Seq.length vm))
returns res: bool
ensures A.pts_to pk #pp vpk ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
  A.pts_to sg #ps vsg **
  pure (Seq.length vpk == pk_len p /\ Seq.length vsg == sig_len p /\
        res == M.verify p vpk vm vc vsg)
{
  if (SZ.gte ctx_len 256sz) {
    false
  } else {
    A.pts_to_len pk;
    HSZ.fits32 ();
    let pkl = SZ.add 32sz (SZ.mul 320sz k);
    let mut tr = [| (S8.zero <: S8.t); 64sz |];
    Hacl.Hash.SHA3.shake256 tr 64sz pk pkl;
    let mut mu = [| (S8.zero <: S8.t); 64sz |];
    mu_ctx_impl mu tr msg msg_len ctx ctx_len;
    verify_mu_impl pk mu sg p k l eta tau ctl g1bits omega gd
  }
}

#pop-options
