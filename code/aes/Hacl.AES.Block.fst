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

(** The AES block cipher, on whichever implementation the machine has.

    [Hacl.AES.Cipher.cipher_portable] computes the S-box from its algebraic
    definition and runs anywhere; [Hacl.AES.NI.cipher_ni] is one [AESENC] per
    round and needs the AES instructions.  The two have the same
    postcondition, so this dispatcher has nothing to prove: both branches
    leave the same specification value behind, and no caller can tell which
    ran.

    The test is per block rather than per message.  That is one perfectly
    predicted branch against a whole block encryption, which is not
    measurable, and it buys the property that {i every} caller -- CTR, GCM,
    and anything added later -- gets the fast path without a dispatching
    variant of its own.

    Feature detection itself is [__builtin_cpu_supports], which reads a
    cached CPUID result. *)
module Hacl.AES.Block

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Vec = Hacl.Vec128
module Copy = Hacl.Impl.Copy

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn cipher_impl ([@@@FStar.Attributes.monomorphize] p: params)
               (st: A.array S8.t) (w: A.array S8.t)
               (#v0 #vw: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to w vw ** pure (
  Seq.length v0 == blocklen /\ Seq.length vw == xkeylen p.pv)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 ** A.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length v0 == blocklen /\
  Seq.length v1 == blocklen /\
  vals v1 == cipher p.pv (vals vw) (vals v0))
{
  if Vec.supported () {
    Hacl.AES.NI.cipher_ni p st w;
  } else {
    Hacl.AES.Cipher.cipher_portable p st w;
  }
}

(** {2 One counter-mode block}

    Counter mode's inner step -- encrypt the counter, exclusive-or the result
    into the message -- rather than just the block cipher.  Keeping it whole
    is what lets the fast path hold the keystream in a register from the
    moment it is produced to the moment it is consumed; see
    [Hacl.AES.NI.ctr_block_ni] for why that matters.  The portable path has
    to write the keystream down, so it takes a sixteen-byte scratch array,
    which the fast path ignores.  Only a caller with a whole block left may
    use this. *)

fn xor_at (msg: A.array S8.t) (idx: SZ.t) (ka: A.array S8.t)
          (#vm: erased (Seq.seq S8.t)) (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to msg vm ** A.pts_to ka #pk vk ** pure (
  Seq.length vk == blocklen /\ SZ.v idx + blocklen <= Seq.length vm)
ensures exists* (vm': Seq.seq S8.t).
  A.pts_to msg vm' ** A.pts_to ka #pk vk ** pure (
  Seq.length vk == blocklen /\ SZ.v idx + blocklen <= Seq.length vm /\
  Seq.length vm' == Seq.length vm /\
  (forall (k: nat). k < Seq.length vm ==>
     Seq.index (vals vm') k ==
       (if SZ.v idx <= k && k < SZ.v idx + blocklen
        then Seq.index (vals vm) k ^^ Seq.index (vals vk) (k - SZ.v idx)
        else Seq.index (vals vm) k)))
{
  A.pts_to_len msg;
  A.pts_to_len ka;
  let mut t = 0sz;
  while (let vt = !t; SZ.lt vt 16sz)
  invariant exists* (vt: SZ.t) (vm1: Seq.seq S8.t).
    pts_to t vt ** A.pts_to msg vm1 ** A.pts_to ka #pk vk **
    pure (SZ.v vt <= blocklen /\ Seq.length vk == blocklen /\
          SZ.v idx + blocklen <= Seq.length vm /\
          Seq.length vm1 == Seq.length vm /\
          (forall (k: nat). k < Seq.length vm ==>
             Seq.index (vals vm1) k ==
               (if SZ.v idx <= k && k < SZ.v idx + SZ.v vt
                then Seq.index (vals vm) k ^^ Seq.index (vals vk) (k - SZ.v idx)
                else Seq.index (vals vm) k)))
  decreases (blocklen - SZ.v (!t))
  {
    let vt = !t;
    let i = SZ.add idx vt;
    let a = A.(msg.(i));
    let b = A.(ka.(vt));
    let y = bxor a b;
    with vm1. assert A.pts_to msg vm1;
    vals_upd vm1 (SZ.v i) y;
    A.((msg.(i) <- y));
    t := SZ.add vt 1sz;
  };
  ()
}

fn ctr_block_impl ([@@@FStar.Attributes.monomorphize] p: params)
                  (msg: A.array S8.t) (idx: SZ.t) (w: A.array S8.t)
                  (ctr: A.array S8.t) (ka: A.array S8.t)
                  (#vm #vw #vc #vk: erased (Seq.seq S8.t))
requires A.pts_to msg vm ** A.pts_to w vw ** A.pts_to ctr vc ** A.pts_to ka vk **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vk == blocklen /\ SZ.v idx + blocklen <= Seq.length vm)
ensures exists* (vm' vk': Seq.seq S8.t).
  A.pts_to msg vm' ** A.pts_to w vw ** A.pts_to ctr vc ** A.pts_to ka vk' **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vk' == blocklen /\ SZ.v idx + blocklen <= Seq.length vm /\
        Seq.length vm' == Seq.length vm /\
        (forall (k: nat). k < Seq.length vm ==>
           Seq.index (vals vm') k ==
             (if SZ.v idx <= k && k < SZ.v idx + blocklen
              then Seq.index (vals vm) k ^^
                   Seq.index (cipher p.pv (vals vw) (vals vc)) (k - SZ.v idx)
              else Seq.index (vals vm) k)))
{
  A.pts_to_len msg;
  A.pts_to_len ctr;
  A.pts_to_len ka;
  if Vec.supported () {
    Hacl.AES.NI.ctr_block_ni p msg idx w ctr;
  } else {
    Copy.copy_exact ka ctr 16sz;
    Hacl.AES.Cipher.cipher_portable p ka w;
    xor_at msg idx ka;
  }
}

#pop-options
