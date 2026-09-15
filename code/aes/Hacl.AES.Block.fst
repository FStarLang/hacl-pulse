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

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Vec = Hacl.Vec128

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
