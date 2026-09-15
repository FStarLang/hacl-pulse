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

(** GHASH's multiplication, on whichever implementation the machine has.

    [Hacl.AES.GF128.gmul_portable] is the shift-and-add loop of SP 800-38D
    and runs anywhere; [Hacl.AES.GF128.NI.gmul_ni] is a dozen instructions
    and needs [PCLMULQDQ].  They have the same postcondition, so this
    dispatcher has nothing to prove, and the test is once per block for the
    same reason as in [Hacl.AES.Block]: one predictable branch against the
    work it guards, and every caller gets the fast path without a variant of
    its own. *)
module Hacl.AES.GMul

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.GF128

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Vec = Hacl.Vec128

fn gmul_impl (a: A.array S8.t) (h: A.array S8.t)
             (#va #vh: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen)
ensures exists* (va': Seq.seq S8.t). A.pts_to a va' ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  Seq.length va' == blocklen /\
  vals va' == gmul (vals va) (vals vh))
{
  if Vec.supported () {
    Hacl.AES.GF128.NI.gmul_ni a h;
  } else {
    Hacl.AES.GF128.gmul_portable a h;
  }
}
