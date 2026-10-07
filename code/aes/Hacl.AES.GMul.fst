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
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Vec = Hacl.Vec128
module Poly = Spec.GF128.Poly
module Alg = Spec.GF128.Algebra

fn gmul_impl (a: A.array S8.t) (h: A.array S8.t)
             (#va #vh: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen)
ensures exists* (va': Seq.seq S8.t). A.pts_to a va' ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  Seq.length va' == blocklen /\
  vals va' == gmul (vals va) (Poly.xtimes (vals vh)))
{
  if Vec.supported () {
    Hacl.AES.GF128.NI.gmul_ni a h;
  } else {
    Hacl.AES.GF128.gmul_portable a h;
    Alg.gmul_xt_right (vals va) (vals vh) 1;
    Hacl.AES.GF128.shift_reduce_impl a;
  }
}

(** [a := gmul (gadd a b@off) h]: the addition and the multiplication
    together, which is the whole of GHASH's inner loop.  The portable branch
    is the two separate routines, which is what the caller would have run
    anyway; the fast branch keeps the accumulator in a register across both,
    and so avoids sixteen bytes of scalar traffic and a store-forwarding
    stall on every block. *)
fn gmul_add_impl (a: A.array S8.t) (h: A.array S8.t) (b: A.array S8.t) (off: SZ.t)
                 (#va #vh: erased (Seq.seq S8.t))
                 (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to h vh ** A.pts_to b #pb vb ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  SZ.v off + blocklen <= Seq.length vb)
ensures exists* (va': Seq.seq S8.t).
  A.pts_to a va' ** A.pts_to h vh ** A.pts_to b #pb vb ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  SZ.v off + blocklen <= Seq.length vb /\ Seq.length va' == blocklen /\
  vals va' == gmul (gadd (vals va)
                         (Seq.slice (vals vb) (SZ.v off) (SZ.v off + blocklen)))
                   (Poly.xtimes (vals vh)))
{
  if Vec.supported () {
    Hacl.AES.GF128.NI.gmul_add_ni a h b off;
  } else {
    Hacl.AES.GF128.gadd_at_impl a b off;
    with vx. assert A.pts_to a vx;
    Hacl.AES.GF128.gmul_portable a h;
    Alg.gmul_xt_right (vals vx) (vals vh) 1;
    Hacl.AES.GF128.shift_reduce_impl a;
  }
}
