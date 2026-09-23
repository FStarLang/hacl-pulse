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

(** The 256-bit field, in Montgomery form, at four limbs of sixty-four
    bits.

    Every operation here works on four limbs held in an array, and every
    one of them is specified against [Spec.Field4].  The limb-level carry
    chains, the conditional subtractions and the Montgomery reduction loops
    are not something a client ever needs to see.

    The one thing a caller does notice: the scratch buffer [s] is an array
    of wide words rather than of limbs.  A sum of two limbs no longer fits
    in a limb, so it is accumulated one width up and narrowed on the way
    out. *)
module Hacl.Impl.Bignum4

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.Montgomery4
open Spec.Field4
open Hacl.Impl.Limb4
open Hacl.Spec.Bytes

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Cast = Hacl.Secret.Cast
module Loops = Hacl.Spec.Loops

val csub_op (a: A.array S64.t) (s: A.array S128.t) (nm: A.array S64.t)
           (top: S64.t) (d: erased modulus)
           (#va: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S128.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to a va ** A.pts_to s vs ** A.pts_to nm #pn vnm **
      pure (modulus_ok d /\ Seq.length va == nl /\ Seq.length vs == nl /\
            Seq.length vnm == nl /\ vals vnm == d.nm /\
            bnd (vals va) base /\ S64.v top <= 1 /\
            eval (vals va) + pow2 256 * S64.v top < 2 * d.m))
    (ensures fun _ -> exists* (va': Seq.seq S64.t) (vs': Seq.seq S128.t).
      A.pts_to a va' ** A.pts_to s vs' ** A.pts_to nm #pn vnm **
      pure (Seq.length va' == nl /\ Seq.length vs' == nl /\
            res d (vals va') /\ vals va' == csub d (vals va) (S64.v top)))

val madd_op (out a b: A.array S64.t) (s: A.array S128.t) (nm: A.array S64.t)
           (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S128.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to a #pa va **
      A.pts_to b #pb vb ** A.pts_to nm #pn vnm **
      pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
            Seq.length vnm == nl /\ vals vnm == d.nm /\
            res d (vals va) /\ res d (vals vb)))
    (ensures fun _ -> exists* (vo': Seq.seq S64.t) (vs': Seq.seq S128.t).
      A.pts_to out vo' ** A.pts_to s vs' ** A.pts_to a #pa va **
      A.pts_to b #pb vb ** A.pts_to nm #pn vnm **
      pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
            res d (vals vo') /\ vals vo' == madd d (vals va) (vals vb)))

val negsub_op (w: A.array S128.t) (a b: A.array S64.t)
             (#vw: erased (Seq.seq S128.t))
             (#pa: perm) (#va: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S64.t))
  : stt S64.t
    (requires A.pts_to w vw ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      pure (Seq.length vw == nl /\ Seq.length va == nl /\ Seq.length vb == nl /\
            bnd (vals va) base /\ bnd (vals vb) base))
    (ensures fun co -> exists* (vw': Seq.seq S128.t).
      A.pts_to w vw' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      pure (Seq.length vw' == nl /\ bnd (vals128 vw') base /\
            vals128 vw' == carry_low (addw (vals va) (negw (vals vb))) /\
            S64.v co == carry_out (addw (vals va) (negw (vals vb)))))

val msub_op (out a b: A.array S64.t) (s: A.array S128.t) (ms: A.array S64.t)
           (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S128.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to out vo ** A.pts_to s vs ** A.pts_to a #pa va **
      A.pts_to b #pb vb ** A.pts_to ms #pm vms **
      pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vs == nl /\
            Seq.length vms == nl /\ vals vms == d.ms /\
            res d (vals va) /\ res d (vals vb)))
    (ensures fun _ -> exists* (vo': Seq.seq S64.t) (vs': Seq.seq S128.t).
      A.pts_to out vo' ** A.pts_to s vs' ** A.pts_to a #pa va **
      A.pts_to b #pb vb ** A.pts_to ms #pm vms **
      pure (Seq.length vo' == nl /\ Seq.length vs' == nl /\
            res d (vals vo') /\ vals vo' == msub d (vals va) (vals vb)))

val mmul_op (out: A.array S64.t) (a b: A.array S64.t) (p t r s: A.array S128.t)
           (ms nm: A.array S64.t) (mu: S64.t) (d: erased modulus)
           (#vo: erased (Seq.seq S64.t)) (#vp: erased (Seq.seq S128.t))
           (#vt: erased (Seq.seq S128.t)) (#vr: erased (Seq.seq S128.t))
           (#vs: erased (Seq.seq S128.t))
           (#pa: perm) (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#pm: perm) (#vms: erased (Seq.seq S64.t))
           (#pn: perm) (#vnm: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to out vo ** A.pts_to p vp ** A.pts_to t vt ** A.pts_to r vr **
      A.pts_to s vs ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
      pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vp == nw /\
            Seq.length vt == ncol /\ Seq.length vr == nl + 1 /\
            Seq.length vs == nl /\
            Seq.length vms == nl /\ Seq.length vnm == nl /\
            vals vms == d.ms /\ vals vnm == d.nm /\ S64.v mu == d.mu /\
            res d (vals va) /\ res d (vals vb)))
    (ensures fun _ -> exists* (vo': Seq.seq S64.t) (vp': Seq.seq S128.t)
                    (vt': Seq.seq S128.t) (vr': Seq.seq S128.t) (vs': Seq.seq S128.t).
      A.pts_to out vo' ** A.pts_to p vp' ** A.pts_to t vt' ** A.pts_to r vr' **
      A.pts_to s vs' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
      pure (Seq.length vo' == nl /\ Seq.length vp' == nw /\
            Seq.length vt' == ncol /\ Seq.length vr' == nl + 1 /\
            Seq.length vs' == nl /\
            res d (vals vo') /\ vals vo' == mmul d (vals va) (vals vb)))

val load_be (a: A.array S64.t) (b: A.array S8.t)
           (#va: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to a va ** A.pts_to b #pb vb **
      pure (Seq.length va == nl /\ Seq.length vb == 32))
    (ensures fun _ -> exists* (va': Seq.seq S64.t).
      A.pts_to a va' ** A.pts_to b #pb vb **
      pure (Seq.length va' == nl /\ bnd (vals va') base /\
            eval (vals va') == be_nat vb))

val store_be (b: A.array S8.t) (a: A.array S64.t)
            (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
  : stt unit
    (requires A.pts_to b vb ** A.pts_to a #pa va **
      pure (Seq.length vb == 32 /\ Seq.length va == nl /\ bnd (vals va) base))
    (ensures fun _ -> exists* (vb': Seq.seq S8.t).
      A.pts_to b vb' ** A.pts_to a #pa va **
      pure (vb' == nat_to_be 32 (eval (vals va))))

