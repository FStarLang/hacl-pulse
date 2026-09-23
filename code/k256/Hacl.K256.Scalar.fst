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

(** The scalar field [Z/n].

    The same eight limbs and the same Montgomery machinery as
    [Hacl.K256.Field], with [qmod] in place of [fmod].  ECDSA needs
    addition, multiplication and inversion here, plus two decoders: one
    that insists the scalar is a proper private key, and one that reduces
    a hash modulo the order.

    Because [Hacl.Impl.Mont4] takes its modulus as data, none of this
    duplicates any code in the emitted C: the two fields share every
    operation and differ only in the table they pass. *)
module Hacl.K256.Scalar

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.K256.Field
open Spec.Mont4
open Hacl.Spec.Bytes
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.Impl.Bignum4
open Hacl.Impl.Mont4
open Hacl.K256.Tables
open Hacl.Impl.Exp4

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module K = Spec.K256
module MA = Spec.ModArith

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 What a scalar is} *)

let qelem (v: Seq.seq S64.t) : prop = res qmod (vals v)

let qmod_m (_: unit) : Lemma (qmod.m == K.order) = ()

let qev (v: Seq.seq S64.t) : GTot K.qelem = mev qmod (vals v)

(** {2 The ring operations} *)

fn qadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == K.qadd (qev va) (qev vb))
{
  qmod_ok (); qmod_m ();
  mev_add qmod (vals va) (vals vb);
  let nm = qnm ();
  aadd out a b nm qmod;
  drop_table nm;
}

fn qmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == K.qmul (qev va) (qev vb))
{
  qmod_ok (); qmod_m ();
  mev_mul qmod (vals va) (vals vb);
  let ms = qms ();
  let nm = qnm ();
  amul out a b ms nm qmu qmod;
  drop_table ms;
  drop_table nm;
}

fn qinv (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == K.qinv (qev va))
{
  qmod_ok (); qmod_m ();
  assert_norm (K.order - 2 < pow2 256);
  limbs_ok (K.order - 2);
  let e = qinv_e ();
  let r1 = qr1 ();
  let ms = qms ();
  let nm = qnm ();
  mexp out a e r1 ms nm qmu qmod;
  drop_table e;
  drop_table r1;
  drop_table ms;
  drop_table nm;
}

(** {2 Comparison} *)

fn qeq (a b: A.array S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem va /\ qelem vb)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (qev va = qev vb))
{
  qmod_ok (); qmod_m ();
  mev_eq qmod (vals va) (vals vb);
  aeq a b
}

fn qis_zero (a: A.array S64.t) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** pure (qelem va)
returns r: bool
ensures A.pts_to a #pa va ** pure (r == (qev va = K.qzero))
{
  qmod_ok (); qmod_m ();
  mev_iszero qmod (vals va);
  mzero_ok ();
  let z = S64.zero;
  let mut az = [| z; 4sz |]; A.pts_to_len az; A.pts_to_len az;
  azero az;
  let r = aeq a az;
  r
}

(** {2 Conversions} *)

inline_for_extraction
fn qto (out a: A.array S64.t)
       (#vo: erased (Seq.seq S64.t))
       (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ res qmod (vals va))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (qelem vo' /\ qev vo' == eval (vals va))
{
  qmod_ok (); qmod_m ();
  mev_to qmod (vals va);
  let ms = qms ();
  let nm = qnm ();
  let r2 = qr2 ();
  amul out a r2 ms nm qmu qmod;
  drop_table ms;
  drop_table nm;
  drop_table r2;
}

inline_for_extraction
fn qfrom (out a: A.array S64.t)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ qelem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == nl /\ bnd (vals vo') base /\
        eval (vals vo') == qev va)
{
  qmod_ok (); qmod_m ();
  mone_ok ();
  mev_of qmod (vals va);
  let ms = qms ();
  let nm = qnm ();
  let one = mone ();
  amul out a one ms nm qmu qmod;
  drop_table ms;
  drop_table nm;
  drop_table one;
}

(** {2 Bytes}

    Two decoders.  [qload] is the private-key and signature-component
    check: thirty-two big-endian bytes are a scalar only when they are
    strictly between zero and the order.  [qload_mod] is the hash
    conversion, which reduces instead of rejecting; one conditional
    subtraction suffices because [2^256] is below twice the order. *)

#push-options "--z3rlimit 200"

fn qload (out: A.array S64.t) (b: A.array S8.t)
         (#vo: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
returns r: bool
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (qelem vo' /\ r == (0 < be_nat vb && be_nat vb < K.order) /\
        (r ==> qev vo' == be_nat vb))
{
  qmod_ok (); qmod_m ();
  assert_norm (pow2 256 < 2 * K.order);
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; let mut asv = [| z128; 4sz |]; A.pts_to_len asv; A.pts_to_len at; A.pts_to_len asv;
  load_be at b;
  let nm = qnm ();
  let lo = abelow at asv nm qmod;
  drop_table nm;
  qto out at;
  let nz = qis_zero out;
  lo && not nz
}

fn qload_mod (out: A.array S64.t) (b: A.array S8.t)
             (#vo: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qev vo' == be_nat vb % K.order)
{
  qmod_ok (); qmod_m ();
  assert_norm (pow2 256 < 2 * K.order);
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; let mut asv = [| z128; 4sz |]; A.pts_to_len asv; A.pts_to_len at; A.pts_to_len asv;
  load_be at b;
  let nm = qnm ();
  ared at asv nm qmod;
  drop_table nm;
  qto out at;
  ()
}

fn qstore (b: A.array S8.t) (a: A.array S64.t)
          (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ qelem va)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == nat_to_be 32 (qev va))
{
  let z = S64.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; A.pts_to_len at;
  qfrom at a;
  store_be b at;
  ()
}

#pop-options

#pop-options
