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

(** Leaving the curve: affine coordinates and bytes.

    Signing and ECDH convert points that depend on a secret scalar, so the
    inverses here are constant-time: the field's is the fixed addition
    chain of {!Hacl.P384.Inverse}, the scalar's ([invmod_ct]) the generic
    constant-time exponentiation.  Everything else is
    straight-line code. *)
module Hacl.P384.Encode

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Spec.Bytes
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Impl.Copy
open Hacl.Bignum.Base
open Hacl.Bignum.Exponentiation
open Hacl.Bignum.Convert
open Hacl.P384.Tables
open Hacl.P384.Lemmas
open Hacl.P384.Field
open Hacl.P384.Verify

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Mem = Hacl.Mem
module Inv = Hacl.P384.Inverse

(** Forty-eight bytes that read back as [x] are [x]'s encoding. *)
let to_be48 (v: Seq.seq S8.t) (x: nat)
  : Lemma (requires Seq.length v == 48 /\ be_nat v == x /\ x < pow2 384)
          (ensures v == nat_to_be 48 x)
  = assert_norm (8 * 48 == 384);
    be_nat_to_be 48 x;
    Spec.RSAPSS.be_nat_inj v (nat_to_be 48 x);
    Seq.lemma_eq_elim v (nat_to_be 48 x)

let aff (x y z: Seq.seq S64.t) : GTot (nat & nat) =
  let zi = P.finv (fev z) in (P.fmul (fev x) zi, P.fmul (fev y) zi)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [res = a^(n-2) mod n], in time independent of [a]. *)
fn invmod_ct (res a nm r2: A.array S64.t) (mu: S64.t)
             (#vres: erased (Seq.seq S64.t))
             (#pa #pn #pr: perm) (#va #vr2: erased (Seq.seq S64.t))
             (#vn: erased (s: Seq.seq S64.t { 1 < num s /\ 0 < Seq.length s }))
requires A.pts_to res vres ** A.pts_to a #pa va **
         A.pts_to nm #pn vn ** A.pts_to r2 #pr vr2 **
  pure (Seq.length vres == 6 /\ Seq.length va == 6 /\
        Seq.length vn == 6 /\ Seq.length vr2 == 6 /\
        num va < num vn /\
        num vr2 == (wt 6 * wt 6) % num vn /\
        (S64.v mu * S64.v (Seq.index vn 0) + 1) % base == 0)
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to a #pa va **
  A.pts_to nm #pn vn ** A.pts_to r2 #pr vr2 **
  pure (Seq.length v == 6 /\ num v == pw (num va) (num vn - 2) % num vn)
{
  facts ();
  SZ.fits_at_least_16 96;
  let z = S64.zero;
  let mut e = [| z; 6sz |];
  Mem.track e; A.pts_to_len e; let mut two = [| z; 6sz |];
  Mem.track two; A.pts_to_len two; let mut am = [| z; 6sz |];
  Mem.track am; A.pts_to_len am; let mut acc = [| z; 6sz |];
  Mem.track acc; A.pts_to_len acc; let mut t = [| z; 6sz |];
  Mem.track t; A.pts_to_len t; let mut wide = [| z; 12sz |];
  Mem.track wide; A.pts_to_len wide;
  zero two 6sz;
  with v0. assert (A.pts_to two v0);
  num_zeros_above v0 0;
  pre_zero v0;
  A.((two.(0sz) <- S64.classify 2uL));
  num_upd v0 0 (S64.classify 2uL);
  let c = sub e nm two 6sz;
  with v2. assert (A.pts_to e v2);
  six_bnd v2;
  inv_exp (num vn) (num v2) (S64.v c) (wt 6);
  mod_exp_consttime res a e 384sz r2 nm 6sz mu am acc t wide;
  Mem.wipe wide 12sz;
  Mem.wipe t 6sz;
  Mem.wipe acc 6sz;
  Mem.wipe am 6sz;
  Mem.wipe two 6sz;
  Mem.wipe e 6sz;
  ()
}

(** The affine coordinates of [(x : y : z)], as plain numbers below [p]. *)
fn to_aff (ax ay x y z: A.array S64.t)
          (#vax #vay: erased (Seq.seq S64.t))
          (#pp: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires A.pts_to ax vax ** A.pts_to ay vay **
  A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (Seq.length vax == 6 /\ Seq.length vay == 6 /\ pt_ok vx vy vz)
ensures exists* (wx wy: Seq.seq S64.t).
  A.pts_to ax wx ** A.pts_to ay wy **
  A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (Seq.length wx == 6 /\ Seq.length wy == 6 /\
        num wx < P.prime /\ num wy < P.prime /\
        (num wx, num wy) == aff vx vy vz)
{
  let z0 = S64.zero;
  let mut zi = [| z0; 6sz |];
  Mem.track zi; A.pts_to_len zi; let mut tx = [| z0; 6sz |];
  Mem.track tx; A.pts_to_len tx; let mut ty = [| z0; 6sz |];
  Mem.track ty; A.pts_to_len ty;
  Inv.finv zi z;
  fmul tx x zi;
  fmul ty y zi;
  ffrom ax tx;
  ffrom ay ty;
  Mem.wipe ty 6sz;
  Mem.wipe tx 6sz;
  Mem.wipe zi 6sz;
  ()
}

(** [out = a || b], each as forty-eight big-endian bytes. *)
fn store_pair (out: A.array S8.t) (a b: A.array S64.t)
              (#vo: erased (Seq.seq S8.t))
              (#pa: perm) (#va: erased (Seq.seq S64.t))
              (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 96 /\ Seq.length va == 6 /\ Seq.length vb == 6)
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length wo == 96 /\
        wo == Seq.append (nat_to_be 48 (num va)) (nat_to_be 48 (num vb)))
{
  facts ();
  six_bnd va;
  six_bnd vb;
  A.pts_to_len out;
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 48sz |];
  Mem.track d0; A.pts_to_len d0; let mut d1 = [| z8; 48sz |];
  Mem.track d1; A.pts_to_len d1;
  to_bytes_be d0 a 6sz;
  to_bytes_be d1 b 6sz;
  with w0. assert (A.pts_to d0 w0);
  with w1. assert (A.pts_to d1 w1);
  to_be48 w0 (num va);
  to_be48 w1 (num vb);
  copy_at out 0sz d0 48sz;
  copy_at out 48sz d1 48sz;
  with wo. assert (A.pts_to out wo);
  assert (pure (Seq.equal wo (Seq.append w0 w1)));
  Mem.wipe d1 48sz;
  Mem.wipe d0 48sz;
  ()
}

(** [out] is the raw affine encoding [x || y] of [(x : y : z)]. *)
fn store_point (out: A.array S8.t) (x y z: A.array S64.t)
               (#vo: erased (Seq.seq S8.t))
               (#pp: perm) (#vx #vy #vz: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (Seq.length vo == 96 /\ pt_ok vx vy vz)
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to x #pp vx ** A.pts_to y #pp vy ** A.pts_to z #pp vz **
  pure (Seq.length wo == 96 /\ wo == P.store_point (pt vx vy vz))
{
  let z0 = S64.zero;
  let mut ax = [| z0; 6sz |];
  Mem.track ax; A.pts_to_len ax; let mut ay = [| z0; 6sz |];
  Mem.track ay; A.pts_to_len ay;
  to_aff ax ay x y z;
  store_pair out ax ay;
  Mem.wipe ay 6sz;
  Mem.wipe ax 6sz;
  ()
}

#pop-options
