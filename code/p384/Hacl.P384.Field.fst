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

(** The field [F_p] of P-384.

    Six limbs holding [x R mod p] with [R = 2^384].  [felem] is the
    invariant and [fev] is the number: the Montgomery factor appears only
    in this module, and each operation says exactly what [Spec.P384] says
    it does.

    Every operation is one call into the generic bignum layer
    ({!Hacl.Bignum.Base}, {!Hacl.Bignum.Montgomery}) with [nn = 6] and the
    constant tables of {!Hacl.P384.Tables}, followed by the one lemma of
    {!Hacl.P384.Lemmas} that turns the representation-level equation into
    a statement about [fev]. *)
module Hacl.P384.Field

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.Bignum.Montgomery
open Hacl.Bignum.Convert
open Hacl.Spec.Bytes
open Hacl.P384.Tables
open Hacl.P384.Lemmas

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Math = FStar.Math.Lemmas
module Mem = Hacl.Mem
module Declassify = Hacl.Secret.Declassify

(** {2 What a field element is} *)

(** [R^-1 mod p]. *)
let rinv : nat =
  183479889321925461653251752109332205360611897149516305954304919627392402791260477631193651879713439593005062

let felem (v: Seq.seq S64.t) : prop = Seq.length v == 6 /\ num v < P.prime

let fev (v: Seq.seq S64.t) : GTot P.felem = num v * rinv % P.prime

let pt (x y z: Seq.seq S64.t) : GTot P.proj_point = (fev x, fev y, fev z)

let pt_ok (x y z: Seq.seq S64.t) : prop = felem x /\ felem y /\ felem z

let facts (_: unit)
  : Lemma (wt 6 == pow2 384 /\ pow2 384 * rinv % P.prime == 1 /\
           SZ.fits 12 /\ SZ.fits 48 /\ SZ.fits 384 /\
           pow2 64 - 1 == 18446744073709551615)
  = assert_norm (wt 6 == pow2 384);
    assert_norm (pow2 384 * rinv % P.prime == 1);
    SZ.fits_at_least_16 12;
    SZ.fits_at_least_16 48;
    SZ.fits_at_least_16 384;
    assert_norm (pow2 64 - 1 == 18446744073709551615)

let num_zero (v: Seq.seq S64.t)
  : Lemma (requires forall (i: nat). i < Seq.length v ==> S64.v (Seq.index v i) == 0)
          (ensures num v == 0)
  = num_zeros_above v 0; pre_zero v

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The ring operations} *)

fn fadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fadd (fev va) (fev vb))
{
  let pm = pms ();
  add_mod out a b pm 6sz;
  with vo'. assert (A.pts_to out vo');
  add_lemma P.prime rinv (num va) (num vb);
  drop_table pm;
}

fn fsub (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fsub (fev va) (fev vb))
{
  let pm = pms ();
  sub_mod out a b pm 6sz;
  with vo'. assert (A.pts_to out vo');
  sub_lemma P.prime rinv (num va) (num vb);
  drop_table pm;
}

fn fmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fmul (fev va) (fev vb))
{
  facts ();
  let pm = pms ();
  let z = S64.zero;
  let mut t = [| z; 12sz |];
  Mem.track t; A.pts_to_len t;
  mont_mul out a b t pm 6sz pmu;
  with vo'. assert (A.pts_to out vo');
  mul_lemma P.prime (pow2 384) rinv (num vo') (num va) (num vb);
  Mem.wipe t 12sz;
  drop_table pm;
}

fn fsqr (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.fmul (fev va) (fev va))
{
  facts ();
  let pm = pms ();
  let z = S64.zero;
  let mut t = [| z; 12sz |];
  Mem.track t; A.pts_to_len t;
  mont_sqr out a t pm 6sz pmu;
  with vo'. assert (A.pts_to out vo');
  mul_lemma P.prime (pow2 384) rinv (num vo') (num va) (num va);
  Mem.wipe t 12sz;
  drop_table pm;
}

(** {2 Constants and copies} *)

fn fcopy (dst src: A.array S64.t)
         (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == 6 /\ felem vs)
ensures exists* (vd': Seq.seq S64.t).
  A.pts_to dst vd' ** A.pts_to src #ps vs **
  pure (felem vd' /\ fev vd' == fev vs)
{
  copy dst src 6sz;
}

fn fzero (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == 6)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (felem vo' /\ fev vo' == P.fzero)
{
  zero out 6sz;
  with vo'. assert (A.pts_to out vo');
  num_zero vo';
  assert (pure (num vo' == 0));
  Math.small_mod 0 P.prime;
  assert (pure (fev vo' == 0));
}

fn fone (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == 6)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (felem vo' /\ fev vo' == P.fone)
{
  facts ();
  const_lemma P.prime (pow2 384) rinv 1;
  let r1 = pr1 ();
  copy out r1 6sz;
  drop_table r1;
}

(** {2 Entering and leaving Montgomery form} *)

(** [fto] takes six plain limbs below the prime. *)
fn fto (out a: A.array S64.t)
       (#vo: erased (Seq.seq S64.t))
       (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ Seq.length va == 6 /\ num va < P.prime)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == num va)
{
  facts ();
  let pm = pms ();
  let r2 = pr2 ();
  let z = S64.zero;
  let mut t = [| z; 12sz |];
  Mem.track t; A.pts_to_len t;
  mont_mul out a r2 t pm 6sz pmu;
  with vo'. assert (A.pts_to out vo');
  to_lemma P.prime (pow2 384) rinv (num vo') (num va);
  Mem.wipe t 12sz;
  drop_table r2;
  drop_table pm;
}

(** [ffrom] gives them back. *)
fn ffrom (out a: A.array S64.t)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == 6 /\ num vo' == fev va)
{
  facts ();
  let pm = pms ();
  let z = S64.zero;
  let mut t = [| z; 12sz |];
  Mem.track t; A.pts_to_len t;
  from_mont out a t pm 6sz pmu;
  with vo'. assert (A.pts_to out vo');
  from_lemma P.prime (pow2 384) rinv (num vo') (num va);
  Mem.wipe t 12sz;
  drop_table pm;
}

(** {2 Comparison}

    The result is declassified.  Callers compare only public values, or
    secret ones whose comparison the return value reveals anyway, such as
    whether an ECDH result is at infinity. *)

fn feq (a b: A.array S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem va /\ felem vb)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (fev va = fev vb))
{
  facts ();
  let m = eq_mask a b 6sz;
  Classical.move_requires (inj_lemma P.prime (pow2 384) rinv (num va)) (num vb);
  U64.eq (Declassify.u64 m) 18446744073709551615uL
}

fn fis_zero (a: A.array S64.t) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** pure (felem va)
returns r: bool
ensures A.pts_to a #pa va ** pure (r == (fev va = P.fzero))
{
  let z = S64.zero;
  let mut az = [| z; 6sz |];
  Mem.track az; A.pts_to_len az;
  fzero az;
  let r = feq a az;
  Mem.wipe az 6sz;
  r
}

(** {2 Curve constants}

    Stored in Montgomery form, so reading one is just reading the table. *)

inline_for_extraction
fn fb () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == P.b_coeff)
{
  facts ();
  const_lemma P.prime (pow2 384) rinv P.b_coeff;
  Math.small_mod P.b_coeff P.prime;
  bm ()
}

(** Three. *)
let three_f : P.felem = assert_norm (3 < P.prime); 3

inline_for_extraction
fn fthree () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == three_f)
{
  facts ();
  const_lemma P.prime (pow2 384) rinv 3;
  assert_norm (3 % P.prime == 3);
  threem ()
}

inline_for_extraction
fn fgx () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == P.g_x)
{
  facts ();
  const_lemma P.prime (pow2 384) rinv P.g_x;
  Math.small_mod P.g_x P.prime;
  gxm ()
}

inline_for_extraction
fn fgy () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == P.g_y)
{
  facts ();
  const_lemma P.prime (pow2 384) rinv P.g_y;
  Math.small_mod P.g_y P.prime;
  gym ()
}

(** {2 Bytes}

    Big-endian, forty-eight bytes.  Decoding is also the range check: a
    coordinate at or above the prime is not a coordinate. *)

fn fload (out: A.array S64.t) (b: A.array S8.t)
         (#vo: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ Seq.length vb == 48)
returns r: bool
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (felem vo' /\ r == (be_nat vb < P.prime) /\
        (r ==> fev vo' == be_nat vb))
{
  facts ();
  let z = S64.zero;
  let mut at = [| z; 6sz |];
  Mem.track at; A.pts_to_len at;
  from_bytes_be at 6sz b;
  let pm = pms ();
  let m = lt_mask at pm 6sz;
  drop_table pm;
  let r = U64.eq (Declassify.u64 m) 18446744073709551615uL;
  if r {
    fto out at;
    Mem.wipe at 6sz;
    r
  } else {
    fzero out;
    Mem.wipe at 6sz;
    r
  }
}

#pop-options
