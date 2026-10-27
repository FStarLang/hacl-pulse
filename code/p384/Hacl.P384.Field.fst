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

    The ring operations are {!Hacl.P384.Field64}, which is specialised to
    this prime; the rest is one call into the generic bignum layer
    ({!Hacl.Bignum.Base}, {!Hacl.Bignum.Montgomery}) with [nn = 6] and the
    constant tables of {!Hacl.P384.Tables}.  Either way the call is
    followed by the one lemma of {!Hacl.P384.Lemmas} that turns the
    representation-level equation into a statement about [fev]. *)
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
module F = Hacl.P384.Field64
module F64 = Hacl.Curve25519.Field64
module W = Spec.Curve25519.Field64

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

(** {!Hacl.P384.Field64} speaks of six words as [ev6] of numerals; this
    module speaks of [num]. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
let num_fv (s: Seq.seq S64.t)
  : Lemma (requires Seq.length s == 6) (ensures num s == F.fv s)
  = let v = vals s in
    let v1 = Seq.slice v 1 6 in
    let v2 = Seq.slice v1 1 5 in
    let v3 = Seq.slice v2 1 4 in
    let v4 = Seq.slice v3 1 3 in
    let v5 = Seq.slice v4 1 2 in
    let v6 = Seq.slice v5 1 1 in
    W.consts ();
    eval_empty v6;
    assert (eval v5 == Seq.index v5 0 + base * eval v6);
    assert (eval v4 == Seq.index v4 0 + base * eval v5);
    assert (eval v3 == Seq.index v3 0 + base * eval v4);
    assert (eval v2 == Seq.index v2 0 + base * eval v3);
    assert (eval v1 == Seq.index v1 0 + base * eval v2);
    assert (eval v == Seq.index v 0 + base * eval v1)
#pop-options

let fv_facts (_: unit) : Lemma (P.prime == F.pp /\ pow2 384 == W.w6) =
  assert_norm (P.prime == F.pp);
  assert_norm (pow2 384 == W.w6)

let add_fv (o a b: nat)
  : Lemma (requires a < P.prime /\ b < P.prime /\ o == (a + b) % F.pp)
          (ensures o < P.prime /\ o * rinv % P.prime == P.fadd (a * rinv % P.prime) (b * rinv % P.prime))
  = fv_facts ();
    add_lemma P.prime rinv a b

let sub_fv (o a b: nat)
  : Lemma (requires a < P.prime /\ b < P.prime /\ o == (a + F.pp - b) % F.pp)
          (ensures o < P.prime /\ o * rinv % P.prime == P.fsub (a * rinv % P.prime) (b * rinv % P.prime))
  = fv_facts ();
    Math.lemma_mod_plus (a - b) 1 P.prime;
    sub_lemma P.prime rinv a b

let mul_fv (o a b: nat)
  : Lemma (requires o < F.pp /\ (W.w6 * o) % F.pp == (a * b) % F.pp)
          (ensures o < P.prime /\ o * rinv % P.prime == P.fmul (a * rinv % P.prime) (b * rinv % P.prime))
  = fv_facts ();
    assert_norm (pow2 384 * rinv % P.prime == 1);
    mul_lemma P.prime (pow2 384) rinv o a b

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
  A.pts_to_len a; A.pts_to_len b;
  num_fv va; num_fv vb; fv_facts ();
  F.fadd out a b;
  with vo'. assert (A.pts_to out vo');
  num_fv vo';
  add_fv (num vo') (num va) (num vb);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fadd (fev va) (fev vb)));
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
  A.pts_to_len a; A.pts_to_len b;
  num_fv va; num_fv vb; fv_facts ();
  F.fsub out a b;
  with vo'. assert (A.pts_to out vo');
  num_fv vo';
  sub_fv (num vo') (num va) (num vb);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fsub (fev va) (fev vb)));
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
  A.pts_to_len a; A.pts_to_len b;
  num_fv va; num_fv vb; fv_facts ();
  F.fmul out a b;
  with vo'. assert (A.pts_to out vo');
  num_fv vo';
  mul_fv (num vo') (num va) (num vb);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fmul (fev va) (fev vb)));
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
  A.pts_to_len a;
  num_fv va; fv_facts ();
  F.fsqr out a;
  with vo'. assert (A.pts_to out vo');
  num_fv vo';
  mul_fv (num vo') (num va) (num va);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fmul (fev va) (fev va)));
}

(** {2 In place}

    [fadd1 o b] is [o := o + b] and [fadd2 o a] is [o := a + o], and so on:
    the digit says which operand the result replaces.  They read their
    operands into words before writing, so the point formulas need no
    scratch copy for a step that reuses a name.  [fdbl] and [fsqr] read one
    element twice under one permission. *)

fn fdbl (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == 6 /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.fadd (fev va) (fev va))
{
  A.pts_to_len a;
  num_fv va; fv_facts ();
  F.fdbl out a;
  with vo'. assert (A.pts_to out vo');
  num_fv vo';
  add_fv (num vo') (num va) (num va);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fadd (fev va) (fev va)));
}

fn fadd1 (o b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to b #pb vb **
  pure (felem vo /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fadd (fev vo) (fev vb))
{
  A.pts_to_len o; A.pts_to_len b;
  num_fv vo; num_fv vb; fv_facts ();
  F.fadd1 o b;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  add_fv (num vo') (num vo) (num vb);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fadd (fev vo) (fev vb)));
}

fn fadd2 (o a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to a #pa va **
  pure (felem vo /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.fadd (fev va) (fev vo))
{
  A.pts_to_len o; A.pts_to_len a;
  num_fv vo; num_fv va; fv_facts ();
  F.fadd1 o a;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  add_fv (num vo') (num va) (num vo);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fadd (fev va) (fev vo)));
}

fn fdbl1 (o: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo **
  pure (felem vo)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (felem vo' /\ fev vo' == P.fadd (fev vo) (fev vo))
{
  A.pts_to_len o;
  num_fv vo; fv_facts ();
  F.fdbl1 o;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  add_fv (num vo') (num vo) (num vo);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fadd (fev vo) (fev vo)));
}

fn fsub1 (o b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to b #pb vb **
  pure (felem vo /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fsub (fev vo) (fev vb))
{
  A.pts_to_len o; A.pts_to_len b;
  num_fv vo; num_fv vb; fv_facts ();
  F.fsub1 o b;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  sub_fv (num vo') (num vo) (num vb);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fsub (fev vo) (fev vb)));
}

fn fsub2 (o a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to a #pa va **
  pure (felem vo /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.fsub (fev va) (fev vo))
{
  A.pts_to_len o; A.pts_to_len a;
  num_fv vo; num_fv va; fv_facts ();
  F.fsub2 o a;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  sub_fv (num vo') (num va) (num vo);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fsub (fev va) (fev vo)));
}

fn fmul1 (o b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to b #pb vb **
  pure (felem vo /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fmul (fev vo) (fev vb))
{
  A.pts_to_len o; A.pts_to_len b;
  num_fv vo; num_fv vb; fv_facts ();
  F.fmul1 o b;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  mul_fv (num vo') (num vo) (num vb);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fmul (fev vo) (fev vb)));
}

fn fmul2 (o a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to a #pa va **
  pure (felem vo /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.fmul (fev va) (fev vo))
{
  A.pts_to_len o; A.pts_to_len a;
  num_fv vo; num_fv va; fv_facts ();
  F.fmul1 o a;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  Math.swap_mul (num vo) (num va);
  mul_fv (num vo') (num va) (num vo);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fmul (fev va) (fev vo)));
}

fn fsqr1 (o: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo **
  pure (felem vo)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (felem vo' /\ fev vo' == P.fmul (fev vo) (fev vo))
{
  A.pts_to_len o;
  num_fv vo; fv_facts ();
  F.fsqr1 o;
  with vo'. assert (A.pts_to o vo');
  num_fv vo';
  mul_fv (num vo') (num vo) (num vo);
  assert (pure (num vo' < P.prime));
  assert (pure (felem vo'));
  assert (pure (fev vo' == P.fmul (fev vo) (fev vo)));
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

(** [fzero_mask a t] is all ones if [a] is zero and all zeroes otherwise,
    in the same time either way; [t] is scratch.  {!fis_zero} answers with
    a public [bool], which is wrong for a secret point at infinity. *)
fn fzero_mask (a t: A.array S64.t)
              (#pa: perm) (#va: erased (Seq.seq S64.t))
              (#vt: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to t vt **
  pure (felem va /\ Seq.length vt == 6)
returns m: S64.t
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to a #pa va ** A.pts_to t vt' **
  pure (Seq.length vt' == 6 /\ is_mask m /\
        (S64.v m == pow2 64 - 1 <==> fev va == P.fzero))
{
  facts ();
  fzero t;
  with vt'. assert (A.pts_to t vt');
  let m = eq_mask a t 6sz;
  Classical.move_requires (inj_lemma P.prime (pow2 384) rinv (num va)) (num vt');
  m
}

(** [fcsel o a m] is [o := a] under an all-ones mask and nothing under a
    zero one, in the same time either way. *)
fn fcsel (o a: A.array S64.t) (m: S64.t)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to a #pa va **
  pure (felem vo /\ felem va /\ is_mask m)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == (if S64.v m = 0 then fev vo else fev va))
{
  mask_bit_ok m;
  cselect o a 6sz m (hide (mask_bit m));
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
