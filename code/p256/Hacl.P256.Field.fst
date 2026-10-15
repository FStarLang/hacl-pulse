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

(** The field [F_p].

    Four limbs holding [x R mod p].  [felem] is the invariant and [fev]
    is the number: after [Spec.Mont4] the Montgomery factor is not
    visible in any statement below, and each operation says exactly what
    [Spec.P256] says it does.

    The ring operations and the entry into Montgomery form are
    {!Hacl.P256.Field64}, which is specialised to this prime; the rest
    call the generic [Hacl.Impl.Mont4] -- fetch the constant tables, call
    the operation, apply the one lemma that turns the representation-level
    equation into a numeric one.  The tables are
    [static const] arrays and the permission on them is never returned,
    which is what [drop_table] records. *)
module Hacl.P256.Field

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Spec.Mont4
open Hacl.Spec.Bytes
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.Impl.Bignum4
open Hacl.Impl.Mont4
open Hacl.P256.Tables

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module P = Spec.P256
module MA = Spec.ModArith
module G = Pulse.Lib.GlobalArray
module Math = FStar.Math.Lemmas
module F = Hacl.P256.Field64
module F64 = Hacl.Curve25519.Field64
module W = Spec.Curve25519.Field64

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 What a field element is} *)

let felem (v: Seq.seq S64.t) : prop = res fmod (vals v)

let fmod_m (_: unit) : Lemma (fmod.m == P.prime) = ()

let fev (v: Seq.seq S64.t) : GTot P.felem = mev fmod (vals v)

(** {2 From {!Hacl.P256.Field64} to [Spec.Mont4]}

    {!Hacl.P256.Field64} speaks of four words as [ev4] of numerals; the
    rest of the library speaks of [eval] of their [vals].  They agree, and
    an operation that produces any residue with the right value produces
    the same limbs as the specification's [mmul], [madd] or [msub], so the
    existing [mev_*] lemmas carry over. *)

#push-options "--fuel 1"
let eval_ev (s: Seq.seq S64.t)
  : Lemma (requires Seq.length s == 4) (ensures eval (vals s) == F64.ev s)
  = let v = vals s in
    let v1 = Seq.slice v 1 4 in
    let v2 = Seq.slice v1 1 3 in
    let v3 = Seq.slice v2 1 2 in
    let v4 = Seq.slice v3 1 1 in
    assert_norm (pow2 64 == W.w);
    eval_empty v4;
    assert (eval v3 == Seq.index v3 0 + base * eval v4);
    assert (eval v2 == Seq.index v2 0 + base * eval v3);
    assert (eval v1 == Seq.index v1 0 + base * eval v2);
    assert (eval v == Seq.index v 0 + base * eval v1)
#pop-options

let fmod_pp (_: unit) : Lemma (fmod.m == F.pp /\ pow2 256 == W.w4) =
  assert_norm (P.prime == F.pp);
  assert_norm (pow2 256 == W.w4)

let felem_of (s: Seq.seq S64.t)
  : Lemma (requires Seq.length s == 4 /\ F64.ev s < F.pp)
          (ensures felem s /\ eval (vals s) == F64.ev s)
  = eval_ev s; vals_bnd s; fmod_pp ()

let mev_eq_of (x y: Seq.seq nat)
  : Lemma (requires eval x == eval y) (ensures mev fmod x == mev fmod y) = ()

let mmul_eq (a b z: Seq.seq nat)
  : Lemma (requires modulus_ok fmod /\ res fmod a /\ res fmod b /\ res fmod z /\
                    pow2 256 * eval z % fmod.m == eval a * eval b % fmod.m)
          (ensures eval z == eval (mmul fmod a b))
  = mmul_ok fmod a b;
    rcancel fmod (eval z) (eval (mmul fmod a b));
    Math.small_mod (eval z) fmod.m;
    Math.small_mod (eval (mmul fmod a b)) fmod.m

(** {2 The ring operations} *)

fn fadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fadd (fev va) (fev vb))
{
  fmod_ok (); fmod_m (); fmod_pp ();
  A.pts_to_len a; A.pts_to_len b; A.pts_to_len out;
  eval_ev va; eval_ev vb;
  mev_add fmod (vals va) (vals vb);
  madd_ok fmod (vals va) (vals vb);
  F.fadd out a b;
  with vo'. assert (A.pts_to out vo');
  felem_of vo';
  mev_eq_of (vals vo') (madd fmod (vals va) (vals vb));
}

fn fsub (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fsub (fev va) (fev vb))
{
  fmod_ok (); fmod_m (); fmod_pp ();
  A.pts_to_len a; A.pts_to_len b; A.pts_to_len out;
  eval_ev va; eval_ev vb;
  mev_sub fmod (vals va) (vals vb);
  msub_ok fmod (vals va) (vals vb);
  F.fsub out a b;
  with vo'. assert (A.pts_to out vo');
  felem_of vo';
  mev_eq_of (vals vo') (msub fmod (vals va) (vals vb));
}

fn fneg (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.fneg (fev va))
{
  fmod_ok (); fmod_m ();
  mev_neg fmod (vals va);
  let ms = fms ();
  aneg out a ms fmod;
  drop_table ms;
}

fn fmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == P.fmul (fev va) (fev vb))
{
  fmod_ok (); fmod_m (); fmod_pp ();
  A.pts_to_len a; A.pts_to_len b; A.pts_to_len out;
  eval_ev va; eval_ev vb;
  mev_mul fmod (vals va) (vals vb);
  F.fmul out a b;
  with vo'. assert (A.pts_to out vo');
  felem_of vo';
  mmul_eq (vals va) (vals vb) (vals vo');
  mev_eq_of (vals vo') (mmul fmod (vals va) (vals vb));
}

(** Squaring is a product with itself; the copy gives the multiplier a
    second buffer and the compiler keeps both in registers. *)
fn fsqr (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.fmul (fev va) (fev va))
{
  let z = S64.zero;
  let mut ac = [| z; 4sz |]; A.pts_to_len ac; A.pts_to_len ac;
  acopy ac a;
  fmul out a ac;
  ()
}

(** {2 Constants and copies} *)

fn fcopy (dst src: A.array S64.t)
         (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == nl /\ felem vs)
ensures exists* (vd': Seq.seq S64.t).
  A.pts_to dst vd' ** A.pts_to src #ps vs **
  pure (felem vd' /\ fev vd' == fev vs)
{
  acopy dst src;
}

fn fzero (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == nl)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (felem vo' /\ fev vo' == P.fzero)
{
  fmod_ok (); fmod_m ();
  mev_zero fmod;
  azero out;
}

fn fone (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == nl)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (felem vo' /\ fev vo' == P.fone)
{
  fmod_ok (); fmod_m ();
  mev_one fmod;
  let r1 = fr1 ();
  acopy out r1;
  drop_table r1;
}

(** {2 Entering and leaving Montgomery form}

    [fto] takes eight plain limbs below the prime; [ffrom] gives them
    back.  Only the byte conversions below use either. *)

fn fto (out a: A.array S64.t)
       (#vo: erased (Seq.seq S64.t))
       (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ res fmod (vals va))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == eval (vals va))
{
  fmod_ok (); fmod_m (); fmod_pp ();
  A.pts_to_len a; A.pts_to_len out;
  mev_to fmod (vals va);
  let r2 = fr2 ();
  with pr vr. assert (A.pts_to r2 #pr vr);
  A.pts_to_len r2;
  eval_ev va; eval_ev vr;
  F.fmul out a r2;
  with vo'. assert (A.pts_to out vo');
  felem_of vo';
  mmul_eq (vals va) (vals vr) (vals vo');
  mev_eq_of (vals vo') (mmul fmod (vals va) (vals vr));
  drop_table r2;
}

fn ffrom (out a: A.array S64.t)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (Seq.length vo' == nl /\ bnd (vals vo') base /\
        eval (vals vo') == fev va)
{
  fmod_ok (); fmod_m ();
  mone_ok ();
  let ms = fms ();
  let nm = fnm ();
  mev_of fmod (vals va);
  let one = mone ();
  amul out a one ms nm fmu fmod;
  drop_table ms;
  drop_table nm;
  drop_table one;
}

(** {2 Comparison} *)

fn feq (a b: A.array S64.t)
       (#pa: perm) (#va: erased (Seq.seq S64.t))
       (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem va /\ felem vb)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (fev va = fev vb))
{
  fmod_ok (); fmod_m ();
  mev_eq fmod (vals va) (vals vb);
  aeq a b
}

fn fis_zero (a: A.array S64.t) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** pure (felem va)
returns r: bool
ensures A.pts_to a #pa va ** pure (r == (fev va = P.fzero))
{
  fmod_ok (); fmod_m ();
  mev_iszero fmod (vals va);
  mzero_ok ();
  let z = S64.zero;
  let mut az = [| z; 4sz |]; A.pts_to_len az; A.pts_to_len az;
  azero az;
  let r = aeq a az;
  r
}

(** {2 Curve constants}

    Stored in Montgomery form, so reading one is just reading the table.
    [mev_uniq] is what turns "these limbs are [b R mod p]" into "this is
    [b]". *)

inline_for_extraction
fn fconst (a: G.static_array S64.t) (x: erased P.felem)
requires pure (vals (G.static_array_elems a) == limbs (reveal x * pow2 256 % P.prime))
returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == reveal x)
{
  fmod_ok (); fmod_m ();
  limbs_ok (reveal x * pow2 256 % P.prime);
  mev_uniq fmod x (limbs (reveal x * pow2 256 % P.prime));
  table a 4sz
}

inline_for_extraction
fn fb () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == P.b_coeff)
{ fconst bm_arr P.b_coeff }

(** Three.  Kept in Montgomery form like the other constants. *)
let three_f : P.felem = assert_norm (3 < P.prime); 3

inline_for_extraction
fn fthree () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == three_f)
{ fconst threem_arr three_f }

inline_for_extraction
fn fgx () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == P.g_x)
{ fconst gxm_arr P.g_x }

inline_for_extraction
fn fgy () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == P.g_y)
{ fconst gym_arr P.g_y }

(** {2 Bytes}

    Big-endian, thirty-two bytes, as every standard that mentions P-256
    says.  Decoding is also the range check: a coordinate at or above the
    prime is not a coordinate. *)

#push-options "--z3rlimit 200"

fn fload (out: A.array S64.t) (b: A.array S8.t)
         (#vo: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
returns r: bool
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (felem vo' /\ r == (be_nat vb < P.prime) /\
        (r ==> fev vo' == be_nat vb))
{
  fmod_ok (); fmod_m ();
  assert_norm (pow2 256 < 2 * P.prime);
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; let mut asv = [| z128; 4sz |]; A.pts_to_len asv; A.pts_to_len at; A.pts_to_len asv;
  load_be at b;
  let nm = fnm ();
  let r = abelow at asv nm fmod;
  drop_table nm;
  fto out at;
  r
}

fn fstore (b: A.array S8.t) (a: A.array S64.t)
          (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ felem va)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == nat_to_be 32 (fev va))
{
  let z = S64.zero;
  let mut at = [| z; 4sz |]; A.pts_to_len at; A.pts_to_len at;
  ffrom at a;
  store_be b at;
  ()
}

#pop-options

#pop-options
