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

(** secp256k1's field [F_p].

    Sixteen limbs holding [x R mod p].  [felem] is the invariant and [fev]
    is the number: after [Spec.Mont256] the Montgomery factor is not
    visible in any statement below, and each operation says exactly what
    [Spec.P256] says it does.

    Every function here is four lines -- fetch the constant tables, call the
    operation from [Hacl.Impl.Mont256], apply the one lemma that turns the
    representation-level equation into a numeric one.  The tables are
    [static const] arrays and the permission on them is never returned,
    which is what [drop_table] records. *)
module Hacl.K256.Field

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.K256.Field
open Spec.Mont256
open Hacl.Spec.Bytes
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.Impl.Bignum256
open Hacl.Impl.Mont256
open Hacl.K256.Tables

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module MA = Spec.ModArith
module G = Pulse.Lib.GlobalArray

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 What a field element is} *)

let felem (v: Seq.seq S64.t) : prop = res fmod (vals v)

let fmod_m (_: unit) : Lemma (fmod.m == K.prime) = ()

let fev (v: Seq.seq S64.t) : GTot K.felem = mev fmod (vals v)

(** {2 The ring operations} *)

fn fadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == K.fadd (fev va) (fev vb))
{
  fmod_ok (); fmod_m ();
  mev_add fmod (vals va) (vals vb);
  let nm = fnm ();
  aadd out a b nm fmod;
  drop_table nm;
}

fn fsub (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ felem va /\ felem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (felem vo' /\ fev vo' == K.fsub (fev va) (fev vb))
{
  fmod_ok (); fmod_m ();
  mev_sub fmod (vals va) (vals vb);
  let ms = fms ();
  asub out a b ms fmod;
  drop_table ms;
}

fn fneg (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == K.fneg (fev va))
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
  pure (felem vo' /\ fev vo' == K.fmul (fev va) (fev vb))
{
  fmod_ok (); fmod_m ();
  mev_mul fmod (vals va) (vals vb);
  let ms = fms ();
  let nm = fnm ();
  amul out a b ms nm fmu fmod;
  drop_table ms;
  drop_table nm;
}

(** Squaring needs a second reference to its argument, and the multiplier
    wants the three buffers distinct: the copy is eight moves against two
    hundred and fifty-six multiplies. *)
fn fsqr (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == K.fmul (fev va) (fev va))
{
  let z = S64.zero;
  let mut ac = [| z; 8sz |]; A.pts_to_len ac; A.pts_to_len ac;
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
  A.pts_to out vo' ** pure (felem vo' /\ fev vo' == K.fzero)
{
  fmod_ok (); fmod_m ();
  mev_zero fmod;
  azero out;
}

fn fone (out: A.array S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to out vo ** pure (Seq.length vo == nl)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** pure (felem vo' /\ fev vo' == K.fone)
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
  fmod_ok (); fmod_m ();
  let ms = fms ();
  let nm = fnm ();
  mev_to fmod (vals va);
  let r2 = fr2 ();
  amul out a r2 ms nm fmu fmod;
  drop_table ms;
  drop_table nm;
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
ensures A.pts_to a #pa va ** pure (r == (fev va = K.fzero))
{
  fmod_ok (); fmod_m ();
  mev_iszero fmod (vals va);
  mzero_ok ();
  let z = S64.zero;
  let mut az = [| z; 8sz |]; A.pts_to_len az; A.pts_to_len az;
  azero az;
  let r = aeq a az;
  r
}

(** {2 Curve constants}

    Stored in Montgomery form, so reading one is just reading the table.
    [mev_uniq] is what turns "these limbs are [b R mod p]" into "this is
    [b]". *)

inline_for_extraction
fn fconst (a: G.static_array S64.t) (x: erased K.felem)
requires pure (vals (G.static_array_elems a) == limbs (reveal x * pow2 256 % K.prime))
returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == reveal x)
{
  fmod_ok (); fmod_m ();
  limbs_ok (reveal x * pow2 256 % K.prime);
  mev_uniq fmod x (limbs (reveal x * pow2 256 % K.prime));
  table a 8sz
}

inline_for_extraction
fn fb () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == K.b_coeff)
{ fconst bm_arr K.b_coeff }

(** [3b = 21], which is the only coefficient the complete formulas need. *)
inline_for_extraction
fn fb3 () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == K.b3)
{ fconst b3m_arr K.b3 }

inline_for_extraction
fn fgx () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == K.g_x)
{ fconst gxm_arr K.g_x }

inline_for_extraction
fn fgy () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (felem v /\ fev v == K.g_y)
{ fconst gym_arr K.g_y }

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
  pure (felem vo' /\ r == (be_nat vb < K.prime) /\
        (r ==> fev vo' == be_nat vb))
{
  fmod_ok (); fmod_m ();
  assert_norm (pow2 256 < 2 * K.prime);
  let z = S64.zero;
  let mut at = [| z; 8sz |]; A.pts_to_len at; let mut asv = [| z; 8sz |]; A.pts_to_len asv; A.pts_to_len at; A.pts_to_len asv;
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
  let mut at = [| z; 8sz |]; A.pts_to_len at; A.pts_to_len at;
  ffrom at a;
  store_be b at;
  ()
}

#pop-options

#pop-options
