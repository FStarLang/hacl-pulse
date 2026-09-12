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

(** Inversion and square roots in [F_p].

    Both are [mexp] with a table from [Spec.P256]: [p - 2] by Fermat, and
    [(p + 1) / 4] because [p] is [3 mod 4].  The square root also squares
    its candidate back and compares, which is what makes [P.fsqrt] an
    [option]. *)
module Hacl.P256.Inverse

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Spec.P256.Mont
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.P256.Mont
open Hacl.P256.Tables
open Hacl.P256.Exp
open Hacl.P256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module MA = Spec.ModArith

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The exponentiation both entry points perform: [out := a^n], with [n]
    given as a table of public limbs whose value is known. *)
inline_for_extraction
fn fexp (out a: A.array S64.t) (e: A.array U64.t) (n: erased nat)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pe: perm) (#ve: erased (Seq.seq U64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to e #pe ve **
  pure (Seq.length vo == nl /\ felem va /\
        reveal n < pow2 256 /\ pvals ve == limbs n)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to e #pe ve **
  pure (felem vo' /\ fev vo' == MA.exp #P.prime (fev va) n)
{
  fmod_ok (); fmod_m ();
  limbs_ok (reveal n);
  let r1 = fr1 ();
  let ms = fms ();
  let nm = fnm ();
  mexp out a e r1 ms nm fmu fmod;
  drop_table r1;
  drop_table ms;
  drop_table nm;
}

(** [out := a^-1].  Zero inverts to zero, as [Spec.ModArith.inv] says. *)
fn finv (out a: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem va)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\ fev vo' == P.finv (fev va))
{
  assert_norm (P.prime - 2 < pow2 256);
  let e = finv_e ();
  fexp out a e (hide (P.prime - 2));
  drop_table e;
}

(** [out := sqrt a] when [a] is a square, and [false] otherwise.  The
    candidate is written to [out] either way; the caller must not use it
    when the result is [false]. *)
fn fsqrt (out a: A.array S64.t)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va **
  pure (Seq.length vo == nl /\ felem va)
returns ok: bool
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va **
  pure (felem vo' /\
        P.fsqrt (fev va) == (if ok then Some (fev vo') else None))
{
  assert_norm ((P.prime + 1) / 4 < pow2 256);
  assert_norm (P.prime % 4 == 3);
  let e = fsqrt_e ();
  fexp out a e (hide ((P.prime + 1) / 4));
  drop_table e;
  let z = S64.zero;
  let mut aq = [| z; 16sz |]; A.pts_to_len aq; A.pts_to_len aq;
  fsqr aq out;
  let ok = feq aq a;
  ok
}

#pop-options
