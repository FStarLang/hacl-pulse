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

    Both are {!Hacl.P256.Exp.fexp} with a table from [Spec.P256]: [p - 2]
    by Fermat, and [(p + 1) / 4] because [p] is [3 mod 4].  The square root also squares
    its candidate back and compares, which is what makes [P.fsqrt] an
    [option]. *)
module Hacl.P256.Inverse

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Spec.Mont4
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.Impl.Mont4
open Hacl.Impl.Lit4
open Hacl.P256.Tables
open Hacl.Impl.Exp4
open Hacl.P256.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module MA = Spec.ModArith
module E = Hacl.P256.Exp
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

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
  limbs_ok (P.prime - 2);
  E.fexp out a e (hide (P.prime - 2));
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
  limbs_ok ((P.prime + 1) / 4);
  E.fexp out a e (hide ((P.prime + 1) / 4));
  drop_table e;
  let z = S64.zero;
  let mut aq = [| z; 4sz |];
  Mem.track aq; A.pts_to_len aq; A.pts_to_len aq;
  fsqr aq out;
  let ok = feq aq a;
  Mem.wipe aq 4sz;
  ok
}

#pop-options
