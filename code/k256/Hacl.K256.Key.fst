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

(** Keys.

    A private key is a scalar strictly between zero and the order.  The
    check already exists as the range test inside [qload]; this is where it
    gets its public name.  The public-key check lives next door in
    {!Hacl.K256.Key.Public}, because a module that mentions both the field
    and the scalar field pays for both contexts in every query.

    Note that the scalar multiplication wants the scalar as sixteen plain
    limbs and not in Montgomery form: it reads bits of the number itself.
    [load_scalar] is therefore not [qload], even though the two agree on
    what they accept. *)
module Hacl.K256.Key

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.K256.Field
open Hacl.Spec.Bytes
open Hacl.Impl.Limb
open Hacl.Impl.Table
open Hacl.Impl.Bignum256
open Hacl.Impl.Mont256
open Spec.Mont256
open Hacl.K256.Tables
open Hacl.K256.Scalar

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module K = Spec.K256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 Scalars as limbs}

    The value is always written; the result says whether it is a usable
    private key.  A caller that ignores the result gets the raw number,
    which is what the reductions in ECDSA want. *)

fn load_scalar (out: A.array S64.t) (b: A.array S8.t)
               (#vo: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
returns r: bool
ensures exists* (wo: Seq.seq S64.t).
  A.pts_to out wo ** A.pts_to b #pb vb **
  pure (Seq.length wo == nl /\ bnd (vals wo) base /\
        eval (vals wo) == be_nat vb /\
        r == (0 < be_nat vb && be_nat vb < K.order))
{
  qmod_ok (); qmod_m (); mzero_ok ();
  assert_norm (pow2 256 < 2 * K.order);
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let mut a2 = [| z; 16sz |]; A.pts_to_len a2; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2;

  load_be out b;
  with wo. assert (A.pts_to out wo);
  assert (pure (eval (vals wo) == be_nat vb));
  acopy a0 out;
  azero a2;
  let nm = qnm ();
  let lo = abelow a0 a1 nm qmod;
  drop_table nm;
  assert (pure (lo == (be_nat vb < K.order)));
  let nz = aeq out a2;
  assert (pure (nz == (be_nat vb = 0)));
  lo && not nz
}

(** {2 The public checks} *)

fn validate_private_key (b: A.array S8.t)
                        (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #pb vb ** pure (Seq.length vb == 32)
returns r: bool
ensures A.pts_to b #pb vb ** pure (r == (0 < be_nat vb && be_nat vb < K.order))
{
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; A.pts_to_len a0;
  let r = load_scalar a0 b;
  r
}

#pop-options
