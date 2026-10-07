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

    A private key is a scalar strictly between zero and the order; a public
    key is a point on the curve.  Both checks already exist -- the first as
    the range test inside [qload], the second as [load_point] -- and this
    module is where they are given their public names.

    Note that the scalar multiplication wants the scalar as eight plain
    limbs and not in Montgomery form: it reads bits of the number itself.
    [load_scalar] is therefore not [qload], even though the two agree on
    what they accept. *)
(** Public keys.

    A public key is sixty-four bytes that decode to a point on the curve.
    [load_point] already does the work; this gives it its public name, in a
    module of its own so that the scalar field never enters the context. *)
module Hacl.K256.Key.Public

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.K256.Field
open Hacl.Spec.Bytes
open Hacl.K256.Point
open Hacl.K256.Encode

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module K = Spec.K256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn validate_public_key (b: A.array S8.t)
                       (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #pb vb ** pure (Seq.length vb == 64)
returns r: bool
ensures A.pts_to b #pb vb ** pure (r == Some? (lpt vb))
{
  let z = S64.zero;
  let mut a0 = [| z; 5sz |]; A.pts_to_len a0; let mut a1 = [| z; 5sz |]; A.pts_to_len a1; let mut a2 = [| z; 5sz |]; A.pts_to_len a2; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2;
  let r = load_point a0 a1 a2 b;
  r
}

#pop-options
