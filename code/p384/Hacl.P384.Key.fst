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

(** Keys: loading a private scalar, and validating either kind of key.

    A private key is forty-eight big-endian bytes encoding a scalar in
    [1, n); a public key is the raw [x || y] of a point on the curve.  The
    cofactor is one, so being on the curve is all there is to check. *)
module Hacl.P384.Key

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Spec.Bytes
open Hacl.Impl.Limb64
open Hacl.Bignum.Base
open Hacl.Bignum.Convert
open Hacl.P384.Field
open Hacl.P384.Verify

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Mem = Hacl.Mem

(** The total wrappers an [ensures] needs. *)
let sk_ok (vb: Seq.seq S8.t) : GTot bool =
  Seq.length vb = 48 && P.validate_private_key vb

let pk_ok (vb: Seq.seq S8.t) : GTot bool =
  Seq.length vb = 96 && P.validate_public_key vb

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Reads a scalar and says whether it is a valid private key.  Only that
    verdict is declassified, never the scalar. *)
fn load_scalar (out: A.array S64.t) (b: A.array S8.t)
               (#vo: erased (Seq.seq S64.t))
               (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == 6 /\ Seq.length vb == 48)
returns r: bool
ensures exists* (wo: Seq.seq S64.t).
  A.pts_to out wo ** A.pts_to b #pb vb **
  pure (Seq.length wo == 6 /\ num wo == be_nat vb /\
        r == (0 < be_nat vb && be_nat vb < P.order))
{
  facts ();
  from_bytes_be out 6sz b;
  scalar_ok out
}

fn validate_private_key (b: A.array S8.t)
                        (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #pb vb ** pure (Seq.length vb == 48)
returns r: bool
ensures A.pts_to b #pb vb ** pure (r == sk_ok vb)
{
  let z = S64.zero;
  let mut k = [| z; 6sz |];
  Mem.track k; A.pts_to_len k;
  let r = load_scalar k b;
  Mem.wipe k 6sz;
  r
}

fn validate_public_key (b: A.array S8.t)
                       (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #pb vb ** pure (Seq.length vb == 96)
returns r: bool
ensures A.pts_to b #pb vb ** pure (r == pk_ok vb)
{
  let z = S64.zero;
  let mut qx = [| z; 6sz |];
  Mem.track qx; A.pts_to_len qx; let mut qy = [| z; 6sz |];
  Mem.track qy; A.pts_to_len qy; let mut qz = [| z; 6sz |];
  Mem.track qz; A.pts_to_len qz;
  let r = load_point qx qy qz b;
  Mem.wipe qz 6sz;
  Mem.wipe qy 6sz;
  Mem.wipe qx 6sz;
  r
}

#pop-options
