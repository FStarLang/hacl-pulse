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

(** The message representative.

    ECDSA signs a scalar, not a message.  For K-256 that scalar is the
    whole thirty-two byte hash, read big-endian and reduced mod the order:
    unlike P-256 there is no other digest length to accommodate, because
    secp256k1 is only ever used with SHA2-256. *)
module Hacl.K256.Msg

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.K256.Field
open Hacl.Spec.Bytes
open Hacl.K256.Scalar

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module Hash = Hacl.Hash.SHA2
module SHA2 = Spec.SHA2
module C = Spec.SHA2.Constants
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** As elsewhere, an [ensures] cannot assume the [requires], so the length
    conditions travel in total wrappers. *)
let mqe (vb: Seq.seq S8.t) : GTot K.qelem =
  if Seq.length vb = 32 then K.msg_as_qelem vb else 0

fn msg_qelem (mq: A.array S64.t) (b: A.array S8.t)
             (#vm: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to mq vm ** A.pts_to b #pb vb **
  pure (Seq.length vm == nl /\ Seq.length vb == 32)
ensures exists* (wm: Seq.seq S64.t).
  A.pts_to mq wm ** A.pts_to b #pb vb **
  pure (qelem wm /\ qev wm == mqe vb)
{
  qload_mod mq b;
}

(** {2 The hashed representative} *)

let s256 (vb: Seq.seq S8.t) : GTot K.qelem =
  if Seq.length vb < pow2 61 then K.sha256_as_qelem vb else 0

fn sha256_qelem (mq: A.array S64.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#vm: erased (Seq.seq S64.t))
                (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to mq vm ** A.pts_to msg #pb vb **
  pure (Seq.length vm == nl /\ Seq.length vb < pow2 61)
         ** pure (SZ.v msg_len == Seq.length vb)
ensures exists* (wm: Seq.seq S64.t).
  A.pts_to mq wm ** A.pts_to msg #pb vb **
  pure (qelem wm /\ qev wm == s256 vb)
{
  K.msg_ok_hashable vb; K.digest_is_32 ();
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 32sz |];
  Mem.track d0; A.pts_to_len d0; A.pts_to_len d0;
  Hash.sha256 d0 msg msg_len;
  msg_qelem mq d0;
  Mem.wipe d0 32sz;
  ()
}

#pop-options
