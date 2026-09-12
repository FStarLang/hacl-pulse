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

    ECDSA signs a scalar, not a message.  That scalar is the leading
    thirty-two bytes of the hash, read big-endian and reduced mod the
    order.  Note that this is a reduction and not the bit-length truncation
    FIPS 186 describes: for P-256 with a 256-bit hash the two coincide, and
    HACL* does it this way for the longer hashes too. *)
module Hacl.P256.Msg

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Spec.Bytes
open Hacl.Impl.Copy
open Hacl.P256.Scalar

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module Hash = Hacl.Hash.SHA2
module SHA2 = Spec.SHA2
module C = Spec.SHA2.Constants

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** As elsewhere, an [ensures] cannot assume the [requires], so the length
    conditions travel in total wrappers. *)
let mqe (vb: Seq.seq S8.t) : GTot P.qelem =
  if 32 <= Seq.length vb then P.msg_as_qelem vb else 0

fn msg_qelem (mq: A.array S64.t) (b: A.array S8.t)
             (#vm: erased (Seq.seq S64.t))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to mq vm ** A.pts_to b #pb vb **
  pure (Seq.length vm == nl /\ 32 <= Seq.length vb)
ensures exists* (wm: Seq.seq S64.t).
  A.pts_to mq wm ** A.pts_to b #pb vb **
  pure (qelem wm /\ qev wm == mqe vb)
{
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 32sz |]; A.pts_to_len d0; A.pts_to_len d0;
  copy_prefix d0 b 32sz;
  with vhb. assert (A.pts_to d0 vhb);
  A.pts_to_len d0;
  assert (pure (Seq.equal vhb (Seq.slice vb 0 32)));
  qload_mod mq d0;
  ()
}

(** {2 The hashed representatives}

    Three digest lengths, one rule: take the first thirty-two bytes.  The
    [pow2 61] bound is SHA2-256's; the 512-bit variants allow far more, so
    one bound serves all three. *)

let s256 (vb: Seq.seq S8.t) : GTot P.qelem =
  if Seq.length vb < pow2 61 then P.sha256_as_qelem vb else 0

let s384 (vb: Seq.seq S8.t) : GTot P.qelem =
  if Seq.length vb < pow2 61 then P.sha384_as_qelem vb else 0

let s512 (vb: Seq.seq S8.t) : GTot P.qelem =
  if Seq.length vb < pow2 61 then P.sha512_as_qelem vb else 0

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
  P.msg_ok_hashable vb; P.digest_ge_32 ();
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 32sz |]; A.pts_to_len d0; A.pts_to_len d0;
  Hash.sha256 d0 msg msg_len;
  msg_qelem mq d0;
  ()
}

fn sha384_qelem (mq: A.array S64.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#vm: erased (Seq.seq S64.t))
                (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to mq vm ** A.pts_to msg #pb vb **
  pure (Seq.length vm == nl /\ Seq.length vb < pow2 61)
         ** pure (SZ.v msg_len == Seq.length vb)
ensures exists* (wm: Seq.seq S64.t).
  A.pts_to mq wm ** A.pts_to msg #pb vb **
  pure (qelem wm /\ qev wm == s384 vb)
{
  P.msg_ok_hashable vb; P.digest_ge_32 ();
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 48sz |]; A.pts_to_len d0; A.pts_to_len d0;
  Hash.sha384 d0 msg msg_len;
  msg_qelem mq d0;
  ()
}

fn sha512_qelem (mq: A.array S64.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#vm: erased (Seq.seq S64.t))
                (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to mq vm ** A.pts_to msg #pb vb **
  pure (Seq.length vm == nl /\ Seq.length vb < pow2 61)
         ** pure (SZ.v msg_len == Seq.length vb)
ensures exists* (wm: Seq.seq S64.t).
  A.pts_to mq wm ** A.pts_to msg #pb vb **
  pure (qelem wm /\ qev wm == s512 vb)
{
  P.msg_ok_hashable vb; P.digest_ge_32 ();
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 64sz |]; A.pts_to_len d0; A.pts_to_len d0;
  Hash.sha512 d0 msg msg_len;
  msg_qelem mq d0;
  ()
}

#pop-options
