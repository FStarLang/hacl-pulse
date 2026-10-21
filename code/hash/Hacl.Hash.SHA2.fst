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

(** The four SHA-2 algorithms, as C functions.

    This is the only module of the hash that is not generic: it names the
    [Spec.SHA2.params] value for each algorithm, which is what makes Custard
    emit four specialized copies of everything in [Hacl.Hash.SHA2.Core].

    The round constants and the initial state come from
    [Hacl.Hash.SHA2.Tables], as [static const] arrays in the program image;
    [Hacl.Impl.Table.table] is what turns one into the read-only slice
    [hash_impl] wants.  Nothing is copied and nothing is initialized at
    startup. *)
module Hacl.Hash.SHA2

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Hacl.Hash.SHA2.Core
open Spec.SHANI
open Hacl.Impl.Table
open Hacl.Hash.SHA2.Tables

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Vec = Hacl.Vec128
module NI = Hacl.Hash.SHA2.NI

(** [Spec.SHA2.max_input] is [2^61] for the thirty-two bit family and [2^125]
    for the sixty-four bit one, so the [2^61] the callers promise is enough for
    both. *)
let max_input_bound (_: unit)
  : Lemma (pow2 61 <= max_input #S32.t /\ pow2 61 <= max_input #S64.t)
  = assert_norm (bits #S32.t == 32);
    assert_norm (bits #S64.t == 64);
    Math.pow2_le_compat 125 61

(** What [NI.hash_impl_ni] asks of the two thirty-two bit parameter sets,
    stated once at top level so that the call sites need not unfold
    [params256_with] inside a query that also carries a heap. *)
#push-options "--fuel 0 --ifuel 0"
let sha2_224_facts (_: unit)
  : Lemma (is_sha256 sha2_224 /\ sha2_224.k == k256 /\ sha2_224.iv == iv224 /\
           SZ.v sha2_224.nhash_bytes == 28)
  = ()

let sha2_256_facts (_: unit)
  : Lemma (is_sha256 sha2_256 /\ sha2_256.k == k256 /\ sha2_256.iv == iv256 /\
           SZ.v sha2_256.nhash_bytes == 32)
  = ()

let sha2_384_facts (_: unit)
  : Lemma (sha2_384.k == k512 /\ sha2_384.iv == iv384 /\ SZ.v sha2_384.nhash_bytes == 48)
  = ()

let sha2_512_facts (_: unit)
  : Lemma (sha2_512.k == k512 /\ sha2_512.iv == iv512 /\ SZ.v sha2_512.nhash_bytes == 64)
  = ()
#pop-options

(** {2 The four algorithms}

    Each takes the digest buffer first, as HACL* does, then the message and
    its length.  These are the C entry points:

      void Hacl_Hash_SHA2_sha256(uint8_t *out, uint8_t *input, size_t len); *)

(** SHA-224. *)
fn sha224 (out: A.array S8.t) (input: A.array S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vout == 28 /\ Seq.length vin < pow2 61)
         ** pure (SZ.v input_len == Seq.length vin)
ensures exists* vout'. A.pts_to out vout' ** A.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_224 vin)
{
  A.pts_to_len out;
  A.pts_to_len input;
  let kt = table k256_arr 64sz;
  let ivt = table iv224_arr 8sz;
  max_input_bound ();
  sha2_224_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to input #pin vin **
    pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_224 vin)
  {
    if (Vec.sha_supported ())
    {
      NI.hash_impl_ni sha2_224 kt ivt out input input_len;
    } else {
      hash_impl sha2_224 kt ivt out input input_len;
    }
  } else {
    hash_impl sha2_224 kt ivt out input input_len;
  };
  drop_table kt;
  drop_table ivt;
}

(** SHA-256. *)
fn sha256 (out: A.array S8.t) (input: A.array S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vout == 32 /\ Seq.length vin < pow2 61)
         ** pure (SZ.v input_len == Seq.length vin)
ensures exists* vout'. A.pts_to out vout' ** A.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_256 vin)
{
  A.pts_to_len out;
  A.pts_to_len input;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  max_input_bound ();
  sha2_256_facts ();
  with pk vkt. assert (A.pts_to kt #pk vkt);
  with pi vivt. assert (A.pts_to ivt #pi vivt);
  if (Hacl.X64.x86_64)
  ensures exists* (vout': Seq.seq S8.t).
    A.pts_to kt #pk vkt ** A.pts_to ivt #pi vivt **
    A.pts_to out vout' ** A.pts_to input #pin vin **
    pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_256 vin)
  {
    if (Vec.sha_supported ())
    {
      NI.hash_impl_ni sha2_256 kt ivt out input input_len;
    } else {
      hash_impl sha2_256 kt ivt out input input_len;
    }
  } else {
    hash_impl sha2_256 kt ivt out input input_len;
  };
  drop_table kt;
  drop_table ivt;
}

(* The eighty-entry [k512] is enough bigger than the sixty-four-entry [k256]
   that relating the array to [params512_with]'s [k] field is best done
   outside the call's query ([sha2_384_facts], [sha2_512_facts]); a little
   headroom over the default budget is kept for the call itself. *)
#push-options "--z3rlimit 10"

(** SHA-384. *)
fn sha384 (out: A.array S8.t) (input: A.array S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vout == 48 /\ Seq.length vin < pow2 61)
         ** pure (SZ.v input_len == Seq.length vin)
ensures exists* vout'. A.pts_to out vout' ** A.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_384 vin)
{
  A.pts_to_len out;
  A.pts_to_len input;
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  max_input_bound ();
  sha2_384_facts ();
  hash_impl sha2_384 kt ivt out input input_len;
  drop_table kt;
  drop_table ivt;
}

(** SHA-512. *)
fn sha512 (out: A.array S8.t) (input: A.array S8.t) (input_len: SZ.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to input #pin vin **
         pure (Seq.length vout == 64 /\ Seq.length vin < pow2 61)
         ** pure (SZ.v input_len == Seq.length vin)
ensures exists* vout'. A.pts_to out vout' ** A.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_512 vin)
{
  A.pts_to_len out;
  A.pts_to_len input;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  max_input_bound ();
  sha2_512_facts ();
  hash_impl sha2_512 kt ivt out input input_len;
  drop_table kt;
  drop_table ivt;
}

#pop-options
