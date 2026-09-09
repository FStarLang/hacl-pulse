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
open Hacl.Impl.Table
open Hacl.Hash.SHA2.Tables

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** [Spec.SHA2.max_input] is [2^61] for the thirty-two bit family and [2^125]
    for the sixty-four bit one, so the [2^61] the callers promise is enough for
    both. *)
let max_input_bound (_: unit)
  : Lemma (pow2 61 <= max_input #S32.t /\ pow2 61 <= max_input #S64.t)
  = assert_norm (bits #S32.t == 32);
    assert_norm (bits #S64.t == 64);
    Math.pow2_le_compat 125 61



(** {2 The four algorithms}

    Each takes the digest buffer first, as HACL* does, and a slice rather than
    a pointer and a length; [Hacl.Hash.SHA2.Ptr] is the flat C interface. *)


(** SHA-224. *)
fn sha224 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 28 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_224 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let kt = table k256_arr 64sz;
  let ivt = table iv224_arr 8sz;
  max_input_bound ();
  hash_impl sha2_224 kt ivt out input;
  drop_table kt;
  drop_table ivt;
}


(** SHA-256. *)
fn sha256 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 32 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S32.t /\ vout' == hash sha2_256 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  max_input_bound ();
  hash_impl sha2_256 kt ivt out input;
  drop_table kt;
  drop_table ivt;
}


(* The eighty-entry [k512] is enough bigger than the sixty-four-entry [k256]
   that relating the array to [params512_with]'s [k] field no longer fits in
   the default budget. *)
#push-options "--z3rlimit 40"

(** SHA-384. *)
fn sha384 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 48 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_384 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  max_input_bound ();
  hash_impl sha2_384 kt ivt out input;
  drop_table kt;
  drop_table ivt;
}


(** SHA-512. *)
fn sha512 (out: S.slice S8.t) (input: S.slice S8.t)
         (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to input #pin vin **
         pure (Seq.length vout == 64 /\ Seq.length vin < pow2 61)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to input #pin vin **
        pure (Seq.length vin < max_input #S64.t /\ vout' == hash sha2_512 vin)
{
  S.pts_to_len out;
  S.pts_to_len input;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  max_input_bound ();
  hash_impl sha2_512 kt ivt out input;
  drop_table kt;
  drop_table ivt;
}

#pop-options
