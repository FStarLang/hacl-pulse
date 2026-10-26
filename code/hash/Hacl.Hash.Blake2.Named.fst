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

(** The named BLAKE2 hashes.

    BLAKE2's digest length is a parameter of the algorithm rather than a
    truncation -- it is mixed into the initial state -- so there is one entry
    point per length rather than one with a length argument.  That is also
    what makes the whole record a compile-time constant, which is what lets
    Custard fold the round count and the four rotation distances into
    literals.  The eight lengths here are the ones RFC 7693 and the common
    profiles name; another is four lines.  For any other length, or for a
    salt, a personalization or tree-hashing parameters, use [blake2b_params]
    and [blake2s_params] at the end of this module, which take the whole
    parameter block at run time.

    Every entry point takes a key, which may be empty.  An empty key is an
    unkeyed hash; a nonempty one is prepended as a whole block and counted. *)
module Hacl.Hash.Blake2.Named

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.Blake2
open Spec.Blake2.Constants
open Hacl.Hash.Blake2
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module G = Pulse.Lib.GlobalArray

(** The two initialization vectors, as [static const] arrays in the program
    image; see [Hacl.Impl.Table]. *)

[@@FStar.Custard.no_specialize]
let iv64_arr : G.static_array S64.t = G.mk_static_array iv64_list
[@@FStar.Custard.no_specialize]
let iv32_arr : G.static_array S32.t = G.mk_static_array iv32_list

let table_lens (_: unit)
  : Lemma (Seq.length (G.static_array_elems iv64_arr) == 8 /\
           Seq.length (G.static_array_elems iv32_arr) == 8)
  = assert_norm (List.Tot.length iv64_list == 8);
    assert_norm (List.Tot.length iv32_list == 8)

(** BLAKE2B with a 512-bit digest. *)
let blake2b_512_p : params S64.t = blake2b_with 64sz

fn blake2b_512 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 64 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_512_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2b_512_p iv64_arr out key key_len msg msg_len;
}

(** BLAKE2B with a 384-bit digest. *)
let blake2b_384_p : params S64.t = blake2b_with 48sz

fn blake2b_384 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 48 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_384_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2b_384_p iv64_arr out key key_len msg msg_len;
}

(** BLAKE2B with a 256-bit digest. *)
let blake2b_256_p : params S64.t = blake2b_with 32sz

fn blake2b_256 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 32 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_256_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2b_256_p iv64_arr out key key_len msg msg_len;
}

(** BLAKE2B with a 160-bit digest. *)
let blake2b_160_p : params S64.t = blake2b_with 20sz

fn blake2b_160 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 20 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_160_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2b_160_p iv64_arr out key key_len msg msg_len;
}

(** BLAKE2S with a 256-bit digest. *)
let blake2s_256_p : params S32.t = blake2s_with 32sz

fn blake2s_256 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 32 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_256_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2s_256_p iv32_arr out key key_len msg msg_len;
}

(** BLAKE2S with a 224-bit digest. *)
let blake2s_224_p : params S32.t = blake2s_with 28sz

fn blake2s_224 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 28 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_224_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2s_224_p iv32_arr out key key_len msg msg_len;
}

(** BLAKE2S with a 160-bit digest. *)
let blake2s_160_p : params S32.t = blake2s_with 20sz

fn blake2s_160 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 20 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_160_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2s_160_p iv32_arr out key key_len msg msg_len;
}

(** BLAKE2S with a 128-bit digest. *)
let blake2s_128_p : params S32.t = blake2s_with 16sz

fn blake2s_128 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         pure (Seq.length vout == 16 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_128_p (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_impl blake2s_128_p iv32_arr out key key_len msg msg_len;
}

(** {2 Under a full parameter block}

    BLAKE2b and BLAKE2s with every field of the parameter block a runtime
    argument: a digest length [out_len] from 1 to the state size, a key, a
    salt and a personalization (each two words: 16 or 8 bytes), and the
    tree-hashing fields.  For a sequential hash the tree fields are fanout 1,
    depth 1 and the rest zero, and with an all-zero salt and personalization
    the result is the named hash of the same length. *)

fn blake2b_params (out: A.array S8.t) (out_len: SZ.t)
              (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
              (salt: A.array S8.t) (personal: A.array S8.t)
              (fanout: U8.t) (depth: U8.t) (leaf_length: U32.t)
              (node_offset: U64.t) (node_depth: U8.t) (inner_length: U8.t)
              (bp: erased (blake2_params S64.t))
              (#vout: erased (Seq.seq S8.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
              (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
              (#ps: perm) (#vs: erased (Seq.seq S8.t))
              (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
         pure (Seq.length vout == SZ.v out_len /\ Seq.length vkey <= 64 /\
               params_match bp out_len fanout depth leaf_length node_offset
                            node_depth inner_length vs vp /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
  pure (Seq.length vkey <= 64 /\
        vout' == blake2_with_params blake2b_512_p bp (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_params_impl blake2b_512_p iv64_arr out out_len key key_len msg msg_len salt personal
                     fanout depth leaf_length node_offset node_depth inner_length bp;
}

fn blake2s_params (out: A.array S8.t) (out_len: SZ.t)
              (key: A.array S8.t) (key_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
              (salt: A.array S8.t) (personal: A.array S8.t)
              (fanout: U8.t) (depth: U8.t) (leaf_length: U32.t)
              (node_offset: U64.t) (node_depth: U8.t) (inner_length: U8.t)
              (bp: erased (blake2_params S32.t))
              (#vout: erased (Seq.seq S8.t))
              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
              (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
              (#ps: perm) (#vs: erased (Seq.seq S8.t))
              (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
         A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
         pure (Seq.length vout == SZ.v out_len /\ Seq.length vkey <= 32 /\
               params_match bp out_len fanout depth leaf_length node_offset
                            node_depth inner_length vs vp /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to key #pk vkey ** A.pts_to msg #pm vmsg **
  A.pts_to salt #ps vs ** A.pts_to personal #pp vp **
  pure (Seq.length vkey <= 32 /\
        vout' == blake2_with_params blake2s_256_p bp (reveal vkey) (reveal vmsg))
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  table_lens ();
  blake2_params_impl blake2s_256_p iv32_arr out out_len key key_len msg msg_len salt personal
                     fanout depth leaf_length node_offset node_depth inner_length bp;
}
