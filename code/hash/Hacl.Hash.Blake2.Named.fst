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
    profiles name; another is four lines.

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
module G = Pulse.Lib.GlobalArray

(** The two initialization vectors, as [static const] arrays in the program
    image; see [Hacl.Impl.Table]. *)

let iv64_arr : G.static_array S64.t = G.mk_static_array iv64_list
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
  let ivt = table iv64_arr 8sz;
  blake2_impl blake2b_512_p ivt out key key_len msg msg_len;
  drop_table ivt;
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
  let ivt = table iv64_arr 8sz;
  blake2_impl blake2b_384_p ivt out key key_len msg msg_len;
  drop_table ivt;
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
  let ivt = table iv64_arr 8sz;
  blake2_impl blake2b_256_p ivt out key key_len msg msg_len;
  drop_table ivt;
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
  let ivt = table iv64_arr 8sz;
  blake2_impl blake2b_160_p ivt out key key_len msg msg_len;
  drop_table ivt;
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
  let ivt = table iv32_arr 8sz;
  blake2_impl blake2s_256_p ivt out key key_len msg msg_len;
  drop_table ivt;
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
  let ivt = table iv32_arr 8sz;
  blake2_impl blake2s_224_p ivt out key key_len msg msg_len;
  drop_table ivt;
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
  let ivt = table iv32_arr 8sz;
  blake2_impl blake2s_160_p ivt out key key_len msg msg_len;
  drop_table ivt;
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
  let ivt = table iv32_arr 8sz;
  blake2_impl blake2s_128_p ivt out key key_len msg msg_len;
  drop_table ivt;
}
