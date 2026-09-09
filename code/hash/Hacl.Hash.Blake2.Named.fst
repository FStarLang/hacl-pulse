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

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module G = FStar.Ghost

(** The two initialization vectors, written into a slice because the
    direct-to-C backend has no constant globals. *)
fn fill_iv64 (b: S.slice S64.t) (#v0: erased (Seq.seq S64.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 8 (S64.classify 0uL))
ensures S.pts_to b iv64
{
  S.pts_to_len b;
  S.((b.(0sz) <- S64.classify 0x6a09e667f3bcc908uL)); S.pts_to_len b;
  S.((b.(1sz) <- S64.classify 0xbb67ae8584caa73buL)); S.pts_to_len b;
  S.((b.(2sz) <- S64.classify 0x3c6ef372fe94f82buL)); S.pts_to_len b;
  S.((b.(3sz) <- S64.classify 0xa54ff53a5f1d36f1uL)); S.pts_to_len b;
  S.((b.(4sz) <- S64.classify 0x510e527fade682d1uL)); S.pts_to_len b;
  S.((b.(5sz) <- S64.classify 0x9b05688c2b3e6c1fuL)); S.pts_to_len b;
  S.((b.(6sz) <- S64.classify 0x1f83d9abfb41bd6buL)); S.pts_to_len b;
  S.((b.(7sz) <- S64.classify 0x5be0cd19137e2179uL)); S.pts_to_len b;
}

fn fill_iv32 (b: S.slice S32.t) (#v0: erased (Seq.seq S32.t))
requires S.pts_to b v0 ** pure (reveal v0 == Seq.create 8 (S32.classify 0ul))
ensures S.pts_to b iv32
{
  S.pts_to_len b;
  S.((b.(0sz) <- S32.classify 0x6a09e667ul)); S.pts_to_len b;
  S.((b.(1sz) <- S32.classify 0xbb67ae85ul)); S.pts_to_len b;
  S.((b.(2sz) <- S32.classify 0x3c6ef372ul)); S.pts_to_len b;
  S.((b.(3sz) <- S32.classify 0xa54ff53aul)); S.pts_to_len b;
  S.((b.(4sz) <- S32.classify 0x510e527ful)); S.pts_to_len b;
  S.((b.(5sz) <- S32.classify 0x9b05688cul)); S.pts_to_len b;
  S.((b.(6sz) <- S32.classify 0x1f83d9abul)); S.pts_to_len b;
  S.((b.(7sz) <- S32.classify 0x5be0cd19ul)); S.pts_to_len b;
}


(** BLAKE2B with a 512-bit digest. *)
let blake2b_512_p : params S64.t = blake2b_with 64sz

fn blake2b_512 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 64 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_512_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S64.classify 0uL;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv64 ivt;
  blake2_impl blake2b_512_p ivt out key msg;
  S.to_array ivt;
}

(** BLAKE2B with a 384-bit digest. *)
let blake2b_384_p : params S64.t = blake2b_with 48sz

fn blake2b_384 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 48 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_384_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S64.classify 0uL;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv64 ivt;
  blake2_impl blake2b_384_p ivt out key msg;
  S.to_array ivt;
}

(** BLAKE2B with a 256-bit digest. *)
let blake2b_256_p : params S64.t = blake2b_with 32sz

fn blake2b_256 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 32 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_256_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S64.classify 0uL;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv64 ivt;
  blake2_impl blake2b_256_p ivt out key msg;
  S.to_array ivt;
}

(** BLAKE2B with a 160-bit digest. *)
let blake2b_160_p : params S64.t = blake2b_with 20sz

fn blake2b_160 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 20 /\ Seq.length vkey <= 64 /\
               Seq.length vmsg + 256 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 256))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 64 /\ vout' == blake2 blake2b_160_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S64.classify 0uL;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv64 ivt;
  blake2_impl blake2b_160_p ivt out key msg;
  S.to_array ivt;
}

(** BLAKE2S with a 256-bit digest. *)
let blake2s_256_p : params S32.t = blake2s_with 32sz

fn blake2s_256 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 32 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_256_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S32.classify 0ul;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv32 ivt;
  blake2_impl blake2s_256_p ivt out key msg;
  S.to_array ivt;
}

(** BLAKE2S with a 224-bit digest. *)
let blake2s_224_p : params S32.t = blake2s_with 28sz

fn blake2s_224 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 28 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_224_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S32.classify 0ul;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv32 ivt;
  blake2_impl blake2s_224_p ivt out key msg;
  S.to_array ivt;
}

(** BLAKE2S with a 160-bit digest. *)
let blake2s_160_p : params S32.t = blake2s_with 20sz

fn blake2s_160 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 20 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_160_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S32.classify 0ul;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv32 ivt;
  blake2_impl blake2s_160_p ivt out key msg;
  S.to_array ivt;
}

(** BLAKE2S with a 128-bit digest. *)
let blake2s_128_p : params S32.t = blake2s_with 16sz

fn blake2s_128 (out: S.slice S8.t) (key: S.slice S8.t) (msg: S.slice S8.t)
            (#vout: erased (Seq.seq S8.t))
            (#pk: perm) (#vkey: erased (Seq.seq S8.t))
            (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
         pure (Seq.length vout == 16 /\ Seq.length vkey <= 32 /\
               Seq.length vmsg + 128 < pow2 64 /\
               SZ.fits (Seq.length vmsg + 128))
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to key #pk vkey ** S.pts_to msg #pm vmsg **
  pure (Seq.length vkey <= 32 /\ vout' == blake2 blake2s_128_p (reveal vkey) (reveal vmsg))
{
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let z = S32.classify 0ul;
  let mut ivarr = [| z; 8sz |];
  A.pts_to_len ivarr;
  let ivt = S.from_array ivarr 8sz;
  fill_iv32 ivt;
  blake2_impl blake2s_128_p ivt out key msg;
  S.to_array ivt;
}
