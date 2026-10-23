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

(** HMAC-SHA-384 and HMAC-SHA-512 on [Hacl.Hash.SHA2.AVX2], for the reason
    and in the way [Hacl.HMAC.NI] does it for HMAC-SHA-224/256: the generic
    [Hacl.HMAC.Core.hmac_impl] cannot branch on the word type, so this is it
    specialized to [params S64.t] with the two long hashes going through
    [hash_prefixed_avx2].  The key block is not specialized. *)
module Hacl.HMAC.AVX2

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Lemmas
open Spec.HMAC
open Hacl.Hash.SHA2.Core
open Hacl.Hash.SHA2.AVX2
open Hacl.HMAC.Core
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Mem = Hacl.Mem

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn hmac_impl_avx2 ([@@@FStar.Attributes.monomorphize] p: params S64.t)
                (kt: A.array S64.t) (ivt: A.array S64.t) (out: A.array S8.t)
                (key: A.array S8.t) (lk: SZ.t) (msg: A.array S8.t) (lm: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq S64.t))
                (#pi: perm) (#vi: erased (Seq.seq S64.t))
                (#vout: erased (Seq.seq S8.t))
                (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
                (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (is_sha512 p /\
               reveal vk == (reveal p.k <: Seq.seq S64.t) /\
               reveal vi == (reveal p.iv <: Seq.seq S64.t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #S64.t /\
               SZ.fits (block_len #S64.t + Seq.length vmsg) /\
               block_len #S64.t + Seq.length vmsg < pow2 61 /\
               block_len #S64.t + Seq.length vmsg < max_input #S64.t)
         ** pure (SZ.v lk == Seq.length vkey)
         ** pure (SZ.v lm == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S64.t /\
        block_len #S64.t + Seq.length vmsg < max_input #S64.t /\
        vout' == hmac p vkey vmsg)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  let z8 = S8.classify 0uy;

  let mut k0arr = [| z8; 128sz |];
  Mem.track k0arr;
  A.pts_to_len k0arr;

  let mut padarr = [| z8; 128sz |];
  Mem.track padarr;
  A.pts_to_len padarr;

  let mut dgarr = [| z8; p.nhash_bytes |];
  Mem.track dgarr;
  A.pts_to_len dgarr;

  key_block_impl p kt ivt k0arr dgarr key lk;
  with vk0'. assert (A.pts_to k0arr vk0');

  fill_xor #S64.t padarr k0arr ipad;
  hash_prefixed_avx2 p kt ivt dgarr padarr msg lm;

  fill_xor #S64.t padarr k0arr opad;
  sizes #S64.t p;
  hash_prefixed_avx2 p kt ivt out padarr dgarr p.nhash_bytes;

  Mem.wipe dgarr p.nhash_bytes;
  Mem.wipe padarr 128sz;
  Mem.wipe k0arr 128sz;
  ()
}

#pop-options
