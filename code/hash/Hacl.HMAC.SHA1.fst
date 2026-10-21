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

(** HMAC-SHA1.

    Three scratch blocks and two calls to [hash_prefixed]: the inner message
    [K0 ^ ipad || msg] and the outer [K0 ^ opad || inner] are never built,
    since the prefix is a block and the rest is read out of the caller's
    buffer.  [Hacl.HMAC.Core]'s [fill_xor] is reused at [S32.t] -- it is a
    loop over a block and knows nothing about the hash -- and so are
    [Spec.HMAC]'s two pointwise lemmas.

      void Hacl_HMAC_SHA1_hmac_sha1(uint8_t *out, uint8_t *key, size_t key_len,
                                    uint8_t *msg, size_t msg_len); *)
module Hacl.HMAC.SHA1

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA1
open Spec.HMAC
open Spec.HMAC.SHA1
open Hacl.Hash.SHA1.Core
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module HC = Hacl.HMAC.Core
module Mem = Hacl.Mem

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** [k0 <- K0].  [k0] must arrive zeroed; [dg] is scratch, used only when the
    key is longer than a block and must itself be hashed. *)
fn key_block_impl (k0: A.array S8.t) (dg: A.array S8.t) (key: A.array S8.t) (lk: SZ.t)
                  (#vk0: erased (Seq.seq S8.t)) (#vdg: erased (Seq.seq S8.t))
                  (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to k0 vk0 ** A.pts_to dg vdg ** A.pts_to key #pkey vkey **
         pure (Seq.length vk0 == block_len /\ Seq.length vdg == hash_bytes /\
               (forall (j: nat). j < block_len ==> Seq.index vk0 j == S8.classify 0uy) /\
               Seq.length vkey < max_input)
         ** pure (SZ.v lk == Seq.length vkey)
ensures exists* (vk0': Seq.seq S8.t) (vdg': Seq.seq S8.t).
  A.pts_to k0 vk0' ** A.pts_to dg vdg' ** A.pts_to key #pkey vkey **
  pure (Seq.length vdg' == hash_bytes /\ Seq.length vkey < max_input /\
        vk0' == key_block vkey)
{
  A.pts_to_len k0;
  A.pts_to_len dg;
  A.pts_to_len key;
  if (SZ.lte lk 64sz)
  {
    copy_prefix k0 key lk;
    with vk0'. assert (A.pts_to k0 vk0');
    key_block_pointwise #S32.t (reveal vk0') (reveal vkey);
    assert (pure (Seq.length vkey <= block_len));
    assert (pure (reveal vk0' ==
                  Seq.append (reveal vkey) (zeros (block_len - Seq.length vkey))));
  }
  else
  {
    hash_impl dg key lk;
    copy_prefix k0 dg 20sz;
    with vk0'. assert (A.pts_to k0 vk0');
    key_block_pointwise #S32.t (reveal vk0') (hash vkey);
    assert (pure (block_len < Seq.length vkey));
    assert (pure (reveal vk0' ==
                  Seq.append (hash vkey) (zeros (block_len - hash_bytes))));
  }
}

(** HMAC-SHA1 of [msg] under [key]. *)
fn hmac_sha1 (out: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t)
             (msg: A.array S8.t) (msg_len: SZ.t)
             (#vout: erased (Seq.seq S8.t))
             (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
             (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (Seq.length vout == 20 /\ Seq.length vkey < pow2 61 /\
               SZ.fits (64 + Seq.length vmsg) /\ 64 + Seq.length vmsg < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
         ** pure (SZ.v msg_len == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to out vout' ** A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input /\ block_len + Seq.length vmsg < max_input /\
        vout' == hmac vkey vmsg)
{
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  let z8 = S8.classify 0uy;

  let mut k0arr = [| z8; 64sz |];
  Mem.track k0arr;
  A.pts_to_len k0arr;
  A.pts_to_len k0arr;

  let mut padarr = [| z8; 64sz |];
  Mem.track padarr;
  A.pts_to_len padarr;
  A.pts_to_len padarr;

  let mut dgarr = [| z8; 20sz |];
  Mem.track dgarr;
  A.pts_to_len dgarr;
  A.pts_to_len dgarr;

  key_block_impl k0arr dgarr key key_len;
  with vk0'. assert (A.pts_to k0arr vk0');

  HC.fill_xor #S32.t padarr k0arr ipad;
  hash_prefixed dgarr padarr msg msg_len;

  HC.fill_xor #S32.t padarr k0arr opad;
  outer_fits ();
  hash_prefixed out padarr dgarr 20sz;

  Mem.wipe dgarr 20sz;
  Mem.wipe padarr 64sz;
  Mem.wipe k0arr 64sz;
  ()
}

#pop-options
