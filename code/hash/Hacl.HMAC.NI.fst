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

(** HMAC-SHA-224/256 on the SHA instructions.

    [Hacl.HMAC.Core.hmac_impl] is generic in the word type, which is what
    lets one function serve all four of SHA-224, SHA-256, SHA-384 and
    SHA-512.  The price is that it cannot branch into
    [Hacl.Hash.SHA2.NI]: that code exists only at thirty-two-bit words, and
    the generic function has no way to ask whether [t] is one.  So it called
    the scalar block function unconditionally, and HMAC-SHA-256 ran scalar
    rounds on machines where plain SHA-256 was already using
    [SHA256RNDS2] -- about five times the cost of hashing the same bytes,
    inherited by HKDF-SHA-256, HMAC-DRBG-SHA-256 and everything built on
    them.

    This is that one function specialized to [params S32.t], with the two
    long hashes going through [hash_prefixed_ni].  It is a copy, and copies
    are a cost; the alternative is a dispatch hook in the [word] class,
    which would put an implementation choice into a type class that is
    otherwise a statement about values.  Two hundred lines of duplication
    against that seemed the better trade, and it is the same trade
    [Hacl.Hash.SHA2.NI]'s [hash_blocks_ni] already made against
    [Hacl.Hash.SHA2.Core]'s [hash_blocks].

    The key block is *not* specialized.  A key longer than sixty-four bytes
    is hashed once, which is at most a handful of blocks against a message
    that may be gigabytes, and [Hacl.HMAC.Core.key_block_impl] computes the
    same value either way. *)
module Hacl.HMAC.NI

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Lemmas
open Spec.SHANI
open Spec.HMAC
open Hacl.Hash.SHA2.Core
open Hacl.Hash.SHA2.NI
open Hacl.HMAC.Core
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Mem = Hacl.Mem

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

fn hmac_impl_ni ([@@@FStar.Attributes.monomorphize] p: params S32.t)
                (kt: A.array S32.t) (ivt: A.array S32.t) (out: A.array S8.t)
                (key: A.array S8.t) (lk: SZ.t) (msg: A.array S8.t) (lm: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq S32.t))
                (#pi: perm) (#vi: erased (Seq.seq S32.t))
                (#vout: erased (Seq.seq S8.t))
                (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
                (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (is_sha256 p /\
               reveal vk == (reveal p.k <: Seq.seq S32.t) /\
               reveal vi == (reveal p.iv <: Seq.seq S32.t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #S32.t /\
               SZ.fits (block_len #S32.t + Seq.length vmsg) /\
               block_len #S32.t + Seq.length vmsg < pow2 61 /\
               block_len #S32.t + Seq.length vmsg < max_input #S32.t)
         ** pure (SZ.v lk == Seq.length vkey)
         ** pure (SZ.v lm == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #S32.t /\
        block_len #S32.t + Seq.length vmsg < max_input #S32.t /\
        vout' == hmac p vkey vmsg)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len key;
  A.pts_to_len msg;
  let z8 = S8.classify 0uy;

  let mut k0arr = [| z8; 64sz |];
  Mem.track k0arr;
  A.pts_to_len k0arr;

  let mut padarr = [| z8; 64sz |];
  Mem.track padarr;
  A.pts_to_len padarr;

  let mut dgarr = [| z8; p.nhash_bytes |];
  Mem.track dgarr;
  A.pts_to_len dgarr;

  key_block_impl p kt ivt k0arr dgarr key lk;
  with vk0'. assert (A.pts_to k0arr vk0');

  fill_xor #S32.t padarr k0arr ipad;
  hash_prefixed_ni p kt ivt dgarr padarr msg lm;

  fill_xor #S32.t padarr k0arr opad;
  sizes #S32.t p;
  hash_prefixed_ni p kt ivt out padarr dgarr p.nhash_bytes;

  Mem.wipe dgarr p.nhash_bytes;
  Mem.wipe padarr 64sz;
  Mem.wipe k0arr 64sz;
  ()
}

#pop-options
