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

(** The incremental interface to HMAC, generic in the SHA-2 parameters.

    HMAC is two hashes, but only the inner one sees the message, so the
    incremental state is an ordinary incremental SHA-2 state plus one saved
    block:

    {[
      acc, buf, tot   the inner hash, which has already absorbed K0 ^ ipad
      opadb           K0 ^ opad, kept for the outer hash
    ]}

    {!init_impl} derives [K0] from the key, absorbs [K0 ^ ipad] and saves
    [K0 ^ opad]; {!update_impl} is the inner hash's [update] and nothing else;
    {!digest_impl} finishes the inner hash into scratch and hashes
    [K0 ^ opad || inner], which is exactly what {!Hacl.HMAC.Core.hash_prefixed}
    already does for the one-shot version.

    So HMAC costs the caller one extra block of state over a bare hash, and an
    [update] costs exactly what the bare hash's [update] costs.  As with the
    hashes there is no allocation, no destructor and no error code, and
    {!digest_impl} leaves the state alone, so a caller may digest and keep
    going.

    The key is consumed by {!init_impl} and is not part of the state: the
    postcondition remembers it ghostly, in [hmac_ok]. *)
module Hacl.Streaming.HMAC.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Core
open Hacl.HMAC.Core
open Hacl.Hash.SHA2.Streaming

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost
module Mem = Hacl.Mem

(** {2 The state invariant}

    The inner hash has seen [K0 ^ ipad] followed by the message, and [opadb]
    holds [K0 ^ opad]. *)

unfold let hmac_ok (#t: Type0) {| word t |} (p: params t)
                   (key: Seq.seq S8.t) (vacc: Seq.seq t) (vbuf: Seq.seq S8.t)
                   (vtot: Seq.seq SZ.t) (vopadb: Seq.seq S8.t)
                   (msg: Seq.seq S8.t) =
  Seq.length key < max_input #t /\
  stream_ok p vacc vbuf vtot (Seq.append (xor_byte #t (key_block p key) ipad) msg) /\
  vopadb == xor_byte #t (key_block p key) opad

(** [Seq.append] of a block and a message is one block longer.  Stated here
    because the bound has to be available before [hmac_ok] can be unfolded. *)
let inner_len (#t: Type0) {| word t |} (p: params t)
              (key: Seq.seq S8.t { Seq.length key < max_input #t })
              (msg: Seq.seq S8.t)
  : Lemma (Seq.length (Seq.append (xor_byte #t (key_block p key) ipad) msg) ==
             block_len #t + Seq.length msg)
  = Seq.lemma_len_append (xor_byte #t (key_block p key) ipad) msg

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** {2 Reset}

    Derive [K0], absorb [K0 ^ ipad] into a fresh inner hash and save
    [K0 ^ opad].  This is the only function that looks at the key. *)

fn init_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (kt: A.array t) (ivt: A.array t) (wsb: A.array t)
             (acc: A.array t) (buf: A.array S8.t) (tot: A.array SZ.t)
             (opadb: A.array S8.t) (key: A.array S8.t) (lk: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vw0: erased (Seq.seq t)) (#vacc: erased (Seq.seq t))
             (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
             (#vop: erased (Seq.seq S8.t))
             (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to wsb vw0 **
         A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to opadb vop ** A.pts_to key #pkey vkey **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vw0 == (rounds p) /\
               Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
               Seq.length vtot == 1 /\ Seq.length vop == block_len #t /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #t)
         ** pure (SZ.v lk == Seq.length vkey)
ensures exists* (vw: Seq.seq t) (vacc': Seq.seq t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t) (vop': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to wsb vw **
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to opadb vop' ** A.pts_to key #pkey vkey **
  pure (Seq.length vw == (rounds p) /\
        hmac_ok p vkey vacc' vbuf' vtot' vop' (Seq.empty #S8.t))
{
  A.pts_to_len kt; A.pts_to_len ivt; A.pts_to_len acc;
  A.pts_to_len buf; A.pts_to_len tot; A.pts_to_len opadb; A.pts_to_len key;
  let bl = block_len_sz #t #w;
  let z8 = S8.classify 0uy;
  sizes #t p;

  let mut k0arr = [| z8; bl |];
  Mem.track k0arr;
  A.pts_to_len k0arr;
  A.pts_to_len k0arr;
  let mut dgarr = [| z8; p.nhash_bytes |];
  Mem.track dgarr;
  A.pts_to_len dgarr;
  A.pts_to_len dgarr;

  key_block_impl p kt ivt k0arr dgarr key lk;
  with vk0. assert (A.pts_to k0arr vk0);

  fill_xor #t opadb k0arr opad;

  let mut ipadarr = [| z8; bl |];
  Mem.track ipadarr;
  A.pts_to_len ipadarr;
  A.pts_to_len ipadarr;
  fill_xor #t ipadarr k0arr ipad;

  Hacl.Hash.SHA2.Streaming.init_impl p ivt acc buf tot;
  Hacl.Hash.SHA2.Streaming.update_impl p kt wsb acc buf tot ipadarr bl
    (Seq.empty #S8.t);

  with vacc'. assert (A.pts_to acc vacc');
  with vbuf'. assert (A.pts_to buf vbuf');
  with vtot'. assert (A.pts_to tot vtot');
  assert (pure (Seq.equal (Seq.append (Seq.empty #S8.t) (xor_byte #t vk0 ipad))
                          (Seq.append (xor_byte #t vk0 ipad) (Seq.empty #S8.t))));
  Mem.wipe ipadarr bl;
  Mem.wipe dgarr p.nhash_bytes;
  Mem.wipe k0arr bl;
  ()
}

#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** {2 Absorb}

    The inner hash's [update], with the invariant rephrased, over the block
    function [blocks]. *)

fn update_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               ([@@@FStar.Attributes.monomorphize] blocks: blocks_t p)
               (kt: A.array t) (wsb: A.array t) (acc: A.array t)
               (buf: A.array S8.t) (tot: A.array SZ.t)
               (data: A.array S8.t) (dlen: SZ.t)
               (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
               (vop: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#vw0: erased (Seq.seq t)) (#vacc: erased (Seq.seq t))
               (#vbuf: erased (Seq.seq S8.t)) (#vtot: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to acc vacc **
         A.pts_to buf vbuf ** A.pts_to tot vtot ** A.pts_to data #pd vdata **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               hmac_ok p key vacc vbuf vtot vop msg /\
               block_len #t + Seq.length msg + Seq.length vdata < pow2 61 /\
               block_len #t + Seq.length msg + Seq.length vdata < max_input #t /\
               SZ.fits (block_len #t + Seq.length msg + Seq.length vdata))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vw: Seq.seq t) (vacc': Seq.seq t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to acc vacc' **
  A.pts_to buf vbuf' ** A.pts_to tot vtot' ** A.pts_to data #pd vdata **
  pure (Seq.length vw == (rounds p) /\
        hmac_ok p key vacc' vbuf' vtot' vop (Seq.append msg vdata))
{
  A.pts_to_len acc; A.pts_to_len buf; A.pts_to_len tot; A.pts_to_len data;
  let seen = G.hide (Seq.append (xor_byte #t (key_block p (reveal key)) ipad)
                                (reveal msg));
  inner_len #t p (reveal key) (reveal msg);
  update_with p blocks kt wsb acc buf tot data dlen seen;
  Seq.append_assoc (xor_byte #t (key_block p (reveal key)) ipad)
                   (reveal msg) (reveal vdata);
  ()
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** {2 Digest}

    Finish the inner hash into scratch, then hash [K0 ^ opad || inner].  The
    state is untouched, so a caller may digest and keep absorbing. *)

fn digest_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (ivt: A.array t) (wsb: A.array t)
               (acc: A.array t) (buf: A.array S8.t) (tot: A.array SZ.t)
               (opadb: A.array S8.t) (out: A.array S8.t)
               (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#vw0: erased (Seq.seq t))
               (#pa: perm) (#vacc: erased (Seq.seq t))
               (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
               (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
               (#pop: perm) (#vop: erased (Seq.seq S8.t))
               (#vout: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to wsb vw0 **
         A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to opadb #pop vop ** A.pts_to out vout **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vw0 == (rounds p) /\ Seq.length vout == (hash_bytes p) /\
               hmac_ok p key vacc vbuf vtot vop msg)
ensures exists* (vw: Seq.seq t) (vout': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to wsb vw **
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to opadb #pop vop ** A.pts_to out vout' **
  pure (Seq.length vw == (rounds p) /\ Seq.length key < max_input #t /\
        block_len #t + Seq.length msg < max_input #t /\
        vout' == hmac p key msg)
{
  A.pts_to_len opadb; A.pts_to_len out;
  let z8 = S8.classify 0uy;
  sizes #t p;
  inner_len #t p (reveal key) (reveal msg);

  let mut dgarr = [| z8; p.nhash_bytes |];
  Mem.track dgarr;
  A.pts_to_len dgarr;
  A.pts_to_len dgarr;

  let seen = G.hide (Seq.append (xor_byte #t (key_block p (reveal key)) ipad)
                                (reveal msg));
  Hacl.Hash.SHA2.Streaming.digest_impl p kt wsb acc buf tot dgarr seen;
  hash_prefixed p kt ivt out opadb dgarr p.nhash_bytes;
  Mem.wipe dgarr p.nhash_bytes;
  ()
}

#pop-options
