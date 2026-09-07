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

(** HMAC over SHA-2, generically in the word type.

    The implementation allocates three small buffers -- the padded key [K0],
    one scratch block for [K0 ^ ipad] and then [K0 ^ opad], and one digest --
    and never copies the message.  Both hashes are computed with
    [Hacl.Hash.SHA2.Core.hash_prefixed], which absorbs the pad block and then
    reads the rest of the message out of the caller's buffer; this is why
    HMAC of a gigabyte costs no more memory than HMAC of a byte. *)
module Hacl.HMAC.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.SHA2.Lemmas
open Spec.HMAC
open Hacl.Hash.SHA2.Core

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

(** The outer message -- one block plus a digest -- is always small. *)
let sizes (#t: Type0) {| word t |} (p: params t)
  : Lemma (SZ.fits (block_len #t + hash_bytes p) /\
           block_len #t + hash_bytes p < pow2 61 /\
           block_len #t + hash_bytes p < max_input #t)
  = outer_fits #t p;
    assert_norm (24 * 16 < pow2 61);
    assert_norm (24 * 16 < pow2 16)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

(** {2 Building blocks} *)

fn copy_prefix (dst: S.slice S8.t) (src: S.slice S8.t) (n: SZ.t)
               (#vd: erased (Seq.seq S8.t)) (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires S.pts_to dst vd ** S.pts_to src #ps vs **
         pure (SZ.v n <= Seq.length vd /\ SZ.v n <= Seq.length vs)
ensures exists* vd'. S.pts_to dst vd' ** S.pts_to src #ps vs **
        pure (Seq.length vd' == Seq.length vd /\
              SZ.v n <= Seq.length vd' /\ SZ.v n <= Seq.length vs /\
              (forall (k: nat). k < SZ.v n ==> Seq.index vd' k == Seq.index vs k) /\
              (forall (k: nat). SZ.v n <= k /\ k < Seq.length vd ==>
                 Seq.index vd' k == Seq.index vd k))
{
  S.pts_to_len dst;
  S.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S8.t).
    pts_to i vi ** S.pts_to dst vd' ** S.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v n /\ Seq.length vd' == Seq.length vd /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' k == Seq.index vs k) /\
          (forall (k: nat). SZ.v vi <= k /\ k < Seq.length vd ==>
             Seq.index vd' k == Seq.index vd k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(src.(vi));
    S.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
}

(** [pad <- k0 ^ c] over a whole block. *)
fn fill_xor (#t: Type0) {| w: word t |} (pad: S.slice S8.t) (k0: S.slice S8.t) (c: U8.t)
            (#vp: erased (Seq.seq S8.t)) (#pk: perm) (#vk0: erased (Seq.seq S8.t))
requires S.pts_to pad vp ** S.pts_to k0 #pk vk0 **
         pure (Seq.length vp == block_len #t /\ Seq.length vk0 == block_len #t)
ensures exists* vp'. S.pts_to pad vp' ** S.pts_to k0 #pk vk0 **
        pure (Seq.length vk0 == block_len #t /\ vp' == xor_byte #t vk0 c)
{
  S.pts_to_len pad;
  S.pts_to_len k0;
  let bl = block_len_sz #t #w;
  let cs = S8.classify c;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi bl)
  invariant exists* (vi: SZ.t) (vp': Seq.seq S8.t).
    pts_to i vi ** S.pts_to pad vp' ** S.pts_to k0 #pk vk0 **
    pure (SZ.v vi <= block_len #t /\ Seq.length vp' == block_len #t /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index vp' k == S8.logxor (Seq.index vk0 k) (S8.classify c)))
  decreases (block_len #t - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(k0.(vi));
    S.((pad.(vi) <- S8.logxor x cs));
    i := SZ.add vi 1sz;
  };
  with vp'. assert (S.pts_to pad vp');
  assert (pure (Seq.length vp' == block_len #t /\
                (forall (k: nat). k < block_len #t ==>
                   Seq.index vp' k == S8.logxor (Seq.index vk0 k) (S8.classify c))));
  xor_byte_pointwise #t (reveal vp') (reveal vk0) c;
  assert (pure (reveal vp' == xor_byte #t (reveal vk0) c));
}

(** {2 The padded key} *)

(** [k0 <- K0].  [k0] must arrive zeroed; [dg] is scratch, used only when the
    key is longer than a block and must itself be hashed. *)
fn key_block_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                  (kt: S.slice t) (ivt: S.slice t)
                  (k0: S.slice S8.t) (dg: S.slice S8.t) (key: S.slice S8.t)
                  (#pk: perm) (#vk: erased (Seq.seq t))
                  (#pi: perm) (#vi: erased (Seq.seq t))
                  (#vk0: erased (Seq.seq S8.t)) (#vdg: erased (Seq.seq S8.t))
                  (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to k0 vk0 **
         S.pts_to dg vdg ** S.pts_to key #pkey vkey **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vk0 == block_len #t /\ Seq.length vdg == (hash_bytes p) /\
               (forall (j: nat). j < block_len #t ==> Seq.index vk0 j == S8.classify 0uy) /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #t)
ensures exists* (vk0': Seq.seq S8.t) (vdg': Seq.seq S8.t).
  S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to k0 vk0' **
  S.pts_to dg vdg' ** S.pts_to key #pkey vkey **
  pure (Seq.length vdg' == (hash_bytes p) /\
        Seq.length vkey < max_input #t /\ vk0' == key_block p vkey)
{
  S.pts_to_len k0;
  S.pts_to_len dg;
  S.pts_to_len key;
  let bl = block_len_sz #t #w;
  let lk = S.len key;
  if (SZ.lte lk bl)
  {
    copy_prefix k0 key lk;
    with vk0'. assert (S.pts_to k0 vk0');
    key_block_pointwise #t (reveal vk0') (reveal vkey);
    assert (pure (Seq.length vkey <= block_len #t));
    assert (pure (reveal vk0' ==
                  Seq.append (reveal vkey) (zeros (block_len #t - Seq.length vkey))));
  }
  else
  {
    hash_impl p kt ivt dg key;
    copy_prefix k0 dg p.nhash_bytes;
    with vk0'. assert (S.pts_to k0 vk0');
    key_block_pointwise #t (reveal vk0') (hash p vkey);
    assert (pure (block_len #t < Seq.length vkey));
    assert (pure (reveal vk0' ==
                  Seq.append (hash p vkey) (zeros (block_len #t - (hash_bytes p)))));
  }
}

(** {2 HMAC} *)

fn hmac_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (kt: S.slice t) (ivt: S.slice t) (out: S.slice S8.t)
             (key: S.slice S8.t) (msg: S.slice S8.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vout: erased (Seq.seq S8.t))
             (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
             (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout **
         S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #t /\
               SZ.fits (block_len #t + Seq.length vmsg) /\
               block_len #t + Seq.length vmsg < pow2 61 /\
               block_len #t + Seq.length vmsg < max_input #t)
ensures exists* vout'.
  S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout' **
  S.pts_to key #pkey vkey ** S.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #t /\
        block_len #t + Seq.length vmsg < max_input #t /\
        vout' == hmac p vkey vmsg)
{
  S.pts_to_len kt;
  S.pts_to_len ivt;
  S.pts_to_len out;
  S.pts_to_len key;
  S.pts_to_len msg;
  let bl = block_len_sz #t #w;
  let z8 = S8.classify 0uy;

  let mut k0arr = [| z8; bl |];
  A.pts_to_len k0arr;
  let k0 = S.from_array k0arr bl;
  S.pts_to_len k0;

  let mut padarr = [| z8; bl |];
  A.pts_to_len padarr;
  let pad = S.from_array padarr bl;
  S.pts_to_len pad;

  let mut dgarr = [| z8; p.nhash_bytes |];
  A.pts_to_len dgarr;
  let dg = S.from_array dgarr p.nhash_bytes;
  S.pts_to_len dg;

  key_block_impl p kt ivt k0 dg key;
  with vk0'. assert (S.pts_to k0 vk0');

  fill_xor #t pad k0 ipad;
  hash_prefixed p kt ivt dg pad msg;

  fill_xor #t pad k0 opad;
  sizes #t p;
  hash_prefixed p kt ivt out pad dg;

  S.to_array dg;
  S.to_array pad;
  S.to_array k0;
}

#pop-options
