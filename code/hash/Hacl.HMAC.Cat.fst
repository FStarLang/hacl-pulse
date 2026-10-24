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

(** HMAC over a message given in four pieces.

    [Hacl.HMAC.Core.hmac_impl] takes one contiguous message, which is the
    right shape for HKDF and for the one-shot API.  HMAC_DRBG instead keys
    over [V || 0x00 || entropy || nonce || personalization], where the last
    three are the caller's buffers and may be sixty-four kilobytes each;
    materialising the concatenation would mean allocating proportionally to
    them.

    So the inner hash is driven incrementally -- [K0 ^ ipad], then the first
    piece, then the second -- exactly as [Hacl.Ed25519] hashes [R || A ||
    msg].  The outer hash is one block and one digest and needs nothing
    special. *)
module Hacl.HMAC.Cat

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC
open Hacl.Hash.SHA2.Core
open Hacl.Hash.SHA2.Streaming
open Hacl.HMAC.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Mem = Hacl.Mem

(** The streaming interface threads what it has seen as a left-nested
    append; the specification is right-nested.  Reconciling the two inside
    the Pulse function costs minutes, and nothing here needs any of the
    context, so it is a lemma. *)
let cat5 (a b c d e: Seq.seq S8.t)
  : Lemma (Seq.append (Seq.append (Seq.append (Seq.append
             (Seq.append (Seq.empty #S8.t) a) b) c) d) e ==
           Seq.append a (Seq.append b (Seq.append c (Seq.append d e))))
  = assert (Seq.equal
      (Seq.append (Seq.append (Seq.append (Seq.append
        (Seq.append (Seq.empty #S8.t) a) b) c) d) e)
      (Seq.append a (Seq.append b (Seq.append c (Seq.append d e)))))

let cat2 (a b: Seq.seq S8.t)
  : Lemma (Seq.append (Seq.append (Seq.empty #S8.t) a) b == Seq.append a b)
  = Seq.append_empty_l a

(** This module is arithmetic-heavy, and the default SMT encoding boxes
    every integer operation, which hides the structure of the products from
    Z3's arithmetic solver.  Encoding linear arithmetic natively and leaving
    only the nonlinear operators wrapped is measurably faster here. *)
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

fn hmac_cat (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
            ([@@@FStar.Attributes.monomorphize] blocks: blocks_t p)
            (kt: A.array t) (ivt: A.array t) (out: A.array S8.t)
            (key: A.array S8.t)
            (a: A.array S8.t) (b: A.array S8.t) (c: A.array S8.t) (d: A.array S8.t)
            (lk: SZ.t) (la: SZ.t) (lb: SZ.t) (lc: SZ.t) (ld: SZ.t)
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#vout: erased (Seq.seq S8.t))
            (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
            (#pa: perm) (#va: erased (Seq.seq S8.t))
            (#pb: perm) (#vb: erased (Seq.seq S8.t))
            (#pc: perm) (#vc: erased (Seq.seq S8.t))
            (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to key #pkey vkey ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         A.pts_to c #pc vc ** A.pts_to d #pd vd **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #t /\
               SZ.fits (block_len #t + Seq.length va + Seq.length vb +
                        Seq.length vc + Seq.length vd) /\
               block_len #t + Seq.length va + Seq.length vb +
                 Seq.length vc + Seq.length vd < pow2 61 /\
               block_len #t + Seq.length va + Seq.length vb +
                 Seq.length vc + Seq.length vd < max_input #t /\
               SZ.v lk == Seq.length vkey /\ SZ.v la == Seq.length va /\
               SZ.v lb == Seq.length vb /\ SZ.v lc == Seq.length vc /\
               SZ.v ld == Seq.length vd)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to key #pkey vkey ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  A.pts_to c #pc vc ** A.pts_to d #pd vd **
  pure (Seq.length vkey < max_input #t /\
        block_len #t + Seq.length va + Seq.length vb +
          Seq.length vc + Seq.length vd < max_input #t /\
        vout' == hmac p vkey (Seq.append va (Seq.append vb (Seq.append vc vd))))
{
  A.pts_to_len kt; A.pts_to_len ivt; A.pts_to_len out;
  A.pts_to_len key; A.pts_to_len a; A.pts_to_len b;
  A.pts_to_len c; A.pts_to_len d;
  let bl = block_len_sz #t #w;
  let z8 = S8.classify 0uy;
  let z0: t = zero #t #w;

  let mut k0arr = [| z8; bl |];
  Mem.track k0arr; A.pts_to_len k0arr;
  A.pts_to_len k0arr;
  let mut padarr = [| z8; bl |];
  Mem.track padarr; A.pts_to_len padarr;
  A.pts_to_len padarr;
  let mut dgarr = [| z8; p.nhash_bytes |];
  Mem.track dgarr; A.pts_to_len dgarr;
  A.pts_to_len dgarr;
  let mut accarr = [| z0; 8sz |];
  Mem.track accarr; A.pts_to_len accarr;
  A.pts_to_len accarr;
  let mut bufarr = [| z8; bl |];
  Mem.track bufarr; A.pts_to_len bufarr;
  A.pts_to_len bufarr;
  let mut totarr = [| 0sz; 1sz |];
  Mem.track totarr; A.pts_to_len totarr;
  A.pts_to_len totarr;
  let mut wsarr = [| z0; p.nrounds |];
  Mem.track wsarr; A.pts_to_len wsarr;
  A.pts_to_len wsarr;

  key_block_impl p kt ivt k0arr dgarr key lk;

  (** {3 The inner hash, in three pieces} *)
  fill_xor #t padarr k0arr ipad;
  with vpad. assert (A.pts_to padarr vpad);
  init_impl p ivt accarr bufarr totarr;
  update_with p blocks kt wsarr accarr bufarr totarr padarr bl (Seq.empty #S8.t);
  update_with p blocks kt wsarr accarr bufarr totarr a la (Seq.append (Seq.empty #S8.t) vpad);
  update_with p blocks kt wsarr accarr bufarr totarr b lb
    (Seq.append (Seq.append (Seq.empty #S8.t) vpad) va);
  update_with p blocks kt wsarr accarr bufarr totarr c lc
    (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) vpad) va) vb);
  update_with p blocks kt wsarr accarr bufarr totarr d ld
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) vpad) va) vb) vc);
  digest_impl p kt wsarr accarr bufarr totarr dgarr
    (Seq.append (Seq.append (Seq.append (Seq.append
      (Seq.append (Seq.empty #S8.t) vpad) va) vb) vc) vd);
  cat5 (reveal vpad) (reveal va) (reveal vb) (reveal vc) (reveal vd);
  with vdg. assert (A.pts_to dgarr vdg);

  (** {3 The outer hash} *)
  fill_xor #t padarr k0arr opad;
  with vpad2. assert (A.pts_to padarr vpad2);
  sizes #t p;
  init_impl p ivt accarr bufarr totarr;
  update_with p blocks kt wsarr accarr bufarr totarr padarr bl (Seq.empty #S8.t);
  update_with p blocks kt wsarr accarr bufarr totarr dgarr p.nhash_bytes
    (Seq.append (Seq.empty #S8.t) vpad2);
  digest_impl p kt wsarr accarr bufarr totarr out
    (Seq.append (Seq.append (Seq.empty #S8.t) vpad2) vdg);
  cat2 (reveal vpad2) (reveal vdg);

  Mem.wipe wsarr p.nrounds;
  Mem.wipe totarr 1sz;
  Mem.wipe bufarr bl;
  Mem.wipe accarr 8sz;
  Mem.wipe dgarr p.nhash_bytes;
  Mem.wipe padarr bl;
  Mem.wipe k0arr bl;
  ()
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** HMAC of one message over the block function [blocks]: what
    [Hacl.HMAC.Core.hmac_impl] computes, for callers (HMAC-DRBG) that want
    the SHA instructions without a specialized copy of their own. *)
fn hmac_one (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
            ([@@@FStar.Attributes.monomorphize] blocks: blocks_t p)
            (kt: A.array t) (ivt: A.array t) (out: A.array S8.t)
            (key: A.array S8.t) (lk: SZ.t) (msg: A.array S8.t) (lm: SZ.t)
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#vout: erased (Seq.seq S8.t))
            (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
            (#pmsg: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #t /\
               SZ.fits (block_len #t + Seq.length vmsg) /\
               block_len #t + Seq.length vmsg < pow2 61 /\
               block_len #t + Seq.length vmsg < max_input #t)
         ** pure (SZ.v lk == Seq.length vkey)
         ** pure (SZ.v lm == Seq.length vmsg)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to key #pkey vkey ** A.pts_to msg #pmsg vmsg **
  pure (Seq.length vkey < max_input #t /\
        block_len #t + Seq.length vmsg < max_input #t /\
        vout' == hmac p vkey vmsg)
{
  A.pts_to_len kt; A.pts_to_len ivt; A.pts_to_len out;
  A.pts_to_len key; A.pts_to_len msg;
  let bl = block_len_sz #t #w;
  let z8 = S8.classify 0uy;
  let z0: t = zero #t #w;

  let mut k0arr = [| z8; bl |];
  Mem.track k0arr; A.pts_to_len k0arr;
  A.pts_to_len k0arr;
  let mut padarr = [| z8; bl |];
  Mem.track padarr; A.pts_to_len padarr;
  A.pts_to_len padarr;
  let mut dgarr = [| z8; p.nhash_bytes |];
  Mem.track dgarr; A.pts_to_len dgarr;
  A.pts_to_len dgarr;
  let mut accarr = [| z0; 8sz |];
  Mem.track accarr; A.pts_to_len accarr;
  A.pts_to_len accarr;
  let mut bufarr = [| z8; bl |];
  Mem.track bufarr; A.pts_to_len bufarr;
  A.pts_to_len bufarr;
  let mut totarr = [| 0sz; 1sz |];
  Mem.track totarr; A.pts_to_len totarr;
  A.pts_to_len totarr;
  let mut wsarr = [| z0; p.nrounds |];
  Mem.track wsarr; A.pts_to_len wsarr;
  A.pts_to_len wsarr;

  key_block_impl p kt ivt k0arr dgarr key lk;

  fill_xor #t padarr k0arr ipad;
  with vpad. assert (A.pts_to padarr vpad);
  init_impl p ivt accarr bufarr totarr;
  update_with p blocks kt wsarr accarr bufarr totarr padarr bl (Seq.empty #S8.t);
  update_with p blocks kt wsarr accarr bufarr totarr msg lm (Seq.append (Seq.empty #S8.t) vpad);
  digest_impl p kt wsarr accarr bufarr totarr dgarr
    (Seq.append (Seq.append (Seq.empty #S8.t) vpad) vmsg);
  cat2 (reveal vpad) (reveal vmsg);
  with vdg. assert (A.pts_to dgarr vdg);

  fill_xor #t padarr k0arr opad;
  with vpad2. assert (A.pts_to padarr vpad2);
  sizes #t p;
  init_impl p ivt accarr bufarr totarr;
  update_with p blocks kt wsarr accarr bufarr totarr padarr bl (Seq.empty #S8.t);
  update_with p blocks kt wsarr accarr bufarr totarr dgarr p.nhash_bytes
    (Seq.append (Seq.empty #S8.t) vpad2);
  digest_impl p kt wsarr accarr bufarr totarr out
    (Seq.append (Seq.append (Seq.empty #S8.t) vpad2) vdg);
  cat2 (reveal vpad2) (reveal vdg);

  Mem.wipe wsarr p.nrounds;
  Mem.wipe totarr 1sz;
  Mem.wipe bufarr bl;
  Mem.wipe accarr 8sz;
  Mem.wipe dgarr p.nhash_bytes;
  Mem.wipe padarr bl;
  Mem.wipe k0arr bl;
  ()
}

#pop-options
