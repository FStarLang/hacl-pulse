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

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8

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

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

fn hmac_cat (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
            (kt: S.slice t) (ivt: S.slice t) (out: S.slice S8.t)
            (key: S.slice S8.t)
            (a: S.slice S8.t) (b: S.slice S8.t) (c: S.slice S8.t) (d: S.slice S8.t)
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#vout: erased (Seq.seq S8.t))
            (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
            (#pa: perm) (#va: erased (Seq.seq S8.t))
            (#pb: perm) (#vb: erased (Seq.seq S8.t))
            (#pc: perm) (#vc: erased (Seq.seq S8.t))
            (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout **
         S.pts_to key #pkey vkey ** S.pts_to a #pa va ** S.pts_to b #pb vb **
         S.pts_to c #pc vc ** S.pts_to d #pd vd **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vkey < pow2 61 /\ Seq.length vkey < max_input #t /\
               SZ.fits (block_len #t + Seq.length va + Seq.length vb +
                        Seq.length vc + Seq.length vd) /\
               block_len #t + Seq.length va + Seq.length vb +
                 Seq.length vc + Seq.length vd < pow2 61 /\
               block_len #t + Seq.length va + Seq.length vb +
                 Seq.length vc + Seq.length vd < max_input #t)
ensures exists* vout'.
  S.pts_to kt #pk vk ** S.pts_to ivt #pi vi ** S.pts_to out vout' **
  S.pts_to key #pkey vkey ** S.pts_to a #pa va ** S.pts_to b #pb vb **
  S.pts_to c #pc vc ** S.pts_to d #pd vd **
  pure (Seq.length vkey < max_input #t /\
        block_len #t + Seq.length va + Seq.length vb +
          Seq.length vc + Seq.length vd < max_input #t /\
        vout' == hmac p vkey (Seq.append va (Seq.append vb (Seq.append vc vd))))
{
  S.pts_to_len kt; S.pts_to_len ivt; S.pts_to_len out;
  S.pts_to_len key; S.pts_to_len a; S.pts_to_len b;
  S.pts_to_len c; S.pts_to_len d;
  let bl = block_len_sz #t #w;
  let z8 = S8.classify 0uy;
  let z0: t = zero #t #w;

  let mut k0arr = [| z8; bl |]; A.pts_to_len k0arr;
  let k0 = S.from_array k0arr bl; S.pts_to_len k0;
  let mut padarr = [| z8; bl |]; A.pts_to_len padarr;
  let pad = S.from_array padarr bl; S.pts_to_len pad;
  let mut dgarr = [| z8; p.nhash_bytes |]; A.pts_to_len dgarr;
  let dg = S.from_array dgarr p.nhash_bytes; S.pts_to_len dg;
  let mut accarr = [| z0; 8sz |]; A.pts_to_len accarr;
  let acc = S.from_array accarr 8sz; S.pts_to_len acc;
  let mut bufarr = [| z8; bl |]; A.pts_to_len bufarr;
  let buf = S.from_array bufarr bl; S.pts_to_len buf;
  let mut totarr = [| 0sz; 1sz |]; A.pts_to_len totarr;
  let tot = S.from_array totarr 1sz; S.pts_to_len tot;
  let mut wsarr = [| z0; p.nrounds |]; A.pts_to_len wsarr;
  let wsb = S.from_array wsarr p.nrounds; S.pts_to_len wsb;

  key_block_impl p kt ivt k0 dg key;

  (** {3 The inner hash, in three pieces} *)
  fill_xor #t pad k0 ipad;
  with vpad. assert (S.pts_to pad vpad);
  init_impl p ivt acc buf tot;
  update_impl p kt wsb acc buf tot pad (Seq.empty #S8.t);
  update_impl p kt wsb acc buf tot a (Seq.append (Seq.empty #S8.t) vpad);
  update_impl p kt wsb acc buf tot b
    (Seq.append (Seq.append (Seq.empty #S8.t) vpad) va);
  update_impl p kt wsb acc buf tot c
    (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) vpad) va) vb);
  update_impl p kt wsb acc buf tot d
    (Seq.append (Seq.append (Seq.append (Seq.append (Seq.empty #S8.t) vpad) va) vb) vc);
  digest_impl p kt wsb acc buf tot dg
    (Seq.append (Seq.append (Seq.append (Seq.append
      (Seq.append (Seq.empty #S8.t) vpad) va) vb) vc) vd);
  cat5 (reveal vpad) (reveal va) (reveal vb) (reveal vc) (reveal vd);

  (** {3 The outer hash} *)
  fill_xor #t pad k0 opad;
  sizes #t p;
  hash_prefixed p kt ivt out pad dg;

  S.to_array wsb; S.to_array tot; S.to_array buf; S.to_array acc;
  S.to_array dg; S.to_array pad; S.to_array k0;
}

#pop-options
