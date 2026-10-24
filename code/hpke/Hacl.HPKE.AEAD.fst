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

(** HPKE's three sealing algorithms behind one interface.

    RFC 9180 registers AES-128-GCM, AES-256-GCM and ChaCha20-Poly1305, and
    names AES-128-GCM mandatory to implement.  All three are here.

    Both families take the output either in place or in a separate buffer
    ({!Hacl.Impl.InOut.inout}); HPKE always passes separate ones.  Their
    specifications disagree about what they are written over: [Spec.GCM]
    speaks of public bytes and [Spec.Chacha20Poly1305] of secret ones.  That
    difference is absorbed here by [Spec.Byte]'s [vals] and [secrets], which
    are ghost renamings and not declassification.

    The algorithm is a [monomorphize] parameter, so a program that seals with
    one of them links one of them. *)
module Hacl.HPKE.AEAD

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.HPKE

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module CP = Hacl.Chacha20Poly1305
module GCM = Hacl.AES.GCM
module IO = Hacl.Impl.InOut

(** The key length as a machine value. *)
let key_len ([@@@FStar.Attributes.monomorphize] a: aead_alg)
  : n: SZ.t { SZ.v n == size_aead_key a }
  = match a with
    | Seal_AES128_GCM -> 16sz
    | Seal_AES256_GCM -> 32sz
    | Seal_Chacha20Poly1305 -> 32sz
    | ExportOnly -> 0sz

(** Every real limit is far above this; see [Spec.HPKE.aead_ok]. *)
let aead_bounds (n: nat)
  : Lemma (requires n < pow2 32)
          (ensures n <= 4294967295 /\ n <= pow2 36 - 32 /\ n <= pow2 61 - 1 /\
                   n <= Spec.Chacha20.max_len 1ul /\ 12 <= pow2 61 - 1)
  = assert_norm (12 <= pow2 61 - 1);
    assert_norm (pow2 32 - 1 <= pow2 36 - 32);
    assert_norm (pow2 32 - 1 <= pow2 61 - 1);
    assert_norm (pow2 32 - 1 <= (pow2 32 - 1) * 64)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"

fn seal_impl ([@@@FStar.Attributes.monomorphize] a: aead_alg { ~(ExportOnly? a) })
             (ct: A.array S8.t) (tag: A.array S8.t)
             (msg: A.array S8.t) (mlen: SZ.t)
             (aad: A.array S8.t) (alen: SZ.t)
             (key: A.array S8.t) (nonce: A.array S8.t)
             (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
             (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pk: perm) (#vkey: erased (Seq.seq S8.t))
             (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to ct vct ** A.pts_to tag vtag ** A.pts_to msg #pm vmsg **
         A.pts_to aad #pa vaad ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vct == Seq.length vmsg /\ Seq.length vtag == 16 /\
               Seq.length vkey == size_aead_key a /\ Seq.length vnon == 12 /\
               Seq.length vmsg < pow2 32 /\ Seq.length vaad < pow2 32 /\
               SZ.fits (Seq.length vmsg + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v mlen == Seq.length vmsg)
         ** pure (SZ.v alen == Seq.length vaad)
ensures exists* vct' vtag'.
  A.pts_to ct vct' ** A.pts_to tag vtag' ** A.pts_to msg #pm vmsg **
  A.pts_to aad #pa vaad ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == size_aead_key a /\ Seq.length vnon == 12 /\
        Seq.length vmsg < pow2 32 /\ Seq.length vaad < pow2 32 /\
        Seq.length vct' == Seq.length vmsg /\ Seq.length vtag' == 16 /\
        (vct', vtag') == aead_seal a vkey vnon vaad vmsg)
{
  A.pts_to_len ct;
  A.pts_to_len tag;
  A.pts_to_len msg;
  A.pts_to_len aad;
  A.pts_to_len key;
  A.pts_to_len nonce;
  aead_bounds (Seq.length vmsg);
  aead_bounds (Seq.length vaad);
  vals_len vnon; vals_len vaad; vals_len vmsg;

  if (Seal_Chacha20Poly1305? a) {
    CP.encrypt_disjoint ct tag msg mlen aad alen key nonce;
  } else {
    assert (pure (Spec.GCM.iv_ok (vals vnon)));
    assert (pure (Spec.GCM.aad_ok (vals vaad)));
    assert (pure (Spec.GCM.msg_ok (vals vmsg)));
    if (Seal_AES128_GCM? a) {
      IO.intro_disjoint ct msg;
      GCM.aes128_encrypt ct tag msg mlen key nonce 12sz aad alen;
      IO.elim_disjoint ct msg;
    } else {
      IO.intro_disjoint ct msg;
      GCM.aes256_encrypt ct tag msg mlen key nonce 12sz aad alen;
      IO.elim_disjoint ct msg;
    }
  }
}

(** Opening answers with a [bool].  On [false] the plaintext buffer holds
    nothing a caller should look at, and no plaintext was ever written,
    which is the property that matters. *)
fn open_impl ([@@@FStar.Attributes.monomorphize] a: aead_alg { ~(ExportOnly? a) })
             (msg: A.array S8.t)
             (ct: A.array S8.t) (clen: SZ.t) (tag: A.array S8.t)
             (aad: A.array S8.t) (alen: SZ.t)
             (key: A.array S8.t) (nonce: A.array S8.t)
             (#vmsg: erased (Seq.seq S8.t))
             (#pc: perm) (#vct: erased (Seq.seq S8.t))
             (#pt: perm) (#vtag: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pk: perm) (#vkey: erased (Seq.seq S8.t))
             (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to msg vmsg ** A.pts_to ct #pc vct ** A.pts_to tag #pt vtag **
         A.pts_to aad #pa vaad ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vmsg == Seq.length vct /\ Seq.length vtag == 16 /\
               Seq.length vkey == size_aead_key a /\ Seq.length vnon == 12 /\
               Seq.length vct < pow2 32 /\ Seq.length vaad < pow2 32 /\
               SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v clen == Seq.length vct)
         ** pure (SZ.v alen == Seq.length vaad)
returns r: bool
ensures exists* vmsg'.
  A.pts_to msg vmsg' ** A.pts_to ct #pc vct ** A.pts_to tag #pt vtag **
  A.pts_to aad #pa vaad ** A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == size_aead_key a /\ Seq.length vnon == 12 /\
        Seq.length vtag == 16 /\
        Seq.length vct < pow2 32 /\ Seq.length vaad < pow2 32 /\
        Seq.length vmsg' == Seq.length vct /\
        (r <==> aead_open_ok a vkey vnon vaad vct vtag) /\
        (r ==> vmsg' == aead_opened a vkey vnon vct))
{
  A.pts_to_len msg;
  A.pts_to_len ct;
  A.pts_to_len tag;
  A.pts_to_len aad;
  A.pts_to_len key;
  A.pts_to_len nonce;
  aead_bounds (Seq.length vct);
  aead_bounds (Seq.length vaad);
  vals_len vnon; vals_len vaad; vals_len vct;

  if (Seal_Chacha20Poly1305? a) {
    let r = CP.decrypt_disjoint msg ct clen tag aad alen key nonce;
    r
  } else {
    if (Seal_AES128_GCM? a) {
      IO.intro_disjoint msg ct;
      let r = GCM.aes128_decrypt msg ct clen tag key nonce 12sz aad alen;
      IO.elim_disjoint msg ct;
      r
    } else {
      IO.intro_disjoint msg ct;
      let r = GCM.aes256_decrypt msg ct clen tag key nonce 12sz aad alen;
      IO.elim_disjoint msg ct;
      r
    }
  }
}

#pop-options
