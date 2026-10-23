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

(** The shipped HPKE ciphersuites, RFC 9180 section 7.

    {!Hacl.HPKE} is a single implementation parameterised by a ciphersuite
    record.  A C caller cannot pass such a record, so this module pins it:
    one set of entry points per ciphersuite, each of which lays out the
    round-constant tables its hash needs and forwards.  The bodies are all
    the same three lines; the file is generated.

    Four suites are shipped, covering the four distinctions that actually
    change the code -- the KEM curve, the KDF hash, and the AEAD:

    - [x25519_sha256_chachapoly]  DHKEM(X25519), HKDF-SHA-256, ChaCha20-Poly1305
    - [x25519_sha512_chachapoly]  DHKEM(X25519), HKDF-SHA-512, ChaCha20-Poly1305
    - [p256_sha256_chachapoly]    DHKEM(P-256),  HKDF-SHA-256, ChaCha20-Poly1305
    - [x25519_sha256_aes128gcm]   DHKEM(X25519), HKDF-SHA-256, AES-128-GCM

    Only the Base mode is exposed here; {!Hacl.HPKE} has all four modes for
    an F* caller. *)
module Hacl.HPKE.Suites

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HPKE
open Hacl.Hash.SHA2.Tables
open Hacl.Impl.Table
open Hacl.HPKE

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module D = Hacl.Hash.SHA2.Dispatch

(** The three KDFs RFC 9180 registers, at the refined type
    {!Spec.HPKE.ciphersuite} wants.  The refinement is what makes
    [kdf_id] total, and it is not syntactically apparent from
    [Spec.SHA2.Constants]: [hash_bytes] projects a [size_t] field. *)

inline_for_extraction
let sha256 : (p: params S32.t { hash_bytes p == 32 }) =
  assert_norm (hash_bytes sha2_256 == 32); sha2_256

inline_for_extraction
let sha512 : (p: params S64.t { hash_bytes p == 64 }) =
  assert_norm (hash_bytes sha2_512 == 64); sha2_512

(** DHKEM(X25519, HKDF-SHA-256), HKDF-SHA-256, ChaCha20-Poly1305. *)
inline_for_extraction
let x25519_sha256_chachapoly : (c: ciphersuite S32.t { ~(ExportOnly? c.aead) /\ size_kdf c == 32 }) =
  { kem = DH_X25519; kdf = sha256; aead = Seal_Chacha20Poly1305 }

(** DHKEM(X25519, HKDF-SHA-256), HKDF-SHA-512, ChaCha20-Poly1305. *)
inline_for_extraction
let x25519_sha512_chachapoly : (c: ciphersuite S64.t { ~(ExportOnly? c.aead) /\ size_kdf c == 64 }) =
  { kem = DH_X25519; kdf = sha512; aead = Seal_Chacha20Poly1305 }

(** DHKEM(P-256, HKDF-SHA-256), HKDF-SHA-256, ChaCha20-Poly1305.  Public keys are 65-byte SEC1 uncompressed points. *)
inline_for_extraction
let p256_sha256_chachapoly : (c: ciphersuite S32.t { ~(ExportOnly? c.aead) /\ size_kdf c == 32 }) =
  { kem = DH_P256; kdf = sha256; aead = Seal_Chacha20Poly1305 }

(** DHKEM(X25519, HKDF-SHA-256), HKDF-SHA-256, AES-128-GCM. *)
inline_for_extraction
let x25519_sha256_aes128gcm : (c: ciphersuite S32.t { ~(ExportOnly? c.aead) /\ size_kdf c == 32 }) =
  { kem = DH_X25519; kdf = sha256; aead = Seal_AES128_GCM }

(** What the run-time choice of block function asks of each suite's KDF. *)
let suite_facts (_: unit)
  : Lemma (Spec.SHANI.is_sha256 x25519_sha256_chachapoly.kdf /\
           Spec.SHANI.is_sha256 p256_sha256_chachapoly.kdf /\
           Spec.SHANI.is_sha256 x25519_sha256_aes128gcm.kdf /\
           Hacl.Hash.SHA2.AVX2.is_sha512 x25519_sha512_chachapoly.kdf)
  = Hacl.Hash.SHA2.sha2_256_facts ();
    Hacl.Hash.SHA2.sha2_512_facts ()

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** {2 x25519_sha256_chachapoly} *)

(** [SetupBaseS] for x25519_sha256_chachapoly: generate an encapsulation for [pkR] with the
    ephemeral private key [skE] and fill in the sender's context.

    [enc] is {!size_dh_public} bytes, [key] {!size_key}, [base_nonce] 12,
    [exporter] {!size_kdf}, and [sq] one 64-bit word, set to zero.  Returns
    [false], leaving the context arbitrary, when [skE] or [pkR] is not a
    valid key. *)
fn x25519_sha256_chachapoly_setup_base_s
    (enc: A.array S8.t)
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to enc venc **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public x25519_sha256_chachapoly.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public x25519_sha256_chachapoly.kem /\
               Seq.length vkey == size_key x25519_sha256_chachapoly /\
               Seq.length vbn == size_nonce x25519_sha256_chachapoly /\
               Seq.length vexp == size_kdf x25519_sha256_chachapoly /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wenc wkey wbn wsq wexp.
  A.pts_to enc wenc **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public x25519_sha256_chachapoly.kem /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length wenc == size_dh_public x25519_sha256_chachapoly.kem /\
        Seq.length wkey == size_key x25519_sha256_chachapoly /\
        Seq.length wbn == size_nonce x25519_sha256_chachapoly /\
        Seq.length wexp == size_kdf x25519_sha256_chachapoly /\ Seq.length wsq == 1 /\
        r == Some? (setup_s x25519_sha256_chachapoly Base vskE None vpkR vinfo Seq.empty Seq.empty) /\
        (r ==> (let (e1, c1) =
                  Some?.v (setup_s x25519_sha256_chachapoly Base vskE None vpkR vinfo Seq.empty Seq.empty) in
                wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = setup_base_s x25519_sha256_chachapoly (D.blocks_dispatch32 x25519_sha256_chachapoly.kdf) kt ivt enc key base_nonce sq exporter
                        skE pkR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** [SetupBaseR] for x25519_sha256_chachapoly: recover the receiver's context from the
    encapsulation [enc] and the private key [skR].  Returns [false] when
    [enc] or [skR] is not a valid key. *)
fn x25519_sha256_chachapoly_setup_base_r
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public x25519_sha256_chachapoly.kem /\
               Seq.length vskR == 32 /\
               Seq.length vkey == size_key x25519_sha256_chachapoly /\
               Seq.length vbn == size_nonce x25519_sha256_chachapoly /\
               Seq.length vexp == size_kdf x25519_sha256_chachapoly /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wkey wbn wsq wexp.
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo **
  pure (Seq.length venc == size_dh_public x25519_sha256_chachapoly.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length wkey == size_key x25519_sha256_chachapoly /\
        Seq.length wbn == size_nonce x25519_sha256_chachapoly /\
        Seq.length wexp == size_kdf x25519_sha256_chachapoly /\ Seq.length wsq == 1 /\
        r == Some? (setup_r x25519_sha256_chachapoly Base venc vskR None vinfo Seq.empty Seq.empty) /\
        (r ==> (let c1 =
                  Some?.v (setup_r x25519_sha256_chachapoly Base venc vskR None vinfo Seq.empty Seq.empty) in
                wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = setup_base_r x25519_sha256_chachapoly (D.blocks_dispatch32 x25519_sha256_chachapoly.kdf) kt ivt key base_nonce sq exporter
                        enc skR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Seal] for x25519_sha256_chachapoly: encapsulate to [pkR] with the ephemeral
    private key [skE] and seal one message at sequence number zero.

    Unlike HACL*, the ciphertext and the tag are separate buffers: [ct] has
    the length of [pt], and [tag] is {!size_tag} bytes. *)
fn x25519_sha256_chachapoly_seal
    (enc: A.array S8.t) (ct: A.array S8.t) (tag: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (pt: A.array S8.t) (pt_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pp: perm) (#vpt: erased (Seq.seq S8.t))
requires A.pts_to enc venc ** A.pts_to ct vct ** A.pts_to tag vtag **
         A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
         pure (Seq.length venc == size_dh_public x25519_sha256_chachapoly.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public x25519_sha256_chachapoly.kem /\
               Seq.length vct == Seq.length vpt /\
               Seq.length vtag == size_tag x25519_sha256_chachapoly /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vpt < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vpt + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v pt_len == Seq.length vpt)
returns r: bool
ensures exists* wenc wct wtag.
  A.pts_to enc wenc ** A.pts_to ct wct ** A.pts_to tag wtag **
  A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public x25519_sha256_chachapoly.kem /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
        Seq.length wenc == size_dh_public x25519_sha256_chachapoly.kem /\
        Seq.length wct == Seq.length vpt /\
        Seq.length wtag == size_tag x25519_sha256_chachapoly /\
        r == Some? (seal_base x25519_sha256_chachapoly vskE vpkR vinfo vaad vpt) /\
        (r ==> (let (e1, c1, t1) = Some?.v (seal_base x25519_sha256_chachapoly vskE vpkR vinfo vaad vpt) in
                wenc == e1 /\ wct == c1 /\ wtag == t1)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = seal_base x25519_sha256_chachapoly (D.blocks_dispatch32 x25519_sha256_chachapoly.kdf) kt ivt enc ct tag skE pkR
                    info info_len aad aad_len pt pt_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Open] for x25519_sha256_chachapoly: the inverse of {!x25519_sha256_chachapoly_seal}.
    Returns [false] -- and leaves [pt] arbitrary -- when the keys are
    invalid or the tag does not check. *)
fn x25519_sha256_chachapoly_open
    (pt: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (ct: A.array S8.t) (ct_len: SZ.t) (tag: A.array S8.t)
    (#vpt: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pc: perm) (#vct: erased (Seq.seq S8.t))
    (#pg: perm) (#vtag: erased (Seq.seq S8.t))
requires A.pts_to pt vpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
         A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
         pure (Seq.length venc == size_dh_public x25519_sha256_chachapoly.kem /\
               Seq.length vskR == 32 /\
               Seq.length vpt == Seq.length vct /\
               Seq.length vtag == size_tag x25519_sha256_chachapoly /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vct < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v ct_len == Seq.length vct)
returns r: bool
ensures exists* wpt.
  A.pts_to pt wpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
  A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
  pure (Seq.length venc == size_dh_public x25519_sha256_chachapoly.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
        Seq.length vtag == size_tag x25519_sha256_chachapoly /\ Seq.length wpt == Seq.length vct /\
        (r <==> open_base_ok x25519_sha256_chachapoly venc vskR vinfo vaad vct vtag) /\
        (r ==> Some? (open_base x25519_sha256_chachapoly venc vskR vinfo vct) /\
               wpt == Some?.v (open_base x25519_sha256_chachapoly venc vskR vinfo vct)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = open_base x25519_sha256_chachapoly (D.blocks_dispatch32 x25519_sha256_chachapoly.kdf) kt ivt pt enc skR
                    info info_len aad aad_len ct ct_len tag;
  drop_table ivt;
  drop_table kt;
  r
}

(** {2 x25519_sha512_chachapoly} *)

(** [SetupBaseS] for x25519_sha512_chachapoly: generate an encapsulation for [pkR] with the
    ephemeral private key [skE] and fill in the sender's context.

    [enc] is {!size_dh_public} bytes, [key] {!size_key}, [base_nonce] 12,
    [exporter] {!size_kdf}, and [sq] one 64-bit word, set to zero.  Returns
    [false], leaving the context arbitrary, when [skE] or [pkR] is not a
    valid key. *)
fn x25519_sha512_chachapoly_setup_base_s
    (enc: A.array S8.t)
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to enc venc **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public x25519_sha512_chachapoly.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public x25519_sha512_chachapoly.kem /\
               Seq.length vkey == size_key x25519_sha512_chachapoly /\
               Seq.length vbn == size_nonce x25519_sha512_chachapoly /\
               Seq.length vexp == size_kdf x25519_sha512_chachapoly /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wenc wkey wbn wsq wexp.
  A.pts_to enc wenc **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public x25519_sha512_chachapoly.kem /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha512_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length wenc == size_dh_public x25519_sha512_chachapoly.kem /\
        Seq.length wkey == size_key x25519_sha512_chachapoly /\
        Seq.length wbn == size_nonce x25519_sha512_chachapoly /\
        Seq.length wexp == size_kdf x25519_sha512_chachapoly /\ Seq.length wsq == 1 /\
        r == Some? (setup_s x25519_sha512_chachapoly Base vskE None vpkR vinfo Seq.empty Seq.empty) /\
        (r ==> (let (e1, c1) =
                  Some?.v (setup_s x25519_sha512_chachapoly Base vskE None vpkR vinfo Seq.empty Seq.empty) in
                wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 577;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  suite_facts ();
  let r = setup_base_s x25519_sha512_chachapoly (D.blocks_dispatch64 x25519_sha512_chachapoly.kdf) kt ivt enc key base_nonce sq exporter
                        skE pkR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** [SetupBaseR] for x25519_sha512_chachapoly: recover the receiver's context from the
    encapsulation [enc] and the private key [skR].  Returns [false] when
    [enc] or [skR] is not a valid key. *)
fn x25519_sha512_chachapoly_setup_base_r
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public x25519_sha512_chachapoly.kem /\
               Seq.length vskR == 32 /\
               Seq.length vkey == size_key x25519_sha512_chachapoly /\
               Seq.length vbn == size_nonce x25519_sha512_chachapoly /\
               Seq.length vexp == size_kdf x25519_sha512_chachapoly /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wkey wbn wsq wexp.
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo **
  pure (Seq.length venc == size_dh_public x25519_sha512_chachapoly.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha512_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length wkey == size_key x25519_sha512_chachapoly /\
        Seq.length wbn == size_nonce x25519_sha512_chachapoly /\
        Seq.length wexp == size_kdf x25519_sha512_chachapoly /\ Seq.length wsq == 1 /\
        r == Some? (setup_r x25519_sha512_chachapoly Base venc vskR None vinfo Seq.empty Seq.empty) /\
        (r ==> (let c1 =
                  Some?.v (setup_r x25519_sha512_chachapoly Base venc vskR None vinfo Seq.empty Seq.empty) in
                wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 577;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  suite_facts ();
  let r = setup_base_r x25519_sha512_chachapoly (D.blocks_dispatch64 x25519_sha512_chachapoly.kdf) kt ivt key base_nonce sq exporter
                        enc skR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Seal] for x25519_sha512_chachapoly: encapsulate to [pkR] with the ephemeral
    private key [skE] and seal one message at sequence number zero.

    Unlike HACL*, the ciphertext and the tag are separate buffers: [ct] has
    the length of [pt], and [tag] is {!size_tag} bytes. *)
fn x25519_sha512_chachapoly_seal
    (enc: A.array S8.t) (ct: A.array S8.t) (tag: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (pt: A.array S8.t) (pt_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pp: perm) (#vpt: erased (Seq.seq S8.t))
requires A.pts_to enc venc ** A.pts_to ct vct ** A.pts_to tag vtag **
         A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
         pure (Seq.length venc == size_dh_public x25519_sha512_chachapoly.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public x25519_sha512_chachapoly.kem /\
               Seq.length vct == Seq.length vpt /\
               Seq.length vtag == size_tag x25519_sha512_chachapoly /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vpt < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vpt + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v pt_len == Seq.length vpt)
returns r: bool
ensures exists* wenc wct wtag.
  A.pts_to enc wenc ** A.pts_to ct wct ** A.pts_to tag wtag **
  A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public x25519_sha512_chachapoly.kem /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha512_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
        Seq.length wenc == size_dh_public x25519_sha512_chachapoly.kem /\
        Seq.length wct == Seq.length vpt /\
        Seq.length wtag == size_tag x25519_sha512_chachapoly /\
        r == Some? (seal_base x25519_sha512_chachapoly vskE vpkR vinfo vaad vpt) /\
        (r ==> (let (e1, c1, t1) = Some?.v (seal_base x25519_sha512_chachapoly vskE vpkR vinfo vaad vpt) in
                wenc == e1 /\ wct == c1 /\ wtag == t1)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 577;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  suite_facts ();
  let r = seal_base x25519_sha512_chachapoly (D.blocks_dispatch64 x25519_sha512_chachapoly.kdf) kt ivt enc ct tag skE pkR
                    info info_len aad aad_len pt pt_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Open] for x25519_sha512_chachapoly: the inverse of {!x25519_sha512_chachapoly_seal}.
    Returns [false] -- and leaves [pt] arbitrary -- when the keys are
    invalid or the tag does not check. *)
fn x25519_sha512_chachapoly_open
    (pt: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (ct: A.array S8.t) (ct_len: SZ.t) (tag: A.array S8.t)
    (#vpt: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pc: perm) (#vct: erased (Seq.seq S8.t))
    (#pg: perm) (#vtag: erased (Seq.seq S8.t))
requires A.pts_to pt vpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
         A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
         pure (Seq.length venc == size_dh_public x25519_sha512_chachapoly.kem /\
               Seq.length vskR == 32 /\
               Seq.length vpt == Seq.length vct /\
               Seq.length vtag == size_tag x25519_sha512_chachapoly /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vct < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v ct_len == Seq.length vct)
returns r: bool
ensures exists* wpt.
  A.pts_to pt wpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
  A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
  pure (Seq.length venc == size_dh_public x25519_sha512_chachapoly.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha512_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
        Seq.length vtag == size_tag x25519_sha512_chachapoly /\ Seq.length wpt == Seq.length vct /\
        (r <==> open_base_ok x25519_sha512_chachapoly venc vskR vinfo vaad vct vtag) /\
        (r ==> Some? (open_base x25519_sha512_chachapoly venc vskR vinfo vct) /\
               wpt == Some?.v (open_base x25519_sha512_chachapoly venc vskR vinfo vct)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 577;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  suite_facts ();
  let r = open_base x25519_sha512_chachapoly (D.blocks_dispatch64 x25519_sha512_chachapoly.kdf) kt ivt pt enc skR
                    info info_len aad aad_len ct ct_len tag;
  drop_table ivt;
  drop_table kt;
  r
}

(** {2 p256_sha256_chachapoly} *)

(** [SetupBaseS] for p256_sha256_chachapoly: generate an encapsulation for [pkR] with the
    ephemeral private key [skE] and fill in the sender's context.

    [enc] is {!size_dh_public} bytes, [key] {!size_key}, [base_nonce] 12,
    [exporter] {!size_kdf}, and [sq] one 64-bit word, set to zero.  Returns
    [false], leaving the context arbitrary, when [skE] or [pkR] is not a
    valid key. *)
fn p256_sha256_chachapoly_setup_base_s
    (enc: A.array S8.t)
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to enc venc **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public p256_sha256_chachapoly.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public p256_sha256_chachapoly.kem /\
               Seq.length vkey == size_key p256_sha256_chachapoly /\
               Seq.length vbn == size_nonce p256_sha256_chachapoly /\
               Seq.length vexp == size_kdf p256_sha256_chachapoly /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wenc wkey wbn wsq wexp.
  A.pts_to enc wenc **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public p256_sha256_chachapoly.kem /\
        Seq.length vinfo < pow2 32 /\ fits p256_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length wenc == size_dh_public p256_sha256_chachapoly.kem /\
        Seq.length wkey == size_key p256_sha256_chachapoly /\
        Seq.length wbn == size_nonce p256_sha256_chachapoly /\
        Seq.length wexp == size_kdf p256_sha256_chachapoly /\ Seq.length wsq == 1 /\
        r == Some? (setup_s p256_sha256_chachapoly Base vskE None vpkR vinfo Seq.empty Seq.empty) /\
        (r ==> (let (e1, c1) =
                  Some?.v (setup_s p256_sha256_chachapoly Base vskE None vpkR vinfo Seq.empty Seq.empty) in
                wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = setup_base_s p256_sha256_chachapoly (D.blocks_dispatch32 p256_sha256_chachapoly.kdf) kt ivt enc key base_nonce sq exporter
                        skE pkR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** [SetupBaseR] for p256_sha256_chachapoly: recover the receiver's context from the
    encapsulation [enc] and the private key [skR].  Returns [false] when
    [enc] or [skR] is not a valid key. *)
fn p256_sha256_chachapoly_setup_base_r
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public p256_sha256_chachapoly.kem /\
               Seq.length vskR == 32 /\
               Seq.length vkey == size_key p256_sha256_chachapoly /\
               Seq.length vbn == size_nonce p256_sha256_chachapoly /\
               Seq.length vexp == size_kdf p256_sha256_chachapoly /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wkey wbn wsq wexp.
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo **
  pure (Seq.length venc == size_dh_public p256_sha256_chachapoly.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits p256_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length wkey == size_key p256_sha256_chachapoly /\
        Seq.length wbn == size_nonce p256_sha256_chachapoly /\
        Seq.length wexp == size_kdf p256_sha256_chachapoly /\ Seq.length wsq == 1 /\
        r == Some? (setup_r p256_sha256_chachapoly Base venc vskR None vinfo Seq.empty Seq.empty) /\
        (r ==> (let c1 =
                  Some?.v (setup_r p256_sha256_chachapoly Base venc vskR None vinfo Seq.empty Seq.empty) in
                wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = setup_base_r p256_sha256_chachapoly (D.blocks_dispatch32 p256_sha256_chachapoly.kdf) kt ivt key base_nonce sq exporter
                        enc skR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Seal] for p256_sha256_chachapoly: encapsulate to [pkR] with the ephemeral
    private key [skE] and seal one message at sequence number zero.

    Unlike HACL*, the ciphertext and the tag are separate buffers: [ct] has
    the length of [pt], and [tag] is {!size_tag} bytes. *)
fn p256_sha256_chachapoly_seal
    (enc: A.array S8.t) (ct: A.array S8.t) (tag: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (pt: A.array S8.t) (pt_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pp: perm) (#vpt: erased (Seq.seq S8.t))
requires A.pts_to enc venc ** A.pts_to ct vct ** A.pts_to tag vtag **
         A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
         pure (Seq.length venc == size_dh_public p256_sha256_chachapoly.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public p256_sha256_chachapoly.kem /\
               Seq.length vct == Seq.length vpt /\
               Seq.length vtag == size_tag p256_sha256_chachapoly /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vpt < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vpt + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v pt_len == Seq.length vpt)
returns r: bool
ensures exists* wenc wct wtag.
  A.pts_to enc wenc ** A.pts_to ct wct ** A.pts_to tag wtag **
  A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public p256_sha256_chachapoly.kem /\
        Seq.length vinfo < pow2 32 /\ fits p256_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
        Seq.length wenc == size_dh_public p256_sha256_chachapoly.kem /\
        Seq.length wct == Seq.length vpt /\
        Seq.length wtag == size_tag p256_sha256_chachapoly /\
        r == Some? (seal_base p256_sha256_chachapoly vskE vpkR vinfo vaad vpt) /\
        (r ==> (let (e1, c1, t1) = Some?.v (seal_base p256_sha256_chachapoly vskE vpkR vinfo vaad vpt) in
                wenc == e1 /\ wct == c1 /\ wtag == t1)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = seal_base p256_sha256_chachapoly (D.blocks_dispatch32 p256_sha256_chachapoly.kdf) kt ivt enc ct tag skE pkR
                    info info_len aad aad_len pt pt_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Open] for p256_sha256_chachapoly: the inverse of {!p256_sha256_chachapoly_seal}.
    Returns [false] -- and leaves [pt] arbitrary -- when the keys are
    invalid or the tag does not check. *)
fn p256_sha256_chachapoly_open
    (pt: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (ct: A.array S8.t) (ct_len: SZ.t) (tag: A.array S8.t)
    (#vpt: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pc: perm) (#vct: erased (Seq.seq S8.t))
    (#pg: perm) (#vtag: erased (Seq.seq S8.t))
requires A.pts_to pt vpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
         A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
         pure (Seq.length venc == size_dh_public p256_sha256_chachapoly.kem /\
               Seq.length vskR == 32 /\
               Seq.length vpt == Seq.length vct /\
               Seq.length vtag == size_tag p256_sha256_chachapoly /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vct < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v ct_len == Seq.length vct)
returns r: bool
ensures exists* wpt.
  A.pts_to pt wpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
  A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
  pure (Seq.length venc == size_dh_public p256_sha256_chachapoly.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits p256_sha256_chachapoly.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
        Seq.length vtag == size_tag p256_sha256_chachapoly /\ Seq.length wpt == Seq.length vct /\
        (r <==> open_base_ok p256_sha256_chachapoly venc vskR vinfo vaad vct vtag) /\
        (r ==> Some? (open_base p256_sha256_chachapoly venc vskR vinfo vct) /\
               wpt == Some?.v (open_base p256_sha256_chachapoly venc vskR vinfo vct)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = open_base p256_sha256_chachapoly (D.blocks_dispatch32 p256_sha256_chachapoly.kdf) kt ivt pt enc skR
                    info info_len aad aad_len ct ct_len tag;
  drop_table ivt;
  drop_table kt;
  r
}

(** {2 x25519_sha256_aes128gcm} *)

(** [SetupBaseS] for x25519_sha256_aes128gcm: generate an encapsulation for [pkR] with the
    ephemeral private key [skE] and fill in the sender's context.

    [enc] is {!size_dh_public} bytes, [key] {!size_key}, [base_nonce] 12,
    [exporter] {!size_kdf}, and [sq] one 64-bit word, set to zero.  Returns
    [false], leaving the context arbitrary, when [skE] or [pkR] is not a
    valid key. *)
fn x25519_sha256_aes128gcm_setup_base_s
    (enc: A.array S8.t)
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to enc venc **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public x25519_sha256_aes128gcm.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public x25519_sha256_aes128gcm.kem /\
               Seq.length vkey == size_key x25519_sha256_aes128gcm /\
               Seq.length vbn == size_nonce x25519_sha256_aes128gcm /\
               Seq.length vexp == size_kdf x25519_sha256_aes128gcm /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wenc wkey wbn wsq wexp.
  A.pts_to enc wenc **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public x25519_sha256_aes128gcm.kem /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_aes128gcm.kdf (Seq.length vinfo) /\
        Seq.length wenc == size_dh_public x25519_sha256_aes128gcm.kem /\
        Seq.length wkey == size_key x25519_sha256_aes128gcm /\
        Seq.length wbn == size_nonce x25519_sha256_aes128gcm /\
        Seq.length wexp == size_kdf x25519_sha256_aes128gcm /\ Seq.length wsq == 1 /\
        r == Some? (setup_s x25519_sha256_aes128gcm Base vskE None vpkR vinfo Seq.empty Seq.empty) /\
        (r ==> (let (e1, c1) =
                  Some?.v (setup_s x25519_sha256_aes128gcm Base vskE None vpkR vinfo Seq.empty Seq.empty) in
                wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = setup_base_s x25519_sha256_aes128gcm (D.blocks_dispatch32 x25519_sha256_aes128gcm.kdf) kt ivt enc key base_nonce sq exporter
                        skE pkR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** [SetupBaseR] for x25519_sha256_aes128gcm: recover the receiver's context from the
    encapsulation [enc] and the private key [skR].  Returns [false] when
    [enc] or [skR] is not a valid key. *)
fn x25519_sha256_aes128gcm_setup_base_r
    (key: A.array S8.t) (base_nonce: A.array S8.t)
    (sq: A.array U64.t) (exporter: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
    (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo **
         pure (Seq.length venc == size_dh_public x25519_sha256_aes128gcm.kem /\
               Seq.length vskR == 32 /\
               Seq.length vkey == size_key x25519_sha256_aes128gcm /\
               Seq.length vbn == size_nonce x25519_sha256_aes128gcm /\
               Seq.length vexp == size_kdf x25519_sha256_aes128gcm /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wkey wbn wsq wexp.
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo **
  pure (Seq.length venc == size_dh_public x25519_sha256_aes128gcm.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_aes128gcm.kdf (Seq.length vinfo) /\
        Seq.length wkey == size_key x25519_sha256_aes128gcm /\
        Seq.length wbn == size_nonce x25519_sha256_aes128gcm /\
        Seq.length wexp == size_kdf x25519_sha256_aes128gcm /\ Seq.length wsq == 1 /\
        r == Some? (setup_r x25519_sha256_aes128gcm Base venc vskR None vinfo Seq.empty Seq.empty) /\
        (r ==> (let c1 =
                  Some?.v (setup_r x25519_sha256_aes128gcm Base venc vskR None vinfo Seq.empty Seq.empty) in
                wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = setup_base_r x25519_sha256_aes128gcm (D.blocks_dispatch32 x25519_sha256_aes128gcm.kdf) kt ivt key base_nonce sq exporter
                        enc skR info info_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Seal] for x25519_sha256_aes128gcm: encapsulate to [pkR] with the ephemeral
    private key [skE] and seal one message at sequence number zero.

    Unlike HACL*, the ciphertext and the tag are separate buffers: [ct] has
    the length of [pt], and [tag] is {!size_tag} bytes. *)
fn x25519_sha256_aes128gcm_seal
    (enc: A.array S8.t) (ct: A.array S8.t) (tag: A.array S8.t)
    (skE: A.array S8.t) (pkR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (pt: A.array S8.t) (pt_len: SZ.t)
    (#venc: erased (Seq.seq S8.t))
    (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
    (#pe: perm) (#vskE: erased (Seq.seq S8.t))
    (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pp: perm) (#vpt: erased (Seq.seq S8.t))
requires A.pts_to enc venc ** A.pts_to ct vct ** A.pts_to tag vtag **
         A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
         pure (Seq.length venc == size_dh_public x25519_sha256_aes128gcm.kem /\
               Seq.length vskE == 32 /\
               Seq.length vpkR == size_dh_public x25519_sha256_aes128gcm.kem /\
               Seq.length vct == Seq.length vpt /\
               Seq.length vtag == size_tag x25519_sha256_aes128gcm /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vpt < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vpt + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v pt_len == Seq.length vpt)
returns r: bool
ensures exists* wenc wct wtag.
  A.pts_to enc wenc ** A.pts_to ct wct ** A.pts_to tag wtag **
  A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
  pure (Seq.length vskE == 32 /\
        Seq.length vpkR == size_dh_public x25519_sha256_aes128gcm.kem /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_aes128gcm.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
        Seq.length wenc == size_dh_public x25519_sha256_aes128gcm.kem /\
        Seq.length wct == Seq.length vpt /\
        Seq.length wtag == size_tag x25519_sha256_aes128gcm /\
        r == Some? (seal_base x25519_sha256_aes128gcm vskE vpkR vinfo vaad vpt) /\
        (r ==> (let (e1, c1, t1) = Some?.v (seal_base x25519_sha256_aes128gcm vskE vpkR vinfo vaad vpt) in
                wenc == e1 /\ wct == c1 /\ wtag == t1)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = seal_base x25519_sha256_aes128gcm (D.blocks_dispatch32 x25519_sha256_aes128gcm.kdf) kt ivt enc ct tag skE pkR
                    info info_len aad aad_len pt pt_len;
  drop_table ivt;
  drop_table kt;
  r
}

(** Single-shot [Open] for x25519_sha256_aes128gcm: the inverse of {!x25519_sha256_aes128gcm_seal}.
    Returns [false] -- and leaves [pt] arbitrary -- when the keys are
    invalid or the tag does not check. *)
fn x25519_sha256_aes128gcm_open
    (pt: A.array S8.t)
    (enc: A.array S8.t) (skR: A.array S8.t)
    (info: A.array S8.t) (info_len: SZ.t)
    (aad: A.array S8.t) (aad_len: SZ.t)
    (ct: A.array S8.t) (ct_len: SZ.t) (tag: A.array S8.t)
    (#vpt: erased (Seq.seq S8.t))
    (#pn: perm) (#venc: erased (Seq.seq S8.t))
    (#pr: perm) (#vskR: erased (Seq.seq S8.t))
    (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
    (#pa: perm) (#vaad: erased (Seq.seq S8.t))
    (#pc: perm) (#vct: erased (Seq.seq S8.t))
    (#pg: perm) (#vtag: erased (Seq.seq S8.t))
requires A.pts_to pt vpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
         A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
         pure (Seq.length venc == size_dh_public x25519_sha256_aes128gcm.kem /\
               Seq.length vskR == 32 /\
               Seq.length vpt == Seq.length vct /\
               Seq.length vtag == size_tag x25519_sha256_aes128gcm /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vct < pow2 32 /\
               SZ.fits (448 + Seq.length vinfo) /\
               SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v ct_len == Seq.length vct)
returns r: bool
ensures exists* wpt.
  A.pts_to pt wpt ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
  A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
  pure (Seq.length venc == size_dh_public x25519_sha256_aes128gcm.kem /\
        Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits x25519_sha256_aes128gcm.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
        Seq.length vtag == size_tag x25519_sha256_aes128gcm /\ Seq.length wpt == Seq.length vct /\
        (r <==> open_base_ok x25519_sha256_aes128gcm venc vskR vinfo vaad vct vtag) /\
        (r ==> Some? (open_base x25519_sha256_aes128gcm venc vskR vinfo vct) /\
               wpt == Some?.v (open_base x25519_sha256_aes128gcm venc vskR vinfo vct)))
{
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits 513;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  suite_facts ();
  let r = open_base x25519_sha256_aes128gcm (D.blocks_dispatch32 x25519_sha256_aes128gcm.kdf) kt ivt pt enc skR
                    info info_len aad aad_len ct ct_len tag;
  drop_table ivt;
  drop_table kt;
  r
}

#pop-options
