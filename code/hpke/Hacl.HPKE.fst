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

(** Hybrid Public Key Encryption, RFC 9180.

    The key schedule, the encryption context and the four setup functions.
    Everything here is generic in the ciphersuite: one record parameter
    carries the KEM, the KDF and the AEAD, and a caller who instantiates it
    at a constant gets, after monomorphisation, exactly the specialised code
    HACL* generates fifteen modules to produce.

    The encryption context is not a type here but four buffers -- key, base
    nonce, sequence number, exporter secret -- which is what HACL*'s
    [Hacl_Impl_HPKE_context_s] is, laid out by the caller rather than by the
    library.  The sequence number is a one-element [uint64_t] array so that
    sealing can advance it in place.

    Export-only ciphersuites are specified in [Spec.HPKE] but not implemented
    here: they would need a key schedule that expands zero-length keys and
    nonces, and a zero-length buffer is not something a C caller can hand
    over. *)
module Hacl.HPKE

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HPKE
open Hacl.Secret.Word.Instances
open Hacl.Impl.Bytes
open Hacl.HPKE.Tables
open Hacl.HPKE.Labeled
open Hacl.HPKE.KEM
open Hacl.HPKE.AEAD
open Hacl.Impl.Copy
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module B = Hacl.Spec.Bytes
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub

(** {2 Sizes and small constants} *)

let mode_byte ([@@@FStar.Attributes.monomorphize] m: mode)
  : b: U8.t { U8.v b == mode_id m }
  = match m with Base -> 0uy | PSK -> 1uy | Auth -> 2uy | AuthPSK -> 3uy

let kdf_len (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t)
  : n: SZ.t { SZ.v n == size_kdf cs }
  = cs.kdf.nhash_bytes

(** {2 The suite identifier}

    ['HPKE'] and the three algorithm identifiers, ten bytes, in front of
    every label the key schedule extracts or expands under. *)

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

fn suite_id_impl (#t: Type0) {| w: word t |}
                 ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t)
                 (out: A.array S8.t)
                 (#vout: erased (Seq.seq S8.t))
requires A.pts_to out vout ** pure (Seq.length vout == 10)
ensures exists* vout'. A.pts_to out vout' **
  pure (Seq.length vout' == 10 /\ vout' == suite_id cs)
{
  A.pts_to_len out;
  let hp = table hpke_prefix_arr 4sz;
  A.pts_to_len hp;
  copy_at out 0sz hp 4sz;

  A.((out.(4sz) <- S8.zero));
  let k1 = if (DH_P256? cs.kem) { S8.classify 0x10uy } else { S8.classify 0x20uy };
  A.((out.(5sz) <- k1));

  A.((out.(6sz) <- S8.zero));
  let d1 = if (cs.kdf.nhash_bytes = 32sz) { S8.classify 0x01uy }
           else { if (cs.kdf.nhash_bytes = 48sz) { S8.classify 0x02uy }
                  else { S8.classify 0x03uy } };
  A.((out.(7sz) <- d1));

  let a0 = if (ExportOnly? cs.aead) { S8.classify 0xffuy } else { S8.zero };
  A.((out.(8sz) <- a0));
  let a1 = if (Seal_AES128_GCM? cs.aead) { S8.classify 0x01uy }
           else { if (Seal_AES256_GCM? cs.aead) { S8.classify 0x02uy }
                  else { if (Seal_Chacha20Poly1305? cs.aead) { S8.classify 0x03uy }
                         else { S8.classify 0xffuy } } };
  A.((out.(9sz) <- a1));

  with wo. assert (A.pts_to out wo);
  A.pts_to_len out;
  assert_norm (pow2 8 == 256);
  B.nat_to_be_index 2 (kem_id cs.kem) 0;
  B.nat_to_be_index 2 (kem_id cs.kem) 1;
  B.nat_to_be_index 2 (kdf_id cs) 0;
  B.nat_to_be_index 2 (kdf_id cs) 1;
  B.nat_to_be_index 2 (aead_id cs.aead) 0;
  B.nat_to_be_index 2 (aead_id cs.aead) 1;
  assert (pure (Seq.index wo 4 == Seq.index (two_bytes (kem_id cs.kem)) 0));
  assert (pure (Seq.index wo 5 == Seq.index (two_bytes (kem_id cs.kem)) 1));
  assert (pure (Seq.index wo 6 == Seq.index (two_bytes (kdf_id cs)) 0));
  assert (pure (Seq.index wo 7 == Seq.index (two_bytes (kdf_id cs)) 1));
  assert (pure (Seq.index wo 8 == Seq.index (two_bytes (aead_id cs.aead)) 0));
  assert (pure (Seq.index wo 9 == Seq.index (two_bytes (aead_id cs.aead)) 1));
  cat4_pointwise wo hpke_prefix (two_bytes (kem_id cs.kem))
                    (two_bytes (kdf_id cs)) (two_bytes (aead_id cs.aead));
  drop_table hp;
}

#pop-options

(** {2 The key schedule}

    RFC 9180 section 5.1.  Two extractions over the mode's pre-shared key and
    [info], a third over the shared secret, then three expansions.  The key
    schedule context is one mode byte and two digests. *)

(** Everything the key schedule needs of a caller's string, from one bound.
    [labeled_extract_impl] allocates a block-sized pad, so the [SZ.fits]
    obligation has to budget for it. *)
let ks_bound (#t: Type0) {| word t |} (p: params t) (n: nat)
  : Lemma (requires n < pow2 32 /\ SZ.fits (256 + 128 + 64 + n))
          (ensures fits p n /\ hash_bytes p <= 128 /\ block_len #t <= 256 /\
                   SZ.fits (block_len #t + 7 + 10 + 16 + n) /\
                   SZ.fits (block_len #t + hash_bytes p + 9 + 10 + 16 + n + 1))
  = prefix_bound p n;
    SZ.fits_lte (block_len #t + 7 + 10 + 16 + n) (256 + 128 + 64 + n);
    SZ.fits_lte (block_len #t + hash_bytes p + 9 + 10 + 16 + n + 1) (256 + 128 + 64 + n)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

fn key_schedule_impl (#t: Type0) {| w: word t |}
                     ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                        { ~(ExportOnly? cs.aead) })
                     ([@@@FStar.Attributes.monomorphize] m: mode)
                     (kt: A.array t) (ivt: A.array t)
                     (key: A.array S8.t) (base_nonce: A.array S8.t)
                     (exporter: A.array S8.t)
                     (shared: A.array S8.t)
                     (info: A.array S8.t) (info_len: SZ.t)
                     (psk: A.array S8.t) (psk_len: SZ.t)
                     (psk_id: A.array S8.t) (psk_id_len: SZ.t)
                     (#pk: perm) (#vk: erased (Seq.seq t))
                     (#pi: perm) (#vi: erased (Seq.seq t))
                     (#vkey: erased (Seq.seq S8.t))
                     (#vbn: erased (Seq.seq S8.t))
                     (#vexp: erased (Seq.seq S8.t))
                     (#ph: perm) (#vsh: erased (Seq.seq S8.t))
                     (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
                     (#pp: perm) (#vpsk: erased (Seq.seq S8.t))
                     (#pq: perm) (#vpid: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to exporter vexp **
         A.pts_to shared #ph vsh ** A.pts_to info #pf vinfo **
         A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vexp == size_kdf cs /\ Seq.length vsh == 32 /\
               Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
               Seq.length vpid < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpsk) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpid) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v psk_len == Seq.length vpsk)
         ** pure (SZ.v psk_id_len == Seq.length vpid)
ensures exists* wkey wbn wexp.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to exporter wexp **
  A.pts_to shared #ph vsh ** A.pts_to info #pf vinfo **
  A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
  pure (Seq.length vsh == 32 /\ Seq.length vinfo < pow2 32 /\
        Seq.length vpsk < pow2 32 /\ Seq.length vpid < pow2 32 /\
        fits cs.kdf (Seq.length vinfo) /\ fits cs.kdf (Seq.length vpsk) /\
        fits cs.kdf (Seq.length vpid) /\
        Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
        Seq.length wexp == size_kdf cs /\
        (let c = key_schedule cs m vsh vinfo vpsk vpid in
         wkey == c.ckey /\ wbn == c.cbase_nonce /\ wexp == c.cexporter))
{
  A.pts_to_len key;
  A.pts_to_len base_nonce;
  A.pts_to_len exporter;
  A.pts_to_len shared;
  A.pts_to_len info;
  A.pts_to_len psk;
  A.pts_to_len psk_id;
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf (Seq.length vpsk);
  ks_bound cs.kdf (Seq.length vpid);
  ks_fits cs;

  let hb = kdf_len cs;
  let z8 = S8.zero;

  let mut sid = [| z8; 10sz |];
  A.pts_to_len sid;
  suite_id_impl cs sid;

  (* psk_id_hash and info_hash *)
  let mut pskh = [| z8; hb |];
  A.pts_to_len pskh;
  let l1 = table label_psk_id_hash_arr 11sz;
  A.pts_to_len l1;
  labeled_extract_nosalt cs.kdf kt ivt pskh sid 10sz l1 11sz psk_id psk_id_len;
  drop_table l1;
  with vpskh. assert (A.pts_to pskh vpskh);

  let mut infoh = [| z8; hb |];
  A.pts_to_len infoh;
  let l2 = table label_info_hash_arr 9sz;
  A.pts_to_len l2;
  labeled_extract_nosalt cs.kdf kt ivt infoh sid 10sz l2 9sz info info_len;
  drop_table l2;
  with vinfoh. assert (A.pts_to infoh vinfoh);

  (* key_schedule_context = mode || psk_id_hash || info_hash *)
  let ks_len = SZ.add 1sz (SZ.add hb hb);
  let mut ks = [| z8; ks_len |];
  A.pts_to_len ks;
  A.((ks.(0sz) <- S8.classify (mode_byte m)));
  copy_at ks 1sz pskh hb;
  copy_at ks (SZ.add 1sz hb) infoh hb;
  with vks. assert (A.pts_to ks vks);
  A.pts_to_len ks;
  cat3_pointwise vks (Seq.create 1 (S8.classify (mode_byte m))) vpskh vinfoh;
  ks_bound cs.kdf (2 * size_kdf cs + 1);

  (* secret = LabeledExtract(shared_secret, "secret", psk) *)
  let mut secret = [| z8; hb |];
  A.pts_to_len secret;
  let l3 = table label_secret_arr 6sz;
  A.pts_to_len l3;
  labeled_extract_impl cs.kdf kt ivt secret sid 10sz shared 32sz l3 6sz psk psk_len;
  drop_table l3;

  let l4 = table label_key_arr 3sz;
  A.pts_to_len l4;
  labeled_expand_impl cs.kdf kt ivt key (key_len cs.aead) secret hb sid 10sz
                      l4 3sz ks ks_len;
  drop_table l4;

  let l5 = table label_base_nonce_arr 10sz;
  A.pts_to_len l5;
  labeled_expand_impl cs.kdf kt ivt base_nonce 12sz secret hb sid 10sz
                      l5 10sz ks ks_len;
  drop_table l5;

  let l6 = table label_exp_arr 3sz;
  A.pts_to_len l6;
  labeled_expand_impl cs.kdf kt ivt exporter hb secret hb sid 10sz
                      l6 3sz ks ks_len;
  drop_table l6;
}

#pop-options

(** {2 ComputeNonce}

    The base nonce exclusive-ored with the sequence number in big-endian.
    The counter is eight bytes and the nonce twelve, so the leading four
    bytes come through unchanged. *)

(** The [k]th byte of a twelve-byte big-endian counter, from its value. *)
let be_byte (n: nat { n < pow2 64 }) (k: nat { k < 12 }) (b: S8.t)
  : Lemma (requires S8.v b == (if k < 4 then 0 else (n / pow2 (8 * (11 - k))) % 256))
          (ensures b == Seq.index (B.nat_to_be 12 n) k)
  = B.nat_to_be_index 12 n k;
    if k < 4 then begin
      Math.pow2_le_compat (8 * (11 - k)) 64;
      Math.small_division_lemma_1 n (pow2 (8 * (11 - k)))
    end;
    S8.v_extensional b (Seq.index (B.nat_to_be 12 n) k)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --using_facts_from '* -Spec.HPKE'"

(** Four zero bytes followed by a big-endian [uint64] is [nat_to_be 12].

    Stated pointwise on the left because that is what {!Hacl.Impl.Bytes.store_be}
    leaves behind, and as a sequence equality on the right because that is what
    the specification is written with. *)
let nonce_be (n: nat { n < pow2 64 }) (o: Seq.lseq S8.t 12)
  : Lemma (requires
      (forall (k: nat). k < 4 ==> S8.v (Seq.index o k) == 0) /\
      (forall (k: nat). k < 8 ==>
         S8.v (Seq.index o (4 + k)) == (n / pow2 (8 * (8 - 1 - k))) % 256))
    (ensures o == B.nat_to_be 12 n)
  = introduce forall (k: nat { k < 12 }). Seq.index o k == Seq.index (B.nat_to_be 12 n) k
    with (if k < 4 then be_byte n k (Seq.index o k)
          else be_byte n k (Seq.index o k));
    Seq.lemma_eq_intro o (B.nat_to_be 12 n)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --using_facts_from '* -Spec.HPKE +Spec.HPKE.xor_bytes'"

(** The pointwise-to-extensional step of [ComputeNonce].  The loop below
    establishes the twelve equations; this turns them into the sequence
    equality the specification is stated with. *)
let nonce_eq (n: nat { n < pow2 64 }) (bn o: Seq.lseq S8.t 12)
  : Lemma (requires (forall (k: nat). k < 12 ==>
             Seq.index o k ==
               S8.logxor (Seq.index bn k) (Seq.index (B.nat_to_be 12 n) k)))
          (ensures o == xor_bytes bn (B.nat_to_be 12 n))
  = Seq.lemma_eq_intro o (xor_bytes bn (B.nat_to_be 12 n))

#pop-options


#push-options "--z3rlimit 200 --fuel 0 --ifuel 0 --using_facts_from '* -Spec.HPKE +Spec.HPKE.xor_bytes'"

(** [out <- base_nonce xor be96(sq)].

    The counter goes into a twelve-byte scratch buffer first -- four zeroes,
    which the allocation already supplies, and then
    {!Hacl.Impl.Bytes.store_be} -- and a loop exclusive-ors the base nonce
    over it.  Writing the twelve bytes as straight-line code instead leaves
    the solver twelve nested [Seq.upd]s to see through at every index, which
    is quadratic and, at twelve, hopeless: the same function took over a
    quarter of an hour to fail before it was a loop, and takes ten seconds
    now. *)
fn compute_nonce_impl (out: A.array S8.t) (bn: A.array S8.t) (sq: U64.t)
                      (#vout: erased (Seq.seq S8.t))
                      (#pb: perm) (#vbn: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to bn #pb vbn **
         pure (Seq.length vout == 12 /\ Seq.length vbn == 12)
ensures exists* vout'. A.pts_to out vout' ** A.pts_to bn #pb vbn **
  pure (Seq.length vbn == 12 /\ Seq.length vout' == 12 /\
        vout' == xor_bytes #12 vbn (B.nat_to_be 12 (U64.v sq)))
{
  A.pts_to_len out;
  A.pts_to_len bn;
  assert_norm (bytes #S64.t == 8);
  let z8 = S8.zero;
  let mut be = [| z8; 12sz |];
  A.pts_to_len be;
  store_be #S64.t be 4sz (S64.classify sq);
  with w1. assert (A.pts_to be w1);
  A.pts_to_len be;
  nonce_be (U64.v sq) w1;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 12sz)
  invariant exists* (vi: SZ.t) (wo: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out wo ** A.pts_to bn #pb vbn ** A.pts_to be w1 **
    pure (SZ.v vi <= 12 /\ Seq.length wo == 12 /\ Seq.length vbn == 12 /\
          Seq.length w1 == 12 /\
          (forall (k: nat). k < 12 ==>
             Seq.index w1 k == Seq.index (B.nat_to_be 12 (U64.v sq)) k) /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index wo k ==
               S8.logxor (Seq.index vbn k)
                         (Seq.index (B.nat_to_be 12 (U64.v sq)) k)))
  decreases (12 - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(be.(vi));
    let b = A.(bn.(vi));
    A.((out.(vi) <- S8.logxor b a));
    i := SZ.add vi 1sz;
  };
  with wo. assert (A.pts_to out wo);
  A.pts_to_len out;
  assert (pure (forall (k: nat). k < 12 ==>
                  Seq.index wo k ==
                    S8.logxor (Seq.index vbn k)
                              (Seq.index (B.nat_to_be 12 (U64.v sq)) k)));
  nonce_eq (U64.v sq) vbn wo;
  assert (pure (reveal wo == xor_bytes #12 (reveal vbn) (B.nat_to_be 12 (U64.v sq))));
}

#pop-options

(** {2 Sealing and opening with a context}

    The context is the four buffers a caller keeps between messages.
    Sealing advances the sequence number in place; running out of sequence
    numbers is a failure, not a wrap, because a repeated nonce would destroy
    the AEAD's security outright. *)

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"

fn context_seal_impl (#t: Type0) {| w: word t |}
                     ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                        { ~(ExportOnly? cs.aead) })
                     (key: A.array S8.t) (base_nonce: A.array S8.t)
                     (sq: A.array U64.t) (exporter: A.array S8.t)
                     (aad: A.array S8.t) (aad_len: SZ.t)
                     (pt: A.array S8.t) (pt_len: SZ.t)
                     (ct: A.array S8.t) (tag: A.array S8.t)
                     (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                     (#pb: perm) (#vbn: erased (Seq.seq S8.t))
                     (#vsq: erased (Seq.seq U64.t))
                     (#px: perm) (#vexp: erased (Seq.seq S8.t))
                     (#pa: perm) (#vaad: erased (Seq.seq S8.t))
                     (#pp: perm) (#vpt: erased (Seq.seq S8.t))
                     (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
requires A.pts_to key #pk vkey ** A.pts_to base_nonce #pb vbn **
         A.pts_to sq vsq ** A.pts_to exporter #px vexp **
         A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
         A.pts_to ct vct ** A.pts_to tag vtag **
         pure (Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vsq == 1 /\ Seq.length vexp == size_kdf cs /\
               Seq.length vct == Seq.length vpt /\ Seq.length vtag == size_tag cs /\
               Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
               SZ.fits (Seq.length vpt + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v pt_len == Seq.length vpt)
returns r: bool
ensures exists* wsq wct wtag.
  A.pts_to key #pk vkey ** A.pts_to base_nonce #pb vbn **
  A.pts_to sq wsq ** A.pts_to exporter #px vexp **
  A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
  A.pts_to ct wct ** A.pts_to tag wtag **
  pure (Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
        Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
        Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
        Seq.length wsq == 1 /\ Seq.length wct == Seq.length vpt /\
        Seq.length wtag == size_tag cs /\
        (let c : context cs = { ckey = vkey; cbase_nonce = vbn;
                                cseq = U64.v (Seq.index vsq 0); cexporter = vexp } in
         r == Some? (context_seal c vaad vpt) /\
         (r ==> (let (c1, t1, c2) = Some?.v (context_seal c vaad vpt) in
                 wct == c1 /\ wtag == t1 /\ U64.v (Seq.index wsq 0) == c2.cseq))))
{
  A.pts_to_len key;
  A.pts_to_len base_nonce;
  A.pts_to_len sq;
  A.pts_to_len exporter;
  A.pts_to_len aad;
  A.pts_to_len pt;
  A.pts_to_len ct;
  A.pts_to_len tag;
  assert_norm (U64.v 18446744073709551615uL == pow2 64 - 1);
  let s = A.(sq.(0sz));
  if (U64.(s =^ 18446744073709551615uL)) {
    false
  } else {
    let z8 = S8.zero;
    let mut nonce = [| z8; 12sz |];
    A.pts_to_len nonce;
    compute_nonce_impl nonce base_nonce s;
    seal_impl cs.aead ct tag pt pt_len aad aad_len key nonce;
    A.((sq.(0sz) <- U64.add s 1uL));
    true
  }
}

fn context_open_impl (#t: Type0) {| w: word t |}
                     ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                        { ~(ExportOnly? cs.aead) })
                     (key: A.array S8.t) (base_nonce: A.array S8.t)
                     (sq: A.array U64.t) (exporter: A.array S8.t)
                     (aad: A.array S8.t) (aad_len: SZ.t)
                     (ct: A.array S8.t) (ct_len: SZ.t) (tag: A.array S8.t)
                     (pt: A.array S8.t)
                     (#pk: perm) (#vkey: erased (Seq.seq S8.t))
                     (#pb: perm) (#vbn: erased (Seq.seq S8.t))
                     (#vsq: erased (Seq.seq U64.t))
                     (#px: perm) (#vexp: erased (Seq.seq S8.t))
                     (#pa: perm) (#vaad: erased (Seq.seq S8.t))
                     (#pc: perm) (#vct: erased (Seq.seq S8.t))
                     (#pt': perm) (#vtag: erased (Seq.seq S8.t))
                     (#vpt: erased (Seq.seq S8.t))
requires A.pts_to key #pk vkey ** A.pts_to base_nonce #pb vbn **
         A.pts_to sq vsq ** A.pts_to exporter #px vexp **
         A.pts_to aad #pa vaad ** A.pts_to ct #pc vct **
         A.pts_to tag #pt' vtag ** A.pts_to pt vpt **
         pure (Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vsq == 1 /\ Seq.length vexp == size_kdf cs /\
               Seq.length vpt == Seq.length vct /\ Seq.length vtag == size_tag cs /\
               Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
               SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v ct_len == Seq.length vct)
returns r: bool
ensures exists* wsq wpt.
  A.pts_to key #pk vkey ** A.pts_to base_nonce #pb vbn **
  A.pts_to sq wsq ** A.pts_to exporter #px vexp **
  A.pts_to aad #pa vaad ** A.pts_to ct #pc vct **
  A.pts_to tag #pt' vtag ** A.pts_to pt wpt **
  pure (Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
        Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
        Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
        Seq.length vtag == size_tag cs /\
        Seq.length wsq == 1 /\ Seq.length wpt == Seq.length vct /\
        (let c : context cs = { ckey = vkey; cbase_nonce = vbn;
                                cseq = U64.v (Seq.index vsq 0); cexporter = vexp } in
         (r <==> context_open_ok c vaad vct vtag) /\
         (r ==> wpt == context_opened c vct /\
                U64.v (Seq.index wsq 0) == U64.v (Seq.index vsq 0) + 1)))
{
  A.pts_to_len key;
  A.pts_to_len base_nonce;
  A.pts_to_len sq;
  A.pts_to_len exporter;
  A.pts_to_len aad;
  A.pts_to_len ct;
  A.pts_to_len tag;
  A.pts_to_len pt;
  assert_norm (U64.v 18446744073709551615uL == pow2 64 - 1);
  let s = A.(sq.(0sz));
  if (U64.(s =^ 18446744073709551615uL)) {
    false
  } else {
    let z8 = S8.zero;
    let mut nonce = [| z8; 12sz |];
    A.pts_to_len nonce;
    compute_nonce_impl nonce base_nonce s;
    let r = open_impl cs.aead pt ct ct_len tag aad aad_len key nonce;
    if r {
      A.((sq.(0sz) <- U64.add s 1uL));
      true
    } else {
      false
    }
  }
}

#pop-options

(** {2 Exporting}

    Any number of independent secrets of any length, from the context's
    exporter secret and a caller-supplied exporter context. *)

#push-options "--z3rlimit 300 --fuel 0 --ifuel 0"

fn context_export_impl (#t: Type0) {| w: word t |}
                       ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t)
                       (kt: A.array t) (ivt: A.array t)
                       (out: A.array S8.t) (out_len: SZ.t)
                       (exporter: A.array S8.t)
                       (exp_ctx: A.array S8.t) (exp_ctx_len: SZ.t)
                       (#pk: perm) (#vk: erased (Seq.seq t))
                       (#pi: perm) (#vi: erased (Seq.seq t))
                       (#vout: erased (Seq.seq S8.t))
                       (#px: perm) (#vexp: erased (Seq.seq S8.t))
                       (#pe: perm) (#vctx: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to exporter #px vexp ** A.pts_to exp_ctx #pe vctx **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length vexp == size_kdf cs /\
               Seq.length vctx < pow2 32 /\
               0 < Seq.length vout /\ Seq.length vout < 65536 /\
               Seq.length vout <= 255 * size_kdf cs /\
               SZ.fits (256 + 128 + 64 + Seq.length vctx))
         ** pure (SZ.v out_len == Seq.length vout)
         ** pure (SZ.v exp_ctx_len == Seq.length vctx)
ensures exists* wout.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out wout **
  A.pts_to exporter #px vexp ** A.pts_to exp_ctx #pe vctx **
  pure (Seq.length vexp == size_kdf cs /\ Seq.length vctx < pow2 32 /\
        fits cs.kdf (Seq.length vctx) /\
        0 < Seq.length vout /\ Seq.length vout < 65536 /\
        Seq.length vout <= 255 * size_kdf cs /\
        Seq.length wout == Seq.length vout /\
        wout == labeled_expand cs.kdf (suite_id cs) vexp label_sec vctx
                               (Seq.length wout))
{
  A.pts_to_len out;
  A.pts_to_len exporter;
  A.pts_to_len exp_ctx;
  ks_bound cs.kdf (Seq.length vctx);

  let z8 = S8.zero;
  let mut sid = [| z8; 10sz |];
  A.pts_to_len sid;
  suite_id_impl cs sid;
  let l = table label_sec_arr 3sz;
  A.pts_to_len l;
  labeled_expand_impl cs.kdf kt ivt out out_len exporter (kdf_len cs) sid 10sz
                      l 3sz exp_ctx exp_ctx_len;
  drop_table l;
}

#pop-options

(** {2 Setup}

    The four modes, as four functions: the sender and the recipient, each in
    an unauthenticated and an authenticated variant.  [Base] and [PSK] differ
    only in the strings a caller passes, and [Auth] and [AuthPSK] likewise,
    so the mode is a parameter rather than a separate entry point. *)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0 --using_facts_from '* -Spec.HPKE.key_schedule -Spec.HPKE.labeled -Spec.HPKE.ks -Spec.HPKE.cat2_pointwise -Spec.HPKE.cat3_pointwise -Spec.HPKE.cat4_pointwise -Spec.HPKE.cat5_pointwise -Spec.HPKE.suite_id'"

fn setup_s_impl (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                ([@@@FStar.Attributes.monomorphize] m: mode { ~(uses_auth m) })
                (kt: A.array t) (ivt: A.array t)
                (enc: A.array S8.t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (skE: A.array S8.t) (pkR: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (psk: A.array S8.t) (psk_len: SZ.t)
                (psk_id: A.array S8.t) (psk_id_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#venc: erased (Seq.seq S8.t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pe: perm) (#vskE: erased (Seq.seq S8.t))
                (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
                (#pp: perm) (#vpsk: erased (Seq.seq S8.t))
                (#pq: perm) (#vpid: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc venc **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\
               Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
               Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
               Seq.length vpid < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpsk) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpid) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v psk_len == Seq.length vpsk)
         ** pure (SZ.v psk_id_len == Seq.length vpid)
returns r: bool
ensures exists* wenc wkey wbn wsq wexp.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc wenc **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
  pure (Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
        Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
        Seq.length vpid < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        fits cs.kdf (Seq.length vpsk) /\ fits cs.kdf (Seq.length vpid) /\
        Seq.length wenc == size_dh_public cs.kem /\
        Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
        Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
        r == Some? (setup_s cs m vskE None vpkR vinfo vpsk vpid) /\
        (r ==> (let (e1, c1) = Some?.v (setup_s cs m vskE None vpkR vinfo vpsk vpid) in
                wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf (Seq.length vpsk);
  ks_bound cs.kdf (Seq.length vpid);
  A.pts_to_len enc;
  A.pts_to_len key;
  A.pts_to_len base_nonce;
  A.pts_to_len sq;
  A.pts_to_len exporter;
  A.pts_to_len skE;
  A.pts_to_len pkR;
  let z8 = S8.zero;
  let mut shared = [| z8; 32sz |];
  A.pts_to_len shared;
  let ok = encap_impl cs.kem shared enc skE pkR;
  if ok {
    key_schedule_impl cs m kt ivt key base_nonce exporter shared
                      info info_len psk psk_len psk_id psk_id_len;
    A.((sq.(0sz) <- 0uL));
    true
  } else {
    false
  }
}

fn setup_r_impl (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                ([@@@FStar.Attributes.monomorphize] m: mode { ~(uses_auth m) })
                (kt: A.array t) (ivt: A.array t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (enc: A.array S8.t) (skR: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (psk: A.array S8.t) (psk_len: SZ.t)
                (psk_id: A.array S8.t) (psk_id_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pn: perm) (#venc: erased (Seq.seq S8.t))
                (#pr: perm) (#vskR: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
                (#pp: perm) (#vpsk: erased (Seq.seq S8.t))
                (#pq: perm) (#vpid: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
               Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
               Seq.length vpid < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpsk) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpid) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v psk_len == Seq.length vpsk)
         ** pure (SZ.v psk_id_len == Seq.length vpid)
returns r: bool
ensures exists* wkey wbn wsq wexp.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
  pure (Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
        Seq.length vpid < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        fits cs.kdf (Seq.length vpsk) /\ fits cs.kdf (Seq.length vpid) /\
        Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
        Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
        r == Some? (setup_r cs m venc vskR None vinfo vpsk vpid) /\
        (r ==> (let c1 = Some?.v (setup_r cs m venc vskR None vinfo vpsk vpid) in
                wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf (Seq.length vpsk);
  ks_bound cs.kdf (Seq.length vpid);
  A.pts_to_len key;
  A.pts_to_len base_nonce;
  A.pts_to_len sq;
  A.pts_to_len exporter;
  A.pts_to_len enc;
  A.pts_to_len skR;
  let z8 = S8.zero;
  let mut shared = [| z8; 32sz |];
  A.pts_to_len shared;
  let ok = decap_impl cs.kem shared enc skR;
  if ok {
    key_schedule_impl cs m kt ivt key base_nonce exporter shared
                      info info_len psk psk_len psk_id psk_id_len;
    A.((sq.(0sz) <- 0uL));
    true
  } else {
    false
  }
}

fn setup_auth_s_impl (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                ([@@@FStar.Attributes.monomorphize] m: mode { uses_auth m })
                (kt: A.array t) (ivt: A.array t)
                (enc: A.array S8.t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (skE: A.array S8.t) (skS: A.array S8.t) (pkR: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (psk: A.array S8.t) (psk_len: SZ.t)
                (psk_id: A.array S8.t) (psk_id_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#venc: erased (Seq.seq S8.t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pe: perm) (#vskE: erased (Seq.seq S8.t))
                (#ps: perm) (#vskS: erased (Seq.seq S8.t))
                (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
                (#pp: perm) (#vpsk: erased (Seq.seq S8.t))
                (#pq: perm) (#vpid: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc venc **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to skS #ps vskS **
         A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\
               Seq.length vskE == 32 /\ Seq.length vskS == 32 /\
               Seq.length vpkR == size_dh_public cs.kem /\
               Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
               Seq.length vpid < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpsk) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpid) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v psk_len == Seq.length vpsk)
         ** pure (SZ.v psk_id_len == Seq.length vpid)
returns r: bool
ensures exists* wenc wkey wbn wsq wexp.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc wenc **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to skS #ps vskS **
  A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
  pure (Seq.length vskE == 32 /\ Seq.length vskS == 32 /\
        Seq.length vpkR == size_dh_public cs.kem /\
        Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
        Seq.length vpid < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        fits cs.kdf (Seq.length vpsk) /\ fits cs.kdf (Seq.length vpid) /\
        Seq.length wenc == size_dh_public cs.kem /\
        Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
        Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
        r == Some? (setup_s cs m vskE (Some (reveal vskS)) vpkR vinfo vpsk vpid) /\
        (r ==> (let (e1, c1) = Some?.v (setup_s cs m vskE (Some (reveal vskS)) vpkR vinfo vpsk vpid) in
                wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf (Seq.length vpsk);
  ks_bound cs.kdf (Seq.length vpid);
  A.pts_to_len enc;
  A.pts_to_len key;
  A.pts_to_len base_nonce;
  A.pts_to_len sq;
  A.pts_to_len exporter;
  A.pts_to_len skE;
  A.pts_to_len skS;
  A.pts_to_len pkR;
  let z8 = S8.zero;
  let mut shared = [| z8; 32sz |];
  A.pts_to_len shared;
  let ok = auth_encap_impl cs.kem shared enc skE skS pkR;
  if ok {
    key_schedule_impl cs m kt ivt key base_nonce exporter shared
                      info info_len psk psk_len psk_id psk_id_len;
    A.((sq.(0sz) <- 0uL));
    true
  } else {
    false
  }
}

fn setup_auth_r_impl (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                ([@@@FStar.Attributes.monomorphize] m: mode { uses_auth m })
                (kt: A.array t) (ivt: A.array t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (enc: A.array S8.t) (skR: A.array S8.t) (pkS: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (psk: A.array S8.t) (psk_len: SZ.t)
                (psk_id: A.array S8.t) (psk_id_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pn: perm) (#venc: erased (Seq.seq S8.t))
                (#pr: perm) (#vskR: erased (Seq.seq S8.t))
                (#pS: perm) (#vpkS: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
                (#pp: perm) (#vpsk: erased (Seq.seq S8.t))
                (#pq: perm) (#vpid: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to pkS #pS vpkS **
         A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
               Seq.length vpkS == size_dh_public cs.kem /\
               Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
               Seq.length vpid < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpsk) /\
               SZ.fits (256 + 128 + 64 + Seq.length vpid) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v psk_len == Seq.length vpsk)
         ** pure (SZ.v psk_id_len == Seq.length vpid)
returns r: bool
ensures exists* wkey wbn wsq wexp.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to pkS #pS vpkS **
  A.pts_to info #pf vinfo ** A.pts_to psk #pp vpsk ** A.pts_to psk_id #pq vpid **
  pure (Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
        Seq.length vpkS == size_dh_public cs.kem /\
        Seq.length vinfo < pow2 32 /\ Seq.length vpsk < pow2 32 /\
        Seq.length vpid < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        fits cs.kdf (Seq.length vpsk) /\ fits cs.kdf (Seq.length vpid) /\
        Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
        Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
        r == Some? (setup_r cs m venc vskR (Some (reveal vpkS)) vinfo vpsk vpid) /\
        (r ==> (let c1 = Some?.v (setup_r cs m venc vskR (Some (reveal vpkS)) vinfo vpsk vpid) in
                wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf (Seq.length vpsk);
  ks_bound cs.kdf (Seq.length vpid);
  A.pts_to_len key;
  A.pts_to_len base_nonce;
  A.pts_to_len sq;
  A.pts_to_len exporter;
  A.pts_to_len enc;
  A.pts_to_len skR;
  A.pts_to_len pkS;
  let z8 = S8.zero;
  let mut shared = [| z8; 32sz |];
  A.pts_to_len shared;
  let ok = auth_decap_impl cs.kem shared enc skR pkS;
  if ok {
    key_schedule_impl cs m kt ivt key base_nonce exporter shared
                      info info_len psk psk_len psk_id psk_id_len;
    A.((sq.(0sz) <- 0uL));
    true
  } else {
    false
  }
}

#pop-options

(** {2 Base mode}

    The unauthenticated, no-pre-shared-key mode, which is what nearly every
    user of HPKE wants and the only one HACL* ships in C.  An empty
    pre-shared key is not a buffer a caller can produce -- a zero-length
    stack allocation is not something C wants to see -- so the two empty
    strings are made here, as zero-length windows onto one spare byte. *)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

fn setup_base_s (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                (kt: A.array t) (ivt: A.array t)
                (enc: A.array S8.t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (skE: A.array S8.t) (pkR: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#venc: erased (Seq.seq S8.t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pe: perm) (#vskE: erased (Seq.seq S8.t))
                (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc venc **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\
               Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
               Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wenc wkey wbn wsq wexp.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc wenc **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo **
  pure (Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
        Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        Seq.length wenc == size_dh_public cs.kem /\
        Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
        Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
        r == Some? (setup_s cs Base vskE None vpkR vinfo Seq.empty Seq.empty) /\
        (r ==> (let (e1, c1) =
                  Some?.v (setup_s cs Base vskE None vpkR vinfo Seq.empty Seq.empty) in
                wenc == e1 /\ wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf 0;
  let z8 = S8.zero;
  let mut o1 = [| z8; 1sz |];
  A.pts_to_len o1;
  let n1 = Sub.sub o1 0sz 0sz;
  with w1. assert (A.pts_to n1 w1);
  A.pts_to_len n1;
  Seq.lemma_eq_elim (reveal w1) (Seq.empty #S8.t);
  let mut o2 = [| z8; 1sz |];
  A.pts_to_len o2;
  let n2 = Sub.sub o2 0sz 0sz;
  with w2. assert (A.pts_to n2 w2);
  A.pts_to_len n2;
  Seq.lemma_eq_elim (reveal w2) (Seq.empty #S8.t);
  let r = setup_s_impl cs Base kt ivt enc key base_nonce sq exporter skE pkR
                       info info_len n1 0sz n2 0sz;
  Sub.unsub_id o2 0 0 n2;
  Sub.unsub_id o1 0 0 n1;
  r
}

fn setup_base_r (#t: Type0) {| w: word t |}
                ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                   { ~(ExportOnly? cs.aead) })
                (kt: A.array t) (ivt: A.array t)
                (key: A.array S8.t) (base_nonce: A.array S8.t)
                (sq: A.array U64.t) (exporter: A.array S8.t)
                (enc: A.array S8.t) (skR: A.array S8.t)
                (info: A.array S8.t) (info_len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#vkey: erased (Seq.seq S8.t)) (#vbn: erased (Seq.seq S8.t))
                (#vsq: erased (Seq.seq U64.t)) (#vexp: erased (Seq.seq S8.t))
                (#pn: perm) (#venc: erased (Seq.seq S8.t))
                (#pr: perm) (#vskR: erased (Seq.seq S8.t))
                (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to key vkey ** A.pts_to base_nonce vbn ** A.pts_to sq vsq **
         A.pts_to exporter vexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
               Seq.length vkey == size_key cs /\ Seq.length vbn == size_nonce cs /\
               Seq.length vexp == size_kdf cs /\ Seq.length vsq == 1 /\
               Seq.length vinfo < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1))
         ** pure (SZ.v info_len == Seq.length vinfo)
returns r: bool
ensures exists* wkey wbn wsq wexp.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to key wkey ** A.pts_to base_nonce wbn ** A.pts_to sq wsq **
  A.pts_to exporter wexp ** A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo **
  pure (Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        Seq.length wkey == size_key cs /\ Seq.length wbn == size_nonce cs /\
        Seq.length wexp == size_kdf cs /\ Seq.length wsq == 1 /\
        r == Some? (setup_r cs Base venc vskR None vinfo Seq.empty Seq.empty) /\
        (r ==> (let c1 =
                  Some?.v (setup_r cs Base venc vskR None vinfo Seq.empty Seq.empty) in
                wkey == c1.ckey /\ wbn == c1.cbase_nonce /\
                wexp == c1.cexporter /\ U64.v (Seq.index wsq 0) == 0)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf 0;
  let z8 = S8.zero;
  let mut o1 = [| z8; 1sz |];
  A.pts_to_len o1;
  let n1 = Sub.sub o1 0sz 0sz;
  with w1. assert (A.pts_to n1 w1);
  A.pts_to_len n1;
  Seq.lemma_eq_elim (reveal w1) (Seq.empty #S8.t);
  let mut o2 = [| z8; 1sz |];
  A.pts_to_len o2;
  let n2 = Sub.sub o2 0sz 0sz;
  with w2. assert (A.pts_to n2 w2);
  A.pts_to_len n2;
  Seq.lemma_eq_elim (reveal w2) (Seq.empty #S8.t);
  let r = setup_r_impl cs Base kt ivt key base_nonce sq exporter enc skR
                       info info_len n1 0sz n2 0sz;
  Sub.unsub_id o2 0 0 n2;
  Sub.unsub_id o1 0 0 n1;
  r
}

#pop-options

(** {2 Single-shot encryption}

    The whole of HPKE for a caller with one message: a fresh ephemeral key,
    an encapsulation, and a single sealing at sequence number zero.  The
    context lives on the stack and dies with the call. *)

#push-options "--z3rlimit 400 --fuel 2 --ifuel 2"

fn seal_base (#t: Type0) {| w: word t |}
             ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                { ~(ExportOnly? cs.aead) })
             (kt: A.array t) (ivt: A.array t)
             (enc: A.array S8.t) (ct: A.array S8.t) (tag: A.array S8.t)
             (skE: A.array S8.t) (pkR: A.array S8.t)
             (info: A.array S8.t) (info_len: SZ.t)
             (aad: A.array S8.t) (aad_len: SZ.t)
             (pt: A.array S8.t) (pt_len: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#venc: erased (Seq.seq S8.t))
             (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
             (#pe: perm) (#vskE: erased (Seq.seq S8.t))
             (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
             (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pp: perm) (#vpt: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc venc **
         A.pts_to ct vct ** A.pts_to tag vtag **
         A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\
               Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
               Seq.length vct == Seq.length vpt /\ Seq.length vtag == size_tag cs /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vpt < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1) /\
               SZ.fits (Seq.length vpt + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v pt_len == Seq.length vpt)
returns r: bool
ensures exists* wenc wct wtag.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to enc wenc **
  A.pts_to ct wct ** A.pts_to tag wtag **
  A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad ** A.pts_to pt #pp vpt **
  pure (Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public cs.kem /\
        Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vpt < pow2 32 /\
        Seq.length wenc == size_dh_public cs.kem /\
        Seq.length wct == Seq.length vpt /\ Seq.length wtag == size_tag cs /\
        r == Some? (seal_base cs vskE vpkR vinfo vaad vpt) /\
        (r ==> (let (e1, c1, t1) = Some?.v (seal_base cs vskE vpkR vinfo vaad vpt) in
                wenc == e1 /\ wct == c1 /\ wtag == t1)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf 0;
  A.pts_to_len ct;
  A.pts_to_len tag;
  let z8 = S8.zero;
  let mut key = [| z8; key_len cs.aead |];
  A.pts_to_len key;
  let mut base_nonce = [| z8; 12sz |];
  A.pts_to_len base_nonce;
  let mut exporter = [| z8; kdf_len cs |];
  A.pts_to_len exporter;
  let mut sq = [| 0uL; 1sz |];
  A.pts_to_len sq;
  let ok = setup_base_s cs kt ivt enc key base_nonce sq exporter skE pkR info info_len;
  if ok {
    let r = context_seal_impl cs key base_nonce sq exporter aad aad_len pt pt_len ct tag;
    r
  } else {
    false
  }
}

fn open_base (#t: Type0) {| w: word t |}
             ([@@@FStar.Attributes.monomorphize] cs: ciphersuite t
                { ~(ExportOnly? cs.aead) })
             (kt: A.array t) (ivt: A.array t)
             (pt: A.array S8.t)
             (enc: A.array S8.t) (skR: A.array S8.t)
             (info: A.array S8.t) (info_len: SZ.t)
             (aad: A.array S8.t) (aad_len: SZ.t)
             (ct: A.array S8.t) (ct_len: SZ.t) (tag: A.array S8.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vpt: erased (Seq.seq S8.t))
             (#pn: perm) (#venc: erased (Seq.seq S8.t))
             (#pr: perm) (#vskR: erased (Seq.seq S8.t))
             (#pf: perm) (#vinfo: erased (Seq.seq S8.t))
             (#pa: perm) (#vaad: erased (Seq.seq S8.t))
             (#pc: perm) (#vct: erased (Seq.seq S8.t))
             (#pg: perm) (#vtag: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to pt vpt **
         A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
         A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
         A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
         pure (reveal vk == (reveal cs.kdf.k <: Seq.seq t) /\
               reveal vi == (reveal cs.kdf.iv <: Seq.seq t) /\
               Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
               Seq.length vpt == Seq.length vct /\ Seq.length vtag == size_tag cs /\
               Seq.length vinfo < pow2 32 /\ Seq.length vaad < pow2 32 /\
               Seq.length vct < pow2 32 /\
               SZ.fits (256 + 128 + 64 + Seq.length vinfo) /\
               SZ.fits (256 + 128 + 64 + 2 * size_kdf cs + 1) /\
               SZ.fits (Seq.length vct + 16) /\ SZ.fits (Seq.length vaad + 16))
         ** pure (SZ.v info_len == Seq.length vinfo)
         ** pure (SZ.v aad_len == Seq.length vaad)
         ** pure (SZ.v ct_len == Seq.length vct)
returns r: bool
ensures exists* wpt.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to pt wpt **
  A.pts_to enc #pn venc ** A.pts_to skR #pr vskR **
  A.pts_to info #pf vinfo ** A.pts_to aad #pa vaad **
  A.pts_to ct #pc vct ** A.pts_to tag #pg vtag **
  pure (Seq.length venc == size_dh_public cs.kem /\ Seq.length vskR == 32 /\
        Seq.length vinfo < pow2 32 /\ fits cs.kdf (Seq.length vinfo) /\
        Seq.length vaad < pow2 32 /\ Seq.length vct < pow2 32 /\
        Seq.length vtag == size_tag cs /\ Seq.length wpt == Seq.length vct /\
        (r <==> open_base_ok cs venc vskR vinfo vaad vct vtag) /\
        (r ==> Some? (open_base cs venc vskR vinfo vct) /\
               wpt == Some?.v (open_base cs venc vskR vinfo vct)))
{
  ks_bound cs.kdf (Seq.length vinfo);
  ks_bound cs.kdf 0;
  A.pts_to_len pt;
  A.pts_to_len ct;
  A.pts_to_len tag;
  let z8 = S8.zero;
  let mut key = [| z8; key_len cs.aead |];
  A.pts_to_len key;
  let mut base_nonce = [| z8; 12sz |];
  A.pts_to_len base_nonce;
  let mut exporter = [| z8; kdf_len cs |];
  A.pts_to_len exporter;
  let mut sq = [| 0uL; 1sz |];
  A.pts_to_len sq;
  let ok = setup_base_r cs kt ivt key base_nonce sq exporter enc skR info info_len;
  if ok {
    let r = context_open_impl cs key base_nonce sq exporter aad aad_len
                              ct ct_len tag pt;
    r
  } else {
    false
  }
}

#pop-options
