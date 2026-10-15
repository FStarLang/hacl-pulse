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

(** HMAC_DRBG over SHA2-256, SHA2-384 and SHA2-512.

    HACL* also offers SHA-1, which this library does not implement; SP
    800-90A withdrew it for new applications in any case.

    The state is three buffers the caller owns: [k] and [v], one digest
    each, and [ctr], a single machine word.  There is no [create_in] and no
    [free].  [instantiate] is the only function that writes the initial
    values, so a state that has not been instantiated is simply one whose
    buffers hold whatever the caller left there.

    Each entry point lays out the round constants and the initial state,
    exactly as [Hacl.HMAC] does, and calls into [Hacl.HMAC.DRBG.Ops].

    This file is generated; see gen_drbg.py in the session notes. *)
module Hacl.HMAC.DRBG

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HMAC
open Spec.HMAC_DRBG
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Tables
open Hacl.Impl.Table
open Hacl.SizeT
open Hacl.HMAC.DRBG.Ops

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

let bounds (_: unit)
  : Lemma (pow2 61 <= max_input #S32.t /\ pow2 61 <= max_input #S64.t)
  = max_input_bound ()

(** Every message the mechanism hashes is at most one block, one digest, a
    tag byte and three inputs of [max_length] bytes each; that is under
    2^18, so it fits a [size_t] and is far below [max_input]. *)
let small (n: nat { n <= 128 + 64 + 1 + 3 * max_length })
  : Lemma (SZ.fits n /\ n < pow2 61)
  = fits32 ();
    assert_norm (128 + 64 + 1 + 3 * max_length < pow2 32);
    SZ.fits_u32_implies_fits n;
    assert_norm (128 + 64 + 1 + 3 * max_length < pow2 61)

(** The bound [Ops.instantiate] asks of the seed material, one lemma per
    word type, stated at top level so that the call sites need not unfold [data_ok] and
    [max_input] inside a query that also carries a heap. *)
let data_bound32 (p: params S32.t) (data: Seq.seq S8.t)
  : Lemma (requires hash_bytes p <= 64 /\ Seq.length data <= 3 * max_length)
          (ensures data_ok p data /\
                   SZ.fits (block_len #S32.t + hash_bytes p + 1 + Seq.length data))
  = bounds ();
    assert_norm (block_len #S32.t == 64);
    small (block_len #S32.t + hash_bytes p + 1 + Seq.length data)

let data_bound64 (p: params S64.t) (data: Seq.seq S8.t)
  : Lemma (requires hash_bytes p <= 64 /\ Seq.length data <= 3 * max_length)
          (ensures data_ok p data /\
                   SZ.fits (block_len #S64.t + hash_bytes p + 1 + Seq.length data))
  = bounds ();
    assert_norm (block_len #S64.t == 128);
    small (block_len #S64.t + hash_bytes p + 1 + Seq.length data)

(** The same for [Ops.reseed], whose size bound is stated over the two
    lengths rather than the length of their concatenation. *)
let reseed_bound64 (p: params S64.t) (ve va: Seq.seq S8.t)
  : Lemma (requires hash_bytes p <= 64 /\ Seq.length ve <= max_length /\
                    Seq.length va <= max_additional_input_length)
          (ensures data_ok p (Seq.append ve va) /\
                   SZ.fits (block_len #S64.t + hash_bytes p + 1 + Seq.length ve + Seq.length va))
  = assert_norm (max_additional_input_length <= max_length);
    data_bound64 p (Seq.append ve va)

(** Instantiate an HMAC_DRBG-sha2_256.  [k] and [v] must have room for 32 bytes
    and [ctr] for one word; all three are overwritten.  For the security the
    mechanism claims, [entropy] must hold at least [min_length] bytes from a
    real entropy source and [nonce] must never repeat. *)
fn instantiate_sha256 (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (entropy: A.array S8.t) (elen: SZ.t) (nonce: A.array S8.t) (nlen: SZ.t)
    (personal: A.array S8.t) (plen: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#vn: erased (Seq.seq S8.t))
    (#p3: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
         pure (Seq.length vkey == 32 /\ Seq.length vval == 32 /\ Seq.length vctr == 1 /\
               Seq.length ve <= max_length /\ Seq.length vn <= max_length /\
               Seq.length vp <= max_personalization_string_length)
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v nlen == Seq.length vn /\
                  SZ.v plen == Seq.length vp)
ensures exists* vkey' vval' vctr'.
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
  pure ((vkey', vval') == upd sha2_256 (initial sha2_256).k (initial sha2_256).v
                              (seed_material ve vn vp) /\
        ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len nonce; A.pts_to_len personal;
  bounds ();
  small (64 + 32 + 1 + Seq.length ve + Seq.length vn + Seq.length vp);
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  sha2_256_facts ();
  data_bound32 sha2_256 (seed_material ve vn vp);
  instantiate sha2_256 kt ivt k v ctr entropy elen nonce nlen personal plen;
  drop_table ivt;
  drop_table kt;
}

(** Reseed an HMAC_DRBG-sha2_256: fresh entropy, optional additional input, and
    the reseed counter back to one. *)
fn reseed_sha256 (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (entropy: A.array S8.t) (elen: SZ.t) (additional: A.array S8.t) (alen: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
         pure (Seq.length vkey == 32 /\ Seq.length vval == 32 /\ Seq.length vctr == 1 /\
               Seq.length ve <= max_length /\
               Seq.length va <= max_additional_input_length)
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v alen == Seq.length va)
ensures exists* vkey' vval' vctr'.
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
  pure ((vkey', vval') == upd sha2_256 vkey vval (Seq.append ve va) /\ ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len additional;
  bounds ();
  small (64 + 32 + 1 + Seq.length ve + Seq.length va);
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  sha2_256_facts ();
  data_bound32 sha2_256 (Seq.append ve va);
  reseed sha2_256 kt ivt k v ctr entropy elen additional alen;
  drop_table ivt;
  drop_table kt;
}

(** Fill [out] from an HMAC_DRBG-sha2_256.  Returns [false], leaving everything
    untouched, if the state has produced [reseed_interval] outputs since it
    was last seeded or if [out] is longer than [max_output_length]. *)
fn generate_sha256 (out: A.array S8.t) (olen: SZ.t)
    (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (additional: A.array S8.t) (alen: SZ.t)
    (#vout: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to k vkey ** A.pts_to v vval **
         A.pts_to ctr vctr ** A.pts_to additional #p1 va **
         pure (Seq.length vkey == 32 /\ Seq.length vval == 32 /\ Seq.length vctr == 1 /\
               Seq.length va <= max_additional_input_length)
         ** pure (SZ.v olen == Seq.length vout /\ SZ.v alen == Seq.length va)
returns ok: bool
ensures exists* vkey' vval' vctr' vout'.
  A.pts_to out vout' ** A.pts_to k vkey' ** A.pts_to v vval' **
  A.pts_to ctr vctr' ** A.pts_to additional #p1 va **
  pure (Seq.length vctr' == 1 /\
        (if ok
         then gene sha2_256 vkey vval (ctr_val vctr) (Seq.length vout) va ==
                Some (vout', reveal vkey', reveal vval', ctr_val vctr')
         else gene sha2_256 vkey vval (ctr_val vctr) (Seq.length vout) va == None /\
              vkey' == reveal vkey /\ vval' == reveal vval /\
              vctr' == reveal vctr /\ vout' == reveal vout))
{
  A.pts_to_len out; A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len additional;
  bounds ();
  small (64 + 32 + 1 + Seq.length va);
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  sha2_256_facts ();
  data_bound32 sha2_256 va;
  let r = generate sha2_256 kt ivt k v ctr out olen additional alen;
  drop_table ivt;
  drop_table kt;
  r
}

(** Instantiate an HMAC_DRBG-sha2_384.  [k] and [v] must have room for 48 bytes
    and [ctr] for one word; all three are overwritten.  For the security the
    mechanism claims, [entropy] must hold at least [min_length] bytes from a
    real entropy source and [nonce] must never repeat. *)
fn instantiate_sha384 (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (entropy: A.array S8.t) (elen: SZ.t) (nonce: A.array S8.t) (nlen: SZ.t)
    (personal: A.array S8.t) (plen: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#vn: erased (Seq.seq S8.t))
    (#p3: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
         pure (Seq.length vkey == 48 /\ Seq.length vval == 48 /\ Seq.length vctr == 1 /\
               Seq.length ve <= max_length /\ Seq.length vn <= max_length /\
               Seq.length vp <= max_personalization_string_length)
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v nlen == Seq.length vn /\
                  SZ.v plen == Seq.length vp)
ensures exists* vkey' vval' vctr'.
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
  pure ((vkey', vval') == upd sha2_384 (initial sha2_384).k (initial sha2_384).v
                              (seed_material ve vn vp) /\
        ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len nonce; A.pts_to_len personal;
  bounds ();
  small (128 + 48 + 1 + Seq.length ve + Seq.length vn + Seq.length vp);
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  sha2_384_facts ();
  data_bound64 sha2_384 (seed_material ve vn vp);
  instantiate sha2_384 kt ivt k v ctr entropy elen nonce nlen personal plen;
  drop_table ivt;
  drop_table kt;
}

(** Reseed an HMAC_DRBG-sha2_384: fresh entropy, optional additional input, and
    the reseed counter back to one. *)
fn reseed_sha384 (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (entropy: A.array S8.t) (elen: SZ.t) (additional: A.array S8.t) (alen: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
         pure (Seq.length vkey == 48 /\ Seq.length vval == 48 /\ Seq.length vctr == 1 /\
               Seq.length ve <= max_length /\
               Seq.length va <= max_additional_input_length)
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v alen == Seq.length va)
ensures exists* vkey' vval' vctr'.
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
  pure ((vkey', vval') == upd sha2_384 vkey vval (Seq.append ve va) /\ ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len additional;
  bounds ();
  small (128 + 48 + 1 + Seq.length ve + Seq.length va);
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  sha2_384_facts ();
  reseed_bound64 sha2_384 ve va;
  reseed sha2_384 kt ivt k v ctr entropy elen additional alen;
  drop_table ivt;
  drop_table kt;
}

(** Fill [out] from an HMAC_DRBG-sha2_384.  Returns [false], leaving everything
    untouched, if the state has produced [reseed_interval] outputs since it
    was last seeded or if [out] is longer than [max_output_length]. *)
fn generate_sha384 (out: A.array S8.t) (olen: SZ.t)
    (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (additional: A.array S8.t) (alen: SZ.t)
    (#vout: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to k vkey ** A.pts_to v vval **
         A.pts_to ctr vctr ** A.pts_to additional #p1 va **
         pure (Seq.length vkey == 48 /\ Seq.length vval == 48 /\ Seq.length vctr == 1 /\
               Seq.length va <= max_additional_input_length)
         ** pure (SZ.v olen == Seq.length vout /\ SZ.v alen == Seq.length va)
returns ok: bool
ensures exists* vkey' vval' vctr' vout'.
  A.pts_to out vout' ** A.pts_to k vkey' ** A.pts_to v vval' **
  A.pts_to ctr vctr' ** A.pts_to additional #p1 va **
  pure (Seq.length vctr' == 1 /\
        (if ok
         then gene sha2_384 vkey vval (ctr_val vctr) (Seq.length vout) va ==
                Some (vout', reveal vkey', reveal vval', ctr_val vctr')
         else gene sha2_384 vkey vval (ctr_val vctr) (Seq.length vout) va == None /\
              vkey' == reveal vkey /\ vval' == reveal vval /\
              vctr' == reveal vctr /\ vout' == reveal vout))
{
  A.pts_to_len out; A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len additional;
  bounds ();
  small (128 + 48 + 1 + Seq.length va);
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  sha2_384_facts ();
  data_bound64 sha2_384 va;
  let r = generate sha2_384 kt ivt k v ctr out olen additional alen;
  drop_table ivt;
  drop_table kt;
  r
}

(** Instantiate an HMAC_DRBG-sha2_512.  [k] and [v] must have room for 64 bytes
    and [ctr] for one word; all three are overwritten.  For the security the
    mechanism claims, [entropy] must hold at least [min_length] bytes from a
    real entropy source and [nonce] must never repeat. *)
fn instantiate_sha512 (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (entropy: A.array S8.t) (elen: SZ.t) (nonce: A.array S8.t) (nlen: SZ.t)
    (personal: A.array S8.t) (plen: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#vn: erased (Seq.seq S8.t))
    (#p3: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
         pure (Seq.length vkey == 64 /\ Seq.length vval == 64 /\ Seq.length vctr == 1 /\
               Seq.length ve <= max_length /\ Seq.length vn <= max_length /\
               Seq.length vp <= max_personalization_string_length)
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v nlen == Seq.length vn /\
                  SZ.v plen == Seq.length vp)
ensures exists* vkey' vval' vctr'.
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
  pure ((vkey', vval') == upd sha2_512 (initial sha2_512).k (initial sha2_512).v
                              (seed_material ve vn vp) /\
        ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len nonce; A.pts_to_len personal;
  bounds ();
  small (128 + 64 + 1 + Seq.length ve + Seq.length vn + Seq.length vp);
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  sha2_512_facts ();
  data_bound64 sha2_512 (seed_material ve vn vp);
  instantiate sha2_512 kt ivt k v ctr entropy elen nonce nlen personal plen;
  drop_table ivt;
  drop_table kt;
}

(** Reseed an HMAC_DRBG-sha2_512: fresh entropy, optional additional input, and
    the reseed counter back to one. *)
fn reseed_sha512 (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (entropy: A.array S8.t) (elen: SZ.t) (additional: A.array S8.t) (alen: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
         pure (Seq.length vkey == 64 /\ Seq.length vval == 64 /\ Seq.length vctr == 1 /\
               Seq.length ve <= max_length /\
               Seq.length va <= max_additional_input_length)
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v alen == Seq.length va)
ensures exists* vkey' vval' vctr'.
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
  pure ((vkey', vval') == upd sha2_512 vkey vval (Seq.append ve va) /\ ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len additional;
  bounds ();
  small (128 + 64 + 1 + Seq.length ve + Seq.length va);
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  sha2_512_facts ();
  reseed_bound64 sha2_512 ve va;
  reseed sha2_512 kt ivt k v ctr entropy elen additional alen;
  drop_table ivt;
  drop_table kt;
}

(** Fill [out] from an HMAC_DRBG-sha2_512.  Returns [false], leaving everything
    untouched, if the state has produced [reseed_interval] outputs since it
    was last seeded or if [out] is longer than [max_output_length]. *)
fn generate_sha512 (out: A.array S8.t) (olen: SZ.t)
    (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
    (additional: A.array S8.t) (alen: SZ.t)
    (#vout: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to k vkey ** A.pts_to v vval **
         A.pts_to ctr vctr ** A.pts_to additional #p1 va **
         pure (Seq.length vkey == 64 /\ Seq.length vval == 64 /\ Seq.length vctr == 1 /\
               Seq.length va <= max_additional_input_length)
         ** pure (SZ.v olen == Seq.length vout /\ SZ.v alen == Seq.length va)
returns ok: bool
ensures exists* vkey' vval' vctr' vout'.
  A.pts_to out vout' ** A.pts_to k vkey' ** A.pts_to v vval' **
  A.pts_to ctr vctr' ** A.pts_to additional #p1 va **
  pure (Seq.length vctr' == 1 /\
        (if ok
         then gene sha2_512 vkey vval (ctr_val vctr) (Seq.length vout) va ==
                Some (vout', reveal vkey', reveal vval', ctr_val vctr')
         else gene sha2_512 vkey vval (ctr_val vctr) (Seq.length vout) va == None /\
              vkey' == reveal vkey /\ vval' == reveal vval /\
              vctr' == reveal vctr /\ vout' == reveal vout))
{
  A.pts_to_len out; A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len additional;
  bounds ();
  small (128 + 64 + 1 + Seq.length va);
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  sha2_512_facts ();
  data_bound64 sha2_512 va;
  let r = generate sha2_512 kt ivt k v ctr out olen additional alen;
  drop_table ivt;
  drop_table kt;
  r
}
