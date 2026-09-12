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

(** The flat C interface to HMAC_DRBG.

    HACL* packs the state into a heap-allocated struct and hands out
    [create_in] and [free].  Here the state is the caller's, three pointers
    wide, exactly as for the streaming hashes:

      void Hacl_HMAC_DRBG_Ptr_instantiate_sha256(
             uint8_t *k, uint8_t *v, size_t *ctr,
             uint8_t *entropy, size_t entropy_len,
             uint8_t *nonce, size_t nonce_len,
             uint8_t *personal, size_t personal_len);

      bool Hacl_HMAC_DRBG_Ptr_generate_sha256(
             uint8_t *out, size_t out_len,
             uint8_t *k, uint8_t *v, size_t *ctr,
             uint8_t *additional, size_t additional_len);

    [k] and [v] must have room for one digest and [ctr] for one [size_t];
    the caller may put them on the stack, in a struct of its own, or
    anywhere else.

    This file is generated; see gen_drbg_ptr.py in the session notes. *)
module Hacl.HMAC.DRBG.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.HMAC
open Spec.HMAC_DRBG
open Spec.SHA2.Constants
open Hacl.HMAC.DRBG.Ops

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64


(** Instantiate an HMAC_DRBG-sha2_256.  [k] and [v] must have room for 32
    bytes and [ctr] for one word. *)
fn instantiate_sha256 (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (entropy: AP.ptr S8.t) (entropy_len: SZ.t)
    (nonce: AP.ptr S8.t) (nonce_len: SZ.t)
    (personal: AP.ptr S8.t) (personal_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#vn: erased (Seq.seq S8.t))
    (#p3: perm) (#vp: erased (Seq.seq S8.t))
requires AP.pts_to k vkey ** AP.pts_to v vval ** AP.pts_to ctr vctr **
         AP.pts_to entropy #p1 ve ** AP.pts_to nonce #p2 vn ** AP.pts_to personal #p3 vp **
         pure (Seq.length vkey == 32 /\ Seq.length vval == 32 /\ Seq.length vctr == 1 /\
               Seq.length ve == SZ.v entropy_len /\ Seq.length ve <= max_length /\
               Seq.length vn == SZ.v nonce_len /\ Seq.length vn <= max_length /\
               Seq.length vp == SZ.v personal_len /\
               Seq.length vp <= max_personalization_string_length)
ensures exists* vkey' vval' vctr'.
  AP.pts_to k vkey' ** AP.pts_to v vval' ** AP.pts_to ctr vctr' **
  AP.pts_to entropy #p1 ve ** AP.pts_to nonce #p2 vn ** AP.pts_to personal #p3 vp **
  pure ((vkey', vval') == upd sha2_256 (initial sha2_256).k (initial sha2_256).v
                              (seed_material ve vn vp) /\
        ctr_ok vctr' 1)
{
  let sk = S.arrayptr_to_slice_intro k 32sz;
  let sv = S.arrayptr_to_slice_intro v 32sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let se = S.arrayptr_to_slice_intro entropy entropy_len;
  let sn = S.arrayptr_to_slice_intro nonce nonce_len;
  let sp = S.arrayptr_to_slice_intro personal personal_len;
  Hacl.HMAC.DRBG.instantiate_sha256 sk sv sc se sn sp;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim sn;
  S.arrayptr_to_slice_elim se;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
}


(** Reseed an HMAC_DRBG-sha2_256. *)
fn reseed_sha256 (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (entropy: AP.ptr S8.t) (entropy_len: SZ.t)
    (additional: AP.ptr S8.t) (additional_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#va: erased (Seq.seq S8.t))
requires AP.pts_to k vkey ** AP.pts_to v vval ** AP.pts_to ctr vctr **
         AP.pts_to entropy #p1 ve ** AP.pts_to additional #p2 va **
         pure (Seq.length vkey == 32 /\ Seq.length vval == 32 /\ Seq.length vctr == 1 /\
               Seq.length ve == SZ.v entropy_len /\ Seq.length ve <= max_length /\
               Seq.length va == SZ.v additional_len /\
               Seq.length va <= max_additional_input_length)
ensures exists* vkey' vval' vctr'.
  AP.pts_to k vkey' ** AP.pts_to v vval' ** AP.pts_to ctr vctr' **
  AP.pts_to entropy #p1 ve ** AP.pts_to additional #p2 va **
  pure ((vkey', vval') == upd sha2_256 vkey vval (Seq.append ve va) /\ ctr_ok vctr' 1)
{
  let sk = S.arrayptr_to_slice_intro k 32sz;
  let sv = S.arrayptr_to_slice_intro v 32sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let se = S.arrayptr_to_slice_intro entropy entropy_len;
  let sa = S.arrayptr_to_slice_intro additional additional_len;
  Hacl.HMAC.DRBG.reseed_sha256 sk sv sc se sa;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim se;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
}


(** Fill [out] from an HMAC_DRBG-sha2_256; [false] means reseed first, or ask
    for less at a time. *)
fn generate_sha256 (out: AP.ptr S8.t) (out_len: SZ.t)
    (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (additional: AP.ptr S8.t) (additional_len: SZ.t)
    (#vout: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#va: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to k vkey ** AP.pts_to v vval **
         AP.pts_to ctr vctr ** AP.pts_to additional #p1 va **
         pure (Seq.length vout == SZ.v out_len /\
               Seq.length vkey == 32 /\ Seq.length vval == 32 /\ Seq.length vctr == 1 /\
               Seq.length va == SZ.v additional_len /\
               Seq.length va <= max_additional_input_length)
returns ok: bool
ensures exists* vkey' vval' vctr' vout'.
  AP.pts_to out vout' ** AP.pts_to k vkey' ** AP.pts_to v vval' **
  AP.pts_to ctr vctr' ** AP.pts_to additional #p1 va **
  pure (Seq.length vctr' == 1 /\
        (if ok
         then gene sha2_256 vkey vval (ctr_val vctr) (Seq.length vout) va ==
                Some (vout', reveal vkey', reveal vval', ctr_val vctr')
         else gene sha2_256 vkey vval (ctr_val vctr) (Seq.length vout) va == None /\
              vkey' == reveal vkey /\ vval' == reveal vval /\
              vctr' == reveal vctr /\ vout' == reveal vout))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let sk = S.arrayptr_to_slice_intro k 32sz;
  let sv = S.arrayptr_to_slice_intro v 32sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let sa = S.arrayptr_to_slice_intro additional additional_len;
  let r = Hacl.HMAC.DRBG.generate_sha256 so sk sv sc sa;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
  r
}


(** Instantiate an HMAC_DRBG-sha2_384.  [k] and [v] must have room for 48
    bytes and [ctr] for one word. *)
fn instantiate_sha384 (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (entropy: AP.ptr S8.t) (entropy_len: SZ.t)
    (nonce: AP.ptr S8.t) (nonce_len: SZ.t)
    (personal: AP.ptr S8.t) (personal_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#vn: erased (Seq.seq S8.t))
    (#p3: perm) (#vp: erased (Seq.seq S8.t))
requires AP.pts_to k vkey ** AP.pts_to v vval ** AP.pts_to ctr vctr **
         AP.pts_to entropy #p1 ve ** AP.pts_to nonce #p2 vn ** AP.pts_to personal #p3 vp **
         pure (Seq.length vkey == 48 /\ Seq.length vval == 48 /\ Seq.length vctr == 1 /\
               Seq.length ve == SZ.v entropy_len /\ Seq.length ve <= max_length /\
               Seq.length vn == SZ.v nonce_len /\ Seq.length vn <= max_length /\
               Seq.length vp == SZ.v personal_len /\
               Seq.length vp <= max_personalization_string_length)
ensures exists* vkey' vval' vctr'.
  AP.pts_to k vkey' ** AP.pts_to v vval' ** AP.pts_to ctr vctr' **
  AP.pts_to entropy #p1 ve ** AP.pts_to nonce #p2 vn ** AP.pts_to personal #p3 vp **
  pure ((vkey', vval') == upd sha2_384 (initial sha2_384).k (initial sha2_384).v
                              (seed_material ve vn vp) /\
        ctr_ok vctr' 1)
{
  let sk = S.arrayptr_to_slice_intro k 48sz;
  let sv = S.arrayptr_to_slice_intro v 48sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let se = S.arrayptr_to_slice_intro entropy entropy_len;
  let sn = S.arrayptr_to_slice_intro nonce nonce_len;
  let sp = S.arrayptr_to_slice_intro personal personal_len;
  Hacl.HMAC.DRBG.instantiate_sha384 sk sv sc se sn sp;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim sn;
  S.arrayptr_to_slice_elim se;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
}


(** Reseed an HMAC_DRBG-sha2_384. *)
fn reseed_sha384 (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (entropy: AP.ptr S8.t) (entropy_len: SZ.t)
    (additional: AP.ptr S8.t) (additional_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#va: erased (Seq.seq S8.t))
requires AP.pts_to k vkey ** AP.pts_to v vval ** AP.pts_to ctr vctr **
         AP.pts_to entropy #p1 ve ** AP.pts_to additional #p2 va **
         pure (Seq.length vkey == 48 /\ Seq.length vval == 48 /\ Seq.length vctr == 1 /\
               Seq.length ve == SZ.v entropy_len /\ Seq.length ve <= max_length /\
               Seq.length va == SZ.v additional_len /\
               Seq.length va <= max_additional_input_length)
ensures exists* vkey' vval' vctr'.
  AP.pts_to k vkey' ** AP.pts_to v vval' ** AP.pts_to ctr vctr' **
  AP.pts_to entropy #p1 ve ** AP.pts_to additional #p2 va **
  pure ((vkey', vval') == upd sha2_384 vkey vval (Seq.append ve va) /\ ctr_ok vctr' 1)
{
  let sk = S.arrayptr_to_slice_intro k 48sz;
  let sv = S.arrayptr_to_slice_intro v 48sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let se = S.arrayptr_to_slice_intro entropy entropy_len;
  let sa = S.arrayptr_to_slice_intro additional additional_len;
  Hacl.HMAC.DRBG.reseed_sha384 sk sv sc se sa;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim se;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
}


(** Fill [out] from an HMAC_DRBG-sha2_384; [false] means reseed first, or ask
    for less at a time. *)
fn generate_sha384 (out: AP.ptr S8.t) (out_len: SZ.t)
    (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (additional: AP.ptr S8.t) (additional_len: SZ.t)
    (#vout: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#va: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to k vkey ** AP.pts_to v vval **
         AP.pts_to ctr vctr ** AP.pts_to additional #p1 va **
         pure (Seq.length vout == SZ.v out_len /\
               Seq.length vkey == 48 /\ Seq.length vval == 48 /\ Seq.length vctr == 1 /\
               Seq.length va == SZ.v additional_len /\
               Seq.length va <= max_additional_input_length)
returns ok: bool
ensures exists* vkey' vval' vctr' vout'.
  AP.pts_to out vout' ** AP.pts_to k vkey' ** AP.pts_to v vval' **
  AP.pts_to ctr vctr' ** AP.pts_to additional #p1 va **
  pure (Seq.length vctr' == 1 /\
        (if ok
         then gene sha2_384 vkey vval (ctr_val vctr) (Seq.length vout) va ==
                Some (vout', reveal vkey', reveal vval', ctr_val vctr')
         else gene sha2_384 vkey vval (ctr_val vctr) (Seq.length vout) va == None /\
              vkey' == reveal vkey /\ vval' == reveal vval /\
              vctr' == reveal vctr /\ vout' == reveal vout))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let sk = S.arrayptr_to_slice_intro k 48sz;
  let sv = S.arrayptr_to_slice_intro v 48sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let sa = S.arrayptr_to_slice_intro additional additional_len;
  let r = Hacl.HMAC.DRBG.generate_sha384 so sk sv sc sa;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
  r
}


(** Instantiate an HMAC_DRBG-sha2_512.  [k] and [v] must have room for 64
    bytes and [ctr] for one word. *)
fn instantiate_sha512 (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (entropy: AP.ptr S8.t) (entropy_len: SZ.t)
    (nonce: AP.ptr S8.t) (nonce_len: SZ.t)
    (personal: AP.ptr S8.t) (personal_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#vn: erased (Seq.seq S8.t))
    (#p3: perm) (#vp: erased (Seq.seq S8.t))
requires AP.pts_to k vkey ** AP.pts_to v vval ** AP.pts_to ctr vctr **
         AP.pts_to entropy #p1 ve ** AP.pts_to nonce #p2 vn ** AP.pts_to personal #p3 vp **
         pure (Seq.length vkey == 64 /\ Seq.length vval == 64 /\ Seq.length vctr == 1 /\
               Seq.length ve == SZ.v entropy_len /\ Seq.length ve <= max_length /\
               Seq.length vn == SZ.v nonce_len /\ Seq.length vn <= max_length /\
               Seq.length vp == SZ.v personal_len /\
               Seq.length vp <= max_personalization_string_length)
ensures exists* vkey' vval' vctr'.
  AP.pts_to k vkey' ** AP.pts_to v vval' ** AP.pts_to ctr vctr' **
  AP.pts_to entropy #p1 ve ** AP.pts_to nonce #p2 vn ** AP.pts_to personal #p3 vp **
  pure ((vkey', vval') == upd sha2_512 (initial sha2_512).k (initial sha2_512).v
                              (seed_material ve vn vp) /\
        ctr_ok vctr' 1)
{
  let sk = S.arrayptr_to_slice_intro k 64sz;
  let sv = S.arrayptr_to_slice_intro v 64sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let se = S.arrayptr_to_slice_intro entropy entropy_len;
  let sn = S.arrayptr_to_slice_intro nonce nonce_len;
  let sp = S.arrayptr_to_slice_intro personal personal_len;
  Hacl.HMAC.DRBG.instantiate_sha512 sk sv sc se sn sp;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim sn;
  S.arrayptr_to_slice_elim se;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
}


(** Reseed an HMAC_DRBG-sha2_512. *)
fn reseed_sha512 (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (entropy: AP.ptr S8.t) (entropy_len: SZ.t)
    (additional: AP.ptr S8.t) (additional_len: SZ.t)
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#ve: erased (Seq.seq S8.t))
    (#p2: perm) (#va: erased (Seq.seq S8.t))
requires AP.pts_to k vkey ** AP.pts_to v vval ** AP.pts_to ctr vctr **
         AP.pts_to entropy #p1 ve ** AP.pts_to additional #p2 va **
         pure (Seq.length vkey == 64 /\ Seq.length vval == 64 /\ Seq.length vctr == 1 /\
               Seq.length ve == SZ.v entropy_len /\ Seq.length ve <= max_length /\
               Seq.length va == SZ.v additional_len /\
               Seq.length va <= max_additional_input_length)
ensures exists* vkey' vval' vctr'.
  AP.pts_to k vkey' ** AP.pts_to v vval' ** AP.pts_to ctr vctr' **
  AP.pts_to entropy #p1 ve ** AP.pts_to additional #p2 va **
  pure ((vkey', vval') == upd sha2_512 vkey vval (Seq.append ve va) /\ ctr_ok vctr' 1)
{
  let sk = S.arrayptr_to_slice_intro k 64sz;
  let sv = S.arrayptr_to_slice_intro v 64sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let se = S.arrayptr_to_slice_intro entropy entropy_len;
  let sa = S.arrayptr_to_slice_intro additional additional_len;
  Hacl.HMAC.DRBG.reseed_sha512 sk sv sc se sa;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim se;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
}


(** Fill [out] from an HMAC_DRBG-sha2_512; [false] means reseed first, or ask
    for less at a time. *)
fn generate_sha512 (out: AP.ptr S8.t) (out_len: SZ.t)
    (k: AP.ptr S8.t) (v: AP.ptr S8.t) (ctr: AP.ptr SZ.t)
    (additional: AP.ptr S8.t) (additional_len: SZ.t)
    (#vout: erased (Seq.seq S8.t))
    (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
    (#vctr: erased (Seq.seq SZ.t))
    (#p1: perm) (#va: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to k vkey ** AP.pts_to v vval **
         AP.pts_to ctr vctr ** AP.pts_to additional #p1 va **
         pure (Seq.length vout == SZ.v out_len /\
               Seq.length vkey == 64 /\ Seq.length vval == 64 /\ Seq.length vctr == 1 /\
               Seq.length va == SZ.v additional_len /\
               Seq.length va <= max_additional_input_length)
returns ok: bool
ensures exists* vkey' vval' vctr' vout'.
  AP.pts_to out vout' ** AP.pts_to k vkey' ** AP.pts_to v vval' **
  AP.pts_to ctr vctr' ** AP.pts_to additional #p1 va **
  pure (Seq.length vctr' == 1 /\
        (if ok
         then gene sha2_512 vkey vval (ctr_val vctr) (Seq.length vout) va ==
                Some (vout', reveal vkey', reveal vval', ctr_val vctr')
         else gene sha2_512 vkey vval (ctr_val vctr) (Seq.length vout) va == None /\
              vkey' == reveal vkey /\ vval' == reveal vval /\
              vctr' == reveal vctr /\ vout' == reveal vout))
{
  let so = S.arrayptr_to_slice_intro out out_len;
  let sk = S.arrayptr_to_slice_intro k 64sz;
  let sv = S.arrayptr_to_slice_intro v 64sz;
  let sc = S.arrayptr_to_slice_intro ctr 1sz;
  let sa = S.arrayptr_to_slice_intro additional additional_len;
  let r = Hacl.HMAC.DRBG.generate_sha512 so sk sv sc sa;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sv;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim so;
  r
}
