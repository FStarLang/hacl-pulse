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

(** The incremental interface to HMAC-SHA-224/256/384/512.

    The state is a bare SHA-2 streaming state -- accumulator, one block of
    buffered bytes, a byte count -- plus one more block holding [K0 ^ opad].
    Four flat arrays, no allocation, no destructor, no error code.  [init]
    takes the key and is the only function that sees it; [update] costs
    exactly what a bare SHA-2 [update] costs; [digest] leaves the state alone,
    so it may be called more than once and absorbing may continue after it.

    Ghostly, a state also carries the key and the message absorbed so far,
    which is what lets [digest] promise [Spec.HMAC.hmac].  Both are [erased].

    Everything of substance is in [Hacl.Streaming.HMAC.Core]; this module
    names the four parameter sets and lays out their tables, exactly as
    [Hacl.Streaming.SHA2] does for the bare hashes. *)
module Hacl.Streaming.HMAC

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HMAC
open Hacl.Hash.SHA2
open Hacl.Hash.SHA2.Tables
open Hacl.Impl.Table
open Hacl.Streaming.HMAC.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Mem = Hacl.Mem
module D = Hacl.Hash.SHA2.Dispatch

(** The two block lengths, as literals.  [block_len] is [16 * (bits / 8)] and
    the type class does not reduce on its own inside a Pulse context. *)
let block_len_32 (_: unit) : Lemma (block_len #S32.t == 64) =
  assert_norm (bits #S32.t == 32)

let block_len_64 (_: unit) : Lemma (block_len #S64.t == 128) =
  assert_norm (bits #S64.t == 64)

(** {2 HMAC-SHA-224} *)

(** Reset the state to the empty message under [key].  [key] may be any
    length; it is hashed down if it exceeds a block. *)
fn hmac_sha224_init (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t)
    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to opadb vop ** A.pts_to key #pkey vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vop == 64 /\
               Seq.length vkey < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t) (vop': Seq.seq S8.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to opadb vop' ** A.pts_to key #pkey vkey **
  pure (hmac_ok sha2_224 vkey vacc' vbuf' vtot' vop' (Seq.empty #S8.t))
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let kt = table k256_arr 64sz;
  let ivt = table iv224_arr 8sz;
  let mut wsarr = [| z; 64sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  init_impl sha2_224 kt ivt wsarr acc buf tot opadb key key_len;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 64sz;
}

(** Absorb [data].  The ghost [key] and [msg] are the key the state was
    initialised with and everything absorbed since. *)
fn hmac_sha224_update (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (data: A.array S8.t) (data_len: SZ.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (hmac_ok sha2_224 key vacc vbuf vtot vop msg /\
               64 + Seq.length msg + Seq.length vdata < pow2 61 /\
               SZ.fits (64 + Seq.length msg + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (hmac_ok sha2_224 key vacc' vbuf' vtot' vop (Seq.append msg vdata))
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let kt = table k256_arr 64sz;
  let mut wsarr = [| z; 64sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  sha2_224_facts ();
  update_impl sha2_224 (D.blocks_dispatch32 sha2_224) kt wsarr acc buf tot data data_len key msg vop;
  drop_table kt;
  Mem.wipe wsarr 64sz;
}

(** Write the tag.  [out] must have room for 28 bytes.  The state is not
    consumed: digesting twice gives the same answer, and absorbing may
    continue afterwards. *)
fn hmac_sha224_digest (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (out: A.array S8.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#pa: perm) (#vacc: erased (Seq.seq S32.t))
    (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
    (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
    (#pop: perm) (#vop: erased (Seq.seq S8.t))
    (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to opadb #pop vop ** A.pts_to out vout **
         pure (hmac_ok sha2_224 key vacc vbuf vtot vop msg /\ Seq.length vout == 28)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to opadb #pop vop ** A.pts_to out vout' **
  pure (Seq.length key < max_input #S32.t /\
        64 + Seq.length msg < max_input #S32.t /\
        vout' == hmac sha2_224 key msg)
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let kt = table k256_arr 64sz;
  let ivt = table iv224_arr 8sz;
  let mut wsarr = [| z; 64sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  digest_impl sha2_224 kt ivt wsarr acc buf tot opadb out key msg;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 64sz;
}

(** {2 HMAC-SHA-256} *)

(** Reset the state to the empty message under [key].  [key] may be any
    length; it is hashed down if it exceeds a block. *)
fn hmac_sha256_init (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t)
    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to opadb vop ** A.pts_to key #pkey vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vop == 64 /\
               Seq.length vkey < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t) (vop': Seq.seq S8.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to opadb vop' ** A.pts_to key #pkey vkey **
  pure (hmac_ok sha2_256 vkey vacc' vbuf' vtot' vop' (Seq.empty #S8.t))
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  let mut wsarr = [| z; 64sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  init_impl sha2_256 kt ivt wsarr acc buf tot opadb key key_len;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 64sz;
}

(** Absorb [data].  The ghost [key] and [msg] are the key the state was
    initialised with and everything absorbed since. *)
fn hmac_sha256_update (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (data: A.array S8.t) (data_len: SZ.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (hmac_ok sha2_256 key vacc vbuf vtot vop msg /\
               64 + Seq.length msg + Seq.length vdata < pow2 61 /\
               SZ.fits (64 + Seq.length msg + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (hmac_ok sha2_256 key vacc' vbuf' vtot' vop (Seq.append msg vdata))
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let kt = table k256_arr 64sz;
  let mut wsarr = [| z; 64sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  sha2_256_facts ();
  update_impl sha2_256 (D.blocks_dispatch32 sha2_256) kt wsarr acc buf tot data data_len key msg vop;
  drop_table kt;
  Mem.wipe wsarr 64sz;
}

(** Write the tag.  [out] must have room for 32 bytes.  The state is not
    consumed: digesting twice gives the same answer, and absorbing may
    continue afterwards. *)
fn hmac_sha256_digest (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (out: A.array S8.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#pa: perm) (#vacc: erased (Seq.seq S32.t))
    (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
    (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
    (#pop: perm) (#vop: erased (Seq.seq S8.t))
    (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to opadb #pop vop ** A.pts_to out vout **
         pure (hmac_ok sha2_256 key vacc vbuf vtot vop msg /\ Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to opadb #pop vop ** A.pts_to out vout' **
  pure (Seq.length key < max_input #S32.t /\
        64 + Seq.length msg < max_input #S32.t /\
        vout' == hmac sha2_256 key msg)
{
  block_len_32 ();
  max_input_bound ();
  let z = S32.classify 0ul;
  let kt = table k256_arr 64sz;
  let ivt = table iv256_arr 8sz;
  let mut wsarr = [| z; 64sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  digest_impl sha2_256 kt ivt wsarr acc buf tot opadb out key msg;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 64sz;
}

(** {2 HMAC-SHA-384} *)

(** Reset the state to the empty message under [key].  [key] may be any
    length; it is hashed down if it exceeds a block. *)
fn hmac_sha384_init (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t)
    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to opadb vop ** A.pts_to key #pkey vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vop == 128 /\
               Seq.length vkey < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t) (vop': Seq.seq S8.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to opadb vop' ** A.pts_to key #pkey vkey **
  pure (hmac_ok sha2_384 vkey vacc' vbuf' vtot' vop' (Seq.empty #S8.t))
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  let mut wsarr = [| z; 80sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  init_impl sha2_384 kt ivt wsarr acc buf tot opadb key key_len;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 80sz;
}

(** Absorb [data].  The ghost [key] and [msg] are the key the state was
    initialised with and everything absorbed since. *)
fn hmac_sha384_update (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (data: A.array S8.t) (data_len: SZ.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (hmac_ok sha2_384 key vacc vbuf vtot vop msg /\
               128 + Seq.length msg + Seq.length vdata < pow2 61 /\
               SZ.fits (128 + Seq.length msg + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (hmac_ok sha2_384 key vacc' vbuf' vtot' vop (Seq.append msg vdata))
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let kt = table k512_arr 80sz;
  let mut wsarr = [| z; 80sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  sha2_384_facts ();
  update_impl sha2_384 (D.blocks_dispatch64 sha2_384) kt wsarr acc buf tot data data_len key msg vop;
  drop_table kt;
  Mem.wipe wsarr 80sz;
}

(** Write the tag.  [out] must have room for 48 bytes.  The state is not
    consumed: digesting twice gives the same answer, and absorbing may
    continue afterwards. *)
fn hmac_sha384_digest (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (out: A.array S8.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#pa: perm) (#vacc: erased (Seq.seq S64.t))
    (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
    (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
    (#pop: perm) (#vop: erased (Seq.seq S8.t))
    (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to opadb #pop vop ** A.pts_to out vout **
         pure (hmac_ok sha2_384 key vacc vbuf vtot vop msg /\ Seq.length vout == 48)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to opadb #pop vop ** A.pts_to out vout' **
  pure (Seq.length key < max_input #S64.t /\
        128 + Seq.length msg < max_input #S64.t /\
        vout' == hmac sha2_384 key msg)
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let kt = table k512_arr 80sz;
  let ivt = table iv384_arr 8sz;
  let mut wsarr = [| z; 80sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  digest_impl sha2_384 kt ivt wsarr acc buf tot opadb out key msg;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 80sz;
}

(** {2 HMAC-SHA-512} *)

(** Reset the state to the empty message under [key].  [key] may be any
    length; it is hashed down if it exceeds a block. *)
fn hmac_sha512_init (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (key: A.array S8.t) (key_len: SZ.t)
    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to opadb vop ** A.pts_to key #pkey vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vop == 128 /\
               Seq.length vkey < pow2 61)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t)
                (vtot': Seq.seq SZ.t) (vop': Seq.seq S8.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to opadb vop' ** A.pts_to key #pkey vkey **
  pure (hmac_ok sha2_512 vkey vacc' vbuf' vtot' vop' (Seq.empty #S8.t))
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  let mut wsarr = [| z; 80sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  init_impl sha2_512 kt ivt wsarr acc buf tot opadb key key_len;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 80sz;
}

(** Absorb [data].  The ghost [key] and [msg] are the key the state was
    initialised with and everything absorbed since. *)
fn hmac_sha512_update (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (data: A.array S8.t) (data_len: SZ.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
    (#vtot: erased (Seq.seq SZ.t)) (#vop: erased (Seq.seq S8.t))
    (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (hmac_ok sha2_512 key vacc vbuf vtot vop msg /\
               128 + Seq.length msg + Seq.length vdata < pow2 61 /\
               SZ.fits (128 + Seq.length msg + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (hmac_ok sha2_512 key vacc' vbuf' vtot' vop (Seq.append msg vdata))
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let kt = table k512_arr 80sz;
  let mut wsarr = [| z; 80sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  sha2_512_facts ();
  update_impl sha2_512 (D.blocks_dispatch64 sha2_512) kt wsarr acc buf tot data data_len key msg vop;
  drop_table kt;
  Mem.wipe wsarr 80sz;
}

(** Write the tag.  [out] must have room for 64 bytes.  The state is not
    consumed: digesting twice gives the same answer, and absorbing may
    continue afterwards. *)
fn hmac_sha512_digest (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
    (opadb: A.array S8.t) (out: A.array S8.t)
    (key: erased (Seq.seq S8.t)) (msg: erased (Seq.seq S8.t))
    (#pa: perm) (#vacc: erased (Seq.seq S64.t))
    (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
    (#ptot: perm) (#vtot: erased (Seq.seq SZ.t))
    (#pop: perm) (#vop: erased (Seq.seq S8.t))
    (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
         A.pts_to opadb #pop vop ** A.pts_to out vout **
         pure (hmac_ok sha2_512 key vacc vbuf vtot vop msg /\ Seq.length vout == 64)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #ptot vtot **
  A.pts_to opadb #pop vop ** A.pts_to out vout' **
  pure (Seq.length key < max_input #S64.t /\
        128 + Seq.length msg < max_input #S64.t /\
        vout' == hmac sha2_512 key msg)
{
  block_len_64 ();
  max_input_bound ();
  let z = S64.classify 0uL;
  let kt = table k512_arr 80sz;
  let ivt = table iv512_arr 8sz;
  let mut wsarr = [| z; 80sz |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;
  digest_impl sha2_512 kt ivt wsarr acc buf tot opadb out key msg;
  drop_table ivt;
  drop_table kt;
  Mem.wipe wsarr 80sz;
}
