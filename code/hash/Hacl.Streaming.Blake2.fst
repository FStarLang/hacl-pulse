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

(** The incremental interface to the eight named BLAKE2 hashes.

    The shape is the one [Hacl.Streaming.SHA2] uses: the caller keeps three
    flat pieces of memory -- the eight-word accumulator, one block of buffered
    bytes, and a single [size_t] -- and there is no allocation, no destructor
    and no error code.  What the [size_t] holds is the length of the *combined
    stream*, the key block followed by the message, which is why a keyed hash
    needs no extra state: it is an unkeyed one whose buffer starts full.

    The key is supplied once, to [init], and is thereafter only a ghost
    argument.  It must be the same sequence at every later call, which is what
    lets [digest] promise [Spec.Blake2.blake2 p key seen].

    Unlike SHA-2, a just-filled block is *not* compressed: BLAKE2 flags its
    last compression and gives it the message length as its counter, so the
    implementation cannot know a full block is not the last one until more
    data arrives.  The buffer therefore holds between one and [block_len]
    bytes rather than between zero and [block_len - 1]. *)
module Hacl.Streaming.Blake2

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.Blake2
open Spec.Blake2.Constants
open Spec.Blake2.Streaming
open Hacl.Hash.Blake2
open Hacl.Hash.Blake2.Core
open Hacl.Hash.Blake2.Named
open Hacl.Hash.Blake2.Streaming
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module G = FStar.Ghost

(** The two block lengths, as literals.  [block_len] is [16 * (bits / 8)] and
    the type class does not reduce on its own inside a Pulse context. *)
let block_len_64 (_: unit)
  : Lemma (block_len #S64.t == 128 /\ max_key_len #S64.t == 64)
  = assert_norm (bits #S64.t == 64)

let block_len_32 (_: unit)
  : Lemma (block_len #S32.t == 64 /\ max_key_len #S32.t == 32)
  = assert_norm (bits #S32.t == 32)

(** {2 The three generic entry points}

    Each takes the initialization vector as a slice -- the named layer below
    materializes it from the program image -- and allocates the scratch the
    compression function needs.  [update] and [digest] want sixteen working
    words, sixteen message words and one block of bytes; [init] wants none of
    them, because it only writes the initial state and the key block. *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn update_gen (#t: Type0) {| w: word t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (ivs: A.array t) (acc: A.array t) (buf: A.array S8.t)
              (tot: A.array SZ.t) (data: A.array S8.t) (data_len: SZ.t)
              (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
              (#pi: perm) (#vi: erased (Seq.seq t))
              (#vacc: erased (Seq.seq t)) (#vbuf: erased (Seq.seq S8.t))
              (#vtot: erased (Seq.seq SZ.t))
              (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to ivs #pi vi ** A.pts_to acc vacc ** A.pts_to buf vbuf **
         A.pts_to tot vtot ** A.pts_to data #pd vdata **
         pure (Seq.length vi == 8 /\ reveal vi == G.reveal p.iv /\
               stream_ok p key seen vacc vbuf vtot /\
               Seq.length (stream #t key seen) + Seq.length vdata +
                 2 * block_len #t < pow2 64 /\
               SZ.fits (Seq.length (stream #t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to ivs #pi vi ** A.pts_to acc vacc' ** A.pts_to buf vbuf' **
  A.pts_to tot vtot' ** A.pts_to data #pd vdata **
  pure (stream_ok p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  let z0: t = zero #t #w;
  let z8 = S8.classify 0uy;
  let bl = block_len_sz #t #w;

  let mut varr = [| z0; 16sz |];
  A.pts_to_len varr;
  let mut marr = [| z0; 16sz |];
  A.pts_to_len marr;
  let mut barr = [| z8; bl |];
  A.pts_to_len barr;
  sigma_len ();
  let sg = table sigma_arr 160sz;
  sigma_seq_ok ();
  A.pts_to_len varr;
  A.pts_to_len marr;
  A.pts_to_len barr;
  A.pts_to_len sg;

  update_impl p acc varr marr barr ivs sg buf tot data data_len key seen;

  drop_table sg;
}

fn digest_gen (#t: Type0) {| w: word t |}
              ([@@@FStar.Attributes.monomorphize] p: params t)
              (ivs: A.array t) (acc: A.array t) (buf: A.array S8.t)
              (tot: A.array SZ.t) (out: A.array S8.t)
              (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
              (#pi: perm) (#vi: erased (Seq.seq t))
              (#pa: perm) (#vacc: erased (Seq.seq t))
              (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
              (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
              (#vout: erased (Seq.seq S8.t))
requires A.pts_to ivs #pi vi ** A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf **
         A.pts_to tot #pt vtot ** A.pts_to out vout **
         pure (Seq.length vi == 8 /\ reveal vi == G.reveal p.iv /\
               Seq.length vout == hash_bytes p /\
               stream_ok p key seen vacc vbuf vtot)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to ivs #pi vi ** A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf **
  A.pts_to tot #pt vtot ** A.pts_to out vout' **
  pure (Seq.length key <= max_key_len #t /\ vout' == blake2 p key seen)
{
  let z0: t = zero #t #w;
  let z8 = S8.classify 0uy;
  let bl = block_len_sz #t #w;

  let mut varr = [| z0; 16sz |];
  A.pts_to_len varr;
  let mut marr = [| z0; 16sz |];
  A.pts_to_len marr;
  let mut barr = [| z8; bl |];
  A.pts_to_len barr;
  sigma_len ();
  let sg = table sigma_arr 160sz;
  sigma_seq_ok ();
  A.pts_to_len varr;
  A.pts_to_len marr;
  A.pts_to_len barr;
  A.pts_to_len sg;

  digest_impl p acc varr marr barr ivs sg buf tot out key seen;

  drop_table sg;
}

#pop-options

(** {2 The eight named hashes}

    One [init]/[update]/[digest] triple each.  The digest length is part of
    the algorithm, so it is part of the name; see [Hacl.Hash.Blake2.Named]. *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

(** {3 BLAKE2B-512} *)

fn blake2b_512_init (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 64)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2b_512_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  init_impl blake2b_512_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2b_512_update (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2b_512_p key seen vacc vbuf vtot /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2b_512_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  update_gen blake2b_512_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2b_512_digest (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2b_512_p key seen vacc vbuf vtot /\ Seq.length vout == 64)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_512_p key seen)
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  digest_gen blake2b_512_p ivt acc buf tot out key seen;
  drop_table ivt;
}

(** {3 BLAKE2B-384} *)

fn blake2b_384_init (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 64)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2b_384_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  init_impl blake2b_384_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2b_384_update (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2b_384_p key seen vacc vbuf vtot /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2b_384_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  update_gen blake2b_384_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2b_384_digest (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2b_384_p key seen vacc vbuf vtot /\ Seq.length vout == 48)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_384_p key seen)
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  digest_gen blake2b_384_p ivt acc buf tot out key seen;
  drop_table ivt;
}

(** {3 BLAKE2B-256} *)

fn blake2b_256_init (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 64)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2b_256_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  init_impl blake2b_256_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2b_256_update (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2b_256_p key seen vacc vbuf vtot /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2b_256_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  update_gen blake2b_256_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2b_256_digest (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2b_256_p key seen vacc vbuf vtot /\ Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_256_p key seen)
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  digest_gen blake2b_256_p ivt acc buf tot out key seen;
  drop_table ivt;
}

(** {3 BLAKE2B-160} *)

fn blake2b_160_init (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 128 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 64)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2b_160_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  init_impl blake2b_160_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2b_160_update (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S64.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2b_160_p key seen vacc vbuf vtot /\
               Seq.length (stream #S64.t key seen) + Seq.length vdata + 256 < pow2 64 /\
               SZ.fits (Seq.length (stream #S64.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2b_160_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  update_gen blake2b_160_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2b_160_digest (acc: A.array S64.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S64.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2b_160_p key seen vacc vbuf vtot /\ Seq.length vout == 20)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 64 /\ vout' == blake2 blake2b_160_p key seen)
{
  block_len_64 ();
  table_lens ();
  let ivt = table iv64_arr 8sz;
  digest_gen blake2b_160_p ivt acc buf tot out key seen;
  drop_table ivt;
}

(** {3 BLAKE2S-256} *)

fn blake2s_256_init (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 32)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2s_256_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  init_impl blake2s_256_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2s_256_update (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2s_256_p key seen vacc vbuf vtot /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2s_256_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  update_gen blake2s_256_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2s_256_digest (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2s_256_p key seen vacc vbuf vtot /\ Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_256_p key seen)
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  digest_gen blake2s_256_p ivt acc buf tot out key seen;
  drop_table ivt;
}

(** {3 BLAKE2S-224} *)

fn blake2s_224_init (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 32)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2s_224_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  init_impl blake2s_224_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2s_224_update (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2s_224_p key seen vacc vbuf vtot /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2s_224_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  update_gen blake2s_224_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2s_224_digest (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2s_224_p key seen vacc vbuf vtot /\ Seq.length vout == 28)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_224_p key seen)
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  digest_gen blake2s_224_p ivt acc buf tot out key seen;
  drop_table ivt;
}

(** {3 BLAKE2S-160} *)

fn blake2s_160_init (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 32)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2s_160_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  init_impl blake2s_160_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2s_160_update (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2s_160_p key seen vacc vbuf vtot /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2s_160_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  update_gen blake2s_160_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2s_160_digest (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2s_160_p key seen vacc vbuf vtot /\ Seq.length vout == 20)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_160_p key seen)
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  digest_gen blake2s_160_p ivt acc buf tot out key seen;
  drop_table ivt;
}

(** {3 BLAKE2S-128} *)

fn blake2s_128_init (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                    (key: A.array S8.t) (key_len: SZ.t)
                    (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                    (#vtot: erased (Seq.seq SZ.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to key #pk vkey **
         pure (Seq.length vacc == 8 /\ Seq.length vbuf == 64 /\
               Seq.length vtot == 1 /\ Seq.length vkey <= 32)
         ** pure (SZ.v key_len == Seq.length vkey)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to key #pk vkey **
  pure (stream_ok blake2s_128_p vkey (Seq.empty #S8.t) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  init_impl blake2s_128_p acc buf tot ivt key key_len;
  drop_table ivt;
}

fn blake2s_128_update (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (data: A.array S8.t) (data_len: SZ.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#vacc: erased (Seq.seq S32.t)) (#vbuf: erased (Seq.seq S8.t))
                      (#vtot: erased (Seq.seq SZ.t))
                      (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to acc vacc ** A.pts_to buf vbuf ** A.pts_to tot vtot **
         A.pts_to data #pd vdata **
         pure (stream_ok blake2s_128_p key seen vacc vbuf vtot /\
               Seq.length (stream #S32.t key seen) + Seq.length vdata + 128 < pow2 64 /\
               SZ.fits (Seq.length (stream #S32.t key seen) + Seq.length vdata))
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vacc': Seq.seq S32.t) (vbuf': Seq.seq S8.t) (vtot': Seq.seq SZ.t).
  A.pts_to acc vacc' ** A.pts_to buf vbuf' ** A.pts_to tot vtot' **
  A.pts_to data #pd vdata **
  pure (stream_ok blake2s_128_p key (Seq.append seen vdata) vacc' vbuf' vtot')
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  update_gen blake2s_128_p ivt acc buf tot data data_len key seen;
  drop_table ivt;
}

fn blake2s_128_digest (acc: A.array S32.t) (buf: A.array S8.t) (tot: A.array SZ.t)
                      (out: A.array S8.t)
                      (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                      (#pa: perm) (#vacc: erased (Seq.seq S32.t))
                      (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                      (#pt: perm) (#vtot: erased (Seq.seq SZ.t))
                      (#vout: erased (Seq.seq S8.t))
requires A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
         A.pts_to out vout **
         pure (stream_ok blake2s_128_p key seen vacc vbuf vtot /\ Seq.length vout == 16)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to acc #pa vacc ** A.pts_to buf #pb vbuf ** A.pts_to tot #pt vtot **
  A.pts_to out vout' **
  pure (Seq.length key <= 32 /\ vout' == blake2 blake2s_128_p key seen)
{
  block_len_32 ();
  table_lens ();
  let ivt = table iv32_arr 8sz;
  digest_gen blake2s_128_p ivt acc buf tot out key seen;
  drop_table ivt;
}

#pop-options
