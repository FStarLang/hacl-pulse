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

(** The incremental interface to Poly1305.

    The state is five flat arrays that the caller owns: the clamped
    multiplier [r] in [Hacl.Poly1305]'s nine-limb form, the five-limb
    accumulator, a copy of the thirty-two-byte key (for [s], which is only
    needed by [digest]), one block of buffered bytes, and a single [size_t]
    saying how many of those are in use.  No allocation, no error code and no
    length limit: the count is kept modulo sixteen, since nothing else
    depends on how much has been absorbed.

      void Hacl_Streaming_Poly1305_poly1305_init(uint64_t *r, uint64_t *acc,
        uint8_t *kb, uint8_t *buf, size_t *pos, uint8_t *key);

    Unlike a hash, Poly1305 treats a full block the same whether or not it is
    the last, so [update] absorbs every whole block as soon as it has one and
    keeps back at most fifteen bytes.  The whole blocks go through
    [Hacl.Poly1305.absorb_blocks], vector path and all; [digest] is the
    one-shot MAC's short last block, reduction and tag, run on a copy of the
    accumulator so the state stays usable.

    The key sits in the state, so [wipe] zeroes all of it, through
    [Hacl.Mem.wipe] so that the stores survive a [free] that follows.
    [init] overwrites everything that depends on the key.

    Ghostly, a state carries the key and the message absorbed since [init],
    which is what lets [digest] promise [Spec.Poly1305.poly1305]. *)
module Hacl.Streaming.Poly1305

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Poly1305.Field
open Hacl.Poly1305.Field
open Hacl.Poly1305.Load
open Hacl.Poly1305.Reduce
open Hacl.Poly1305
open Hacl.Impl.Copy
open Hacl.Spec.Chunks

module A = Pulse.Lib.Array
module Sub = Hacl.Impl.Sub
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module G = FStar.Ghost
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Spec = Spec.Poly1305
module SS = Spec.Poly1305.Streaming
module Mem = Hacl.Mem

(** {2 The state invariant} *)

(** The accumulator and the buffer, against everything absorbed so far: the
    accumulator holds the whole blocks, the buffer the bytes after them. *)
unfold let acc_ok (rv: nat) (vh: Seq.seq S64.t) (vbuf: Seq.seq S8.t) (seen: Seq.seq S8.t) =
  Seq.length vh == 5 /\ bounded vh 27 /\ Seq.length vbuf == 16 /\
  feval vh % prime == Spec.blocks_acc seen 0 (Seq.length seen / 16) rv 0 /\
  (forall (k: nat). k < Seq.length seen % 16 ==>
     Seq.index vbuf k == Seq.index seen (Seq.length seen / 16 * 16 + k))

unfold let r_ok (key: Seq.seq S8.t) (vr: Seq.seq S64.t) =
  Seq.length key == 32 /\
  Seq.length vr == 9 /\ bounded vr 26 /\ has5 vr /\ feval vr == Spec.r_of key

unfold let stream_ok (key: Seq.seq S8.t) (vr: Seq.seq S64.t) (vh: Seq.seq S64.t)
                     (vk: Seq.seq S8.t) (vbuf: Seq.seq S8.t) (vpos: Seq.seq SZ.t)
                     (seen: Seq.seq S8.t) =
  r_ok key vr /\ vk == key /\
  Seq.length vpos == 1 /\ SZ.v (Seq.index vpos 0) == Seq.length seen % 16 /\
  acc_ok (Spec.r_of key) vh vbuf seen

(** {2 Helpers} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn copy5 (dst: A.array S64.t) (src: A.array S64.t)
         (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
         pure (Seq.length vd == 5 /\ Seq.length vs == 5)
ensures exists* vd'. A.pts_to dst vd' ** A.pts_to src #ps vs ** pure (vd' == reveal vs)
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let x0 = A.(src.(0sz));
  let x1 = A.(src.(1sz));
  let x2 = A.(src.(2sz));
  let x3 = A.(src.(3sz));
  let x4 = A.(src.(4sz));
  A.((dst.(0sz) <- x0));
  A.((dst.(1sz) <- x1));
  A.((dst.(2sz) <- x2));
  A.((dst.(3sz) <- x3));
  A.((dst.(4sz) <- x4));
  with vd'. assert (A.pts_to dst vd');
  assert (pure (Seq.equal vd' vs));
}

#pop-options

(** The arithmetic of [update]'s three counts, out of the separation-logic
    query: [len seen1] is [nb] whole blocks and [tl] bytes. *)
let counts (lseen ldata p fill rest nfull tl: nat)
  : Lemma (requires p == lseen % 16 /\ p + fill == 16 /\ fill <= ldata /\
                    rest == ldata - fill /\ nfull == rest / 16 /\ tl == rest % 16)
          (ensures (lseen + ldata) / 16 == lseen / 16 + 1 + nfull /\
                   (lseen + ldata) % 16 == tl /\
                   (lseen / 16 + 1) * 16 == lseen + fill /\
                   (lseen / 16 + 1 + nfull) * 16 == lseen + ldata - tl /\
                   16 * (lseen / 16 + 1 + nfull) <= lseen + ldata)
  = Math.euclidean_division_definition lseen 16;
    Math.euclidean_division_definition rest 16;
    Math.lemma_mod_lt rest 16;
    let nb = lseen / 16 + 1 + nfull in
    assert (lseen + ldata == nb * 16 + tl);
    Math.lemma_div_plus tl nb 16;
    Math.lemma_mod_plus tl nb 16;
    Math.small_div tl 16;
    Math.small_mod tl 16

let counts_short (lseen ldata p: nat)
  : Lemma (requires p == lseen % 16 /\ p + ldata < 16)
          (ensures (lseen + ldata) / 16 == lseen / 16 /\
                   (lseen + ldata) % 16 == p + ldata)
  = Math.euclidean_division_definition lseen 16;
    Math.lemma_div_plus (p + ldata) (lseen / 16) 16;
    Math.lemma_mod_plus (p + ldata) (lseen / 16) 16;
    Math.small_div (p + ldata) 16;
    Math.small_mod (p + ldata) 16

(** {2 The two cases of [update]} *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 400"

(** The buffer has just been filled: absorb it, then whatever whole blocks of
    [data] follow, then keep the trailing bytes.  Split out of [update_impl]
    for the same reason as [Hacl.Hash.MD5.Streaming.update_full]: both cases
    in one query is more than the solver will take. *)
fn update_full (r: A.array S64.t) (acc: A.array S64.t)
               (d: A.array S64.t) (e: A.array S64.t)
               (buf: A.array S8.t) (pos: A.array SZ.t)
               (data: A.array S8.t) (dlen: SZ.t) (fill: SZ.t)
               (rv: erased nat) (seen: erased (Seq.seq S8.t)) (seen1: erased (Seq.seq S8.t))
               (#vr: erased (Seq.seq S64.t)) (#vh: erased (Seq.seq S64.t))
               (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
               (#vbuf: erased (Seq.seq S8.t)) (#vpos: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to r vr ** A.pts_to acc vh ** A.pts_to d vd ** A.pts_to e ve **
         A.pts_to buf vbuf ** A.pts_to pos vpos ** A.pts_to data #pd vdata **
         pure (Seq.length vr == 9 /\ bounded vr 26 /\ has5 vr /\ feval vr == reveal rv /\
               Seq.length vh == 5 /\ bounded vh 27 /\
               Seq.length vd == 5 /\ Seq.length ve == 5 /\
               Seq.length vbuf == 16 /\ Seq.length vpos == 1 /\
               reveal seen1 == Seq.append (reveal seen) (reveal vdata) /\
               Seq.length seen % 16 + SZ.v fill == 16 /\ SZ.v fill <= Seq.length vdata /\
               feval vh % prime ==
                 Spec.blocks_acc seen1 0 (Seq.length seen / 16) rv 0 /\
               (forall (k: nat). k < 16 ==>
                  Seq.index vbuf k == Seq.index seen1 (Seq.length seen / 16 * 16 + k)))
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t)
                (vbuf': Seq.seq S8.t) (vpos': Seq.seq SZ.t).
  A.pts_to r vr ** A.pts_to acc vh' ** A.pts_to d vd' ** A.pts_to e ve' **
  A.pts_to buf vbuf' ** A.pts_to pos vpos' ** A.pts_to data #pd vdata **
  pure (Seq.length vd' == 5 /\ Seq.length ve' == 5 /\
        Seq.length vpos' == 1 /\ SZ.v (Seq.index vpos' 0) == Seq.length seen1 % 16 /\
        acc_ok rv vh' vbuf' seen1)
{
  A.pts_to_len data;
  A.pts_to_len buf;
  Seq.lemma_len_append (reveal seen) (reveal vdata);
  let nb0 = G.hide (Seq.length seen / 16);
  let restlen = SZ.sub dlen fill;
  let nfull = SZ.div restlen 16sz;
  let tl = SZ.rem restlen 16sz;
  counts (Seq.length seen) (Seq.length vdata) (Seq.length seen % 16) (SZ.v fill)
         (SZ.v restlen) (SZ.v nfull) (SZ.v tl);

  (* The buffer, as block [nb0] of [seen1]. *)
  absorb_blocks acc r d e buf 1sz #_ #_ #_ #_ #_ #_
    #(hide (Spec.blocks_acc seen1 0 nb0 rv 0));
  SS.blocks_acc_extend seen1 vbuf nb0 1 rv 0;

  (* The whole blocks of [data] after the [fill] bytes that topped it up. *)
  Math.euclidean_division_definition (SZ.v restlen) 16;
  SZ.fits_lte (SZ.v nfull * 16) (SZ.v restlen);
  let hi = SZ.add fill (SZ.mul nfull 16sz);
  split3 (reveal vdata) (SZ.v fill) (SZ.v hi);
  let sub = Sub.sub data fill hi;
  with vsub. assert (A.pts_to sub #pd vsub);
  assert (pure (Seq.length vsub == SZ.v nfull * 16));
  tail_agrees 16 (reveal seen) (reveal vdata) (nb0 + 1) (SZ.v fill) (SZ.v nfull * 16);
  absorb_blocks acc r d e sub nfull #_ #_ #_ #_ #_ #_
    #(hide (Spec.blocks_acc seen1 0 (nb0 + 1) rv 0));
  SS.blocks_acc_extend seen1 vsub (nb0 + 1) (SZ.v nfull) rv 0;
  Sub.unsub_id data (SZ.v fill) (SZ.v hi) sub;

  (* And the bytes after those. *)
  tail_agrees 16 (reveal seen) (reveal vdata) (nb0 + 1 + SZ.v nfull)
              (SZ.v dlen - SZ.v tl) (SZ.v tl);
  copy_range buf 0sz data (SZ.sub dlen tl) tl;
  A.pts_to_len pos;
  A.((pos.(0sz) <- tl));
}

#pop-options

(** {2 The operations} *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"

(** Start a new message under [key]. *)
let init_facts (r: nat)
  : Lemma (Seq.length (Seq.empty #S8.t) / 16 == 0 /\ Seq.length (Seq.empty #S8.t) % 16 == 0 /\
           0 % Spec.Poly1305.Field.prime == 0 /\
           (forall (v: Seq.seq S64.t). bounded v 26 ==> bounded v 27))
  = Math.pow2_lt_compat 27 26;
    Math.small_mod 0 Spec.Poly1305.Field.prime

let buf_slice_eq (vbuf seen: Seq.seq S8.t) (p: nat)
  : Lemma (requires Seq.length vbuf == 16 /\ p == Seq.length seen % 16 /\
                    (forall (k: nat). k < Seq.length seen % 16 ==>
                       Seq.index vbuf k == Seq.index seen (Seq.length seen / 16 * 16 + k)))
          (ensures (let n = Seq.length seen / 16 in
                    16 * n + p == Seq.length seen /\
                    Seq.slice vbuf 0 p == Seq.slice seen (16 * n) (16 * n + p)))
  = let n = Seq.length seen / 16 in
    Math.euclidean_division_definition (Seq.length seen) 16;
    Math.lemma_mod_lt (Seq.length seen) 16;
    Math.swap_mul n 16;
    let s1 = Seq.slice vbuf 0 p in
    let s2 = Seq.slice seen (16 * n) (16 * n + p) in
    let aux (i: nat{i < p}) : Lemma (Seq.index s1 i == Seq.index s2 i) =
      assert (Seq.index vbuf i == Seq.index seen (n * 16 + i)) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s1 s2

fn init_impl (r: A.array S64.t) (acc: A.array S64.t) (kb: A.array S8.t)
             (buf: A.array S8.t) (pos: A.array SZ.t) (key: A.array S8.t)
             (#vr: erased (Seq.seq S64.t)) (#vh: erased (Seq.seq S64.t))
             (#vk: erased (Seq.seq S8.t)) (#vbuf: erased (Seq.seq S8.t))
             (#vpos: erased (Seq.seq SZ.t))
             (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to r vr ** A.pts_to acc vh ** A.pts_to kb vk **
         A.pts_to buf vbuf ** A.pts_to pos vpos ** A.pts_to key #pkey vkey **
         pure (Seq.length vr == 9 /\ Seq.length vh == 5 /\ Seq.length vk == 32 /\
               Seq.length vbuf == 16 /\ Seq.length vpos == 1 /\ Seq.length vkey == 32)
ensures exists* (vr': Seq.seq S64.t) (vh': Seq.seq S64.t) (vk': Seq.seq S8.t)
                (vpos': Seq.seq SZ.t).
  A.pts_to r vr' ** A.pts_to acc vh' ** A.pts_to kb vk' **
  A.pts_to buf vbuf ** A.pts_to pos vpos' ** A.pts_to key #pkey vkey **
  pure (stream_ok vkey vr' vh' vk' vbuf vpos' (Seq.empty #S8.t))
{
  A.pts_to_len pos;
  load_r r key;
  set_zero acc;
  copy_exact kb key 32sz;
  A.((pos.(0sz) <- 0sz));
  Math.pow2_lt_compat 27 26;
  SS.blocks_acc_zero (Seq.empty #S8.t) (Spec.r_of vkey) 0;
  init_facts (Spec.r_of vkey);
}

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 400"

(** Absorb [data]. *)
fn update_impl (r: A.array S64.t) (acc: A.array S64.t)
               (d: A.array S64.t) (e: A.array S64.t)
               (buf: A.array S8.t) (pos: A.array SZ.t)
               (data: A.array S8.t) (dlen: SZ.t)
               (rv: erased nat) (seen: erased (Seq.seq S8.t))
               (#vr: erased (Seq.seq S64.t)) (#vh: erased (Seq.seq S64.t))
               (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
               (#vbuf: erased (Seq.seq S8.t)) (#vpos: erased (Seq.seq SZ.t))
               (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to r vr ** A.pts_to acc vh ** A.pts_to d vd ** A.pts_to e ve **
         A.pts_to buf vbuf ** A.pts_to pos vpos ** A.pts_to data #pd vdata **
         pure (Seq.length vr == 9 /\ bounded vr 26 /\ has5 vr /\ feval vr == reveal rv /\
               Seq.length vd == 5 /\ Seq.length ve == 5 /\
               Seq.length vpos == 1 /\ SZ.v (Seq.index vpos 0) == Seq.length seen % 16 /\
               acc_ok rv vh vbuf seen)
         ** pure (SZ.v dlen == Seq.length vdata)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t)
                (vbuf': Seq.seq S8.t) (vpos': Seq.seq SZ.t).
  A.pts_to r vr ** A.pts_to acc vh' ** A.pts_to d vd' ** A.pts_to e ve' **
  A.pts_to buf vbuf' ** A.pts_to pos vpos' ** A.pts_to data #pd vdata **
  pure (Seq.length vd' == 5 /\ Seq.length ve' == 5 /\
        Seq.length vpos' == 1 /\
        SZ.v (Seq.index vpos' 0) == Seq.length (Seq.append seen vdata) % 16 /\
        acc_ok rv vh' vbuf' (Seq.append seen vdata))
{
  A.pts_to_len buf;
  A.pts_to_len pos;
  A.pts_to_len data;
  let p = A.(pos.(0sz));
  let fill = szmin (SZ.sub 16sz p) dlen;
  let seen1 = G.hide (Seq.append (reveal seen) (reveal vdata));
  Seq.lemma_len_append (reveal seen) (reveal vdata);
  Math.euclidean_division_definition (Seq.length seen) 16;
  Spec.blocks_acc_prefix (reveal seen) (reveal vdata) (Seq.length seen / 16) rv 0;

  copy_range buf p data 0sz fill;
  with vbuf1. assert (A.pts_to buf vbuf1);
  buf_agrees 16 (reveal seen) (reveal vdata) (reveal vbuf) (reveal vbuf1)
             (Seq.length seen / 16) (SZ.v p) (SZ.v fill);

  if (SZ.eq (SZ.add p fill) 16sz)
  {
    update_full r acc d e buf pos data dlen fill rv seen seen1;
  }
  else
  {
    (* All of [data] fitted in the buffer. *)
    counts_short (Seq.length seen) (Seq.length vdata) (SZ.v p);
    A.((pos.(0sz) <- SZ.add p dlen));
  }
}

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 400"

(** The tag of everything absorbed so far.  The state is left alone. *)
fn digest_impl (r: A.array S64.t) (acc: A.array S64.t) (kb: A.array S8.t)
               (buf: A.array S8.t) (pos: A.array SZ.t) (out: A.array S8.t)
               (d: A.array S64.t) (e: A.array S64.t) (t: A.array S64.t)
               (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
               (#vr: erased (Seq.seq S64.t))
               (#pa: perm) (#vh: erased (Seq.seq S64.t))
               (#pk: perm) (#vk: erased (Seq.seq S8.t))
               (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
               (#pp: perm) (#vpos: erased (Seq.seq SZ.t))
               (#vout: erased (Seq.seq S8.t))
               (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
               (#vt: erased (Seq.seq S64.t))
requires A.pts_to r vr ** A.pts_to acc #pa vh ** A.pts_to kb #pk vk **
         A.pts_to buf #pb vbuf ** A.pts_to pos #pp vpos ** A.pts_to out vout **
         A.pts_to d vd ** A.pts_to e ve ** A.pts_to t vt **
         pure (stream_ok key vr vh vk vbuf vpos seen /\ Seq.length vout == 16 /\
               Seq.length vd == 5 /\ Seq.length ve == 5 /\ Seq.length vt == 5)
ensures exists* (vout': Seq.seq S8.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t)
                (vt': Seq.seq S64.t).
  A.pts_to r vr ** A.pts_to acc #pa vh ** A.pts_to kb #pk vk **
  A.pts_to buf #pb vbuf ** A.pts_to pos #pp vpos ** A.pts_to out vout' **
  A.pts_to d vd' ** A.pts_to e ve' ** A.pts_to t vt' **
  pure (Seq.length key == 32 /\ vout' == Spec.poly1305 seen key)
{
  A.pts_to_len pos;
  let p = A.(pos.(0sz));
  let n = G.hide (Seq.length seen / 16);
  let rv = G.hide (Spec.r_of key);
  let a = G.hide (Spec.blocks_acc seen 0 n rv 0);
  Math.euclidean_division_definition (Seq.length seen) 16;
  Math.lemma_mod_lt (Seq.length seen) 16;

  copy5 t acc;
  absorb_tail t r d e buf 0sz p #_ #_ #_ #_ #_ #_ #a;
  with vt1. assert (A.pts_to t vt1);
  buf_slice_eq vbuf seen (SZ.v p);
  mac_tail seen rv n (SZ.v p) a (feval vt1);
  reduce t;
  store_tag out t kb;
}

#pop-options

(** {2 The public interface} *)

(** Start a new message under the thirty-two-byte [key].  Any previous
    contents of the state are overwritten. *)
fn poly1305_init (r: A.array S64.t) (acc: A.array S64.t) (kb: A.array S8.t)
                 (buf: A.array S8.t) (pos: A.array SZ.t) (key: A.array S8.t)
                 (#vr: erased (Seq.seq S64.t)) (#vh: erased (Seq.seq S64.t))
                 (#vk: erased (Seq.seq S8.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vpos: erased (Seq.seq SZ.t))
                 (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to r vr ** A.pts_to acc vh ** A.pts_to kb vk **
         A.pts_to buf vbuf ** A.pts_to pos vpos ** A.pts_to key #pkey vkey **
         pure (Seq.length vr == 9 /\ Seq.length vh == 5 /\ Seq.length vk == 32 /\
               Seq.length vbuf == 16 /\ Seq.length vpos == 1 /\ Seq.length vkey == 32)
ensures exists* (vr': Seq.seq S64.t) (vh': Seq.seq S64.t) (vk': Seq.seq S8.t)
                (vpos': Seq.seq SZ.t).
  A.pts_to r vr' ** A.pts_to acc vh' ** A.pts_to kb vk' **
  A.pts_to buf vbuf ** A.pts_to pos vpos' ** A.pts_to key #pkey vkey **
  pure (stream_ok vkey vr' vh' vk' vbuf vpos' (Seq.empty #S8.t))
{
  init_impl r acc kb buf pos key;
}

(** Absorb [data].  The ghost [key] and [seen] are the key the state was
    initialised with and everything absorbed since.  [kb] is not touched, so
    it is not passed: only its ghost contents [vk] appear. *)
fn poly1305_update (r: A.array S64.t) (acc: A.array S64.t)
                   (buf: A.array S8.t) (pos: A.array SZ.t)
                   (data: A.array S8.t) (data_len: SZ.t)
                   (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                   (#vr: erased (Seq.seq S64.t)) (#vh: erased (Seq.seq S64.t))
                   (#vk: erased (Seq.seq S8.t))
                   (#vbuf: erased (Seq.seq S8.t)) (#vpos: erased (Seq.seq SZ.t))
                   (#pd: perm) (#vdata: erased (Seq.seq S8.t))
requires A.pts_to r vr ** A.pts_to acc vh **
         A.pts_to buf vbuf ** A.pts_to pos vpos ** A.pts_to data #pd vdata **
         pure (stream_ok key vr vh vk vbuf vpos seen)
         ** pure (SZ.v data_len == Seq.length vdata)
ensures exists* (vh': Seq.seq S64.t) (vbuf': Seq.seq S8.t) (vpos': Seq.seq SZ.t).
  A.pts_to r vr ** A.pts_to acc vh' **
  A.pts_to buf vbuf' ** A.pts_to pos vpos' ** A.pts_to data #pd vdata **
  pure (stream_ok key vr vh' vk vbuf' vpos' (Seq.append seen vdata))
{
  let z = S64.zero;
  let mut darr = [| z; 5sz |];
  Mem.track darr;
  A.pts_to_len darr;
  let mut earr = [| z; 5sz |];
  Mem.track earr;
  A.pts_to_len earr;
  update_impl r acc darr earr buf pos data data_len (hide (Spec.r_of key)) seen;
  Mem.wipe earr 5sz;
  Mem.wipe darr 5sz;
}

(** Write the tag of everything absorbed so far to the sixteen bytes at
    [out].  The state is not consumed: digesting twice gives the same answer,
    and absorbing may continue afterwards. *)
fn poly1305_digest (r: A.array S64.t) (acc: A.array S64.t) (kb: A.array S8.t)
                   (buf: A.array S8.t) (pos: A.array SZ.t) (out: A.array S8.t)
                   (key: erased (Seq.seq S8.t)) (seen: erased (Seq.seq S8.t))
                   (#vr: erased (Seq.seq S64.t))
                   (#pa: perm) (#vh: erased (Seq.seq S64.t))
                   (#pk: perm) (#vk: erased (Seq.seq S8.t))
                   (#pb: perm) (#vbuf: erased (Seq.seq S8.t))
                   (#pp: perm) (#vpos: erased (Seq.seq SZ.t))
                   (#vout: erased (Seq.seq S8.t))
requires A.pts_to r vr ** A.pts_to acc #pa vh ** A.pts_to kb #pk vk **
         A.pts_to buf #pb vbuf ** A.pts_to pos #pp vpos ** A.pts_to out vout **
         pure (stream_ok key vr vh vk vbuf vpos seen /\ Seq.length vout == 16)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to r vr ** A.pts_to acc #pa vh ** A.pts_to kb #pk vk **
  A.pts_to buf #pb vbuf ** A.pts_to pos #pp vpos ** A.pts_to out vout' **
  pure (Seq.length key == 32 /\ vout' == Spec.poly1305 seen key)
{
  let z = S64.zero;
  let mut darr = [| z; 5sz |];
  Mem.track darr;
  A.pts_to_len darr;
  let mut earr = [| z; 5sz |];
  Mem.track earr;
  A.pts_to_len earr;
  let mut tarr = [| z; 5sz |];
  Mem.track tarr;
  A.pts_to_len tarr;
  digest_impl r acc kb buf pos out darr earr tarr key seen;
  Mem.wipe tarr 5sz;
  Mem.wipe earr 5sz;
  Mem.wipe darr 5sz;
}

(** Zero the whole state, key included.  Call it before releasing the
    memory; [Hacl.Mem.wipe]'s stores are not removed by an optimizer that
    sees a [free] coming. *)
fn poly1305_wipe (r: A.array S64.t) (acc: A.array S64.t) (kb: A.array S8.t)
                 (buf: A.array S8.t) (pos: A.array SZ.t)
                 (#vr: erased (Seq.seq S64.t)) (#vh: erased (Seq.seq S64.t))
                 (#vk: erased (Seq.seq S8.t)) (#vbuf: erased (Seq.seq S8.t))
                 (#vpos: erased (Seq.seq SZ.t))
requires A.pts_to r vr ** A.pts_to acc vh ** A.pts_to kb vk **
         A.pts_to buf vbuf ** A.pts_to pos vpos **
         pure (Seq.length vr == 9 /\ Seq.length vh == 5 /\ Seq.length vk == 32 /\
               Seq.length vbuf == 16 /\ Seq.length vpos == 1)
ensures exists* (vr': Seq.seq S64.t) (vh': Seq.seq S64.t) (vk': Seq.seq S8.t)
                (vbuf': Seq.seq S8.t) (vpos': Seq.seq SZ.t).
  A.pts_to r vr' ** A.pts_to acc vh' ** A.pts_to kb vk' **
  A.pts_to buf vbuf' ** A.pts_to pos vpos' **
  pure (Seq.length vr' == 9 /\ Seq.length vh' == 5 /\ Seq.length vk' == 32 /\
        Seq.length vbuf' == 16 /\ Seq.length vpos' == 1)
{
  A.pts_to_len r;
  A.pts_to_len acc;
  A.pts_to_len kb;
  A.pts_to_len buf;
  A.pts_to_len pos;
  Mem.track r;
  Mem.wipe r 9sz;
  Mem.track acc;
  Mem.wipe acc 5sz;
  Mem.track kb;
  Mem.wipe kb 32sz;
  Mem.track buf;
  Mem.wipe buf 16sz;
  A.((pos.(0sz) <- 0sz));
  A.pts_to_len r;
  A.pts_to_len acc;
  A.pts_to_len kb;
  A.pts_to_len buf;
}
