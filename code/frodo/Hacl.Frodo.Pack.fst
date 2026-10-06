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

(** Packing a matrix into [logq] bits per entry, and back.

    The reference implementation moves eight entries at a time through a
    128-bit shift register.  This one is bit-serial, which is what the
    specification says and which is the same code for every [logq]; the
    price is a division per bit, some ten milliseconds on Frodo-1344
    against roughly fifty for the lattice arithmetic around it.  A shift
    register would buy that back and is worth writing if packing ever shows
    up in a profile. *)
module Hacl.Frodo.Pack

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module M = Spec.Frodo.Matrix
module F = Spec.Frodo
module Math = FStar.Math.Lemmas

(** Every offset this module computes is bounded by [d * len], which is at
    most sixteen times ten thousand odd; the platform assumption that
    [size_t] holds thirty-two bits is enough for all of them. *)
let fits_small (x: nat) : Lemma (requires x < pow2 32) (ensures SZ.fits x) =
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits x

let bit_offset_bound (d: nat) (len: nat) (i: nat)
  : Lemma (requires len % 8 == 0 /\ i < d * (len / 8))
          (ensures 8 * i + 8 <= d * len)
  = Math.lemma_mult_le_right 8 (i + 1) (d * (len / 8));
    Math.paren_mul_right d (len / 8) 8;
    Math.euclidean_division_definition len 8

let pow2_small () : Lemma (pow2 1 == 2 /\ pow2 2 == 4 /\ pow2 3 == 8 /\ pow2 4 == 16 /\
                          pow2 5 == 32 /\ pow2 6 == 64 /\ pow2 7 == 128 /\ pow2 8 == 256) =
  assert_norm (pow2 1 == 2); assert_norm (pow2 2 == 4);
  assert_norm (pow2 3 == 8); assert_norm (pow2 4 == 16);
  assert_norm (pow2 5 == 32); assert_norm (pow2 6 == 64);
  assert_norm (pow2 7 == 128); assert_norm (pow2 8 == 256)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 0"

(** Bit [pos] of the packed stream: bit [d - 1 - pos mod d] of entry
    [pos / d], counting from the least significant. *)
fn pack_bit (m: A.array S16.t) (d: SZ.t { 0 < SZ.v d /\ SZ.v d <= 16 }) (len: SZ.t) (pos: SZ.t)
            (#p: perm) (#vm: erased (Seq.seq S16.t))
requires A.pts_to m #p vm **
         pure (Seq.length vm == SZ.v len /\ SZ.v d * SZ.v len < pow2 32)
returns b: S16.t
ensures A.pts_to m #p vm ** pure (S16.v b == F.pack_bit (SZ.v d) vm (SZ.v pos))
{
  A.pts_to_len m;
  fits_small (SZ.v d * SZ.v len);
  if (SZ.lt pos (SZ.mul d len)) {
    M.div_lt (SZ.v pos) (SZ.v len) (SZ.v d);
    let q = SZ.div pos d;
    let r = SZ.rem pos d;
    let sh = SZ.sub (SZ.sub d 1sz) r;
    let x = A.(m.(q));
    let y = S16.shift_right x (SZ.sizet_to_uint32 sh);
    S16.logand_mask_low y 1ul;
    S16.logand y (S16.mask_low 1ul)
  } else {
    S16.zero
  }
}

(** Eight of them, most significant first.  Written out rather than folded
    because the specification is written out, and because eight terms is
    less to prove about than a loop. *)
fn pack_byte (m: A.array S16.t) (d: SZ.t { 0 < SZ.v d /\ SZ.v d <= 16 }) (len: SZ.t) (i: SZ.t)
             (#p: perm) (#vm: erased (Seq.seq S16.t))
requires A.pts_to m #p vm **
         pure (Seq.length vm == SZ.v len /\ SZ.v d * SZ.v len < pow2 32 /\ 8 * SZ.v i + 8 <= SZ.v d * SZ.v len)
returns b: S8.t
ensures A.pts_to m #p vm ** pure (S8.v b == F.byte_val (SZ.v d) vm (SZ.v i))
{
  pow2_small ();
  fits_small (8 * SZ.v i + 8);
  fits_small (SZ.v i);
  let base = SZ.mul 8sz i;
  let b0 = pack_bit m d len base;
  let b1 = pack_bit m d len (SZ.add base 1sz);
  let b2 = pack_bit m d len (SZ.add base 2sz);
  let b3 = pack_bit m d len (SZ.add base 3sz);
  let b4 = pack_bit m d len (SZ.add base 4sz);
  let b5 = pack_bit m d len (SZ.add base 5sz);
  let b6 = pack_bit m d len (SZ.add base 6sz);
  let b7 = pack_bit m d len (SZ.add base 7sz);
  let a1 = S16.add_mod (S16.shift_left b0 7ul) (S16.shift_left b1 6ul);
  assert (pure (S16.v b0 < 2 /\ S16.v b1 < 2 /\ S16.v b2 < 2 /\ S16.v b3 < 2 /\
                S16.v b4 < 2 /\ S16.v b5 < 2 /\ S16.v b6 < 2 /\ S16.v b7 < 2));
  assert (pure (S16.v a1 == 128 * S16.v b0 + 64 * S16.v b1 /\ S16.v a1 <= 192));
  let a2 = S16.add_mod a1 (S16.shift_left b2 5ul);
  assert (pure (S16.v a2 == S16.v a1 + 32 * S16.v b2 /\ S16.v a2 <= 224));
  let a3 = S16.add_mod a2 (S16.shift_left b3 4ul);
  assert (pure (S16.v a3 == S16.v a2 + 16 * S16.v b3 /\ S16.v a3 <= 240));
  let a4 = S16.add_mod a3 (S16.shift_left b4 3ul);
  assert (pure (S16.v a4 == S16.v a3 + 8 * S16.v b4 /\ S16.v a4 <= 248));
  let a5 = S16.add_mod a4 (S16.shift_left b5 2ul);
  assert (pure (S16.v a5 == S16.v a4 + 4 * S16.v b5 /\ S16.v a5 <= 252));
  let a6 = S16.add_mod a5 (S16.shift_left b6 1ul);
  assert (pure (S16.v a6 == S16.v a5 + 2 * S16.v b6 /\ S16.v a6 <= 254));
  let a7 = S16.add_mod a6 b7;
  assert (pure (S16.v a7 == S16.v a6 + S16.v b7 /\ S16.v a7 < 256));
  let out = S16.lo a7;
  assert (pure (S8.v out == S16.v a7 % pow2 8));
  Math.small_mod (S16.v a7) (pow2 8);
  assert (pure (S8.v out == S16.v a7));
  out
}

(* [F.pack]'s shape lives in refinements on its return type and in the body of
   [Seq.init_ghost]; restating both as standalone lemmas keeps them available
   where the result is only applied. *)
let pack_len (d: pos { d <= 16 }) (len: nat { len % 8 == 0 }) (m: Seq.lseq S16.t len)
  : Lemma (Seq.length (F.pack d len m) == d * (len / 8))
          [SMTPat (F.pack d len m)]
  = ()

let pack_at (d: pos { d <= 16 }) (len: nat { len % 8 == 0 }) (m: Seq.lseq S16.t len)
            (i: nat { i < d * (len / 8) })
  : Lemma (S8.v (Seq.index (F.pack d len m) i) == F.byte_val d m i)
          [SMTPat (Seq.index (F.pack d len m) i)]
  = ()

(* One more byte of [F.pack] laid down; spelled out as a top-level lemma so the
   loop below does not have to re-derive it in a large context. *)
let pack_extend (d: pos { d <= 16 }) (m: Seq.seq S16.t) (s: Seq.seq S8.t)
                (x: S8.t) (i: nat { i < Seq.length s })
  : Lemma (requires (forall (k: nat). k < i ==>
                       S8.v (Seq.index s k) == F.byte_val d m k) /\
                    S8.v x == F.byte_val d m i)
          (ensures (forall (k: nat). k < i + 1 ==>
                      S8.v (Seq.index (Seq.upd s i x) k) == F.byte_val d m k))
  = ()

(** [out <- pack d m]. *)
fn pack (out: A.array S8.t) (m: A.array S16.t) (d: SZ.t { 0 < SZ.v d /\ SZ.v d <= 16 })
        (len: SZ.t { SZ.v len % 8 == 0 })
        (#p: perm) (#vo: erased (Seq.seq S8.t))
        (#vm: erased (Seq.lseq S16.t (SZ.v len)))
requires A.pts_to out vo ** A.pts_to m #p vm **
         pure (Seq.length vo == SZ.v d * (SZ.v len / 8) /\
               SZ.v d * SZ.v len < pow2 32)
ensures exists* v. A.pts_to out v ** A.pts_to m #p vm **
        pure (v == F.pack (SZ.v d) (SZ.v len) vm)
{
  A.pts_to_len out;
  A.pts_to_len m;
  fits_small (SZ.v d * SZ.v len);
  let n = SZ.mul d (SZ.div len 8sz);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to m #p vm **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          (forall (k: nat). k < SZ.v vi ==>
             S8.v (Seq.index v k) == F.byte_val (SZ.v d) vm k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    bit_offset_bound (SZ.v d) (SZ.v len) (SZ.v vi);
    let b = pack_byte m d len vi;
    with v0. assert (A.pts_to out v0);
    pack_extend (SZ.v d) vm v0 b (SZ.v vi);
    A.((out.(vi) <- b));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  assert (pure (Seq.length v == SZ.v d * (SZ.v len / 8) /\
                (forall (k: nat). k < SZ.v d * (SZ.v len / 8) ==>
                   S8.v (Seq.index v k) == F.byte_val (SZ.v d) vm k)));
  pack_len (SZ.v d) (SZ.v len) vm;
  Seq.lemma_eq_intro v (F.pack (SZ.v d) (SZ.v len) vm);
  assert (pure (v == F.pack (SZ.v d) (SZ.v len) vm));
}

(** {2 Unpacking}

    The same stream read the other way: [d] bits at a time, most
    significant first, each group becoming one entry. *)

fn stream_bit (b: A.array S8.t) (blen: SZ.t) (pos: SZ.t)
              (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (Seq.length vb == SZ.v blen)
returns x: S16.t
ensures A.pts_to b #p vb ** pure (S16.v x == F.stream_bit vb (SZ.v pos))
{
  A.pts_to_len b;
  let q = SZ.div pos 8sz;
  if (SZ.lt q blen) {
    let r = SZ.rem pos 8sz;
    let sh = SZ.sub 7sz r;
    let y = A.(b.(q));
    let z = S8.shift_right y (SZ.sizet_to_uint32 sh);
    Math.pow2_le_compat 16 8;
    let e = S16.of_bytes_le z (S8.classify 0uy);
    S16.logand_mask_low e 1ul;
    S16.logand e (S16.mask_low 1ul)
  } else {
    S16.zero
  }
}

fn unpack_entry (b: A.array S8.t) (blen: SZ.t) (d: SZ.t { 0 < SZ.v d /\ SZ.v d <= 16 }) (off: SZ.t)
                (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb **
         pure (Seq.length vb == SZ.v blen /\ SZ.v off + SZ.v d < pow2 32)
returns x: S16.t
ensures A.pts_to b #p vb ** pure (S16.v x == F.unpack_val vb (SZ.v off) (SZ.v d))
{
  fits_small (SZ.v off + SZ.v d);
  let mut acc = S16.zero;
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk d)
  invariant exists* (vk: SZ.t) (vacc: S16.t).
    pts_to k vk ** pts_to acc vacc ** A.pts_to b #p vb **
    pure (SZ.v vk <= SZ.v d /\ S16.v vacc == F.unpack_val vb (SZ.v off) (SZ.v vk))
  decreases (SZ.v d - SZ.v (!k))
  {
    let vk = !k;
    let vacc = !acc;
    let bit = stream_bit b blen (SZ.add off vk);
    Math.pow2_le_compat 16 (SZ.v vk + 1);
    acc := S16.add_mod (S16.add_mod vacc vacc) bit;
    k := SZ.add vk 1sz;
  };
  !acc
}

(** [m <- unpack d b]. *)
fn unpack (m: A.array S16.t) (b: A.array S8.t) (d: SZ.t { 0 < SZ.v d /\ SZ.v d <= 16 })
          (len: SZ.t { SZ.v len % 8 == 0 })
          (#p: perm) (#vm: erased (Seq.seq S16.t))
          (#vb: erased (Seq.lseq S8.t (SZ.v d * (SZ.v len / 8))))
requires A.pts_to m vm ** A.pts_to b #p vb **
         pure (Seq.length vm == SZ.v len /\ SZ.v d * SZ.v len < pow2 32)
ensures exists* v. A.pts_to m v ** A.pts_to b #p vb **
        pure (v == F.unpack (SZ.v d) (SZ.v len) vb)
{
  A.pts_to_len m;
  A.pts_to_len b;
  fits_small (SZ.v d * SZ.v len);
  let blen = SZ.mul d (SZ.div len 8sz);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to m v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             S16.v (Seq.index v k) == F.unpack_val vb (k * SZ.v d) (SZ.v d)))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (SZ.v d) (SZ.v vi + 1) (SZ.v len);
    fits_small (SZ.v vi * SZ.v d);
    let x = unpack_entry b blen d (SZ.mul vi d);
    A.((m.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to m v);
  assert (pure (Seq.length v == SZ.v len /\
                (forall (k: nat). k < SZ.v len ==>
                   S16.v (Seq.index v k) == F.unpack_val vb (k * SZ.v d) (SZ.v d))));
  Math.pow2_le_compat 16 (SZ.v d);
  Seq.lemma_eq_intro v (F.unpack (SZ.v d) (SZ.v len) vb);
  assert (pure (v == F.unpack (SZ.v d) (SZ.v len) vb));
}

#pop-options
