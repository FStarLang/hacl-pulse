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

(** The Poly1305 one-time authenticator, as specified in RFC 8439.

    The specification is arithmetic on natural numbers: there are no limbs
    here, and no secret integers except in the byte sequences that come in and
    go out.  Everything the implementation does with five twenty-six-bit limbs
    is justified against this, in [Hacl.Poly1305.Field].

    Clamping is written the way RFC 8439 writes it -- as a mask on four
    particular bytes of the key -- rather than as one 128-bit [logand].  The
    two are the same, but the byte form is what an implementation can do
    limb by limb without a bit-level argument.

    As in [Spec.Blake2], the message is viewed as blocks without ever building
    the block sequence: [block_of] computes the [i]th block directly out of
    the message, so the implementation's loop invariant never has to mention a
    [Seq.append]. *)
module Spec.Poly1305

open Hacl.Spec.Loops
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

(** {2 The field} *)

let prime : pos = pow2 130 - 5

let size_block = 16
let size_key = 32
let size_tag = 16

(** {2 The key}

    A Poly1305 key is thirty-two bytes: the first sixteen become the
    multiplier [r], after clamping, and the last sixteen the additive part
    [s]. *)

(** RFC 8439's clamp: bytes 3, 7, 11 and 15 keep their low four bits, and
    bytes 4, 8 and 12 lose their low two. *)
let clamp_byte (i: nat { i < 16 }) (b: S8.t) : S8.t =
  if i % 4 = 3 then S8.logand b (S8.classify 0x0fuy)
  else if i % 4 = 0 && i > 0 then S8.logand b (S8.classify 0xfcuy)
  else b

let clamp (rb: Seq.lseq S8.t 16) : Seq.lseq S8.t 16 =
  Seq.init 16 (fun i -> clamp_byte i (Seq.index rb i))

let r_of (k: Seq.lseq S8.t 32) : GTot nat =
  le_nat_bound (clamp (Seq.slice k 0 16));
  le_nat (clamp (Seq.slice k 0 16))

let s_of (k: Seq.lseq S8.t 32) : GTot nat =
  le_nat_bound (Seq.slice k 16 32);
  le_nat (Seq.slice k 16 32)

(** {2 Blocks}

    A block contributes its little-endian value plus a one placed just above
    its top byte -- for a full block that is [2^128], for a short final block
    it is lower.  That extra bit is what stops a message from being extended
    with zero bytes. *)

let block_val (b: Seq.seq S8.t { Seq.length b <= 16 }) : GTot nat =
  le_nat_bound b;
  le_nat b + pow2 (8 * Seq.length b)

let block_val_bound (b: Seq.seq S8.t { Seq.length b <= 16 })
  : Lemma (block_val b < pow2 129)
  = le_nat_bound b;
    Math.pow2_le_compat 128 (8 * Seq.length b);
    Math.pow2_le_compat 128 (8 * Seq.length b)

(** The number of blocks, and the [i]th one, computed straight out of the
    message. *)
let nblocks (len: nat) : nat = (len + 15) / 16

let block_len (len: nat) (i: nat { i < nblocks len }) : n: nat { 1 <= n /\ n <= 16 } =
  Math.euclidean_division_definition (len + 15) 16;
  Math.lemma_mod_lt (len + 15) 16;
  Math.lemma_mult_le_left 16 (i + 1) (nblocks len);
  if 16 * i + 16 <= len then 16 else len - 16 * i

let block_of (msg: Seq.seq S8.t) (i: nat { i < nblocks (Seq.length msg) })
  : b: Seq.seq S8.t { Seq.length b == block_len (Seq.length msg) i }
  = Seq.slice msg (16 * i) (16 * i + block_len (Seq.length msg) i)

(** [repeati_g] hands its step function every natural number, so the block
    view has to be total; out of range it is the empty sequence, which the
    fold never reaches. *)
let block_at (msg: Seq.seq S8.t) (i: nat) : b: Seq.seq S8.t { Seq.length b <= 16 } =
  if i < nblocks (Seq.length msg) then block_of msg i else Seq.empty

(** {2 The accumulator} *)

let update (r: nat) (acc: nat) (b: Seq.seq S8.t { Seq.length b <= 16 }) : GTot nat =
  ((acc + block_val b) * r) % prime

let poly (msg: Seq.seq S8.t) (r: nat) : GTot nat =
  repeati_g (nblocks (Seq.length msg))
            (fun i acc -> update r acc (block_at msg i))
            0

(** {2 The tag}

    The accumulator, plus [s], truncated to sixteen little-endian bytes. *)

let finish (acc: nat) (s: nat) : GTot (Seq.lseq S8.t 16) =
  nat_to_le 16 ((acc + s) % pow2 128)

let poly1305 (msg: Seq.seq S8.t) (k: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 16) =
  finish (poly msg (r_of k)) (s_of k)

(** {2 Facts about the block view}

    Exactly the shape [Spec.Blake2] needed: the last block is the only short
    one, and the block count is what the implementation's loop runs to. *)

let nblocks_bound (len: nat) : Lemma (16 * nblocks len < len + 16) =
  Math.euclidean_division_definition (len + 15) 16;
  Math.lemma_mod_lt (len + 15) 16

let nblocks_full (len: nat) (i: nat { i < nblocks len })
  : Lemma (requires i + 1 < nblocks len) (ensures block_len len i == 16)
  = Math.lemma_mult_le_left 16 (i + 2) (nblocks len);
    nblocks_bound len

let block_bound (len: nat) (i: nat { i < nblocks len })
  : Lemma (16 * i + block_len len i <= len)
  = nblocks_bound len;
    Math.lemma_mult_le_left 16 (i + 1) (nblocks len)

(** {2 Clamping, pointwise}

    [clamp] is a [Seq.init], so an implementation that masks seven particular
    bytes has to be matched against it index by index.  These two lemmas are
    that match: the first says what one index of the result is, and the
    second lifts sixteen of those to the sequence. *)

let clamp_index (rb: Seq.lseq S8.t 16) (i: nat { i < 16 })
  : Lemma (Seq.index (clamp rb) i == clamp_byte i (Seq.index rb i))
  = ()

let clamp_eq (rb: Seq.lseq S8.t 16) (vt: Seq.seq S8.t)
  : Lemma (requires Seq.length vt == 16 /\
                    (forall (i: nat). i < 16 ==>
                       Seq.index vt i == clamp_byte i (Seq.index rb i)))
          (ensures vt == clamp rb)
  = Seq.lemma_eq_intro vt (clamp rb)

(** The block count as a division and a remainder, which is how the
    implementation runs it: a loop over the full blocks and then, if there is
    a remainder, one short block. *)
let nblocks_split (len: nat)
  : Lemma (nblocks len == len / 16 + (if len % 16 = 0 then 0 else 1))
  = Math.euclidean_division_definition len 16;
    Math.lemma_mod_lt len 16;
    if len % 16 = 0 then Math.division_multiplication_lemma len 16 1
