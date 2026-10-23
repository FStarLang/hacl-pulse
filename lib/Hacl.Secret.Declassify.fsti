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

(** Turning a secret back into a value the program may look at.

    Every use of this module is a place where the constant-time argument stops
    being a typing property and becomes a claim someone has to check.  There
    should be very few of them, they should be easy to find -- grepping for
    this module name finds all of them -- and each should be accompanied by an
    argument for why the value is not secret after all.

    Legitimate uses look like: a public length that was computed with secret
    arithmetic; the result of a constant-time tag comparison, which is a single
    bit the caller is entitled to; a value that a standard says is transmitted
    in the clear. *)
module Hacl.Secret.Declassify

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SA = Hacl.Secret.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

val u8 (x: S8.t) : r: U8.t { U8.v r == S8.v x }
val u32 (x: S32.t) : r: U32.t { U32.v r == S32.v x }
val u64 (x: S64.t) : r: U64.t { U64.v r == S64.v x }

(** The common case: a mask produced by [eq_mask] or [gte_mask] is one bit of
    information the caller asked for, and this is how that bit is delivered.
    Stated at 8 bits because that is the width every tag comparison is
    accumulated at. *)
val bool_of_mask (mask: S8.t)
  : Pure bool
      (requires S8.v mask == 0 \/ S8.v mask == pow2 8 - 1)
      (ensures fun b -> b <==> S8.v mask == pow2 8 - 1)

(** {2 Sequences and buffers}

    The inverse of [S8.classify_seq] and [Hacl.Secret.Array.to_secret], for
    clients that keep their data in public-byte buffers and lend them to the
    library through [Hacl.Secret.Array.secret].  Apply them only to bytes
    that are public by design -- a MAC, a ciphertext, a public key -- or to
    the caller's own data being handed back. *)

val u8_seq (s: Seq.seq S8.t) : r: Seq.seq U8.t { Seq.length r == Seq.length s }

val u8_seq_index (s: Seq.seq S8.t) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (u8_seq s) i == u8 (Seq.index s i))
          [SMTPat (Seq.index (u8_seq s) i)]

val u8_seq_slice (s: Seq.seq S8.t) (i: nat) (j: nat { i <= j /\ j <= Seq.length s })
  : Lemma (Seq.slice (u8_seq s) i j == u8_seq (Seq.slice s i j))
          [SMTPat (Seq.slice (u8_seq s) i j)]

val u8_seq_append (s1 s2: Seq.seq S8.t)
  : Lemma (u8_seq (Seq.append s1 s2) == Seq.append (u8_seq s1) (u8_seq s2))
          [SMTPat (u8_seq (Seq.append s1 s2))]

val u8_seq_classify_seq (s: Seq.seq U8.t)
  : Lemma (u8_seq (S8.classify_seq s) == s) [SMTPat (u8_seq (S8.classify_seq s))]

val classify_seq_u8_seq (s: Seq.seq S8.t)
  : Lemma (S8.classify_seq (u8_seq s) == s) [SMTPat (S8.classify_seq (u8_seq s))]

(** Give back a buffer lent with [Hacl.Secret.Array.to_secret], its contents
    now readable as public bytes. *)
ghost fn of_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq S8.t))
  requires A.pts_to (SA.secret a) #p s
  ensures A.pts_to a #p (u8_seq s)
