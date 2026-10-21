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

(** The key schedule's [SubWord], on whichever implementation the machine has.

    The AES key schedule applies the S-box to four bytes at a time, and the
    portable S-box of [Hacl.AES.Core] is the algebraic one: an inverse in
    GF(2^8) computed as [a^254] by fifteen field multiplications, each of
    which is seven [xtime]s and eight conditional exclusive-ors.  That is
    somewhere around three hundred and fifty operations, and because each
    depends on the one before it is also around three hundred and fifty
    cycles.  A table would be four cycles, but the key schedule's input is
    the key, so a table would be a cache-timing oracle on the key and is not
    an option.

    Expanding an AES-128 key needs forty of these S-boxes and an AES-256 key
    fifty-two, so the schedule alone costs about fourteen thousand cycles --
    which is the whole cost of a short AES-GCM call, several times over.

    [AESKEYGENASSIST] does four S-boxes in one instruction, in constant time,
    and is exactly what the hardware provides for this.  The round constant
    it also exclusive-ors in is left as zero and applied afterwards in the
    ordinary way, so that one binding serves every round rather than one per
    immediate.

    The dispatch is per word, so thirteen perfectly predicted branches for a
    whole key schedule.  Both branches leave the same specification value
    behind and no caller can tell which ran. *)
module Hacl.AES.SubWord

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Vec = Hacl.Vec128

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Refinement subtyping does not cross [erased], so the sixteen-byte window
    a load wants is reached through an explicit coercion.  This is the same
    coercion as [Hacl.AES.NI.as_blk] and exists twice only because neither
    module should depend on the other. *)
let as_blk (s: Seq.seq S8.t { Seq.length s == blocklen })
  : Pure (Seq.lseq S8.t blocklen) (requires True) (ensures fun r -> r == s)
  = s

(** The axiom's postcondition is a quantified statement about [subword a],
    which does not survive Pulse's binding of the result to a variable at
    [--ifuel 0].  This lemma is the one instance of it that is wanted, in a
    pure context where the refinement is still visible. *)
let subword_index (a: Vec.t) (i: nat { i < 4 })
  : Lemma (Seq.index (Vec.bv (Vec.subword a)) (8 + i) ==
           sbox (Seq.index (Vec.bv a) (12 + i)))
  = ()

(** {2 The fast path}

    The scratch array is the caller's rather than this function's because a
    key schedule calls it thirteen times and one sixteen-byte frame is
    cheaper than thirteen.  Only bytes twelve to fifteen are written and only
    bytes eight to eleven are read; the other eight hold whatever the caller
    left there, which is why the postcondition says nothing about them. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn subword_ni (s: A.array S8.t) (x0 x1 x2 x3: S8.t)
              (#vs: erased (Seq.seq S8.t))
requires A.pts_to s vs ** pure (Seq.length vs == blocklen)
ensures exists* (vs': Seq.seq S8.t). A.pts_to s vs' ** pure (
  Seq.length vs' == blocklen /\
  Seq.index (vals vs') 8 == sbox (S8.v x0) /\
  Seq.index (vals vs') 9 == sbox (S8.v x1) /\
  Seq.index (vals vs') 10 == sbox (S8.v x2) /\
  Seq.index (vals vs') 11 == sbox (S8.v x3))
{
  A.pts_to_len s;
  A.((s.(12sz) <- x0));
  A.((s.(13sz) <- x1));
  A.((s.(14sz) <- x2));
  A.((s.(15sz) <- x3));
  with v. assert A.pts_to s v;
  A.pts_to_len s;
  assert (pure (Seq.index v 12 == x0 /\ Seq.index v 13 == x1 /\
                Seq.index v 14 == x2 /\ Seq.index v 15 == x3));
  vals_index v 12; vals_index v 13; vals_index v 14; vals_index v 15;
  let a = Vec.load s #(as_blk v);
  let r = Vec.subword a;
  assert (pure (Vec.bv a == vals v));
  subword_index a 0; subword_index a 1; subword_index a 2; subword_index a 3;
  assert (pure (Seq.index (Vec.bv r) 8 == sbox (Seq.index (vals v) 12) /\
                Seq.index (Vec.bv r) 9 == sbox (Seq.index (vals v) 13) /\
                Seq.index (Vec.bv r) 10 == sbox (Seq.index (vals v) 14) /\
                Seq.index (Vec.bv r) 11 == sbox (Seq.index (vals v) 15)));
  Vec.store s r #(as_blk v);
  assert (pure (Vec.bv r == vals (Vec.vv r)));
}

(** {2 The portable path} *)

fn subword_portable (s: A.array S8.t) (x0 x1 x2 x3: S8.t)
                    (#vs: erased (Seq.seq S8.t))
requires A.pts_to s vs ** pure (Seq.length vs == blocklen)
ensures exists* (vs': Seq.seq S8.t). A.pts_to s vs' ** pure (
  Seq.length vs' == blocklen /\
  Seq.index (vals vs') 8 == sbox (S8.v x0) /\
  Seq.index (vals vs') 9 == sbox (S8.v x1) /\
  Seq.index (vals vs') 10 == sbox (S8.v x2) /\
  Seq.index (vals vs') 11 == sbox (S8.v x3))
{
  A.pts_to_len s;
  A.((s.(8sz) <- sbox_impl x0));
  A.((s.(9sz) <- sbox_impl x1));
  A.((s.(10sz) <- sbox_impl x2));
  A.((s.(11sz) <- sbox_impl x3));
  with v. assert A.pts_to s v;
  A.pts_to_len s;
  vals_index v 8; vals_index v 9; vals_index v 10; vals_index v 11;
}

(** {2 The dispatcher} *)

fn subword4 (s: A.array S8.t) (x0 x1 x2 x3: S8.t)
            (#vs: erased (Seq.seq S8.t))
requires A.pts_to s vs ** pure (Seq.length vs == blocklen)
ensures exists* (vs': Seq.seq S8.t). A.pts_to s vs' ** pure (
  Seq.length vs' == blocklen /\
  Seq.index (vals vs') 8 == sbox (S8.v x0) /\
  Seq.index (vals vs') 9 == sbox (S8.v x1) /\
  Seq.index (vals vs') 10 == sbox (S8.v x2) /\
  Seq.index (vals vs') 11 == sbox (S8.v x3))
{
  if (Hacl.X64.x86_64) {
    if Vec.supported () {
      subword_ni s x0 x1 x2 x3;
    } else {
      subword_portable s x0 x1 x2 x3;
    }
  } else {
    subword_portable s x0 x1 x2 x3;
  }
}

#pop-options
