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

(** The 256-bit vector, as eight thirty-two-bit lanes: AVX2.

    {2 What this module is}

    Like [Hacl.Vec128], everything here is an [assume val] realized by an
    intrinsic in [c/Hacl_Vec256.h], and is therefore trusted computing base.
    Each binding is one instruction, and each postcondition is stated against
    the secret-integer operations the rest of the library is verified with --
    [S32.add_mod], [S32.logxor], [S32.rotate_left] -- rather than against a
    second model of the instruction.  [tests/test_vec256.c] evaluates every
    one of them against a scalar transcription on random inputs.

    {2 Why it exists}

    ChaCha20 is a stream cipher whose blocks are independent, so eight of them
    can be computed at once, one per lane, by exactly the instructions the
    scalar block function uses.  That is what [Hacl.Chacha20.Vec256] does.
    The only operations it needs beyond lane-wise arithmetic are the
    shuffles that turn eight blocks held a word per register into eight
    blocks held contiguously, which is what the six permutations at the end
    of this module are for.

    {2 How a caller uses it}

    Exactly as for [Hacl.Vec128]: [supported ()] is the only function that
    may be called from ordinary code, and everything else must be reached
    from a function carrying [CPrologue avx2_target] and
    [custard_c_closure_prologue avx2_target].

    {2 The value of a vector}

    A vector denotes thirty-two secret bytes in memory order, [vv].  Its
    lanes are those bytes read as eight little-endian words, which is what
    x86 means by a lane, so [lanes] is a definition and not an axiom.  The
    load, the store and the exclusive-or are stated on bytes, because that is
    what a message is; the arithmetic is stated on lanes, because that is what
    ChaCha20 is.  [vxor] is stated both ways: it is the one instruction both
    sides use, and saying so is cheaper than proving that a bitwise operation
    commutes with the little-endian reading of a word. *)
module Hacl.Vec256

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64

(** {2 The type} *)

[@@custard_extern "Hacl_Vec256_t"; custard_c_header "Hacl_Vec256.h"]
assume val t : Type0

(** The thirty-two bytes a vector holds, in memory order. *)
assume val vv (x: t) : GTot (Seq.lseq S8.t 32)

(** The same, as eight little-endian words: lane [i] is bytes [4i .. 4i+3]. *)
let lanes (x: t) : GTot (Seq.lseq S32.t 8) =
  words_from_le #S32.t 8 (vv x)

let lane (x: t) (i: nat { i < 8 }) : GTot S32.t = Seq.index (lanes x) i

(** The target string that a function reaching this module must carry. *)
unfold let avx2_target : string = "__attribute__((target(\"avx2\")))"

(** {2 The run-time check} *)

[@@custard_extern "Hacl_Vec256_supported"; custard_c_header "Hacl_Vec256.h"]
assume val supported (_: unit) : bool

(** {2 Memory}

    Thirty-two bytes, unaligned, in both directions. *)

[@@custard_extern "Hacl_Vec256_load"; custard_c_header "Hacl_Vec256.h"]
assume val load (p: A.array S8.t) (#v: erased (Seq.lseq S8.t 32)) (#pm: perm)
  : stt t (requires A.pts_to p #pm v)
          (ensures fun r -> A.pts_to p #pm v ** pure (vv r == reveal v))

[@@custard_extern "Hacl_Vec256_store"; custard_c_header "Hacl_Vec256.h"]
assume val store (p: A.array S8.t) (x: t) (#v: erased (Seq.lseq S8.t 32))
  : stt unit (requires A.pts_to p v)
             (ensures fun _ -> A.pts_to p (vv x))

(** {2 Constants} *)

[@@custard_extern "Hacl_Vec256_zero"; custard_c_header "Hacl_Vec256.h"]
assume val zero (_: unit) : r: t { forall (i: nat). i < 8 ==> lane r i == S32.zero }

(** The same word in all eight lanes: [VPBROADCASTD]. *)
[@@custard_extern "Hacl_Vec256_bcast"; custard_c_header "Hacl_Vec256.h"]
assume val bcast (x: S32.t) : r: t { forall (i: nat). i < 8 ==> lane r i == x }

(** Lane [i] holds [i]: what is added to a broadcast block counter to give
    eight consecutive ones. *)
[@@custard_extern "Hacl_Vec256_iota"; custard_c_header "Hacl_Vec256.h"]
assume val iota (_: unit) : r: t { forall (i: nat). i < 8 ==> S32.v (lane r i) == i }

(** {2 Lane arithmetic} *)

[@@custard_extern "Hacl_Vec256_add32"; custard_c_header "Hacl_Vec256.h"]
assume val add32 (a b: t)
  : r: t { forall (i: nat). i < 8 ==> lane r i == S32.add_mod (lane a i) (lane b i) }

(** Stated twice, on bytes and on lanes; see the module comment. *)
[@@custard_extern "Hacl_Vec256_xor"; custard_c_header "Hacl_Vec256.h"]
assume val vxor (a b: t)
  : r: t { (forall (i: nat). i < 32 ==>
              Seq.index (vv r) i == S8.logxor (Seq.index (vv a) i) (Seq.index (vv b) i)) /\
           (forall (i: nat). i < 8 ==> lane r i == S32.logxor (lane a i) (lane b i)) }

(** A rotation of every lane by the same distance.  The distance is an
    argument rather than part of the name because every call site passes a
    literal; [c/Hacl_Vec256.h] turns sixteen and eight into a byte shuffle and
    anything else into two shifts and an or. *)
[@@custard_extern "Hacl_Vec256_rotl"; custard_c_header "Hacl_Vec256.h"]
assume val rotl (a: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 32 })
  : r: t { forall (i: nat). i < 8 ==> lane r i == S32.rotate_left (lane a i) s }

(** {2 Permutations}

    The four unpacks work within each 128-bit half independently, which is
    why each axiom is two groups of four; the two cross-half permutes then
    pick one half from each operand.  Together they are an 8 x 8 transpose
    of thirty-two-bit words; see [Hacl.Chacha20.Vec256]. *)

[@@custard_extern "Hacl_Vec256_unpacklo32"; custard_c_header "Hacl_Vec256.h"]
assume val unpacklo32 (a b: t)
  : r: t { lane r 0 == lane a 0 /\ lane r 1 == lane b 0 /\
           lane r 2 == lane a 1 /\ lane r 3 == lane b 1 /\
           lane r 4 == lane a 4 /\ lane r 5 == lane b 4 /\
           lane r 6 == lane a 5 /\ lane r 7 == lane b 5 }

[@@custard_extern "Hacl_Vec256_unpackhi32"; custard_c_header "Hacl_Vec256.h"]
assume val unpackhi32 (a b: t)
  : r: t { lane r 0 == lane a 2 /\ lane r 1 == lane b 2 /\
           lane r 2 == lane a 3 /\ lane r 3 == lane b 3 /\
           lane r 4 == lane a 6 /\ lane r 5 == lane b 6 /\
           lane r 6 == lane a 7 /\ lane r 7 == lane b 7 }

[@@custard_extern "Hacl_Vec256_unpacklo64"; custard_c_header "Hacl_Vec256.h"]
assume val unpacklo64 (a b: t)
  : r: t { lane r 0 == lane a 0 /\ lane r 1 == lane a 1 /\
           lane r 2 == lane b 0 /\ lane r 3 == lane b 1 /\
           lane r 4 == lane a 4 /\ lane r 5 == lane a 5 /\
           lane r 6 == lane b 4 /\ lane r 7 == lane b 5 }

[@@custard_extern "Hacl_Vec256_unpackhi64"; custard_c_header "Hacl_Vec256.h"]
assume val unpackhi64 (a b: t)
  : r: t { lane r 0 == lane a 2 /\ lane r 1 == lane a 3 /\
           lane r 2 == lane b 2 /\ lane r 3 == lane b 3 /\
           lane r 4 == lane a 6 /\ lane r 5 == lane a 7 /\
           lane r 6 == lane b 6 /\ lane r 7 == lane b 7 }

(** [VPERM2I128] with [0x20]: the low half of [a], then the low half of [b]. *)
[@@custard_extern "Hacl_Vec256_lo128"; custard_c_header "Hacl_Vec256.h"]
assume val lo128 (a b: t)
  : r: t { lane r 0 == lane a 0 /\ lane r 1 == lane a 1 /\
           lane r 2 == lane a 2 /\ lane r 3 == lane a 3 /\
           lane r 4 == lane b 0 /\ lane r 5 == lane b 1 /\
           lane r 6 == lane b 2 /\ lane r 7 == lane b 3 }

(** [VPERM2I128] with [0x31]: the high half of [a], then the high half of [b]. *)
[@@custard_extern "Hacl_Vec256_hi128"; custard_c_header "Hacl_Vec256.h"]
assume val hi128 (a b: t)
  : r: t { lane r 0 == lane a 4 /\ lane r 1 == lane a 5 /\
           lane r 2 == lane a 6 /\ lane r 3 == lane a 7 /\
           lane r 4 == lane b 4 /\ lane r 5 == lane b 5 /\
           lane r 6 == lane b 6 /\ lane r 7 == lane b 7 }

(** {2 Four sixty-four-bit lanes}

    Poly1305 runs four interleaved accumulators, one per sixty-four-bit
    lane, in radix [2^26].  A sixty-four-bit lane is two thirty-two-bit ones,
    low first, which is a definition; so the unpacks and permutes above are
    already statements about it.  The arithmetic is stated on natural
    numbers, with the wrap-around written out, so that the field code can
    reason about limbs without going through [UInt64]. *)

let lane64 (x: t) (i: nat { i < 4 }) : GTot nat =
  S32.v (lane x (2 * i)) + pow2 32 * S32.v (lane x (2 * i + 1))

[@@custard_extern "Hacl_Vec256_add64"; custard_c_header "Hacl_Vec256.h"]
assume val add64 (a b: t)
  : r: t { forall (i: nat). i < 4 ==> lane64 r i == (lane64 a i + lane64 b i) % pow2 64 }

(** [VPMULUDQ]: the low thirty-two bits of each lane, multiplied out to
    sixty-four. *)
[@@custard_extern "Hacl_Vec256_mul32"; custard_c_header "Hacl_Vec256.h"]
assume val mul32 (a b: t)
  : r: t { forall (i: nat). i < 4 ==>
             lane64 r i == (lane64 a i % pow2 32) * (lane64 b i % pow2 32) }

[@@custard_extern "Hacl_Vec256_shr64"; custard_c_header "Hacl_Vec256.h"]
assume val shr64 (a: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 })
  : r: t { forall (i: nat). i < 4 ==> lane64 r i == lane64 a i / pow2 (U32.v s) }

[@@custard_extern "Hacl_Vec256_shl64"; custard_c_header "Hacl_Vec256.h"]
assume val shl64 (a: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 })
  : r: t { forall (i: nat). i < 4 ==>
             lane64 r i == (lane64 a i * pow2 (U32.v s)) % pow2 64 }

(** [VPAND] with [2^26 - 1] in every sixty-four-bit lane. *)
[@@custard_extern "Hacl_Vec256_mask26"; custard_c_header "Hacl_Vec256.h"]
assume val mask26 (a: t)
  : r: t { forall (i: nat). i < 4 ==> lane64 r i == lane64 a i % pow2 26 }

[@@custard_extern "Hacl_Vec256_bcast64"; custard_c_header "Hacl_Vec256.h"]
assume val bcast64 (x: S64.t)
  : r: t { forall (i: nat). i < 4 ==> lane64 r i == S64.v x }

(** Four words, lane zero first. *)
[@@custard_extern "Hacl_Vec256_set64"; custard_c_header "Hacl_Vec256.h"]
assume val set64 (x0 x1 x2 x3: S64.t)
  : r: t { lane64 r 0 == S64.v x0 /\ lane64 r 1 == S64.v x1 /\
           lane64 r 2 == S64.v x2 /\ lane64 r 3 == S64.v x3 }

(** The four lanes to four words of memory, unaligned. *)
[@@custard_extern "Hacl_Vec256_store64"; custard_c_header "Hacl_Vec256.h"]
assume val store64 (p: A.array S64.t) (x: t) (#v: erased (Seq.seq S64.t))
  : stt unit (requires A.pts_to p v ** pure (Seq.length v == 4))
             (ensures fun _ -> exists* (v': Seq.seq S64.t). A.pts_to p v' **
                pure (Seq.length v' == 4 /\
                      (forall (i: nat). i < 4 ==> S64.v (Seq.index v' i) == lane64 x i)))
