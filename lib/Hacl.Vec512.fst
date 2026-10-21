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

(** The 512-bit vector, as sixteen thirty-two-bit lanes: AVX-512F.

    {2 What this module is}

    The same thing as [Hacl.Vec256], twice as wide: every binding is an
    [assume val] realized by one intrinsic in [c/Hacl_Vec512.h], is
    therefore trusted computing base, and is checked against a scalar
    transcription by [tests/test_vec512.c].  Only what ChaCha20 needs is
    here.

    {2 Why it exists}

    [Hacl.Chacha20.Vec512] runs sixteen ChaCha20 blocks at once, one per
    lane.  Two things make it more than a wider [Hacl.Chacha20.Vec256].
    AVX-512 has a rotate instruction, [VPROLD], so each of the four rotations
    in a quarter round is one instruction rather than a shuffle or three.
    And it has thirty-two registers, so the sixteen-word state and the
    temporaries never leave them.

    {2 How a caller uses it}

    As for [Hacl.Vec256]: [supported ()] is the only function that may be
    called from ordinary code, and everything else must be reached from a
    function carrying [CPrologue avx512_target] and
    [custard_c_closure_prologue avx512_target], and since all of it is x86-64
    only, also [custard_c_closure_guard "defined(__x86_64__)"], with its
    callers testing [Hacl.X64.x86_64] first.

    {2 The value of a vector}

    Sixty-four secret bytes in memory order, [vv], whose lanes are the
    sixteen little-endian words, by definition.  A ChaCha20 block is exactly
    one register. *)
module Hacl.Vec512

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

(** {2 The type} *)

[@@custard_extern "Hacl_Vec512_t"; custard_c_header "Hacl_Vec512.h"]
assume val t : Type0

(** The sixty-four bytes a vector holds, in memory order. *)
assume val vv (x: t) : GTot (Seq.lseq S8.t 64)

(** The same, as sixteen little-endian words: lane [i] is bytes [4i .. 4i+3]. *)
let lanes (x: t) : GTot (Seq.lseq S32.t 16) =
  words_from_le #S32.t 16 (vv x)

let lane (x: t) (i: nat { i < 16 }) : GTot S32.t = Seq.index (lanes x) i

(** The target string that a function reaching this module must carry. *)
unfold let avx512_target : string = "__attribute__((target(\"avx512f\")))"

(** {2 The run-time check} *)

[@@custard_extern "Hacl_Vec512_supported"; custard_c_header "Hacl_Vec512.h"]
assume val supported (_: unit) : bool

(** {2 Memory}

    Sixty-four bytes, unaligned, in both directions. *)

[@@custard_extern "Hacl_Vec512_load"; custard_c_header "Hacl_Vec512.h"]
assume val load (p: A.array S8.t) (#v: erased (Seq.lseq S8.t 64)) (#pm: perm)
  : stt t (requires A.pts_to p #pm v)
          (ensures fun r -> A.pts_to p #pm v ** pure (vv r == reveal v))

[@@custard_extern "Hacl_Vec512_store"; custard_c_header "Hacl_Vec512.h"]
assume val store (p: A.array S8.t) (x: t) (#v: erased (Seq.lseq S8.t 64))
  : stt unit (requires A.pts_to p v)
             (ensures fun _ -> A.pts_to p (vv x))

(** {2 Constants} *)

[@@custard_extern "Hacl_Vec512_zero"; custard_c_header "Hacl_Vec512.h"]
assume val zero (_: unit) : r: t { forall (i: nat). i < 16 ==> lane r i == S32.zero }

(** The same word in all sixteen lanes: [VPBROADCASTD]. *)
[@@custard_extern "Hacl_Vec512_bcast"; custard_c_header "Hacl_Vec512.h"]
assume val bcast (x: S32.t) : r: t { forall (i: nat). i < 16 ==> lane r i == x }

(** Lane [i] holds [i]. *)
[@@custard_extern "Hacl_Vec512_iota"; custard_c_header "Hacl_Vec512.h"]
assume val iota (_: unit) : r: t { forall (i: nat). i < 16 ==> S32.v (lane r i) == i }

(** {2 Lane arithmetic} *)

[@@custard_extern "Hacl_Vec512_add32"; custard_c_header "Hacl_Vec512.h"]
assume val add32 (a b: t)
  : r: t { forall (i: nat). i < 16 ==> lane r i == S32.add_mod (lane a i) (lane b i) }

(** Stated on bytes and on lanes, as in [Hacl.Vec256]. *)
[@@custard_extern "Hacl_Vec512_xor"; custard_c_header "Hacl_Vec512.h"]
assume val vxor (a b: t)
  : r: t { (forall (i: nat). i < 64 ==>
              Seq.index (vv r) i == S8.logxor (Seq.index (vv a) i) (Seq.index (vv b) i)) /\
           (forall (i: nat). i < 16 ==> lane r i == S32.logxor (lane a i) (lane b i)) }

(** [VPROLD]: one instruction for every distance. *)
[@@custard_extern "Hacl_Vec512_rotl"; custard_c_header "Hacl_Vec512.h"]
assume val rotl (a: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 32 })
  : r: t { forall (i: nat). i < 16 ==> lane r i == S32.rotate_left (lane a i) s }

(** {2 Permutations}

    The four unpacks work within each of the four 128-bit groups
    independently, exactly as their AVX2 namesakes do within each of two;
    the four [VSHUFI32X4] selections then move whole groups.  Together they
    are a 16 x 16 transpose of thirty-two-bit words; see
    [Hacl.Chacha20.Vec512]. *)

[@@custard_extern "Hacl_Vec512_unpacklo32"; custard_c_header "Hacl_Vec512.h"]
assume val unpacklo32 (a b: t)
  : r: t { lane r 0 == lane a 0 /\ lane r 1 == lane b 0 /\ lane r 2 == lane a 1 /\ lane r 3 == lane b 1 /\
           lane r 4 == lane a 4 /\ lane r 5 == lane b 4 /\ lane r 6 == lane a 5 /\ lane r 7 == lane b 5 /\
           lane r 8 == lane a 8 /\ lane r 9 == lane b 8 /\ lane r 10 == lane a 9 /\ lane r 11 == lane b 9 /\
           lane r 12 == lane a 12 /\ lane r 13 == lane b 12 /\ lane r 14 == lane a 13 /\ lane r 15 == lane b 13 }

[@@custard_extern "Hacl_Vec512_unpackhi32"; custard_c_header "Hacl_Vec512.h"]
assume val unpackhi32 (a b: t)
  : r: t { lane r 0 == lane a 2 /\ lane r 1 == lane b 2 /\ lane r 2 == lane a 3 /\ lane r 3 == lane b 3 /\
           lane r 4 == lane a 6 /\ lane r 5 == lane b 6 /\ lane r 6 == lane a 7 /\ lane r 7 == lane b 7 /\
           lane r 8 == lane a 10 /\ lane r 9 == lane b 10 /\ lane r 10 == lane a 11 /\ lane r 11 == lane b 11 /\
           lane r 12 == lane a 14 /\ lane r 13 == lane b 14 /\ lane r 14 == lane a 15 /\ lane r 15 == lane b 15 }

[@@custard_extern "Hacl_Vec512_unpacklo64"; custard_c_header "Hacl_Vec512.h"]
assume val unpacklo64 (a b: t)
  : r: t { lane r 0 == lane a 0 /\ lane r 1 == lane a 1 /\ lane r 2 == lane b 0 /\ lane r 3 == lane b 1 /\
           lane r 4 == lane a 4 /\ lane r 5 == lane a 5 /\ lane r 6 == lane b 4 /\ lane r 7 == lane b 5 /\
           lane r 8 == lane a 8 /\ lane r 9 == lane a 9 /\ lane r 10 == lane b 8 /\ lane r 11 == lane b 9 /\
           lane r 12 == lane a 12 /\ lane r 13 == lane a 13 /\ lane r 14 == lane b 12 /\ lane r 15 == lane b 13 }

[@@custard_extern "Hacl_Vec512_unpackhi64"; custard_c_header "Hacl_Vec512.h"]
assume val unpackhi64 (a b: t)
  : r: t { lane r 0 == lane a 2 /\ lane r 1 == lane a 3 /\ lane r 2 == lane b 2 /\ lane r 3 == lane b 3 /\
           lane r 4 == lane a 6 /\ lane r 5 == lane a 7 /\ lane r 6 == lane b 6 /\ lane r 7 == lane b 7 /\
           lane r 8 == lane a 10 /\ lane r 9 == lane a 11 /\ lane r 10 == lane b 10 /\ lane r 11 == lane b 11 /\
           lane r 12 == lane a 14 /\ lane r 13 == lane a 15 /\ lane r 14 == lane b 14 /\ lane r 15 == lane b 15 }

(** [VSHUFI32X4] with [0x44]: 128-bit groups 0 and 1 of [a], then 0 and 1 of [b]. *)
[@@custard_extern "Hacl_Vec512_sel_lo"; custard_c_header "Hacl_Vec512.h"]
assume val sel_lo (a b: t)
  : r: t { lane r 0 == lane a 0 /\ lane r 1 == lane a 1 /\ lane r 2 == lane a 2 /\ lane r 3 == lane a 3 /\
           lane r 4 == lane a 4 /\ lane r 5 == lane a 5 /\ lane r 6 == lane a 6 /\ lane r 7 == lane a 7 /\
           lane r 8 == lane b 0 /\ lane r 9 == lane b 1 /\ lane r 10 == lane b 2 /\ lane r 11 == lane b 3 /\
           lane r 12 == lane b 4 /\ lane r 13 == lane b 5 /\ lane r 14 == lane b 6 /\ lane r 15 == lane b 7 }

(** [VSHUFI32X4] with [0xEE]: 128-bit groups 2 and 3 of [a], then 2 and 3 of [b]. *)
[@@custard_extern "Hacl_Vec512_sel_hi"; custard_c_header "Hacl_Vec512.h"]
assume val sel_hi (a b: t)
  : r: t { lane r 0 == lane a 8 /\ lane r 1 == lane a 9 /\ lane r 2 == lane a 10 /\ lane r 3 == lane a 11 /\
           lane r 4 == lane a 12 /\ lane r 5 == lane a 13 /\ lane r 6 == lane a 14 /\ lane r 7 == lane a 15 /\
           lane r 8 == lane b 8 /\ lane r 9 == lane b 9 /\ lane r 10 == lane b 10 /\ lane r 11 == lane b 11 /\
           lane r 12 == lane b 12 /\ lane r 13 == lane b 13 /\ lane r 14 == lane b 14 /\ lane r 15 == lane b 15 }

(** [VSHUFI32X4] with [0x88]: 128-bit groups 0 and 2 of [a], then 0 and 2 of [b]. *)
[@@custard_extern "Hacl_Vec512_sel_even"; custard_c_header "Hacl_Vec512.h"]
assume val sel_even (a b: t)
  : r: t { lane r 0 == lane a 0 /\ lane r 1 == lane a 1 /\ lane r 2 == lane a 2 /\ lane r 3 == lane a 3 /\
           lane r 4 == lane a 8 /\ lane r 5 == lane a 9 /\ lane r 6 == lane a 10 /\ lane r 7 == lane a 11 /\
           lane r 8 == lane b 0 /\ lane r 9 == lane b 1 /\ lane r 10 == lane b 2 /\ lane r 11 == lane b 3 /\
           lane r 12 == lane b 8 /\ lane r 13 == lane b 9 /\ lane r 14 == lane b 10 /\ lane r 15 == lane b 11 }

(** [VSHUFI32X4] with [0xDD]: 128-bit groups 1 and 3 of [a], then 1 and 3 of [b]. *)
[@@custard_extern "Hacl_Vec512_sel_odd"; custard_c_header "Hacl_Vec512.h"]
assume val sel_odd (a b: t)
  : r: t { lane r 0 == lane a 4 /\ lane r 1 == lane a 5 /\ lane r 2 == lane a 6 /\ lane r 3 == lane a 7 /\
           lane r 4 == lane a 12 /\ lane r 5 == lane a 13 /\ lane r 6 == lane a 14 /\ lane r 7 == lane a 15 /\
           lane r 8 == lane b 4 /\ lane r 9 == lane b 5 /\ lane r 10 == lane b 6 /\ lane r 11 == lane b 7 /\
           lane r 12 == lane b 12 /\ lane r 13 == lane b 13 /\ lane r 14 == lane b 14 /\ lane r 15 == lane b 15 }
