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

(** The 128-bit vector, and the AES and carry-less-multiply instructions.

    {2 What this module is}

    Everything here is an [assume val], and every one of them is realized by a
    C intrinsic in [c/Hacl_Vec128.h].  This is the second entry in the
    library's trusted computing base, after the entropy shim, and it is a much
    bigger one: the postcondition of [aesenc] {i is} the claim that the
    hardware's [AESENC] computes [Spec.AES.round], and nothing in F* can check
    that claim.

    Two things keep it honest.  First, each postcondition is written against
    the specification the rest of the library is verified against, not against
    a second model of the instruction -- so there is exactly one notion of
    what AES is, and the axiom either matches it or is visibly wrong.  Second,
    [tests/test_vec128.c] runs each axiom against the portable implementation
    on random inputs, which is real evidence and is the reason the axioms are
    stated in a form a test can evaluate.

    {2 Why it exists}

    [Hacl.AES.Core] computes the S-box as inversion in GF(2^8) followed by an
    affine map, because a table lookup at a secret index leaks through the
    cache.  That is correct and constant-time and about a megabyte a second.
    The AES instructions do a whole round in one instruction, in constant
    time, and are two orders of magnitude faster.  The portable path stays,
    because not every machine has them.

    {2 How a caller uses it}

    [supported ()] is a [__builtin_cpu_supports] check, and it is the only
    function here that may be called from ordinary code.  Everything else has
    to be reached from a function marked

    {[
      [@@CPrologue vec_target; custard_c_closure_prologue vec_target]
    ]}

    which puts [__attribute__((target("aes,pclmul,ssse3,sse4.1")))] on that
    function and on a copy of every function it reaches; the originals stay
    undecorated for baseline callers.  A helper that baseline code also calls
    must not acquire the attribute, or it would fault on a machine without the
    instructions.

    All of it is x86-64 only, and [c/Hacl_Vec128.h] defines nothing on any
    other target.  So that function also carries
    [custard_c_closure_guard "defined(__x86_64__)"], which compiles it and its
    copies only under that [#if], and the call to it -- and the call to
    [supported ()] that picks it -- sits in the [then] branch of a test of
    [Hacl.X64.x86_64]; see there.

    {2 The value of a vector}

    A [vec128] denotes sixteen secret bytes, in the order they occupy memory,
    which is the order [Spec.AES] uses for a block and the order GHASH's
    big-endian convention is applied to.  [vv] is that denotation and [bv] is
    it at the specification's level of secrecy. *)
module Hacl.Vec128

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module U32 = FStar.UInt32
module CL = Spec.CLMUL
module S32 = Hacl.Secret.UInt32
module SHANI = Spec.SHANI
module SHA1NI = Spec.SHA1NI
module CLess = Spec.CarryLess

(** {2 The type} *)

[@@custard_extern "Hacl_Vec128_t"; custard_c_header "Hacl_Vec128.h"]
assume val t : Type0

(** The sixteen bytes a vector holds, in memory order. *)
assume val vv (x: t) : GTot (Seq.lseq S8.t 16)

(** The same, as a [Spec.AES.block]. *)
let bv (x: t) : GTot block =
  let s = vv x in
  vals_len s;
  vals s

(** The target string that a function reaching this module must carry.  It is
    a literal rather than a definition at every use site so that the two
    spellings cannot drift apart. *)
unfold let vec_target : string = "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))"

(** {2 The run-time check}

    This is the only function in the module that a caller without the target
    attribute may call, and it is what makes the attribute safe on everything
    else.  On a machine or a target without the instructions it is [false] and
    the rest of the module is unreachable. *)

[@@custard_extern "Hacl_Vec128_supported"; custard_c_header "Hacl_Vec128.h"]
assume val supported (_: unit) : bool

(** {2 Memory}

    Both of these take a sixteen-byte array rather than an array and an
    offset: [Hacl.Impl.Sub.sub] already turns a longer array into one of
    these, and a length that is part of the type is one fewer precondition. *)

[@@custard_extern "Hacl_Vec128_load"; custard_c_header "Hacl_Vec128.h"]
assume val load (p: A.array S8.t) (#v: erased (Seq.lseq S8.t 16)) (#pm: perm)
  : stt t (requires A.pts_to p #pm v)
          (ensures fun r -> A.pts_to p #pm v ** pure (vv r == reveal v))

[@@custard_extern "Hacl_Vec128_store"; custard_c_header "Hacl_Vec128.h"]
assume val store (p: A.array S8.t) (x: t) (#v: erased (Seq.lseq S8.t 16))
  : stt unit (requires A.pts_to p v)
             (ensures fun _ -> A.pts_to p (vv x))

(** {2 Bitwise} *)

[@@custard_extern "Hacl_Vec128_zero"; custard_c_header "Hacl_Vec128.h"]
assume val zero (_: unit) : r: t { vv r == Seq.create 16 S8.zero }

(** Trusted, like [zero]: all-zero bytes are a vector. *)
[@@FStar.Tactics.Typeclasses.tcinstance]
assume val zeroable_t : Hacl.Zeroable.zeroable t

[@@custard_extern "Hacl_Vec128_xor"; custard_c_header "Hacl_Vec128.h"]
assume val vxor (a b: t) : r: t { bv r == xor_block (bv a) (bv b) }

(** {2 AES}

    [AESENC] is exactly [Spec.AES.round] and [AESENCLAST] exactly
    [Spec.AES.last_round], on a state and a round key both held in memory
    order.  Note the argument order: the instruction takes the state first and
    the key second, and the specification takes the key first. *)

[@@custard_extern "Hacl_Vec128_aesenc"; custard_c_header "Hacl_Vec128.h"]
assume val aesenc (st k: t) : r: t { bv r == round (bv k) (bv st) }

[@@custard_extern "Hacl_Vec128_aesenclast"; custard_c_header "Hacl_Vec128.h"]
assume val aesenclast (st k: t) : r: t { bv r == last_round (bv k) (bv st) }

(** [AESKEYGENASSIST] with a zero round constant.  The instruction computes
    [SubWord] of two of the four input words and [RotWord (SubWord _)] of the
    same two, exclusive-ored with the immediate; with the immediate zero the
    rotated copies carry no extra information and only the two plain ones are
    worth stating.  Of those, only the one taken from the top word is used
    here, so the axiom is written over the four bytes at offset twelve.

    This exists for the key schedule, whose [SubWord] is otherwise four
    evaluations of the algebraic S-box of [Hacl.AES.Core] --- around three
    hundred and fifty serially dependent operations each.  Nothing else in
    the library needs it: [aesenc] already has the S-box inside it. *)

[@@custard_extern "Hacl_Vec128_subword"; custard_c_header "Hacl_Vec128.h"]
assume val subword (a: t)
  : r: t { forall (i: nat). i < 4 ==>
             Seq.index (bv r) (8 + i) == sbox (Seq.index (bv a) (12 + i)) }

(** [SubWord] of the top word, rotated and copied into all four words: byte
    [i] of the result is byte [8 + ((i + 1) % 4)] of the argument.  Applied to
    [subword]'s result that is [rot_word (sub_word w3)] four times over, which
    is the term FIPS 197 adds to every word of a round key at a multiple of
    the key length.  One [PSHUFB] against a constant mask. *)

[@@custard_extern "Hacl_Vec128_bcast_rot"; custard_c_header "Hacl_Vec128.h"]
assume val bcast_rot (a: t)
  : r: t { (forall (i: nat). i < 16 ==>
              Seq.index (bv r) i == Seq.index (bv a) (8 + ((i + 1) % 4))) /\
           (forall (i: nat). 4 <= i /\ i < 16 ==>
              Seq.index (bv r) i == Seq.index (bv r) (i - 4)) }

(** The same without the rotation, which is what AES-256 wants halfway
    between its round-constant steps. *)

[@@custard_extern "Hacl_Vec128_bcast_sub"; custard_c_header "Hacl_Vec128.h"]
assume val bcast_sub (a: t)
  : r: t { (forall (i: nat). i < 16 ==>
              Seq.index (bv r) i == Seq.index (bv a) (8 + (i % 4))) /\
           (forall (i: nat). 4 <= i /\ i < 16 ==>
              Seq.index (bv r) i == Seq.index (bv r) (i - 4)) }

(** One byte in the low end of each of the four words and zero elsewhere.
    The round constant wants to meet a register, and this is two instructions
    rather than a store and a load. *)

[@@custard_extern "Hacl_Vec128_word_bcast"; custard_c_header "Hacl_Vec128.h"]
assume val word_bcast (x: S8.t)
  : r: t { (forall (i: nat). i < 16 ==>
              Seq.index (bv r) i == (if i % 4 = 0 then S8.v x else 0)) /\
           (forall (i: nat). 4 <= i /\ i < 16 ==>
              Seq.index (bv r) i == Seq.index (bv r) (i - 4)) }

(** {2 Carry-less multiplication}

    [PCLMULQDQ] multiplies one 64-bit lane of each operand, reading both as
    little-endian integers, and writes the 127-bit product into the whole
    register.  [Spec.CLMUL.lane] is that 64-bit operand as a polynomial and
    [Spec.CarryLess.conv] is the coefficient of [x^k] in the product, so each
    axiom is one line and each is a statement about polynomials rather than
    about a second model of the instruction.

    Note that the axioms are written with [Spec.CLMUL.lebiti], which is bit
    [k] for any integer [k] at all and [false] outside the register.  That
    makes every shift below a plain reindexing with no side condition. *)

[@@custard_extern "Hacl_Vec128_clmul_ll"; custard_c_header "Hacl_Vec128.h"]
assume val clmul_ll (a b: t)
  : r: t { forall (k: int). CL.lebiti (bv r) k ==
                            CLess.conv (CL.lane (bv a) false) (CL.lane (bv b) false) k }

[@@custard_extern "Hacl_Vec128_clmul_lh"; custard_c_header "Hacl_Vec128.h"]
assume val clmul_lh (a b: t)
  : r: t { forall (k: int). CL.lebiti (bv r) k ==
                            CLess.conv (CL.lane (bv a) false) (CL.lane (bv b) true) k }

[@@custard_extern "Hacl_Vec128_clmul_hl"; custard_c_header "Hacl_Vec128.h"]
assume val clmul_hl (a b: t)
  : r: t { forall (k: int). CL.lebiti (bv r) k ==
                            CLess.conv (CL.lane (bv a) true) (CL.lane (bv b) false) k }

[@@custard_extern "Hacl_Vec128_clmul_hh"; custard_c_header "Hacl_Vec128.h"]
assume val clmul_hh (a b: t)
  : r: t { forall (k: int). CL.lebiti (bv r) k ==
                            CLess.conv (CL.lane (bv a) true) (CL.lane (bv b) true) k }

(** {2 Shifts}

    A shift of the whole register by whole bytes is multiplication of the
    little-endian bit string by [x^(8n)], and the axiom says exactly that.
    The lane shifts do the same within each half, which is the one place the
    hardware's notion of "128-bit value" is not a single integer. *)

(** The four-byte shift is the key schedule's, not GHASH's, so it is stated a
    byte at a time: byte [i] of the result is byte [i - 4] of the argument,
    and zero where that is off the end.  The eight-byte shift below belongs to
    the multiplier and keeps the bit-level form. *)

[@@custard_extern "Hacl_Vec128_shift_left_bytes_4"; custard_c_header "Hacl_Vec128.h"]
assume val shift_left_bytes_4 (a: t)
  : r: t { forall (i: nat). i < 16 ==>
             Seq.index (bv r) i == (if i < 4 then 0 else Seq.index (bv a) (i - 4)) }

[@@custard_extern "Hacl_Vec128_shift_right_bytes_4"; custard_c_header "Hacl_Vec128.h"]
assume val shift_right_bytes_4 (a: t)
  : r: t { forall (k: int). 0 <= k /\ k < 128 ==>
                            CL.lebiti (bv r) k == CL.lebiti (bv a) (k + 32) }

[@@custard_extern "Hacl_Vec128_shift_left_bytes_8"; custard_c_header "Hacl_Vec128.h"]
assume val shift_left_bytes_8 (a: t)
  : r: t { forall (k: int). 0 <= k /\ k < 128 ==>
                            CL.lebiti (bv r) k == CL.lebiti (bv a) (k - 64) }

[@@custard_extern "Hacl_Vec128_shift_right_bytes_8"; custard_c_header "Hacl_Vec128.h"]
assume val shift_right_bytes_8 (a: t)
  : r: t { forall (k: int). 0 <= k /\ k < 128 ==>
                            CL.lebiti (bv r) k == CL.lebiti (bv a) (k + 64) }

[@@custard_extern "Hacl_Vec128_shift_left_lanes64"; custard_c_header "Hacl_Vec128.h"]
assume val shift_left_lanes64 (a: t) (n: U32.t { U32.v n < 64 })
  : r: t { forall (k: int). 0 <= k /\ k < 128 ==>
             CL.lebiti (bv r) k ==
               (k % 64 >= U32.v n && CL.lebiti (bv a) (k - U32.v n)) }

[@@custard_extern "Hacl_Vec128_shift_right_lanes64"; custard_c_header "Hacl_Vec128.h"]
assume val shift_right_lanes64 (a: t) (n: U32.t { U32.v n < 64 })
  : r: t { forall (k: int). 0 <= k /\ k < 128 ==>
             CL.lebiti (bv r) k ==
               (k % 64 + U32.v n < 64 && CL.lebiti (bv a) (k + U32.v n)) }

(** {2 Byte reversal}

    GHASH numbers the bits of a block from the top of byte zero downwards and
    the multiplier numbers them from the bottom of byte zero upwards, so every
    GHASH operand crosses this once on the way in and once on the way out.
    [Spec.CLMUL.bswap_lebit] is the statement that the round trip is a bit
    reversal, which is what makes [Spec.CarryLess.conv_rev] applicable. *)

[@@custard_extern "Hacl_Vec128_bswap"; custard_c_header "Hacl_Vec128.h"]
assume val bswap (a: t) : r: t { bv r == CL.bswap (bv a) }

(** {2 The GHASH reduction constant}

    [Spec.GF128.r_block] is [0xe1] followed by fifteen zero bytes, and the
    multiplication by it is two thirds of a GHASH multiply, so it is worth a
    register-materializing constant rather than a load from the stack. *)

[@@custard_extern "Hacl_Vec128_reduction"; custard_c_header "Hacl_Vec128.h"]
assume val reduction (_: unit) : r: t { bv r == Spec.GF128.r_block }

(** {2 SHA-256}

    A second instruction set, with a target and a feature test of its own: a
    machine may have AES without SHA or the other way round, and a function
    compiled for one must not be reached by a caller compiled for the other.
    [sha_target] is what [Hacl.Hash.SHA2.NI] carries and [sha_supported] is
    what guards it.

    The axioms below are stated with [Spec.SHANI], which reads a register as
    four 32-bit words and says what the packing is; they are claims about
    [Spec.SHA2] and not a second definition of the hash. *)

unfold let sha_target : string = "__attribute__((target(\"ssse3,sse4.1,sha\")))"

[@@custard_extern "Hacl_Vec128_sha_supported"; custard_c_header "Hacl_Vec128.h"]
assume val sha_supported (_: unit) : bool

(** {3 Memory, four words at a time}

    The SHA-2 state is an array of words, not of bytes, so these take one
    rather than the other.  [Spec.SHANI.lanes] is the register read as four
    words, lane zero lowest in memory, which is what a little-endian load of
    four [uint32_t]s gives. *)

[@@custard_extern "Hacl_Vec128_load32"; custard_c_header "Hacl_Vec128.h"]
assume val load32 (p: A.array S32.t) (#v: erased (Seq.lseq S32.t 4)) (#pm: perm)
  : stt t (requires A.pts_to p #pm v)
          (ensures fun r -> A.pts_to p #pm v ** pure (SHANI.lanes (vv r) == reveal v))

[@@custard_extern "Hacl_Vec128_store32"; custard_c_header "Hacl_Vec128.h"]
assume val store32 (p: A.array S32.t) (x: t) (#v: erased (Seq.lseq S32.t 4))
  : stt unit (requires A.pts_to p v)
             (ensures fun _ -> A.pts_to p (SHANI.lanes (vv x)))

(** {3 Lane arithmetic and permutation}

    Each of these is one instruction with one immediate, so there is one
    binding per immediate rather than one taking a selector, as for [clmul].
    The postconditions are written lane by lane; [Spec.SHANI.lane] numbers
    them from the low end. *)

[@@custard_extern "Hacl_Vec128_add32"; custard_c_header "Hacl_Vec128.h"]
assume val add32 (a b: t)
  : r: t { forall (i: nat). i < 4 ==>
             SHANI.lane (vv r) i ==
               S32.add_mod (SHANI.lane (vv a) i) (SHANI.lane (vv b) i) }

(** One in lane zero and zero elsewhere, the addend of the counter-mode
    increment.  [PADDD] does not carry between lanes, so adding this is
    [Spec.AES.inc32] on a byte-reversed counter block; [Hacl.AES.Counter]
    is where that is proved.  [PADDD] is SSE2, so neither
    this nor [add32] needs a target attribute, which is what lets the same
    binding serve the SHA-256 schedule and the AES counter. *)
[@@custard_extern "Hacl_Vec128_lane_one"; custard_c_header "Hacl_Vec128.h"]
assume val lane_one (_: unit)
  : r: t { S32.v (SHANI.lane (vv r) 0) == 1 /\
           S32.v (SHANI.lane (vv r) 1) == 0 /\
           S32.v (SHANI.lane (vv r) 2) == 0 /\
           S32.v (SHANI.lane (vv r) 3) == 0 }

(** [PSHUFD] with [0xB1]: exchange the lanes within each pair. *)
[@@custard_extern "Hacl_Vec128_shuffle_swap_pairs"; custard_c_header "Hacl_Vec128.h"]
assume val shuffle_swap_pairs (a: t)
  : r: t { SHANI.lane (vv r) 0 == SHANI.lane (vv a) 1 /\
           SHANI.lane (vv r) 1 == SHANI.lane (vv a) 0 /\
           SHANI.lane (vv r) 2 == SHANI.lane (vv a) 3 /\
           SHANI.lane (vv r) 3 == SHANI.lane (vv a) 2 }

(** [PSHUFD] with [0x1B]: reverse all four. *)
[@@custard_extern "Hacl_Vec128_shuffle_reverse"; custard_c_header "Hacl_Vec128.h"]
assume val shuffle_reverse (a: t)
  : r: t { SHANI.lane (vv r) 0 == SHANI.lane (vv a) 3 /\
           SHANI.lane (vv r) 1 == SHANI.lane (vv a) 2 /\
           SHANI.lane (vv r) 2 == SHANI.lane (vv a) 1 /\
           SHANI.lane (vv r) 3 == SHANI.lane (vv a) 0 }

(** [PSHUFD] with [0x0E]: bring the high pair down.  Only the low two lanes
    are ever read afterwards, but the instruction is total and the axiom says
    what it leaves in the other two. *)
[@@custard_extern "Hacl_Vec128_shuffle_high_pair"; custard_c_header "Hacl_Vec128.h"]
assume val shuffle_high_pair (a: t)
  : r: t { SHANI.lane (vv r) 0 == SHANI.lane (vv a) 2 /\
           SHANI.lane (vv r) 1 == SHANI.lane (vv a) 3 /\
           SHANI.lane (vv r) 2 == SHANI.lane (vv a) 0 /\
           SHANI.lane (vv r) 3 == SHANI.lane (vv a) 0 }

(** [PALIGNR] by four bytes: one word of [a] follows three of [b]. *)
[@@custard_extern "Hacl_Vec128_align_right_4"; custard_c_header "Hacl_Vec128.h"]
assume val align_right_4 (a b: t)
  : r: t { SHANI.lane (vv r) 0 == SHANI.lane (vv b) 1 /\
           SHANI.lane (vv r) 1 == SHANI.lane (vv b) 2 /\
           SHANI.lane (vv r) 2 == SHANI.lane (vv b) 3 /\
           SHANI.lane (vv r) 3 == SHANI.lane (vv a) 0 }

(** [PALIGNR] by eight bytes. *)
[@@custard_extern "Hacl_Vec128_align_right_8"; custard_c_header "Hacl_Vec128.h"]
assume val align_right_8 (a b: t)
  : r: t { SHANI.lane (vv r) 0 == SHANI.lane (vv b) 2 /\
           SHANI.lane (vv r) 1 == SHANI.lane (vv b) 3 /\
           SHANI.lane (vv r) 2 == SHANI.lane (vv a) 0 /\
           SHANI.lane (vv r) 3 == SHANI.lane (vv a) 1 }

(** [PBLENDW] with [0xF0]: the low pair from [a] and the high pair from [b]. *)
[@@custard_extern "Hacl_Vec128_blend_high"; custard_c_header "Hacl_Vec128.h"]
assume val blend_high (a b: t)
  : r: t { SHANI.lane (vv r) 0 == SHANI.lane (vv a) 0 /\
           SHANI.lane (vv r) 1 == SHANI.lane (vv a) 1 /\
           SHANI.lane (vv r) 2 == SHANI.lane (vv b) 2 /\
           SHANI.lane (vv r) 3 == SHANI.lane (vv b) 3 }

(** A load followed by [PSHUFB] with a fixed mask, which reverses the bytes
    within each word: a message block is read big-endian by FIPS 180-4 and
    the lanes are little-endian.  The two are bound together because the
    shuffle is never wanted on its own. *)
[@@custard_extern "Hacl_Vec128_load_be32"; custard_c_header "Hacl_Vec128.h"]
assume val load_be32 (p: A.array S8.t) (#v: erased (Seq.lseq S8.t 16)) (#pm: perm)
  : stt t (requires A.pts_to p #pm v)
          (ensures fun r -> A.pts_to p #pm v **
                            pure (SHANI.lanes (vv r) == Hacl.Spec.Bytes.words_from_be 4 v))

(** {3 The hash instructions} *)

(** [SHA256RNDS2]: two rounds.  The result is the new [ABEF]; the [ABEF] that
    went in is already the new [CDGH], which is why the two registers
    alternate and nothing is permuted between rounds.  The round input is
    [k + w], already summed, in the low two lanes of [k]. *)
[@@custard_extern "Hacl_Vec128_sha256rnds2"; custard_c_header "Hacl_Vec128.h"]
assume val sha256rnds2 (cdgh abef k: t)
  : r: t { SHANI.unpack (vv r) (vv abef) ==
             SHANI.round (SHANI.round (SHANI.unpack (vv abef) (vv cdgh))
                                      (SHANI.lane (vv k) 0))
                         (SHANI.lane (vv k) 1) }

(** [SHA256MSG1]: four [w + sigma0 w'] at once. *)
[@@custard_extern "Hacl_Vec128_sha256msg1"; custard_c_header "Hacl_Vec128.h"]
assume val sha256msg1 (a b: t)
  : r: t { forall (i: nat). i < 4 ==>
             SHANI.lane (vv r) i == SHANI.msg1 (vv a) (vv b) i }

(** [SHA256MSG2]: the [sigma1] half, serial within the group of four. *)
[@@custard_extern "Hacl_Vec128_sha256msg2"; custard_c_header "Hacl_Vec128.h"]
assume val sha256msg2 (a b: t)
  : r: t { forall (i: nat). i < 4 ==>
             SHANI.lane (vv r) i == SHANI.msg2 (vv a) (vv b) i }

(** {2 SHA-1}

    The same feature bit and the same target as SHA-256.  The axioms are
    stated with [Spec.SHA1NI]; the instructions keep the earliest word in
    the high lane. *)

[@@custard_extern "Hacl_Vec128_xor32"; custard_c_header "Hacl_Vec128.h"]
assume val xor32 (a b: t)
  : r: t { forall (i: nat). i < 4 ==>
             SHANI.lane (vv r) i == S32.logxor (SHANI.lane (vv a) i) (SHANI.lane (vv b) i) }

(** A word into the high lane, zero in the rest; and back out. *)
[@@custard_extern "Hacl_Vec128_high_lane"; custard_c_header "Hacl_Vec128.h"]
assume val high_lane (x: S32.t)
  : r: t { SHANI.lane (vv r) 3 == x /\ SHANI.lane (vv r) 2 == S32.zero /\
           SHANI.lane (vv r) 1 == S32.zero /\ SHANI.lane (vv r) 0 == S32.zero }

[@@custard_extern "Hacl_Vec128_get_high_lane"; custard_c_header "Hacl_Vec128.h"]
assume val get_high_lane (a: t) : r: S32.t { r == SHANI.lane (vv a) 3 }

(** [SHA1RNDS4], one binding per immediate. *)
[@@custard_extern "Hacl_Vec128_sha1rnds4_0"; custard_c_header "Hacl_Vec128.h"]
assume val sha1rnds4_0 (abcd w: t) : r: t { SHA1NI.rnds4_out 0 (vv abcd) (vv w) (vv r) }

[@@custard_extern "Hacl_Vec128_sha1rnds4_1"; custard_c_header "Hacl_Vec128.h"]
assume val sha1rnds4_1 (abcd w: t) : r: t { SHA1NI.rnds4_out 1 (vv abcd) (vv w) (vv r) }

[@@custard_extern "Hacl_Vec128_sha1rnds4_2"; custard_c_header "Hacl_Vec128.h"]
assume val sha1rnds4_2 (abcd w: t) : r: t { SHA1NI.rnds4_out 2 (vv abcd) (vv w) (vv r) }

[@@custard_extern "Hacl_Vec128_sha1rnds4_3"; custard_c_header "Hacl_Vec128.h"]
assume val sha1rnds4_3 (abcd w: t) : r: t { SHA1NI.rnds4_out 3 (vv abcd) (vv w) (vv r) }

[@@custard_extern "Hacl_Vec128_sha1nexte"; custard_c_header "Hacl_Vec128.h"]
assume val sha1nexte (a b: t)
  : r: t { forall (i: nat). i < 4 ==> SHANI.lane (vv r) i == SHA1NI.nexte (vv a) (vv b) i }

[@@custard_extern "Hacl_Vec128_sha1msg1"; custard_c_header "Hacl_Vec128.h"]
assume val sha1msg1 (a b: t)
  : r: t { forall (i: nat). i < 4 ==> SHANI.lane (vv r) i == SHA1NI.msg1 (vv a) (vv b) i }

[@@custard_extern "Hacl_Vec128_sha1msg2"; custard_c_header "Hacl_Vec128.h"]
assume val sha1msg2 (a b: t)
  : r: t { forall (i: nat). i < 4 ==> SHANI.lane (vv r) i == SHA1NI.msg2 (vv a) (vv b) i }
