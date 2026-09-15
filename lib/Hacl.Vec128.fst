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
      [@@CPrologue vec_target; custard_c_closure_prologue vec_target ""]
    ]}

    which puts [__attribute__((target("aes,pclmul,ssse3,sse4.1")))] on that
    function and on every function it reaches -- and, by passing [""] as the
    shared prologue, on {i only} those reached exclusively through it.  A
    helper that baseline code also calls must not acquire the attribute, or it
    would fault on a machine without the instructions.

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

[@@custard_extern "Hacl_Vec128_shift_left_bytes_4"; custard_c_header "Hacl_Vec128.h"]
assume val shift_left_bytes_4 (a: t)
  : r: t { forall (k: int). 0 <= k /\ k < 128 ==>
                            CL.lebiti (bv r) k == CL.lebiti (bv a) (k - 32) }

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
