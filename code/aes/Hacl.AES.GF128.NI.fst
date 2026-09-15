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

(** GHASH's multiplication on the carry-less multiplier.

    [Hacl.AES.GF128.gmul_portable] is a hundred and twenty-eight shift-and-add
    steps, in constant time, and it is what runs everywhere.  This is the
    same function in about a dozen instructions, and it is what runs on a
    machine with [PCLMULQDQ].

    The whole computation is pure -- a [Hacl.Vec128.t] is a value, not a
    location -- so all of it but the load and the store is ordinary F*.  The
    shape is:

    - {b One product.}  [PCLMULQDQ] multiplies one 64-bit lane by one, so a
      128x128 product is four of them, assembled by
      [Spec.CLMUL.lo_of_lanes] and [Spec.CLMUL.hi_of_lanes].

    - {b One shift.}  The multiplier reads its operands little-endian and
      GHASH numbers its bits the other way round, so the operands are
      byte-reversed on the way in.  Reversal commutes with multiplication
      only up to one place -- [Spec.CarryLess.conv_rev] -- so the 256-bit
      result is shifted up by a bit before being reversed back.

    - {b Three times.}  What comes back is a 255-bit product, not a field
      element.  Its low half is already reduced and its high half has to be
      multiplied by [x^128], which is the reduction constant; that product's
      high half has degree at most six, and {i its} high half is empty.  So
      the same routine run three times is the entire multiplication, and
      [Spec.GF128.Poly.gmul_three] is the statement that the three low halves
      added together are the answer.

    [Hacl.AES.GMul.gmul_impl] picks between this and the portable version at
    run time. *)
module Hacl.AES.GF128.NI

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Vec = Hacl.Vec128
module CL = Spec.CLMUL
module CLess = Spec.CarryLess
module G = Spec.GF128
module Poly = Spec.GF128.Poly
module Classical = FStar.Classical

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Reading a register bit by bit} *)

let xor_bits (a b: Vec.t) (k: int)
  : Lemma (CL.lebiti (Vec.bv (Vec.vxor a b)) k ==
           (CL.lebiti (Vec.bv a) k <> CL.lebiti (Vec.bv b) k))
  = CL.xor_is_gadd (Vec.bv a) (Vec.bv b);
    CL.lexori (Vec.bv a) (Vec.bv b) k

let xor_block_bv (a b: Vec.t)
  : Lemma (Vec.bv (Vec.vxor a b) == G.gadd (Vec.bv a) (Vec.bv b))
  = CL.xor_is_gadd (Vec.bv a) (Vec.bv b)

(** Every register is a block, so its bits vanish outside the register. *)
let bounded_lebiti (a: Vec.t) : Lemma (CL.bounded (CL.lebiti (Vec.bv a))) = ()

(** {2 One shifted product}

    Given [x] and [y], the two halves of their carry-less product, brought
    back into GHASH's bit order.  Everything here is one instruction. *)

inline_for_extraction
let shifted_product (x y: Vec.t)
  : Pure (Vec.t & Vec.t) (requires True)
         (ensures fun r ->
            Poly.halves (Vec.bv x) (Vec.bv y) (Vec.bv (fst r)) (Vec.bv (snd r)))
  = let xa = Vec.bswap x in
    let yb = Vec.bswap y in

    (* Four multiplies, and the two crossed ones added together. *)
    let ll = Vec.clmul_ll xa yb in
    let lh = Vec.clmul_lh xa yb in
    let hl = Vec.clmul_hl xa yb in
    let hh = Vec.clmul_hh xa yb in
    let mid = Vec.vxor lh hl in
    let midlo = Vec.shift_left_bytes_8 mid in
    let midhi = Vec.shift_right_bytes_8 mid in
    let lo = Vec.vxor ll midlo in
    let hi = Vec.vxor hh midhi in

    Classical.forall_intro (xor_bits lh hl);
    Classical.forall_intro (xor_bits ll midlo);
    Classical.forall_intro (xor_bits hh midhi);
    CL.lo_of_lanes (Vec.bv x) (Vec.bv y) (Vec.bv ll) (Vec.bv mid) (Vec.bv lo);
    CL.hi_of_lanes (Vec.bv x) (Vec.bv y) (Vec.bv hh) (Vec.bv mid) (Vec.bv hi);

    (* The one-bit left shift of the 256-bit pair.  [c] and [d] carry the top
       bit of each low lane into the lane above it, and [c] additionally
       carries the top bit of [lo] into [hi]. *)
    let c = Vec.shift_right_lanes64 lo 63ul in
    let d = Vec.shift_right_lanes64 hi 63ul in
    let qlo = Vec.vxor (Vec.shift_left_lanes64 lo 1ul)
                       (Vec.shift_left_bytes_8 c) in
    let qhi = Vec.vxor (Vec.vxor (Vec.shift_left_lanes64 hi 1ul)
                                 (Vec.shift_left_bytes_8 d))
                       (Vec.shift_right_bytes_8 c) in

    Classical.forall_intro
      (xor_bits (Vec.shift_left_lanes64 lo 1ul) (Vec.shift_left_bytes_8 c));
    Classical.forall_intro
      (xor_bits (Vec.shift_left_lanes64 hi 1ul) (Vec.shift_left_bytes_8 d));
    Classical.forall_intro
      (xor_bits (Vec.vxor (Vec.shift_left_lanes64 hi 1ul)
                          (Vec.shift_left_bytes_8 d))
                (Vec.shift_right_bytes_8 c));
    CL.shift_lo (Vec.bv x) (Vec.bv y) (Vec.bv lo) (Vec.bv c) (Vec.bv qlo);
    CL.shift_hi (Vec.bv x) (Vec.bv y) (Vec.bv lo) (Vec.bv hi)
                (Vec.bv c) (Vec.bv d) (Vec.bv qhi);
    CL.clmul_halves (Vec.bv x) (Vec.bv y) (Vec.bv qlo) (Vec.bv qhi);

    (Vec.bswap qhi, Vec.bswap qlo)

(** {2 The multiplication} *)

inline_for_extraction
let gmul_vec (x y: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> Vec.bv r == G.gmul (Vec.bv x) (Vec.bv y))
  = let rc = Vec.reduction () in
    let p1 = shifted_product x y in
    let p2 = shifted_product (snd p1) rc in
    let p3 = shifted_product (snd p2) rc in
    Poly.gmul_three (Vec.bv x) (Vec.bv y)
                    (Vec.bv (fst p1)) (Vec.bv (snd p1))
                    (Vec.bv (fst p2)) (Vec.bv (snd p2))
                    (Vec.bv (fst p3)) (Vec.bv (snd p3));
    xor_block_bv (fst p2) (fst p3);
    xor_block_bv (fst p1) (Vec.vxor (fst p2) (fst p3));
    Vec.vxor (fst p1) (Vec.vxor (fst p2) (fst p3))

(** {2 The driver} *)

(** Refinement subtyping does not cross [erased], so the sixteen-byte window
    a load wants is reached through an explicit coercion. *)
let as_blk (s: Seq.seq S8.t { Seq.length s == blocklen })
  : Pure (Seq.lseq S8.t blocklen) (requires True) (ensures fun r -> r == s)
  = s

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn gmul_ni (a: A.array S8.t) (h: A.array S8.t)
           (#va #vh: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen)
ensures exists* (va': Seq.seq S8.t). A.pts_to a va' ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  Seq.length va' == blocklen /\
  vals va' == G.gmul (vals va) (vals vh))
{
  A.pts_to_len a;
  A.pts_to_len h;
  let x = Vec.load a #(as_blk va);
  let y = Vec.load h #(as_blk vh);
  let r = gmul_vec x y;
  Vec.store a r #(as_blk va);
  vals_len (Vec.vv r);
  ()
}

#pop-options
