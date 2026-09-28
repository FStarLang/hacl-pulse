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
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Sub = Hacl.Impl.Sub
module Vec = Hacl.Vec128
module CL = Spec.CLMUL
module CLess = Spec.CarryLess
module G = Spec.GF128
module Poly = Spec.GF128.Poly
module Alg = Spec.GF128.Algebra
module Classical = FStar.Classical
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas

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
let raw_product (x y: Vec.t)
  : Pure (Vec.t & Vec.t) (requires True)
         (ensures fun r ->
            Poly.halves (Vec.bv x) (Vec.bv y)
                        (CL.bswap (Vec.bv (snd r))) (CL.bswap (Vec.bv (fst r))))
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

    (qlo, qhi)

(** {2 Multiplying by the reduction constant}

    [Spec.GF128.r_block] is [x^7 + x^2 + x + 1], so a product with it is four
    copies of the other operand shifted by nought, one, two and seven, added
    together -- see [Spec.GF128.Poly.mul_r_coef].  A 128-bit shift is not one
    instruction, because the shift units work a lane at a time and drop no
    carry between the lanes, but it is two, which beats a [PCLMULQDQ] on both
    latency and throughput.  The nine shifts and six exclusive-ors here
    replace eight multiplies in [gmul_vec] below.

    The argument and both results are in the multiplier's little-endian bit
    order, which is why the [bswap]s are on the specification side: the whole
    point of doing it this way is that the reduction never leaves that order,
    so [gmul_vec] reverses bytes three times instead of twelve. *)

(** A full 128-bit right shift by [n]: the lane-wise shift of [a], plus the
    bits that fall out of the high lane, which reach the low lane through
    [h].  [m] is [64 - n], passed separately so that both shift counts reach
    the intrinsics as literals. *)
inline_for_extraction
let full_shr (a h: Vec.t) (n m: U32.t)
  : Pure Vec.t
         (requires U32.v n >= 1 /\ U32.v n < 64 /\ U32.v m == 64 - U32.v n /\
                   (forall (k: int). 0 <= k /\ k < 128 ==>
                      CL.lebiti (Vec.bv h) k == CL.lebiti (Vec.bv a) (k + 64)))
         (ensures fun r -> forall (k: int). 0 <= k /\ k < 128 ==>
                        CL.lebiti (Vec.bv r) k ==
                        CL.lebiti (Vec.bv a) (k + U32.v n))
  = let sh = Vec.shift_right_lanes64 a n in
    let c = Vec.shift_left_lanes64 h m in
    let q = Vec.vxor sh c in
    Classical.forall_intro (xor_bits sh c);
    CL.shr_gen (CL.lebiti (Vec.bv a)) (CL.lebiti (Vec.bv h))
               (CL.lebiti (Vec.bv sh)) (CL.lebiti (Vec.bv q)) (U32.v n);
    q

(** A full 128-bit left shift by [64 + m], which is one instruction: [l] has
    already moved the lanes up and zeroed the low one, so nothing carries. *)
inline_for_extraction
let full_shl (a l: Vec.t) (m: U32.t)
  : Pure Vec.t
         (requires U32.v m < 64 /\ CL.bounded (CL.lebiti (Vec.bv a)) /\
                   (forall (k: int). 0 <= k /\ k < 128 ==>
                      CL.lebiti (Vec.bv l) k == CL.lebiti (Vec.bv a) (k - 64)))
         (ensures fun r -> forall (k: int). 0 <= k /\ k < 128 ==>
                        CL.lebiti (Vec.bv r) k ==
                        CL.lebiti (Vec.bv a) (k - 64 - U32.v m))
  = let t = Vec.shift_left_lanes64 l m in
    CL.shl_gen (CL.lebiti (Vec.bv a)) (CL.lebiti (Vec.bv l))
               (CL.lebiti (Vec.bv t)) (U32.v m);
    t

(** The two four-term sums, over bare bit functions so that the registers'
    refinements stay out of the query. *)

let rxor_lo (fa f1 f2 f7 fu: int -> bool)
  : Lemma (requires
      (forall (k: int). 0 <= k /\ k < 128 ==> f1 k == fa (k + 1)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==> f2 k == fa (k + 2)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==> f7 k == fa (k + 7)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fu k == ((fa k <> f1 k) <> (f2 k <> f7 k))))
    (ensures forall (k: int). 0 <= k /\ k < 128 ==> fu k == CL.rxor fa k) = ()

let rxor_hi (fa f1 f2 f7 fw: int -> bool)
  : Lemma (requires
      CL.bounded fa /\
      (forall (k: int). 0 <= k /\ k < 128 ==> f1 k == fa (k - 127)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==> f2 k == fa (k - 126)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==> f7 k == fa (k - 121)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==> fw k == ((f1 k <> f2 k) <> f7 k)))
    (ensures forall (k: int). 0 <= k /\ k < 128 ==>
                         fw k == CL.rxor fa (k - 128)) = ()

(** {2 Multiplying by the reduction constant}

    [Spec.GF128.r_block] is [x^7 + x^2 + x + 1], so a product with it is four
    copies of the other operand shifted by nought, one, two and seven, added
    together -- see [Spec.GF128.Poly.mul_r_coef].  A 128-bit shift is not one
    instruction, because the shift units work a lane at a time and carry
    nothing between the lanes, but it is at most two, which beats a
    [PCLMULQDQ] on both latency and throughput.  The nine shifts and six
    exclusive-ors here replace eight multiplies in [gmul_vec] below.

    The argument and both results are in the multiplier's little-endian bit
    order, which is why the [bswap]s are on the specification side: the point
    of doing it this way is that the reduction never leaves that order, so
    [gmul_vec] reverses bytes three times instead of twelve. *)

inline_for_extraction
let mul_r_vec (a: Vec.t)
  : Pure (Vec.t & Vec.t) (requires True)
         (ensures fun r ->
            Poly.halves (CL.bswap (Vec.bv a)) G.r_block
                        (CL.bswap (Vec.bv (fst r))) (CL.bswap (Vec.bv (snd r))))
  = bounded_lebiti a;
    let h = Vec.shift_right_bytes_8 a in
    let l = Vec.shift_left_bytes_8 a in

    let q1 = full_shr a h 1ul 63ul in
    let q2 = full_shr a h 2ul 62ul in
    let q7 = full_shr a h 7ul 57ul in
    let ua = Vec.vxor (Vec.vxor a q1) (Vec.vxor q2 q7) in

    (* Shifts by 127, 126 and 121.  The fourth term of the sum would be a
       shift by 128, which is zero. *)
    let t1 = full_shl a l 63ul in
    let t2 = full_shl a l 62ul in
    let t7 = full_shl a l 57ul in
    let wa = Vec.vxor (Vec.vxor t1 t2) t7 in

    Classical.forall_intro (xor_bits a q1);
    Classical.forall_intro (xor_bits q2 q7);
    Classical.forall_intro (xor_bits (Vec.vxor a q1) (Vec.vxor q2 q7));
    rxor_lo (CL.lebiti (Vec.bv a)) (CL.lebiti (Vec.bv q1))
            (CL.lebiti (Vec.bv q2)) (CL.lebiti (Vec.bv q7))
            (CL.lebiti (Vec.bv ua));
    Classical.forall_intro (xor_bits t1 t2);
    Classical.forall_intro (xor_bits (Vec.vxor t1 t2) t7);
    rxor_hi (CL.lebiti (Vec.bv a)) (CL.lebiti (Vec.bv t1))
            (CL.lebiti (Vec.bv t2)) (CL.lebiti (Vec.bv t7))
            (CL.lebiti (Vec.bv wa));
    CL.mul_r_halves (Vec.bv a) (Vec.bv ua) (Vec.bv wa);

    (ua, wa)

(** {2 The multiplication} *)

inline_for_extraction
let gmul_vec (x y: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> Vec.bv r == G.gmul (Vec.bv x) (Vec.bv y))
  = let p1 = raw_product x y in
    let qlo = fst p1 in
    let qhi = snd p1 in
    let p2 = mul_r_vec qlo in
    let p3 = mul_r_vec (snd p2) in
    let u1 = Vec.bswap qhi in
    let u2 = Vec.bswap (fst p2) in
    let u3 = Vec.bswap (fst p3) in
    Poly.gmul_three (Vec.bv x) (Vec.bv y)
                    (Vec.bv u1) (CL.bswap (Vec.bv qlo))
                    (Vec.bv u2) (CL.bswap (Vec.bv (snd p2)))
                    (Vec.bv u3) (CL.bswap (Vec.bv (snd p3)));
    xor_block_bv u2 u3;
    xor_block_bv u1 (Vec.vxor u2 u3);
    Vec.vxor u1 (Vec.vxor u2 u3)

(** {2 Four multiplies, one reduction}

    The four-way GHASH loop needs the sum of four field products, not the
    four products, and a 256-bit carry-less product is linear in each
    operand.  So the four products may be accumulated as two registers ---
    the sum of the low halves and the sum of the high halves --- and the fold
    back into the field applied once to that sum.

    That is worth a great deal, because the fold is the expensive part.  Each
    [mul_r_vec] is about twenty shifts and exclusive-ors, and [gmul_vec] runs
    two of them for four [PCLMULQDQ]s; doing it once for four multiplies
    rather than four times takes a four-block turn from roughly two hundred
    and fifty vector operations to a hundred and ten.

    [Spec.GF128.Algebra.gmul_defer4] is the statement that this is the same
    answer, and [Spec.CLMUL.bswap_gadd] is what lets the accumulation happen
    in the multiplier's bit order: the six exclusive-ors below are on
    unreversed registers, and only three byte reversals happen at the end
    rather than twelve. *)

(** Four registers added, with the bookkeeping that says the reversal of the
    sum is the sum of the reversals.  The exclusive-ors happen on unreversed
    registers -- that is the point -- so every accumulation in this section
    goes through here and the [bswap]s stay at the end. *)
inline_for_extraction
let xor4 (a b c d: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> CL.bswap (Vec.bv r) ==
            Alg.sum4 (CL.bswap (Vec.bv a)) (CL.bswap (Vec.bv b))
                     (CL.bswap (Vec.bv c)) (CL.bswap (Vec.bv d)))
  = xor_block_bv c d;
    xor_block_bv b (Vec.vxor c d);
    xor_block_bv a (Vec.vxor b (Vec.vxor c d));
    CL.bswap_gadd (Vec.bv c) (Vec.bv d);
    CL.bswap_gadd (Vec.bv b) (G.gadd (Vec.bv c) (Vec.bv d));
    CL.bswap_gadd (Vec.bv a)
                  (G.gadd (Vec.bv b) (G.gadd (Vec.bv c) (Vec.bv d)));
    Vec.vxor a (Vec.vxor b (Vec.vxor c d))

(** The same for eight, in [sum8]'s shape: two fours and then one more. *)
inline_for_extraction
let xor8 (a b c d e f g h: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> CL.bswap (Vec.bv r) ==
            Alg.sum8 (CL.bswap (Vec.bv a)) (CL.bswap (Vec.bv b))
                     (CL.bswap (Vec.bv c)) (CL.bswap (Vec.bv d))
                     (CL.bswap (Vec.bv e)) (CL.bswap (Vec.bv f))
                     (CL.bswap (Vec.bv g)) (CL.bswap (Vec.bv h)))
  = let lo = xor4 a b c d in
    let hi = xor4 e f g h in
    xor_block_bv lo hi;
    CL.bswap_gadd (Vec.bv lo) (Vec.bv hi);
    Vec.vxor lo hi

inline_for_extraction
let gmul4_vec (x1 y1 x2 y2 x3 y3 x4 y4: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> Vec.bv r ==
            Alg.sum4 (G.gmul (Vec.bv x1) (Vec.bv y1))
                     (G.gmul (Vec.bv x2) (Vec.bv y2))
                     (G.gmul (Vec.bv x3) (Vec.bv y3))
                     (G.gmul (Vec.bv x4) (Vec.bv y4)))
  = let a1 = raw_product x1 y1 in
    let a2 = raw_product x2 y2 in
    let a3 = raw_product x3 y3 in
    let a4 = raw_product x4 y4 in

    let lo = xor4 (fst a1) (fst a2) (fst a3) (fst a4) in
    let hi = xor4 (snd a1) (snd a2) (snd a3) (snd a4) in

    let p2 = mul_r_vec lo in
    let p3 = mul_r_vec (snd p2) in

    let u  = Vec.bswap hi in
    let u2 = Vec.bswap (fst p2) in
    let u3 = Vec.bswap (fst p3) in

    Alg.gmul_defer4 (Vec.bv x1) (Vec.bv y1)
                    (CL.bswap (Vec.bv (snd a1))) (CL.bswap (Vec.bv (fst a1)))
                    (Vec.bv x2) (Vec.bv y2)
                    (CL.bswap (Vec.bv (snd a2))) (CL.bswap (Vec.bv (fst a2)))
                    (Vec.bv x3) (Vec.bv y3)
                    (CL.bswap (Vec.bv (snd a3))) (CL.bswap (Vec.bv (fst a3)))
                    (Vec.bv x4) (Vec.bv y4)
                    (CL.bswap (Vec.bv (snd a4))) (CL.bswap (Vec.bv (fst a4)))
                    (CL.bswap (Vec.bv (fst p2))) (CL.bswap (Vec.bv (snd p2)))
                    (CL.bswap (Vec.bv (fst p3))) (CL.bswap (Vec.bv (snd p3)));

    xor_block_bv u2 u3;
    xor_block_bv u (Vec.vxor u2 u3);
    Vec.vxor u (Vec.vxor u2 u3)

(** {2 Eight multiplies, one reduction}

    The same again, one level up.  The reduction is a fixed cost per group,
    so paying it once for a hundred and twenty-eight bytes rather than once
    for sixty-four removes about a fifth of what a four-block turn spends on
    it; and the eight carry-less products are independent of one another, so
    the multiplier's pipeline has twice as much to work on.

    [Spec.GF128.Algebra.gmul_defer8] is the statement, and it is
    [gmul_defer4] with four replaced by eight.  Nothing about the reduction
    changes at all: there is still exactly one [mul_r_vec] pair below. *)

inline_for_extraction
let gmul8_vec (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7 x8 y8: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> Vec.bv r ==
            Alg.sum8 (G.gmul (Vec.bv x1) (Vec.bv y1))
                     (G.gmul (Vec.bv x2) (Vec.bv y2))
                     (G.gmul (Vec.bv x3) (Vec.bv y3))
                     (G.gmul (Vec.bv x4) (Vec.bv y4))
                     (G.gmul (Vec.bv x5) (Vec.bv y5))
                     (G.gmul (Vec.bv x6) (Vec.bv y6))
                     (G.gmul (Vec.bv x7) (Vec.bv y7))
                     (G.gmul (Vec.bv x8) (Vec.bv y8)))
  = let a1 = raw_product x1 y1 in
    let a2 = raw_product x2 y2 in
    let a3 = raw_product x3 y3 in
    let a4 = raw_product x4 y4 in
    let a5 = raw_product x5 y5 in
    let a6 = raw_product x6 y6 in
    let a7 = raw_product x7 y7 in
    let a8 = raw_product x8 y8 in

    let lo = xor8 (fst a1) (fst a2) (fst a3) (fst a4)
                  (fst a5) (fst a6) (fst a7) (fst a8) in
    let hi = xor8 (snd a1) (snd a2) (snd a3) (snd a4)
                  (snd a5) (snd a6) (snd a7) (snd a8) in

    let p2 = mul_r_vec lo in
    let p3 = mul_r_vec (snd p2) in

    let u  = Vec.bswap hi in
    let u2 = Vec.bswap (fst p2) in
    let u3 = Vec.bswap (fst p3) in

    Alg.gmul_defer8 (Vec.bv x1) (Vec.bv y1)
                    (CL.bswap (Vec.bv (snd a1))) (CL.bswap (Vec.bv (fst a1)))
                    (Vec.bv x2) (Vec.bv y2)
                    (CL.bswap (Vec.bv (snd a2))) (CL.bswap (Vec.bv (fst a2)))
                    (Vec.bv x3) (Vec.bv y3)
                    (CL.bswap (Vec.bv (snd a3))) (CL.bswap (Vec.bv (fst a3)))
                    (Vec.bv x4) (Vec.bv y4)
                    (CL.bswap (Vec.bv (snd a4))) (CL.bswap (Vec.bv (fst a4)))
                    (Vec.bv x5) (Vec.bv y5)
                    (CL.bswap (Vec.bv (snd a5))) (CL.bswap (Vec.bv (fst a5)))
                    (Vec.bv x6) (Vec.bv y6)
                    (CL.bswap (Vec.bv (snd a6))) (CL.bswap (Vec.bv (fst a6)))
                    (Vec.bv x7) (Vec.bv y7)
                    (CL.bswap (Vec.bv (snd a7))) (CL.bswap (Vec.bv (fst a7)))
                    (Vec.bv x8) (Vec.bv y8)
                    (CL.bswap (Vec.bv (snd a8))) (CL.bswap (Vec.bv (fst a8)))
                    (CL.bswap (Vec.bv (fst p2))) (CL.bswap (Vec.bv (snd p2)))
                    (CL.bswap (Vec.bv (fst p3))) (CL.bswap (Vec.bv (snd p3)));

    xor_block_bv u2 u3;
    xor_block_bv u (Vec.vxor u2 u3);
    Vec.vxor u (Vec.vxor u2 u3)

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

(** {2 Multiply-add}

    GHASH never multiplies without first adding the next block in, and the
    two together are the whole of its inner loop.  Fusing them is worth more
    than it looks: the addition on its own is sixteen bytes read, exclusive-
    ored and written back one at a time, and it sits between a sixteen-byte
    vector store (the previous multiply's result) and a sixteen-byte vector
    load (this one's operand), so every block pays a store-forwarding stall
    on top of the byte traffic.  Done this way the accumulator is loaded
    once, stays in a register through the add and the multiply, and is
    stored once. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn gmul_add_ni (a: A.array S8.t) (h: A.array S8.t) (b: A.array S8.t) (off: SZ.t)
               (#va #vh: erased (Seq.seq S8.t))
               (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to h vh ** A.pts_to b #pb vb ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  SZ.v off + blocklen <= Seq.length vb)
ensures exists* (va': Seq.seq S8.t).
  A.pts_to a va' ** A.pts_to h vh ** A.pts_to b #pb vb ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  SZ.v off + blocklen <= Seq.length vb /\ Seq.length va' == blocklen /\
  vals va' == G.gmul (G.gadd (vals va)
                             (Seq.slice (vals vb) (SZ.v off) (SZ.v off + blocklen)))
                     (vals vh))
{
  A.pts_to_len a;
  A.pts_to_len h;
  A.pts_to_len b;
  let x = Vec.load a #(as_blk va);
  let y = Vec.load h #(as_blk vh);

  let off2 = SZ.add off 16sz;
  let db = Sub.sub b off off2;
  vals_slice vb (SZ.v off) (SZ.v off2);
  let dv = Vec.load db #(as_blk (Seq.slice vb (SZ.v off) (SZ.v off2)));
  Sub.unsub_id b (SZ.v off) (SZ.v off2) db;

  xor_block_bv x dv;
  let r = gmul_vec (Vec.vxor x dv) y;
  Vec.store a r #(as_blk va);
  vals_len (Vec.vv r);
  ()
}

(** {2 The whole inner loop}

    [gmul_add_ni] above is one block, and calling it a block at a time is
    what the dispatcher in [Hacl.AES.GMul] did: a function call, a CPUID
    feature test, an aliasing check and a load and a store of the
    accumulator, all per sixteen bytes of input, wrapped around a multiply
    that is now well under thirty instructions.  GHASH is a Horner
    evaluation, so the accumulator is a serial dependency and every one of
    those loads waits on the previous store.

    So the loop itself comes down here.  The feature test happens once, the
    hash key is loaded once, and the accumulator lives in a register from the
    first block to the last. *)

(** One turn of it, on the pure side: the slice of the input at [i] is block
    [i / blocklen] of the prefix being hashed. *)
let ghash_step (hh acc0: G.block) (d: Seq.seq elem) (n i: nat)
  : Lemma (requires n % blocklen == 0 /\ n <= Seq.length d /\
                    i % blocklen == 0 /\ i + blocklen <= n)
          (ensures (let dd = Seq.slice d 0 n in
                    Seq.length dd % blocklen == 0 /\
                    i / blocklen + 1 <= G.nblocks dd /\
                    (i + blocklen) / blocklen == i / blocklen + 1 /\
                    G.ghash_from hh acc0 dd (i / blocklen + 1) ==
                      G.gmul (G.gadd (G.ghash_from hh acc0 dd (i / blocklen))
                                     (Seq.slice d i (i + blocklen))) hh))
  = let dd = Seq.slice d 0 n in
    let k = i / blocklen in
    Math.euclidean_division_definition i blocklen;
    Math.division_addition_lemma i blocklen 1;
    Math.distributivity_add_left k 1 blocklen;
    Math.lemma_div_le (i + blocklen) n blocklen;
    Math.multiple_division_lemma (n / blocklen) blocklen;
    Math.euclidean_division_definition n blocklen;
    G.ghash_from_step hh acc0 dd k;
    Seq.slice_slice d 0 n (k * blocklen) (k * blocklen + blocklen)

#push-options "--fuel 1"
(** Entering the loop. *)
let ghash_zero (hh acc0: G.block)
               (dd: Seq.seq elem { Seq.length dd % blocklen == 0 })
  : Lemma (G.ghash_from hh acc0 dd 0 == acc0) = ()
#pop-options

(** Four turns of the loop at once.

    [Spec.GF128.Algebra.horner4] does the algebra.  All this lemma adds is
    the index arithmetic that turns four applications of [ghash_step] into a
    single statement about [ghash_from] four blocks further on, with the four
    products independent of one another. *)
let ghash_step4 (hh acc0 h2 h3 h4: G.block) (d: Seq.seq elem) (n i: nat)
  : Lemma (requires n % blocklen == 0 /\ n <= Seq.length d /\
                    i % blocklen == 0 /\ i + 4 * blocklen <= n /\
                    h2 == G.gmul hh hh /\ h3 == G.gmul h2 hh /\
                    h4 == G.gmul h3 hh)
          (ensures (let dd = Seq.slice d 0 n in
                    Seq.length dd % blocklen == 0 /\
                    i / blocklen + 4 <= G.nblocks dd /\
                    (i + 4 * blocklen) / blocklen == i / blocklen + 4 /\
                    G.ghash_from hh acc0 dd (i / blocklen + 4) ==
                      G.gadd
                        (G.gmul (G.gadd (G.ghash_from hh acc0 dd (i / blocklen))
                                        (Seq.slice d i (i + blocklen))) h4)
                        (G.gadd
                          (G.gmul (Seq.slice d (i + blocklen) (i + 2 * blocklen)) h3)
                          (G.gadd
                            (G.gmul (Seq.slice d (i + 2 * blocklen) (i + 3 * blocklen)) h2)
                            (G.gmul (Seq.slice d (i + 3 * blocklen) (i + 4 * blocklen)) hh)))))
  = ghash_step hh acc0 d n i;
    ghash_step hh acc0 d n (i + blocklen);
    ghash_step hh acc0 d n (i + 2 * blocklen);
    ghash_step hh acc0 d n (i + 3 * blocklen);
    let dd = Seq.slice d 0 n in
    Alg.horner4 (G.ghash_from hh acc0 dd (i / blocklen))
                (Seq.slice d i (i + blocklen))
                (Seq.slice d (i + blocklen) (i + 2 * blocklen))
                (Seq.slice d (i + 2 * blocklen) (i + 3 * blocklen))
                (Seq.slice d (i + 3 * blocklen) (i + 4 * blocklen))
                hh h2 h3 h4

(** Eight turns of the loop at once, on the same pattern. *)
let ghash_step8 (hh acc0 h2 h3 h4 h5 h6 h7 h8: G.block)
                (d: Seq.seq elem) (n i: nat)
  : Lemma (requires n % blocklen == 0 /\ n <= Seq.length d /\
                    i % blocklen == 0 /\ i + 8 * blocklen <= n /\
                    h2 == G.gmul hh hh /\ h3 == G.gmul h2 hh /\
                    h4 == G.gmul h3 hh /\ h5 == G.gmul h4 hh /\
                    h6 == G.gmul h5 hh /\ h7 == G.gmul h6 hh /\
                    h8 == G.gmul h7 hh)
          (ensures (let dd = Seq.slice d 0 n in
                    Seq.length dd % blocklen == 0 /\
                    i / blocklen + 8 <= G.nblocks dd /\
                    (i + 8 * blocklen) / blocklen == i / blocklen + 8 /\
                    G.ghash_from hh acc0 dd (i / blocklen + 8) ==
                      Alg.sum8
                        (G.gmul (G.gadd (G.ghash_from hh acc0 dd (i / blocklen))
                                        (Seq.slice d i (i + blocklen))) h8)
                        (G.gmul (Seq.slice d (i + blocklen) (i + 2 * blocklen)) h7)
                        (G.gmul (Seq.slice d (i + 2 * blocklen) (i + 3 * blocklen)) h6)
                        (G.gmul (Seq.slice d (i + 3 * blocklen) (i + 4 * blocklen)) h5)
                        (G.gmul (Seq.slice d (i + 4 * blocklen) (i + 5 * blocklen)) h4)
                        (G.gmul (Seq.slice d (i + 5 * blocklen) (i + 6 * blocklen)) h3)
                        (G.gmul (Seq.slice d (i + 6 * blocklen) (i + 7 * blocklen)) h2)
                        (G.gmul (Seq.slice d (i + 7 * blocklen) (i + 8 * blocklen)) hh)))
  = ghash_step hh acc0 d n i;
    ghash_step hh acc0 d n (i + blocklen);
    ghash_step hh acc0 d n (i + 2 * blocklen);
    ghash_step hh acc0 d n (i + 3 * blocklen);
    ghash_step hh acc0 d n (i + 4 * blocklen);
    ghash_step hh acc0 d n (i + 5 * blocklen);
    ghash_step hh acc0 d n (i + 6 * blocklen);
    ghash_step hh acc0 d n (i + 7 * blocklen);
    let dd = Seq.slice d 0 n in
    Alg.horner8 (G.ghash_from hh acc0 dd (i / blocklen))
                (Seq.slice d i (i + blocklen))
                (Seq.slice d (i + blocklen) (i + 2 * blocklen))
                (Seq.slice d (i + 2 * blocklen) (i + 3 * blocklen))
                (Seq.slice d (i + 3 * blocklen) (i + 4 * blocklen))
                (Seq.slice d (i + 4 * blocklen) (i + 5 * blocklen))
                (Seq.slice d (i + 5 * blocklen) (i + 6 * blocklen))
                (Seq.slice d (i + 6 * blocklen) (i + 7 * blocklen))
                (Seq.slice d (i + 7 * blocklen) (i + 8 * blocklen))
                hh h2 h3 h4 h5 h6 h7 h8

(** The same for the one-block loop: a partial block cannot fit. *)
let step1_bounds (vi n: nat)
  : Lemma (requires vi % blocklen == 0 /\ n % blocklen == 0 /\ vi < n)
          (ensures vi + blocklen <= n)
  = Math.lemma_mod_sub_distr n vi blocklen;
    if n - vi < blocklen then Math.small_mod (n - vi) blocklen

(** Index arithmetic for the four-way loop, kept out of the Pulse context
    where it would have to be found among a hundred other hypotheses. *)
let step4_bounds (vi lim n: nat)
  : Lemma (requires vi % 64 == 0 /\ lim % 64 == 0 /\ vi < lim /\ lim <= n)
          (ensures vi % blocklen == 0 /\ vi + 4 * blocklen <= n /\
                   (vi + 4 * blocklen) % 64 == 0 /\
                   vi + 4 * blocklen <= lim)
  = Math.euclidean_division_definition vi 64;
    Math.euclidean_division_definition lim 64;
    Math.multiple_modulo_lemma (4 * (vi / 64)) 16;
    Math.multiple_modulo_lemma (vi / 64 + 1) 64

(** The four-way limit, again out of the Pulse context. *)
let lim_bounds (n: nat)
  : Lemma (requires n % blocklen == 0)
          (ensures (n - n % 64) % 64 == 0 /\ n - n % 64 <= n /\
                   (n - n % 64) % blocklen == 0)
  = Math.euclidean_division_definition n 64;
    Math.multiple_modulo_lemma (n / 64) 64;
    Math.multiple_modulo_lemma (4 * (n / 64)) 16

inline_for_extraction
let four_limit (n: SZ.t { SZ.v n % blocklen == 0 })
  : Pure SZ.t (requires True)
         (ensures fun r -> SZ.v r % 64 == 0 /\ SZ.v r <= SZ.v n /\
                           SZ.v r % blocklen == 0)
  = lim_bounds (SZ.v n);
    SZ.sub n (SZ.rem n 64sz)

(** Index arithmetic for the eight-way loop. *)
let step8_bounds (vi lim n: nat)
  : Lemma (requires vi % 128 == 0 /\ lim % 128 == 0 /\ vi < lim /\ lim <= n)
          (ensures vi % blocklen == 0 /\ vi % 64 == 0 /\
                   vi + 8 * blocklen <= n /\
                   (vi + 8 * blocklen) % 128 == 0 /\
                   vi + 8 * blocklen <= lim)
  = Math.euclidean_division_definition vi 128;
    Math.euclidean_division_definition lim 128;
    Math.multiple_modulo_lemma (8 * (vi / 128)) 16;
    Math.multiple_modulo_lemma (2 * (vi / 128)) 64;
    Math.multiple_modulo_lemma (vi / 128 + 1) 128

(** The eight-way limit, and the fact that it does not overshoot the
    four-way one: what the eight-way pass leaves behind is at most one
    sixty-four byte group, which the four-way pass then takes. *)
let lim8_bounds (n: nat)
  : Lemma (requires n % blocklen == 0)
          (ensures (let l8 = n - n % 128 in
                    l8 % 128 == 0 /\ l8 % 64 == 0 /\ l8 % blocklen == 0 /\
                    l8 <= n /\ l8 <= n - n % 64))
  = Math.euclidean_division_definition n 128;
    Math.euclidean_division_definition n 64;
    Math.multiple_modulo_lemma (n / 128) 128;
    Math.multiple_modulo_lemma (2 * (n / 128)) 64;
    Math.multiple_modulo_lemma (8 * (n / 128)) 16;
    Math.lemma_div_le (n - n % 128) n 64;
    Math.multiple_division_lemma (2 * (n / 128)) 64;
    Math.lemma_mult_le_right 64 (2 * (n / 128)) (n / 64)

inline_for_extraction
let eight_limit (n: SZ.t { SZ.v n % blocklen == 0 })
  : Pure SZ.t (requires True)
         (ensures fun r -> SZ.v r % 128 == 0 /\ SZ.v r % 64 == 0 /\
                           SZ.v r % blocklen == 0 /\ SZ.v r <= SZ.v n /\
                           SZ.v r <= SZ.v n - SZ.v n % 64)
  = lim8_bounds (SZ.v n);
    SZ.sub n (SZ.rem n 128sz)

(** The length of the prefix being hashed, out of the Pulse context, where
    the query that establishes it competes with a hundred other hypotheses. *)
let slice_len_mod (vd: Seq.seq S8.t) (n: nat)
  : Lemma (requires n <= Seq.length vd /\ n % blocklen == 0)
          (ensures Seq.length vd == Seq.length (vals vd) /\
                   Seq.length (Seq.slice (vals vd) 0 n) == n /\
                   Seq.length (Seq.slice (vals vd) 0 n) % blocklen == 0)
  = vals_len vd

(** The four-way block loop.

    Bytes [start] to [lim], both multiples of sixty-four, are consumed against
    the four precomputed powers of the hash key.  The accumulator never leaves
    a register and the four multiplies of a turn do not depend on one another,
    which is the whole point: the Horner chain is broken.

    [start] is not always zero, because the eight-way loop below runs first
    and leaves at most one group of four behind.  [acc0] is the accumulator
    the whole hash began with, which only the specification needs, and [cur0]
    is where the eight-way pass got to. *)
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn ghash_loop4_ni (cur0 y y2 y3 y4: Vec.t) (d: A.array S8.t)
                  (n: SZ.t) (start: SZ.t) (lim: SZ.t)
                  (#acc0: erased G.block)
                  (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  SZ.v lim <= SZ.v n /\ SZ.v lim % 64 == 0 /\
  SZ.v start <= SZ.v lim /\ SZ.v start % 64 == 0 /\
  Vec.bv cur0 == G.ghash_from (Vec.bv y) (reveal acc0)
                              (Seq.slice (vals vd) 0 (SZ.v n))
                              (SZ.v start / blocklen) /\
  Vec.bv y2 == G.gmul (Vec.bv y) (Vec.bv y) /\
  Vec.bv y3 == G.gmul (Vec.bv y2) (Vec.bv y) /\
  Vec.bv y4 == G.gmul (Vec.bv y3) (Vec.bv y))
returns r: Vec.t
ensures A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v lim / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  Vec.bv r == G.ghash_from (Vec.bv y) (reveal acc0)
                           (Seq.slice (vals vd) 0 (SZ.v n)) (SZ.v lim / blocklen))
{
  A.pts_to_len d;
  Math.lemma_div_le (SZ.v lim) (SZ.v n) blocklen;
  Math.lemma_div_le (SZ.v start) (SZ.v n) blocklen;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;
  let mut av = cur0;
  let mut i = start;

  while (let vi = !i; SZ.lt vi lim)
  invariant exists* (vi: SZ.t) (cur: Vec.t).
    pts_to i vi ** pts_to av cur **
    A.pts_to d #pd vd **
    pure (SZ.v vi <= SZ.v lim /\ SZ.v vi % 64 == 0 /\
          SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
          SZ.v lim <= SZ.v n /\ SZ.v lim % 64 == 0 /\
          SZ.v vi / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
          Vec.bv cur == G.ghash_from (Vec.bv y) (reveal acc0)
                                     (Seq.slice (vals vd) 0 (SZ.v n))
                                     (SZ.v vi / blocklen))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    step4_bounds (SZ.v vi) (SZ.v lim) (SZ.v n);
    let vi1 = SZ.add vi 16sz;
    let vi2 = SZ.add vi 32sz;
    let vi3 = SZ.add vi 48sz;
    let vi4 = SZ.add vi 64sz;

    let db0 = Sub.sub d vi vi1;
    vals_slice vd (SZ.v vi) (SZ.v vi1);
    let d0 = Vec.load db0 #(as_blk (Seq.slice vd (SZ.v vi) (SZ.v vi1)));
    Sub.unsub_id d (SZ.v vi) (SZ.v vi1) db0;

    let db1 = Sub.sub d vi1 vi2;
    vals_slice vd (SZ.v vi1) (SZ.v vi2);
    let d1 = Vec.load db1 #(as_blk (Seq.slice vd (SZ.v vi1) (SZ.v vi2)));
    Sub.unsub_id d (SZ.v vi1) (SZ.v vi2) db1;

    let db2 = Sub.sub d vi2 vi3;
    vals_slice vd (SZ.v vi2) (SZ.v vi3);
    let d2 = Vec.load db2 #(as_blk (Seq.slice vd (SZ.v vi2) (SZ.v vi3)));
    Sub.unsub_id d (SZ.v vi2) (SZ.v vi3) db2;

    let db3 = Sub.sub d vi3 vi4;
    vals_slice vd (SZ.v vi3) (SZ.v vi4);
    let d3 = Vec.load db3 #(as_blk (Seq.slice vd (SZ.v vi3) (SZ.v vi4)));
    Sub.unsub_id d (SZ.v vi3) (SZ.v vi4) db3;

    let cur = !av;
    xor_block_bv cur d0;
    let res = gmul4_vec (Vec.vxor cur d0) y4 d1 y3 d2 y2 d3 y;
    ghash_step4 (Vec.bv y) (reveal acc0) (Vec.bv y2) (Vec.bv y3) (Vec.bv y4)
                (vals vd) (SZ.v n) (SZ.v vi);
    av := res;
    i := vi4;
  };

  let fin = !av;
  fin
}

(** The eight-way block loop.

    The same shape again, against eight powers.  What it buys is the
    reduction: [gmul8_vec] folds once for a hundred and twenty-eight bytes
    where two turns of [gmul4_vec] fold twice for the same, and the fold is
    about forty vector operations.  The eight products are also independent,
    so twice as many [PCLMULQDQ]s are available to the multiplier at once. *)
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn ghash_loop8_ni (a0 y y2 y3 y4 y5 y6 y7 y8: Vec.t) (d: A.array S8.t)
                  (n: SZ.t) (lim: SZ.t)
                  (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  SZ.v lim <= SZ.v n /\ SZ.v lim % 128 == 0 /\
  Vec.bv y2 == G.gmul (Vec.bv y) (Vec.bv y) /\
  Vec.bv y3 == G.gmul (Vec.bv y2) (Vec.bv y) /\
  Vec.bv y4 == G.gmul (Vec.bv y3) (Vec.bv y) /\
  Vec.bv y5 == G.gmul (Vec.bv y4) (Vec.bv y) /\
  Vec.bv y6 == G.gmul (Vec.bv y5) (Vec.bv y) /\
  Vec.bv y7 == G.gmul (Vec.bv y6) (Vec.bv y) /\
  Vec.bv y8 == G.gmul (Vec.bv y7) (Vec.bv y))
returns r: Vec.t
ensures A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v lim / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  Vec.bv r == G.ghash_from (Vec.bv y) (Vec.bv a0)
                           (Seq.slice (vals vd) 0 (SZ.v n)) (SZ.v lim / blocklen))
{
  A.pts_to_len d;
  Math.lemma_div_le (SZ.v lim) (SZ.v n) blocklen;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;
  ghash_zero (Vec.bv y) (Vec.bv a0) (Seq.slice (vals vd) 0 (SZ.v n));
  let mut av = a0;
  let mut i = 0sz;

  while (let vi = !i; SZ.lt vi lim)
  invariant exists* (vi: SZ.t) (cur: Vec.t).
    pts_to i vi ** pts_to av cur **
    A.pts_to d #pd vd **
    pure (SZ.v vi <= SZ.v lim /\ SZ.v vi % 128 == 0 /\
          SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
          SZ.v lim <= SZ.v n /\ SZ.v lim % 128 == 0 /\
          SZ.v vi / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
          Vec.bv cur == G.ghash_from (Vec.bv y) (Vec.bv a0)
                                     (Seq.slice (vals vd) 0 (SZ.v n))
                                     (SZ.v vi / blocklen))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    step8_bounds (SZ.v vi) (SZ.v lim) (SZ.v n);
    let vi1 = SZ.add vi 16sz;
    let vi2 = SZ.add vi 32sz;
    let vi3 = SZ.add vi 48sz;
    let vi4 = SZ.add vi 64sz;
    let vi5 = SZ.add vi 80sz;
    let vi6 = SZ.add vi 96sz;
    let vi7 = SZ.add vi 112sz;
    let vi8 = SZ.add vi 128sz;

    let db0 = Sub.sub d vi vi1;
    vals_slice vd (SZ.v vi) (SZ.v vi1);
    let d0 = Vec.load db0 #(as_blk (Seq.slice vd (SZ.v vi) (SZ.v vi1)));
    Sub.unsub_id d (SZ.v vi) (SZ.v vi1) db0;

    let db1 = Sub.sub d vi1 vi2;
    vals_slice vd (SZ.v vi1) (SZ.v vi2);
    let d1 = Vec.load db1 #(as_blk (Seq.slice vd (SZ.v vi1) (SZ.v vi2)));
    Sub.unsub_id d (SZ.v vi1) (SZ.v vi2) db1;

    let db2 = Sub.sub d vi2 vi3;
    vals_slice vd (SZ.v vi2) (SZ.v vi3);
    let d2 = Vec.load db2 #(as_blk (Seq.slice vd (SZ.v vi2) (SZ.v vi3)));
    Sub.unsub_id d (SZ.v vi2) (SZ.v vi3) db2;

    let db3 = Sub.sub d vi3 vi4;
    vals_slice vd (SZ.v vi3) (SZ.v vi4);
    let d3 = Vec.load db3 #(as_blk (Seq.slice vd (SZ.v vi3) (SZ.v vi4)));
    Sub.unsub_id d (SZ.v vi3) (SZ.v vi4) db3;

    let db4 = Sub.sub d vi4 vi5;
    vals_slice vd (SZ.v vi4) (SZ.v vi5);
    let d4 = Vec.load db4 #(as_blk (Seq.slice vd (SZ.v vi4) (SZ.v vi5)));
    Sub.unsub_id d (SZ.v vi4) (SZ.v vi5) db4;

    let db5 = Sub.sub d vi5 vi6;
    vals_slice vd (SZ.v vi5) (SZ.v vi6);
    let d5 = Vec.load db5 #(as_blk (Seq.slice vd (SZ.v vi5) (SZ.v vi6)));
    Sub.unsub_id d (SZ.v vi5) (SZ.v vi6) db5;

    let db6 = Sub.sub d vi6 vi7;
    vals_slice vd (SZ.v vi6) (SZ.v vi7);
    let d6 = Vec.load db6 #(as_blk (Seq.slice vd (SZ.v vi6) (SZ.v vi7)));
    Sub.unsub_id d (SZ.v vi6) (SZ.v vi7) db6;

    let db7 = Sub.sub d vi7 vi8;
    vals_slice vd (SZ.v vi7) (SZ.v vi8);
    let d7 = Vec.load db7 #(as_blk (Seq.slice vd (SZ.v vi7) (SZ.v vi8)));
    Sub.unsub_id d (SZ.v vi7) (SZ.v vi8) db7;

    let cur = !av;
    xor_block_bv cur d0;
    let res = gmul8_vec (Vec.vxor cur d0) y8 d1 y7 d2 y6 d3 y5
                        d4 y4 d5 y3 d6 y2 d7 y;
    ghash_step8 (Vec.bv y) (Vec.bv a0) (Vec.bv y2) (Vec.bv y3) (Vec.bv y4)
                (Vec.bv y5) (Vec.bv y6) (Vec.bv y7) (Vec.bv y8)
                (vals vd) (SZ.v n) (SZ.v vi);
    av := res;
    i := vi8;
  };

  let fin = !av;
  fin
}

(** Entering the block loops: the eight-way pass, then the four-way pass for
    the group of four it may have left behind, and otherwise nothing at all.
    Kept in a function of its own so that the branches are checked against a
    handful of hypotheses rather than against everything the caller knows.

    The powers of the hash key are computed here, inside the test, so a
    message too short to reach either loop pays for none of them.  Four more
    multiplies than before is about a hundred cycles, and they are only
    incurred once a hundred and twenty-eight bytes are in hand. *)
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn ghash_start (a0: Vec.t) (y: Vec.t) (d: A.array S8.t)
               (n: SZ.t) (lim8: SZ.t) (lim: SZ.t)
               (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  SZ.v lim <= SZ.v n /\ SZ.v lim % 64 == 0 /\
  SZ.v lim8 <= SZ.v lim /\ SZ.v lim8 % 128 == 0)
returns r: Vec.t
ensures A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v lim / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  Vec.bv r == G.ghash_from (Vec.bv y) (Vec.bv a0)
                           (Seq.slice (vals vd) 0 (SZ.v n)) (SZ.v lim / blocklen))
{
  A.pts_to_len d;
  vals_len vd;
  slice_len_mod vd (SZ.v n);
  Math.lemma_div_le (SZ.v lim) (SZ.v n) blocklen;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;
  if SZ.gt lim 0sz
  {
    let y2 = gmul_vec y y;
    let y3 = gmul_vec y2 y;
    let y4 = gmul_vec y3 y;
    if SZ.gt lim8 0sz
    {
      let y5 = gmul_vec y4 y;
      let y6 = gmul_vec y5 y;
      let y7 = gmul_vec y6 y;
      let y8 = gmul_vec y7 y;
      let r8 = ghash_loop8_ni a0 y y2 y3 y4 y5 y6 y7 y8 d n lim8;
      Math.multiple_modulo_lemma (SZ.v lim8 / 128 * 2) 64;
      Math.euclidean_division_definition (SZ.v lim8) 128;
      ghash_loop4_ni r8 y y2 y3 y4 d n lim8 lim #(hide (Vec.bv a0))
    }
    else
    {
      ghash_zero (Vec.bv y) (Vec.bv a0) (Seq.slice (vals vd) 0 (SZ.v n));
      ghash_loop4_ni a0 y y2 y3 y4 d n 0sz lim #(hide (Vec.bv a0))
    }
  }
  else
  {
    ghash_zero (Vec.bv y) (Vec.bv a0) (Seq.slice (vals vd) 0 (SZ.v n));
    a0
  }
}

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn ghash_loop_ni (acc: A.array S8.t) (h: A.array S8.t) (d: A.array S8.t) (n: SZ.t)
                 (#va0 #vh: erased (Seq.seq S8.t))
                 (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to acc va0 ** A.pts_to h vh ** A.pts_to d #pd vd ** pure (
  Seq.length va0 == blocklen /\ Seq.length vh == blocklen /\
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0)
ensures exists* (va1: Seq.seq S8.t).
  A.pts_to acc va1 ** A.pts_to h vh ** A.pts_to d #pd vd ** pure (
  Seq.length va0 == blocklen /\ Seq.length vh == blocklen /\
  Seq.length va1 == blocklen /\
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v n / blocklen == G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  vals va1 == G.ghash_from (vals vh) (vals va0)
                           (Seq.slice (vals vd) 0 (SZ.v n)) (SZ.v n / blocklen))
{
  let lim = four_limit n;
  let lim8 = eight_limit n;
  A.pts_to_len acc;
  A.pts_to_len h;
  A.pts_to_len d;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;

  let y = Vec.load h #(as_blk vh);
  let a0 = Vec.load acc #(as_blk va0);
  let r = ghash_start a0 y d n lim8 lim;
  let mut av = r;
  let mut i = lim;

  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (cur: Vec.t).
    pts_to i vi ** pts_to av cur **
    A.pts_to acc va0 ** A.pts_to h vh ** A.pts_to d #pd vd **
    pure (SZ.v vi <= SZ.v n /\ SZ.v vi % blocklen == 0 /\
          Seq.length va0 == blocklen /\ Seq.length vh == blocklen /\
          SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
          Vec.vv y == reveal vh /\
          SZ.v vi / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
          Vec.bv cur == G.ghash_from (vals vh) (vals va0)
                                     (Seq.slice (vals vd) 0 (SZ.v n))
                                     (SZ.v vi / blocklen))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    step1_bounds (SZ.v vi) (SZ.v n);
    let vi2 = SZ.add vi 16sz;
    let db = Sub.sub d vi vi2;
    vals_slice vd (SZ.v vi) (SZ.v vi2);
    let dv = Vec.load db #(as_blk (Seq.slice vd (SZ.v vi) (SZ.v vi2)));
    Sub.unsub_id d (SZ.v vi) (SZ.v vi2) db;
    let cur = !av;
    xor_block_bv cur dv;
    let r = gmul_vec (Vec.vxor cur dv) y;
    ghash_step (vals vh) (vals va0) (vals vd) (SZ.v n) (SZ.v vi);
    Math.division_addition_lemma (SZ.v vi) blocklen 1;
    av := r;
    i := vi2;
  };

  let fin = !av;
  Vec.store acc fin #(as_blk va0);
  vals_len (Vec.vv fin);
  ()
}

#pop-options
