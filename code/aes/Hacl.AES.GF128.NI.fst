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

(** {2 One product, unshifted}

    Given [x] and [y], the two halves of their carry-less product, brought
    back into GHASH's bit order.  Everything here is one instruction.

    The customary one-bit left shift of the 256-bit pair is {i not} here.
    GHASH's bit order is the reverse of the multiplier's, and the reversal
    leaves the product one place out -- coefficient [m] of what the hardware
    computes is coefficient [254 - m] of the polynomial GHASH wants, not
    [255 - m] -- so every implementation of GHASH on [PCLMULQDQ] has had to
    shift the pair by one to line them up.  That is six instructions on the
    critical path of every multiplication, about a fifth of the whole.

    Omitting it leaves the halves of the product {i times x}, so the routine
    computes [x * a * b] rather than [a * b].  Every multiplication GHASH
    performs has a power of the hash key as one operand, so dividing the
    hash key by [x] once, when the key is set up, cancels the factor
    everywhere at no cost at all.  [Spec.GF128.Poly.xdiv] is that division
    and [Spec.CLMUL.gmulx_three] is the identity.

    The arrangement is Gueron and Kounavis's; what is new here is that it is
    proved rather than argued, and the proof came to three short lemmas
    ([Spec.GF128.Poly.psplit], [Spec.GF128.Algebra.pmod_shift1] and
    [Spec.GF128.Poly.xtimes_xdiv]) because the reduction was already stated
    as a linear map on coefficient sequences. *)

(** {3 Karatsuba}

    Of the four multiplies, two are only ever wanted added together, and over
    a field of characteristic two their sum is one multiply:

      [(x0 + x1) (y0 + y1) + x0 y0 + x1 y1  =  x0 y1 + x1 y0.]

    Folding an operand's two lanes together is a shift and an exclusive-or,
    and recovering the crossed sum afterwards is two more exclusive-ors, so
    the trade is one [PCLMULQDQ] for four cheap instructions -- worth it on
    every machine that has the instruction at all.

    This returns the three registers {i before} the middle term is assembled
    into the halves, because the bulk loops want to put that assembly off; the
    halves appear only as the ghost blocks [Spec.CLMUL.kfold_lo] and
    [Spec.CLMUL.kfold_hi], which are never computed when a group of blocks is
    being multiplied. *)

(** The middle term the two folds below are stated with: a ghost block, since
    the implementation never puts it in a register until the group is over. *)
unfold let kmid_of (ll hh mf: Vec.t) : GTot G.block
  = CL.kmid (Vec.bv ll) (Vec.bv hh) (Vec.bv mf)

inline_for_extraction
let kara_parts (x y: Vec.t)
  : Pure (Vec.t & Vec.t & Vec.t) (requires True)
         (ensures fun r ->
            let (ll, hh, mf) = r in
            let mm = CL.kmid (Vec.bv ll) (Vec.bv hh) (Vec.bv mf) in
            Poly.halvesp (CL.pshift1 (Vec.bv x) (Vec.bv y))
                         (CL.bswap (CL.kfold_hi (Vec.bv hh) mm))
                         (CL.bswap (CL.kfold_lo (Vec.bv ll) mm)))
  = let xa = Vec.bswap x in
    let yb = Vec.bswap y in

    (* Each operand's two lanes added together, in its low lane. *)
    let xs = Vec.shift_right_bytes_8 xa in
    let ys = Vec.shift_right_bytes_8 yb in
    let xf = Vec.vxor xa xs in
    let yf = Vec.vxor yb ys in

    (* Three multiplies.  Taking the squares back out of the folded one is
       left to the caller, because it is linear and the caller may have
       several of these to add up first. *)
    let ll = Vec.clmul_ll xa yb in
    let hh = Vec.clmul_hh xa yb in
    let mf = Vec.clmul_ll xf yf in

    Classical.forall_intro (xor_bits xa xs);
    Classical.forall_intro (xor_bits yb ys);
    CL.fold_lane (Vec.bv xa) (Vec.bv xf);
    CL.fold_lane (Vec.bv yb) (Vec.bv yf);
    CL.kmid_isbits (Vec.bv ll) (Vec.bv hh) (Vec.bv mf);
    Classical.forall_intro (CL.kara_mid_lanes (Vec.bv xa) (Vec.bv yb));
    CL.kfold_lo_isbits (Vec.bv ll) (kmid_of ll hh mf);
    CL.kfold_hi_isbits (Vec.bv hh) (kmid_of ll hh mf);
    CL.lo_of_lanes (Vec.bv x) (Vec.bv y) (Vec.bv ll) (kmid_of ll hh mf)
                   (CL.kfold_lo (Vec.bv ll) (kmid_of ll hh mf));
    CL.hi_of_lanes (Vec.bv x) (Vec.bv y) (Vec.bv hh) (kmid_of ll hh mf)
                   (CL.kfold_hi (Vec.bv hh) (kmid_of ll hh mf));
    CL.clmul_halves_ns (Vec.bv x) (Vec.bv y)
                       (CL.kfold_lo (Vec.bv ll) (kmid_of ll hh mf))
                       (CL.kfold_hi (Vec.bv hh) (kmid_of ll hh mf));

    (ll, hh, mf)

(** Assembling the middle term into the halves: two shifts and two exclusive-
    ors.  A single multiplication pays this immediately; a group of four or of
    eight pays it once for the whole group. *)

inline_for_extraction
let kara_fold (ll hh mf: Vec.t)
  : Pure (Vec.t & Vec.t) (requires True)
         (ensures fun r ->
            let mm = CL.kmid (Vec.bv ll) (Vec.bv hh) (Vec.bv mf) in
            Vec.bv (fst r) == CL.kfold_lo (Vec.bv ll) mm /\
            Vec.bv (snd r) == CL.kfold_hi (Vec.bv hh) mm)
  = let sq = Vec.vxor ll hh in
    let mm = Vec.vxor mf sq in
    let mlo = Vec.shift_left_bytes_8 mm in
    let mhi = Vec.shift_right_bytes_8 mm in
    let lo = Vec.vxor ll mlo in
    let hi = Vec.vxor hh mhi in

    xor_block_bv ll hh;
    xor_block_bv mf sq;
    Classical.forall_intro (xor_bits ll mlo);
    Classical.forall_intro (xor_bits hh mhi);
    CL.kfold_lo_bits (Vec.bv ll) (Vec.bv mm) (Vec.bv lo);
    CL.kfold_hi_bits (Vec.bv hh) (Vec.bv mm) (Vec.bv hi);

    (lo, hi)

(** One multiplication on its own keeps all four multiplies.  Karatsuba trades
    one [PCLMULQDQ] for about five cheap instructions, and two of those sit on
    the dependency chain; that is a good trade only when the fold at the end is
    shared across a group, which is why the single-block multiplier below is
    the four-multiply one and the bulk loops are not.  Measured on Skylake, the
    Karatsuba form here cost 128-byte AES-GCM twelve per cent. *)

inline_for_extraction
let raw_product (x y: Vec.t)
  : Pure (Vec.t & Vec.t) (requires True)
         (ensures fun r ->
            Poly.halvesp (CL.pshift1 (Vec.bv x) (Vec.bv y))
                         (CL.bswap (Vec.bv (snd r)))
                         (CL.bswap (Vec.bv (fst r))))
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
    CL.clmul_halves_ns (Vec.bv x) (Vec.bv y) (Vec.bv lo) (Vec.bv hi);

    (lo, hi)

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
         (ensures fun r ->
            Vec.bv r == G.gmul (Vec.bv x) (Poly.xtimes (Vec.bv y)))
  = let p1 = raw_product x y in
    let qlo = fst p1 in
    let qhi = snd p1 in
    let p2 = mul_r_vec qlo in
    let p3 = mul_r_vec (snd p2) in
    let u1 = Vec.bswap qhi in
    let u2 = Vec.bswap (fst p2) in
    let u3 = Vec.bswap (fst p3) in
    CL.gmulx_three (Vec.bv x) (Vec.bv y)
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
            Alg.sum4 (G.gmul (Vec.bv x1) (Poly.xtimes (Vec.bv y1)))
                     (G.gmul (Vec.bv x2) (Poly.xtimes (Vec.bv y2)))
                     (G.gmul (Vec.bv x3) (Poly.xtimes (Vec.bv y3)))
                     (G.gmul (Vec.bv x4) (Poly.xtimes (Vec.bv y4))))
  = let (l1, h1, m1) = kara_parts x1 y1 in
    let (l2, h2, m2) = kara_parts x2 y2 in
    let (l3, h3, m3) = kara_parts x3 y3 in
    let (l4, h4, m4) = kara_parts x4 y4 in

    (* Three accumulators across the group; the squares come back out of
       the folded product once, and the halves are assembled once. *)
    let ls = xor4 l1 l2 l3 l4 in
    let hs = xor4 h1 h2 h3 h4 in
    let ms = xor4 m1 m2 m3 m4 in
    let (lo, hi) = kara_fold ls hs ms in

    let p2 = mul_r_vec lo in
    let p3 = mul_r_vec (snd p2) in

    let u  = Vec.bswap hi in
    let u2 = Vec.bswap (fst p2) in
    let u3 = Vec.bswap (fst p3) in

    (* The sum of the registers is the sum of the blocks they stand for ... *)
    CL.bswap_sum4 (Vec.bv l1) (Vec.bv l2) (Vec.bv l3) (Vec.bv l4);
    CL.bswap_inj (Vec.bv ls)
                (Alg.sum4 (Vec.bv l1) (Vec.bv l2) (Vec.bv l3) (Vec.bv l4));
    CL.bswap_sum4 (Vec.bv h1) (Vec.bv h2) (Vec.bv h3) (Vec.bv h4);
    CL.bswap_inj (Vec.bv hs)
                (Alg.sum4 (Vec.bv h1) (Vec.bv h2) (Vec.bv h3) (Vec.bv h4));
    CL.bswap_sum4 (Vec.bv m1) (Vec.bv m2) (Vec.bv m3) (Vec.bv m4);
    CL.bswap_inj (Vec.bv ms)
                (Alg.sum4 (Vec.bv m1) (Vec.bv m2) (Vec.bv m3) (Vec.bv m4));
    (* ... and both the correction and the assembly commute with it. *)
    CL.kmid_sum4 (Vec.bv l1) (Vec.bv h1) (Vec.bv m1) (Vec.bv l2) (Vec.bv h2)
                (Vec.bv m2) (Vec.bv l3) (Vec.bv h3) (Vec.bv m3) (Vec.bv l4)
                (Vec.bv h4) (Vec.bv m4);
    CL.kfold_lo_sum4 (Vec.bv l1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))
                (Vec.bv l2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))
                (Vec.bv l3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))
                (Vec.bv l4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4));
    CL.kfold_hi_sum4 (Vec.bv h1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))
                (Vec.bv h2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))
                (Vec.bv h3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))
                (Vec.bv h4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4));
    CL.bswap_sum4
                (CL.kfold_lo (Vec.bv l1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1)))
                (CL.kfold_lo (Vec.bv l2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2)))
                (CL.kfold_lo (Vec.bv l3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3)))
                (CL.kfold_lo (Vec.bv l4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4)));
    CL.bswap_sum4
                (CL.kfold_hi (Vec.bv h1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1)))
                (CL.kfold_hi (Vec.bv h2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2)))
                (CL.kfold_hi (Vec.bv h3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3)))
                (CL.kfold_hi (Vec.bv h4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4)));

    Alg.pmod_defer4 (CL.pshift1 (Vec.bv x1) (Vec.bv y1))
                    (CL.pshift1 (Vec.bv x2) (Vec.bv y2))
                    (CL.pshift1 (Vec.bv x3) (Vec.bv y3))
                    (CL.pshift1 (Vec.bv x4) (Vec.bv y4))
                    (CL.bswap (CL.kfold_hi (Vec.bv h1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4))))
                    (CL.bswap (Vec.bv (fst p2))) (CL.bswap (Vec.bv (snd p2)))
                    (CL.bswap (Vec.bv (fst p3))) (CL.bswap (Vec.bv (snd p3)));
    CL.pmodx (Vec.bv x1) (Vec.bv y1);
    CL.pmodx (Vec.bv x2) (Vec.bv y2);
    CL.pmodx (Vec.bv x3) (Vec.bv y3);
    CL.pmodx (Vec.bv x4) (Vec.bv y4);

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
            Alg.sum8 (G.gmul (Vec.bv x1) (Poly.xtimes (Vec.bv y1)))
                     (G.gmul (Vec.bv x2) (Poly.xtimes (Vec.bv y2)))
                     (G.gmul (Vec.bv x3) (Poly.xtimes (Vec.bv y3)))
                     (G.gmul (Vec.bv x4) (Poly.xtimes (Vec.bv y4)))
                     (G.gmul (Vec.bv x5) (Poly.xtimes (Vec.bv y5)))
                     (G.gmul (Vec.bv x6) (Poly.xtimes (Vec.bv y6)))
                     (G.gmul (Vec.bv x7) (Poly.xtimes (Vec.bv y7)))
                     (G.gmul (Vec.bv x8) (Poly.xtimes (Vec.bv y8))))
  = let (l1, h1, m1) = kara_parts x1 y1 in
    let (l2, h2, m2) = kara_parts x2 y2 in
    let (l3, h3, m3) = kara_parts x3 y3 in
    let (l4, h4, m4) = kara_parts x4 y4 in
    let (l5, h5, m5) = kara_parts x5 y5 in
    let (l6, h6, m6) = kara_parts x6 y6 in
    let (l7, h7, m7) = kara_parts x7 y7 in
    let (l8, h8, m8) = kara_parts x8 y8 in

    (* Three accumulators across the group; the squares come back out of
       the folded product once, and the halves are assembled once. *)
    let ls = xor8 l1 l2 l3 l4 l5 l6 l7 l8 in
    let hs = xor8 h1 h2 h3 h4 h5 h6 h7 h8 in
    let ms = xor8 m1 m2 m3 m4 m5 m6 m7 m8 in
    let (lo, hi) = kara_fold ls hs ms in

    let p2 = mul_r_vec lo in
    let p3 = mul_r_vec (snd p2) in

    let u  = Vec.bswap hi in
    let u2 = Vec.bswap (fst p2) in
    let u3 = Vec.bswap (fst p3) in

    (* The sum of the registers is the sum of the blocks they stand for ... *)
    CL.bswap_sum8 (Vec.bv l1) (Vec.bv l2) (Vec.bv l3) (Vec.bv l4) (Vec.bv l5)
                (Vec.bv l6) (Vec.bv l7) (Vec.bv l8);
    CL.bswap_inj (Vec.bv ls)
                (Alg.sum8 (Vec.bv l1) (Vec.bv l2) (Vec.bv l3) (Vec.bv l4) (Vec.bv l5) (Vec.bv l6) (Vec.bv l7) (Vec.bv l8));
    CL.bswap_sum8 (Vec.bv h1) (Vec.bv h2) (Vec.bv h3) (Vec.bv h4) (Vec.bv h5)
                (Vec.bv h6) (Vec.bv h7) (Vec.bv h8);
    CL.bswap_inj (Vec.bv hs)
                (Alg.sum8 (Vec.bv h1) (Vec.bv h2) (Vec.bv h3) (Vec.bv h4) (Vec.bv h5) (Vec.bv h6) (Vec.bv h7) (Vec.bv h8));
    CL.bswap_sum8 (Vec.bv m1) (Vec.bv m2) (Vec.bv m3) (Vec.bv m4) (Vec.bv m5)
                (Vec.bv m6) (Vec.bv m7) (Vec.bv m8);
    CL.bswap_inj (Vec.bv ms)
                (Alg.sum8 (Vec.bv m1) (Vec.bv m2) (Vec.bv m3) (Vec.bv m4) (Vec.bv m5) (Vec.bv m6) (Vec.bv m7) (Vec.bv m8));
    (* ... and both the correction and the assembly commute with it. *)
    CL.kmid_sum8 (Vec.bv l1) (Vec.bv h1) (Vec.bv m1) (Vec.bv l2) (Vec.bv h2)
                (Vec.bv m2) (Vec.bv l3) (Vec.bv h3) (Vec.bv m3) (Vec.bv l4)
                (Vec.bv h4) (Vec.bv m4) (Vec.bv l5) (Vec.bv h5) (Vec.bv m5)
                (Vec.bv l6) (Vec.bv h6) (Vec.bv m6) (Vec.bv l7) (Vec.bv h7)
                (Vec.bv m7) (Vec.bv l8) (Vec.bv h8) (Vec.bv m8);
    CL.kfold_lo_sum8 (Vec.bv l1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))
                (Vec.bv l2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))
                (Vec.bv l3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))
                (Vec.bv l4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4))
                (Vec.bv l5) (CL.kmid (Vec.bv l5) (Vec.bv h5) (Vec.bv m5))
                (Vec.bv l6) (CL.kmid (Vec.bv l6) (Vec.bv h6) (Vec.bv m6))
                (Vec.bv l7) (CL.kmid (Vec.bv l7) (Vec.bv h7) (Vec.bv m7))
                (Vec.bv l8) (CL.kmid (Vec.bv l8) (Vec.bv h8) (Vec.bv m8));
    CL.kfold_hi_sum8 (Vec.bv h1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))
                (Vec.bv h2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))
                (Vec.bv h3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))
                (Vec.bv h4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4))
                (Vec.bv h5) (CL.kmid (Vec.bv l5) (Vec.bv h5) (Vec.bv m5))
                (Vec.bv h6) (CL.kmid (Vec.bv l6) (Vec.bv h6) (Vec.bv m6))
                (Vec.bv h7) (CL.kmid (Vec.bv l7) (Vec.bv h7) (Vec.bv m7))
                (Vec.bv h8) (CL.kmid (Vec.bv l8) (Vec.bv h8) (Vec.bv m8));
    CL.bswap_sum8
                (CL.kfold_lo (Vec.bv l1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1)))
                (CL.kfold_lo (Vec.bv l2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2)))
                (CL.kfold_lo (Vec.bv l3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3)))
                (CL.kfold_lo (Vec.bv l4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4)))
                (CL.kfold_lo (Vec.bv l5) (CL.kmid (Vec.bv l5) (Vec.bv h5) (Vec.bv m5)))
                (CL.kfold_lo (Vec.bv l6) (CL.kmid (Vec.bv l6) (Vec.bv h6) (Vec.bv m6)))
                (CL.kfold_lo (Vec.bv l7) (CL.kmid (Vec.bv l7) (Vec.bv h7) (Vec.bv m7)))
                (CL.kfold_lo (Vec.bv l8) (CL.kmid (Vec.bv l8) (Vec.bv h8) (Vec.bv m8)));
    CL.bswap_sum8
                (CL.kfold_hi (Vec.bv h1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1)))
                (CL.kfold_hi (Vec.bv h2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2)))
                (CL.kfold_hi (Vec.bv h3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3)))
                (CL.kfold_hi (Vec.bv h4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4)))
                (CL.kfold_hi (Vec.bv h5) (CL.kmid (Vec.bv l5) (Vec.bv h5) (Vec.bv m5)))
                (CL.kfold_hi (Vec.bv h6) (CL.kmid (Vec.bv l6) (Vec.bv h6) (Vec.bv m6)))
                (CL.kfold_hi (Vec.bv h7) (CL.kmid (Vec.bv l7) (Vec.bv h7) (Vec.bv m7)))
                (CL.kfold_hi (Vec.bv h8) (CL.kmid (Vec.bv l8) (Vec.bv h8) (Vec.bv m8)));

    Alg.pmod_defer8 (CL.pshift1 (Vec.bv x1) (Vec.bv y1))
                    (CL.pshift1 (Vec.bv x2) (Vec.bv y2))
                    (CL.pshift1 (Vec.bv x3) (Vec.bv y3))
                    (CL.pshift1 (Vec.bv x4) (Vec.bv y4))
                    (CL.pshift1 (Vec.bv x5) (Vec.bv y5))
                    (CL.pshift1 (Vec.bv x6) (Vec.bv y6))
                    (CL.pshift1 (Vec.bv x7) (Vec.bv y7))
                    (CL.pshift1 (Vec.bv x8) (Vec.bv y8))
                    (CL.bswap (CL.kfold_hi (Vec.bv h1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l1) (CL.kmid (Vec.bv l1) (Vec.bv h1) (Vec.bv m1))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l2) (CL.kmid (Vec.bv l2) (Vec.bv h2) (Vec.bv m2))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l3) (CL.kmid (Vec.bv l3) (Vec.bv h3) (Vec.bv m3))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l4) (CL.kmid (Vec.bv l4) (Vec.bv h4) (Vec.bv m4))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h5) (CL.kmid (Vec.bv l5) (Vec.bv h5) (Vec.bv m5))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l5) (CL.kmid (Vec.bv l5) (Vec.bv h5) (Vec.bv m5))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h6) (CL.kmid (Vec.bv l6) (Vec.bv h6) (Vec.bv m6))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l6) (CL.kmid (Vec.bv l6) (Vec.bv h6) (Vec.bv m6))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h7) (CL.kmid (Vec.bv l7) (Vec.bv h7) (Vec.bv m7))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l7) (CL.kmid (Vec.bv l7) (Vec.bv h7) (Vec.bv m7))))
                    (CL.bswap (CL.kfold_hi (Vec.bv h8) (CL.kmid (Vec.bv l8) (Vec.bv h8) (Vec.bv m8))))
                    (CL.bswap (CL.kfold_lo (Vec.bv l8) (CL.kmid (Vec.bv l8) (Vec.bv h8) (Vec.bv m8))))
                    (CL.bswap (Vec.bv (fst p2))) (CL.bswap (Vec.bv (snd p2)))
                    (CL.bswap (Vec.bv (fst p3))) (CL.bswap (Vec.bv (snd p3)));
    CL.pmodx (Vec.bv x1) (Vec.bv y1);
    CL.pmodx (Vec.bv x2) (Vec.bv y2);
    CL.pmodx (Vec.bv x3) (Vec.bv y3);
    CL.pmodx (Vec.bv x4) (Vec.bv y4);
    CL.pmodx (Vec.bv x5) (Vec.bv y5);
    CL.pmodx (Vec.bv x6) (Vec.bv y6);
    CL.pmodx (Vec.bv x7) (Vec.bv y7);
    CL.pmodx (Vec.bv x8) (Vec.bv y8);

    xor_block_bv u2 u3;
    xor_block_bv u (Vec.vxor u2 u3);
    Vec.vxor u (Vec.vxor u2 u3)

(** {2 The same reduction, from sums gathered elsewhere}

    [gmul8_vec] computes its eight Karatsuba triples and adds them up in one
    place.  The stitched AES-GCM loop in [Hacl.AES.GCM.Stitch] cannot: it
    computes one triple between each pair of [AESENC] rounds, so that the
    multiplier and the cipher unit work at the same time, and adds each into
    three running sums as it goes.  What is left is the part below -- the
    middle-term assembly and the reduction -- applied to sums it did not see
    being formed.  The triples are named by {!kp_ll}, {!kp_hh} and
    {!kp_mf}, which are [kara_parts] one register at a time, and the operands
    are ghosts: nothing here computes with them. *)

let parts_ok (x y ll hh mf: Vec.t) : prop =
  Poly.halvesp (CL.pshift1 (Vec.bv x) (Vec.bv y))
               (CL.bswap (CL.kfold_hi (Vec.bv hh) (CL.kmid (Vec.bv ll) (Vec.bv hh) (Vec.bv mf))))
               (CL.bswap (CL.kfold_lo (Vec.bv ll) (CL.kmid (Vec.bv ll) (Vec.bv hh) (Vec.bv mf))))

inline_for_extraction
let kp_ll (x y: Vec.t) : Vec.t = Vec.clmul_ll (Vec.bswap x) (Vec.bswap y)

inline_for_extraction
let kp_hh (x y: Vec.t) : Vec.t = Vec.clmul_hh (Vec.bswap x) (Vec.bswap y)

inline_for_extraction
let kp_mf (x y: Vec.t) : Vec.t =
  let xa = Vec.bswap x in
  let yb = Vec.bswap y in
  Vec.clmul_ll (Vec.vxor xa (Vec.shift_right_bytes_8 xa))
               (Vec.vxor yb (Vec.shift_right_bytes_8 yb))

(** [kara_parts]'s proof, for the three registers taken one at a time. *)
let kp_ok (x y: Vec.t)
  : Lemma (parts_ok x y (kp_ll x y) (kp_hh x y) (kp_mf x y))
  = let xa = Vec.bswap x in
    let yb = Vec.bswap y in
    let xs = Vec.shift_right_bytes_8 xa in
    let ys = Vec.shift_right_bytes_8 yb in
    let xf = Vec.vxor xa xs in
    let yf = Vec.vxor yb ys in
    let ll = Vec.clmul_ll xa yb in
    let hh = Vec.clmul_hh xa yb in
    let mf = Vec.clmul_ll xf yf in
    assert (ll == kp_ll x y);
    assert (hh == kp_hh x y);
    assert (mf == kp_mf x y);
    Classical.forall_intro (xor_bits xa xs);
    Classical.forall_intro (xor_bits yb ys);
    CL.fold_lane (Vec.bv xa) (Vec.bv xf);
    CL.fold_lane (Vec.bv yb) (Vec.bv yf);
    CL.kmid_isbits (Vec.bv ll) (Vec.bv hh) (Vec.bv mf);
    Classical.forall_intro (CL.kara_mid_lanes (Vec.bv xa) (Vec.bv yb));
    CL.kfold_lo_isbits (Vec.bv ll) (kmid_of ll hh mf);
    CL.kfold_hi_isbits (Vec.bv hh) (kmid_of ll hh mf);
    CL.lo_of_lanes (Vec.bv x) (Vec.bv y) (Vec.bv ll) (kmid_of ll hh mf)
                   (CL.kfold_lo (Vec.bv ll) (kmid_of ll hh mf));
    CL.hi_of_lanes (Vec.bv x) (Vec.bv y) (Vec.bv hh) (kmid_of ll hh mf)
                   (CL.kfold_hi (Vec.bv hh) (kmid_of ll hh mf));
    CL.clmul_halves_ns (Vec.bv x) (Vec.bv y)
                       (CL.kfold_lo (Vec.bv ll) (kmid_of ll hh mf))
                       (CL.kfold_hi (Vec.bv hh) (kmid_of ll hh mf))

(** Eight exclusive-ors taken left to right, which is the order a loop that
    adds one term at a time produces, are [sum8]. *)
let xor_left8 (a b c d e f g h: Vec.t)
  : Lemma (Vec.bv (Vec.vxor (Vec.vxor (Vec.vxor (Vec.vxor (Vec.vxor (Vec.vxor
             (Vec.vxor a b) c) d) e) f) g) h) ==
           Alg.sum8 (Vec.bv a) (Vec.bv b) (Vec.bv c) (Vec.bv d)
                    (Vec.bv e) (Vec.bv f) (Vec.bv g) (Vec.bv h))
  = let x2 = Vec.vxor a b in
    let x3 = Vec.vxor x2 c in
    let x4 = Vec.vxor x3 d in
    let x5 = Vec.vxor x4 e in
    let x6 = Vec.vxor x5 f in
    let x7 = Vec.vxor x6 g in
    xor_block_bv a b; xor_block_bv x2 c; xor_block_bv x3 d;
    xor_block_bv x4 e; xor_block_bv x5 f; xor_block_bv x6 g;
    xor_block_bv x7 h;
    let ba = Vec.bv a in let bb = Vec.bv b in let bc = Vec.bv c in
    let bd = Vec.bv d in let be = Vec.bv e in let bf = Vec.bv f in
    let bg = Vec.bv g in let bh = Vec.bv h in
    Alg.gadd_assoc (G.gadd ba bb) bc bd;
    Alg.gadd_assoc ba bb (G.gadd bc bd);
    let s4 = Vec.bv (reveal x4) in
    Alg.gadd_assoc (G.gadd (G.gadd s4 be) bf) bg bh;
    Alg.gadd_assoc (G.gadd s4 be) bf (G.gadd bg bh);
    Alg.gadd_assoc s4 be (G.gadd bf (G.gadd bg bh))

inline_for_extraction
let gmul8_fin (x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 x7 y7 x8 y8: erased Vec.t) (ls hs ms: Vec.t)
  : Pure Vec.t
         (requires
                    Vec.bv (ls) == Alg.sum8 (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_ll (reveal x4) (reveal y4))) (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_ll (reveal x8) (reveal y8))) /\
                    Vec.bv (hs) == Alg.sum8 (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) /\
                    Vec.bv (ms) == Alg.sum8 (Vec.bv (kp_mf (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x2) (reveal y2))) (Vec.bv (kp_mf (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x7) (reveal y7))) (Vec.bv (kp_mf (reveal x8) (reveal y8))))
         (ensures fun r -> Vec.bv r ==
            Alg.sum8 (G.gmul (Vec.bv (reveal x1)) (Poly.xtimes (Vec.bv (reveal y1))))
                     (G.gmul (Vec.bv (reveal x2)) (Poly.xtimes (Vec.bv (reveal y2))))
                     (G.gmul (Vec.bv (reveal x3)) (Poly.xtimes (Vec.bv (reveal y3))))
                     (G.gmul (Vec.bv (reveal x4)) (Poly.xtimes (Vec.bv (reveal y4))))
                     (G.gmul (Vec.bv (reveal x5)) (Poly.xtimes (Vec.bv (reveal y5))))
                     (G.gmul (Vec.bv (reveal x6)) (Poly.xtimes (Vec.bv (reveal y6))))
                     (G.gmul (Vec.bv (reveal x7)) (Poly.xtimes (Vec.bv (reveal y7))))
                     (G.gmul (Vec.bv (reveal x8)) (Poly.xtimes (Vec.bv (reveal y8)))))
  = let (lo, hi) = kara_fold ls hs ms in

    let p2 = mul_r_vec lo in
    let p3 = mul_r_vec (snd p2) in

    let u  = Vec.bswap hi in
    let u2 = Vec.bswap (fst p2) in
    let u3 = Vec.bswap (fst p3) in

    kp_ok (reveal x1) (reveal y1);
    kp_ok (reveal x2) (reveal y2);
    kp_ok (reveal x3) (reveal y3);
    kp_ok (reveal x4) (reveal y4);
    kp_ok (reveal x5) (reveal y5);
    kp_ok (reveal x6) (reveal y6);
    kp_ok (reveal x7) (reveal y7);
    kp_ok (reveal x8) (reveal y8);
    (* ... and both the correction and the assembly commute with it. *)
    CL.kmid_sum8 (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x1) (reveal y1))) (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x2) (reveal y2)))
                (Vec.bv (kp_mf (reveal x2) (reveal y2))) (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x3) (reveal y3))) (Vec.bv (kp_ll (reveal x4) (reveal y4)))
                (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x4) (reveal y4))) (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x5) (reveal y5)))
                (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x6) (reveal y6))) (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x7) (reveal y7)))
                (Vec.bv (kp_mf (reveal x7) (reveal y7))) (Vec.bv (kp_ll (reveal x8) (reveal y8))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) (Vec.bv (kp_mf (reveal x8) (reveal y8)));
    CL.kfold_lo_sum8 (Vec.bv (kp_ll (reveal x1) (reveal y1))) (CL.kmid (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x1) (reveal y1))))
                (Vec.bv (kp_ll (reveal x2) (reveal y2))) (CL.kmid (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x2) (reveal y2))) (Vec.bv (kp_mf (reveal x2) (reveal y2))))
                (Vec.bv (kp_ll (reveal x3) (reveal y3))) (CL.kmid (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x3) (reveal y3))))
                (Vec.bv (kp_ll (reveal x4) (reveal y4))) (CL.kmid (Vec.bv (kp_ll (reveal x4) (reveal y4))) (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x4) (reveal y4))))
                (Vec.bv (kp_ll (reveal x5) (reveal y5))) (CL.kmid (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x5) (reveal y5))))
                (Vec.bv (kp_ll (reveal x6) (reveal y6))) (CL.kmid (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x6) (reveal y6))))
                (Vec.bv (kp_ll (reveal x7) (reveal y7))) (CL.kmid (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x7) (reveal y7))) (Vec.bv (kp_mf (reveal x7) (reveal y7))))
                (Vec.bv (kp_ll (reveal x8) (reveal y8))) (CL.kmid (Vec.bv (kp_ll (reveal x8) (reveal y8))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) (Vec.bv (kp_mf (reveal x8) (reveal y8))));
    CL.kfold_hi_sum8 (Vec.bv (kp_hh (reveal x1) (reveal y1))) (CL.kmid (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x1) (reveal y1))))
                (Vec.bv (kp_hh (reveal x2) (reveal y2))) (CL.kmid (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x2) (reveal y2))) (Vec.bv (kp_mf (reveal x2) (reveal y2))))
                (Vec.bv (kp_hh (reveal x3) (reveal y3))) (CL.kmid (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x3) (reveal y3))))
                (Vec.bv (kp_hh (reveal x4) (reveal y4))) (CL.kmid (Vec.bv (kp_ll (reveal x4) (reveal y4))) (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x4) (reveal y4))))
                (Vec.bv (kp_hh (reveal x5) (reveal y5))) (CL.kmid (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x5) (reveal y5))))
                (Vec.bv (kp_hh (reveal x6) (reveal y6))) (CL.kmid (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x6) (reveal y6))))
                (Vec.bv (kp_hh (reveal x7) (reveal y7))) (CL.kmid (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x7) (reveal y7))) (Vec.bv (kp_mf (reveal x7) (reveal y7))))
                (Vec.bv (kp_hh (reveal x8) (reveal y8))) (CL.kmid (Vec.bv (kp_ll (reveal x8) (reveal y8))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) (Vec.bv (kp_mf (reveal x8) (reveal y8))));
    CL.bswap_sum8
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x1) (reveal y1))) (CL.kmid (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x1) (reveal y1)))))
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x2) (reveal y2))) (CL.kmid (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x2) (reveal y2))) (Vec.bv (kp_mf (reveal x2) (reveal y2)))))
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x3) (reveal y3))) (CL.kmid (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x3) (reveal y3)))))
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x4) (reveal y4))) (CL.kmid (Vec.bv (kp_ll (reveal x4) (reveal y4))) (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x4) (reveal y4)))))
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x5) (reveal y5))) (CL.kmid (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x5) (reveal y5)))))
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x6) (reveal y6))) (CL.kmid (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x6) (reveal y6)))))
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x7) (reveal y7))) (CL.kmid (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x7) (reveal y7))) (Vec.bv (kp_mf (reveal x7) (reveal y7)))))
                (CL.kfold_lo (Vec.bv (kp_ll (reveal x8) (reveal y8))) (CL.kmid (Vec.bv (kp_ll (reveal x8) (reveal y8))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) (Vec.bv (kp_mf (reveal x8) (reveal y8)))));
    CL.bswap_sum8
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x1) (reveal y1))) (CL.kmid (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x1) (reveal y1)))))
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x2) (reveal y2))) (CL.kmid (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x2) (reveal y2))) (Vec.bv (kp_mf (reveal x2) (reveal y2)))))
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x3) (reveal y3))) (CL.kmid (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x3) (reveal y3)))))
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x4) (reveal y4))) (CL.kmid (Vec.bv (kp_ll (reveal x4) (reveal y4))) (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x4) (reveal y4)))))
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x5) (reveal y5))) (CL.kmid (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x5) (reveal y5)))))
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x6) (reveal y6))) (CL.kmid (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x6) (reveal y6)))))
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x7) (reveal y7))) (CL.kmid (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x7) (reveal y7))) (Vec.bv (kp_mf (reveal x7) (reveal y7)))))
                (CL.kfold_hi (Vec.bv (kp_hh (reveal x8) (reveal y8))) (CL.kmid (Vec.bv (kp_ll (reveal x8) (reveal y8))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) (Vec.bv (kp_mf (reveal x8) (reveal y8)))));

    Alg.pmod_defer8 (CL.pshift1 (Vec.bv (reveal x1)) (Vec.bv (reveal y1)))
                    (CL.pshift1 (Vec.bv (reveal x2)) (Vec.bv (reveal y2)))
                    (CL.pshift1 (Vec.bv (reveal x3)) (Vec.bv (reveal y3)))
                    (CL.pshift1 (Vec.bv (reveal x4)) (Vec.bv (reveal y4)))
                    (CL.pshift1 (Vec.bv (reveal x5)) (Vec.bv (reveal y5)))
                    (CL.pshift1 (Vec.bv (reveal x6)) (Vec.bv (reveal y6)))
                    (CL.pshift1 (Vec.bv (reveal x7)) (Vec.bv (reveal y7)))
                    (CL.pshift1 (Vec.bv (reveal x8)) (Vec.bv (reveal y8)))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x1) (reveal y1))) (CL.kmid (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x1) (reveal y1))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x1) (reveal y1))) (CL.kmid (Vec.bv (kp_ll (reveal x1) (reveal y1))) (Vec.bv (kp_hh (reveal x1) (reveal y1))) (Vec.bv (kp_mf (reveal x1) (reveal y1))))))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x2) (reveal y2))) (CL.kmid (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x2) (reveal y2))) (Vec.bv (kp_mf (reveal x2) (reveal y2))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x2) (reveal y2))) (CL.kmid (Vec.bv (kp_ll (reveal x2) (reveal y2))) (Vec.bv (kp_hh (reveal x2) (reveal y2))) (Vec.bv (kp_mf (reveal x2) (reveal y2))))))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x3) (reveal y3))) (CL.kmid (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x3) (reveal y3))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x3) (reveal y3))) (CL.kmid (Vec.bv (kp_ll (reveal x3) (reveal y3))) (Vec.bv (kp_hh (reveal x3) (reveal y3))) (Vec.bv (kp_mf (reveal x3) (reveal y3))))))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x4) (reveal y4))) (CL.kmid (Vec.bv (kp_ll (reveal x4) (reveal y4))) (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x4) (reveal y4))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x4) (reveal y4))) (CL.kmid (Vec.bv (kp_ll (reveal x4) (reveal y4))) (Vec.bv (kp_hh (reveal x4) (reveal y4))) (Vec.bv (kp_mf (reveal x4) (reveal y4))))))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x5) (reveal y5))) (CL.kmid (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x5) (reveal y5))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x5) (reveal y5))) (CL.kmid (Vec.bv (kp_ll (reveal x5) (reveal y5))) (Vec.bv (kp_hh (reveal x5) (reveal y5))) (Vec.bv (kp_mf (reveal x5) (reveal y5))))))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x6) (reveal y6))) (CL.kmid (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x6) (reveal y6))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x6) (reveal y6))) (CL.kmid (Vec.bv (kp_ll (reveal x6) (reveal y6))) (Vec.bv (kp_hh (reveal x6) (reveal y6))) (Vec.bv (kp_mf (reveal x6) (reveal y6))))))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x7) (reveal y7))) (CL.kmid (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x7) (reveal y7))) (Vec.bv (kp_mf (reveal x7) (reveal y7))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x7) (reveal y7))) (CL.kmid (Vec.bv (kp_ll (reveal x7) (reveal y7))) (Vec.bv (kp_hh (reveal x7) (reveal y7))) (Vec.bv (kp_mf (reveal x7) (reveal y7))))))
                    (CL.bswap (CL.kfold_hi (Vec.bv (kp_hh (reveal x8) (reveal y8))) (CL.kmid (Vec.bv (kp_ll (reveal x8) (reveal y8))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) (Vec.bv (kp_mf (reveal x8) (reveal y8))))))
                    (CL.bswap (CL.kfold_lo (Vec.bv (kp_ll (reveal x8) (reveal y8))) (CL.kmid (Vec.bv (kp_ll (reveal x8) (reveal y8))) (Vec.bv (kp_hh (reveal x8) (reveal y8))) (Vec.bv (kp_mf (reveal x8) (reveal y8))))))
                    (CL.bswap (Vec.bv (fst p2))) (CL.bswap (Vec.bv (snd p2)))
                    (CL.bswap (Vec.bv (fst p3))) (CL.bswap (Vec.bv (snd p3)));
    CL.pmodx (Vec.bv (reveal x1)) (Vec.bv (reveal y1));
    CL.pmodx (Vec.bv (reveal x2)) (Vec.bv (reveal y2));
    CL.pmodx (Vec.bv (reveal x3)) (Vec.bv (reveal y3));
    CL.pmodx (Vec.bv (reveal x4)) (Vec.bv (reveal y4));
    CL.pmodx (Vec.bv (reveal x5)) (Vec.bv (reveal y5));
    CL.pmodx (Vec.bv (reveal x6)) (Vec.bv (reveal y6));
    CL.pmodx (Vec.bv (reveal x7)) (Vec.bv (reveal y7));
    CL.pmodx (Vec.bv (reveal x8)) (Vec.bv (reveal y8));

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
  vals va' == G.gmul (vals va) (Poly.xtimes (vals vh)))
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
                     (Poly.xtimes (vals vh)))
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

(** Aggregating four blocks to a reduction used to cost three
    multiplications to raise the hash key to the fourth power, which one
    group did not earn back: measured on a bare [ghash_upd], sixty-four
    bytes was 69.7 ns aggregated against 64.7 serial, so the pass began at
    two groups.  The powers now come out of the expanded-key context, where
    they were computed once, so there is nothing to earn back and the pass
    begins as soon as there is a group to run it on. *)
inline_for_extraction
let four_limit (n: SZ.t { SZ.v n % blocklen == 0 })
  : Pure SZ.t (requires True)
         (ensures fun r -> SZ.v r % 64 == 0 /\ SZ.v r <= SZ.v n /\
                           SZ.v r % blocklen == 0 /\
                           SZ.v r == SZ.v n - SZ.v n % 64)
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

(** Eight to a reduction used to cost four more multiplications for [H^5]
    to [H^8] and saves one reduction in eight rather than one in four, so it
    needed a good deal of data to pay: it was behind the four-way pass at
    five hundred and twelve bytes (289.8 ns against 270.4) and level at
    seven hundred and sixty-eight.  With the powers held in the context that
    threshold goes the same way as the four-way one, and for the same
    reason.  The bound is still taken against [lim] rather than [n] so that
    the eight-way limit cannot overshoot the four-way one. *)
inline_for_extraction
let eight_limit (n: SZ.t { SZ.v n % blocklen == 0 }) (lim: SZ.t)
  : Pure SZ.t (requires SZ.v lim <= SZ.v n /\
                        SZ.v lim == SZ.v n - SZ.v n % 64)
         (ensures fun r -> SZ.v r % 128 == 0 /\ SZ.v r % 64 == 0 /\
                           SZ.v r % blocklen == 0 /\ SZ.v r <= SZ.v n /\
                           SZ.v r <= SZ.v lim)
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
  Vec.bv cur0 == G.ghash_from (Poly.xtimes (Vec.bv y)) (reveal acc0)
                              (Seq.slice (vals vd) 0 (SZ.v n))
                              (SZ.v start / blocklen) /\
  Poly.xtimes (Vec.bv y2) == G.gmul (Poly.xtimes (Vec.bv y)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y3) == G.gmul (Poly.xtimes (Vec.bv y2)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y4) == G.gmul (Poly.xtimes (Vec.bv y3)) (Poly.xtimes (Vec.bv y)))
returns r: Vec.t
ensures A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v lim / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  Vec.bv r == G.ghash_from (Poly.xtimes (Vec.bv y)) (reveal acc0)
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
          Vec.bv cur == G.ghash_from (Poly.xtimes (Vec.bv y)) (reveal acc0)
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
    ghash_step4 (Poly.xtimes (Vec.bv y)) (reveal acc0)
                (Poly.xtimes (Vec.bv y2)) (Poly.xtimes (Vec.bv y3))
                (Poly.xtimes (Vec.bv y4))
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
  Poly.xtimes (Vec.bv y2) == G.gmul (Poly.xtimes (Vec.bv y)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y3) == G.gmul (Poly.xtimes (Vec.bv y2)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y4) == G.gmul (Poly.xtimes (Vec.bv y3)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y5) == G.gmul (Poly.xtimes (Vec.bv y4)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y6) == G.gmul (Poly.xtimes (Vec.bv y5)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y7) == G.gmul (Poly.xtimes (Vec.bv y6)) (Poly.xtimes (Vec.bv y)) /\
  Poly.xtimes (Vec.bv y8) == G.gmul (Poly.xtimes (Vec.bv y7)) (Poly.xtimes (Vec.bv y)))
returns r: Vec.t
ensures A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v lim / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  Vec.bv r == G.ghash_from (Poly.xtimes (Vec.bv y)) (Vec.bv a0)
                           (Seq.slice (vals vd) 0 (SZ.v n)) (SZ.v lim / blocklen))
{
  A.pts_to_len d;
  Math.lemma_div_le (SZ.v lim) (SZ.v n) blocklen;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;
  ghash_zero (Poly.xtimes (Vec.bv y)) (Vec.bv a0) (Seq.slice (vals vd) 0 (SZ.v n));
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
          Vec.bv cur == G.ghash_from (Poly.xtimes (Vec.bv y)) (Vec.bv a0)
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
    ghash_step8 (Poly.xtimes (Vec.bv y)) (Vec.bv a0)
                (Poly.xtimes (Vec.bv y2)) (Poly.xtimes (Vec.bv y3))
                (Poly.xtimes (Vec.bv y4)) (Poly.xtimes (Vec.bv y5))
                (Poly.xtimes (Vec.bv y6)) (Poly.xtimes (Vec.bv y7))
                (Poly.xtimes (Vec.bv y8))
                (vals vd) (SZ.v n) (SZ.v vi);
    av := res;
    i := vi8;
  };

  let fin = !av;
  fin
}

(** One step of the power recurrence, in the pre-divided representation.

    The loops below hold the powers of the hash key divided by [x], because
    that is what makes the multiplier's omitted shift cancel.  The recurrence
    itself is unchanged -- [y_(i+1) := gmul_vec y_i y_1] -- and this lemma is
    the one line that says so: advancing both sides once turns the relation
    the multiplier gives into the relation the loops assume. *)
#push-options "--fuel 2 --ifuel 0"
let power_step (a b: G.block)
  : Lemma (Poly.xtimes (G.gmul a (Poly.xtimes b)) ==
           G.gmul (Poly.xtimes a) (Poly.xtimes b))
  = Alg.gmul_xt_left a (Poly.xtimes b) 1
#pop-options

(** One power out of the context.

    The window is reached with {!Hacl.Impl.Sub.sub}, which is a pointer
    offset and nothing else; the receipt is traded straight back, so the
    caller sees the array it handed over. *)
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
inline_for_extraction
fn load_pow (h: A.array S8.t) (i: SZ.t)
            (#ph: perm) (#vh: erased (Seq.seq S8.t))
requires A.pts_to h #ph vh ** pure (Seq.length vh == 128 /\ SZ.v i < 8)
returns r: Vec.t
ensures A.pts_to h #ph vh **
  pure (Seq.length vh == 128 /\ Vec.bv r == Alg.hblk (vals vh) (SZ.v i))
{
  A.pts_to_len h;
  vals_len vh;
  let lo = SZ.mul i 16sz;
  let hi = SZ.add lo 16sz;
  let b = Sub.sub h lo hi;
  vals_slice vh (SZ.v lo) (SZ.v hi);
  let r = Vec.load b #(as_blk (Seq.slice vh (SZ.v lo) (SZ.v hi)));
  Sub.unsub_id h (SZ.v lo) (SZ.v hi) b;
  vals_len (Vec.vv r);
  r
}

(** Entering the block loops: the eight-way pass, then the four-way pass for
    the group of four it may have left behind, and otherwise nothing at all.
    Kept in a function of its own so that the branches are checked against a
    handful of hypotheses rather than against everything the caller knows.

    The powers of the hash key are read out of the expanded-key context,
    where [Hacl.AES.GCM.hkey_impl] put them.  They used to be computed here,
    on every call, which is seven multiplications a message rather than
    seven a key, and which is why both aggregation thresholds existed.  A
    message too short to reach either loop still pays nothing: the loads are
    inside the test. *)
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn ghash_start (a0: Vec.t) (y: Vec.t) (h: A.array S8.t) (d: A.array S8.t)
               (n: SZ.t) (lim8: SZ.t) (lim: SZ.t)
               (#ph: perm) (#vh: erased (Seq.seq S8.t))
               (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to h #ph vh ** A.pts_to d #pd vd ** pure (
  Alg.pows_ok (vals vh) /\ Seq.length vh == 128 /\
  Vec.bv y == Alg.hblk (vals vh) 0 /\
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  SZ.v lim <= SZ.v n /\ SZ.v lim % 64 == 0 /\
  SZ.v lim8 <= SZ.v lim /\ SZ.v lim8 % 128 == 0)
returns r: Vec.t
ensures A.pts_to h #ph vh ** A.pts_to d #pd vd ** pure (
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v lim / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  Vec.bv r == G.ghash_from (Poly.xtimes (Vec.bv y)) (Vec.bv a0)
                           (Seq.slice (vals vd) 0 (SZ.v n)) (SZ.v lim / blocklen))
{
  A.pts_to_len d;
  A.pts_to_len h;
  vals_len vd;
  vals_len vh;
  slice_len_mod vd (SZ.v n);
  Math.lemma_div_le (SZ.v lim) (SZ.v n) blocklen;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;
  if SZ.gt lim 0sz
  {
    let y2 = load_pow h 1sz;
    let y3 = load_pow h 2sz;
    let y4 = load_pow h 3sz;
    if SZ.gt lim8 0sz
    {
      let y5 = load_pow h 4sz;
      let y6 = load_pow h 5sz;
      let y7 = load_pow h 6sz;
      let y8 = load_pow h 7sz;
      let r8 = ghash_loop8_ni a0 y y2 y3 y4 y5 y6 y7 y8 d n lim8;
      Math.multiple_modulo_lemma (SZ.v lim8 / 128 * 2) 64;
      Math.euclidean_division_definition (SZ.v lim8) 128;
      ghash_loop4_ni r8 y y2 y3 y4 d n lim8 lim #(hide (Vec.bv a0))
    }
    else
    {
      ghash_zero (Poly.xtimes (Vec.bv y)) (Vec.bv a0) (Seq.slice (vals vd) 0 (SZ.v n));
      ghash_loop4_ni a0 y y2 y3 y4 d n 0sz lim #(hide (Vec.bv a0))
    }
  }
  else
  {
    ghash_zero (Poly.xtimes (Vec.bv y)) (Vec.bv a0) (Seq.slice (vals vd) 0 (SZ.v n));
    a0
  }
}

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))" ""]
fn ghash_loop_ni (acc: A.array S8.t) (h: A.array S8.t) (d: A.array S8.t) (n: SZ.t)
                 (#va0 #vh: erased (Seq.seq S8.t))
                 (#pd: perm) (#vd: erased (Seq.seq S8.t))
requires A.pts_to acc va0 ** A.pts_to h vh ** A.pts_to d #pd vd ** pure (
  Seq.length va0 == blocklen /\ Alg.pows_ok (vals vh) /\ Seq.length vh == 128 /\
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0)
ensures exists* (va1: Seq.seq S8.t).
  A.pts_to acc va1 ** A.pts_to h vh ** A.pts_to d #pd vd ** pure (
  Seq.length va0 == blocklen /\ Seq.length vh == 128 /\
  Seq.length va1 == blocklen /\
  SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
  Seq.length (Seq.slice (vals vd) 0 (SZ.v n)) % blocklen == 0 /\
  SZ.v n / blocklen == G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
  vals va1 == G.ghash_from (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0)
                           (Seq.slice (vals vd) 0 (SZ.v n)) (SZ.v n / blocklen))
{
  let lim = four_limit n;
  let lim8 = eight_limit n lim;
  A.pts_to_len acc;
  A.pts_to_len h;
  A.pts_to_len d;
  vals_len vh;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;

  let y = load_pow h 0sz;
  let a0 = Vec.load acc #(as_blk va0);
  let r = ghash_start a0 y h d n lim8 lim;
  let mut av = r;
  let mut i = lim;

  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (cur: Vec.t).
    pts_to i vi ** pts_to av cur **
    A.pts_to acc va0 ** A.pts_to h vh ** A.pts_to d #pd vd **
    pure (SZ.v vi <= SZ.v n /\ SZ.v vi % blocklen == 0 /\
          Seq.length va0 == blocklen /\ Seq.length vh == 128 /\
          SZ.v n <= Seq.length vd /\ SZ.v n % blocklen == 0 /\
          Vec.bv y == Alg.hblk (vals vh) 0 /\
          SZ.v vi / blocklen <= G.nblocks (Seq.slice (vals vd) 0 (SZ.v n)) /\
          Vec.bv cur == G.ghash_from (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0)
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
    ghash_step (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0) (vals vd) (SZ.v n) (SZ.v vi);
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
