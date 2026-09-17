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
  A.pts_to_len acc;
  A.pts_to_len h;
  A.pts_to_len d;
  Math.multiple_division_lemma (SZ.v n / blocklen) blocklen;
  Math.euclidean_division_definition (SZ.v n) blocklen;

  ghash_zero (vals vh) (vals va0) (Seq.slice (vals vd) 0 (SZ.v n));
  let y = Vec.load h #(as_blk vh);
  let a0 = Vec.load acc #(as_blk va0);
  let mut av = a0;
  let mut i = 0sz;

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
