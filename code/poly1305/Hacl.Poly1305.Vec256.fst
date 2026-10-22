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

(** Poly1305 on AVX2: four blocks at a time, one per sixty-four-bit lane.

    {2 The idea}

    Four accumulators run side by side, lane [j] absorbing blocks
    [j, j+4, j+8, ...], and each is multiplied by [r^4] instead of [r]
    between blocks.  At the end lane [j] is multiplied by the power of [r]
    its blocks are still owed and the four are added.  Why that is the
    specification's single chain is [Spec.Poly1305.Vec]; this module is the
    claim that the vector code computes those numbers.

    {2 The arithmetic}

    A lane holds a limb of radix [2^26], as [Hacl.Poly1305.Field] does, so
    the field multiplication is the scalar one with every operation widened
    to four lanes: twenty-five [VPMULUDQ]s and the same two-way carry chain.
    The only change is that the multiplier is a power of [r] that has been
    through a carry, so its limbs are bounded by [2^27] rather than [2^26];
    [Spec.Poly1305.Vec.mul_reduce_ok27] is the scalar lemma with that bit.

    {2 The order of the lanes}

    Two thirty-two-byte loads and an unpack put the low words of four blocks
    in one register and the high words in another, but [VPUNPCKLQDQ] works
    inside each half, so the lanes come out holding blocks [0, 2, 1, 3]
    rather than [0, 1, 2, 3].  Rather than spend a permute per group fixing
    that, the final multiplication gives lane [j] the power its block needs:
    [r^4, r^2, r^3, r]. *)
module Hacl.Poly1305.Vec256

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Spec.Loops
open Spec.Poly1305.Field
open Spec.Poly1305.Vec
open Hacl.Poly1305.Field

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module G = FStar.Ghost
module V = Hacl.Vec256
module Sub = Hacl.Impl.Sub
module Classical = FStar.Classical
module Spec = Spec.Poly1305
module Mem = Hacl.Mem

(** {2 The vector operations}

    The intrinsics are total, so the code calls them directly and every fact
    about what a lane holds is proved in a lemma, one lane at a time.  The
    Pulse functions below only ever have to see that the vector they stored
    is the expression the lemma talks about. *)

inline_for_extraction noextract
let vshr26 (a: V.t) : V.t = V.shr64 a 26ul

inline_for_extraction noextract
let vtimes5 (a: V.t) : V.t = V.add64 (V.shl64 a 2ul) a

(** One column of the schoolbook product: five products summed. *)
inline_for_extraction noextract
let vcol (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4: V.t) : V.t =
  V.add64 (V.add64 (V.add64 (V.add64 (V.mul32 a0 b0) (V.mul32 a1 b1))
                            (V.mul32 a2 b2)) (V.mul32 a3 b3)) (V.mul32 a4 b4)

(** The carry chain of [Spec.Poly1305.Field.chain], by name. *)
inline_for_extraction noextract
let cx1 (e0 e1: V.t) : V.t = V.add64 e1 (vshr26 e0)
inline_for_extraction noextract
let cx4 (e3 e4: V.t) : V.t = V.add64 e4 (vshr26 e3)
inline_for_extraction noextract
let cx01 (e0 x4: V.t) : V.t = V.add64 (V.mask26 e0) (vtimes5 (vshr26 x4))
inline_for_extraction noextract
let cx2 (e2 x1: V.t) : V.t = V.add64 e2 (vshr26 x1)
inline_for_extraction noextract
let cx31 (e3 x2: V.t) : V.t = V.add64 (V.mask26 e3) (vshr26 x2)
inline_for_extraction noextract
let cadd (x y: V.t) : V.t = V.add64 (V.mask26 x) (vshr26 y)

(** {2 One lane at a time} *)

let l64 (x: V.t) (i: nat) : GTot nat = if i < 4 then V.lane64 x i else 0

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

let add_lane (a b: V.t) (i: nat)
  : Lemma (requires i < 4 /\ l64 a i + l64 b i < pow2 64)
          (ensures l64 (V.add64 a b) i == l64 a i + l64 b i)
  = Math.small_mod (l64 a i + l64 b i) (pow2 64)

let mul_lane (a b: V.t) (i: nat)
  : Lemma (requires i < 4 /\ l64 a i < pow2 28 /\ l64 b i < pow2 30)
          (ensures l64 (V.mul32 a b) i == l64 a i * l64 b i /\
                   l64 (V.mul32 a b) i < pow2 58)
  = let x = l64 a i in
    let y = l64 b i in
    Math.pow2_lt_compat 32 28;
    Math.pow2_lt_compat 32 30;
    Math.small_mod x (pow2 32);
    Math.small_mod y (pow2 32);
    assert_norm ((pow2 28 - 1) * (pow2 30 - 1) < pow2 58);
    Math.lemma_mult_le_right y x (pow2 28 - 1);
    Math.lemma_mult_le_left (pow2 28 - 1) y (pow2 30 - 1)

let shr_lane (a: V.t) (i: nat)
  : Lemma (requires i < 4) (ensures l64 (vshr26 a) i == l64 a i / radix)
  = ()

let mask_lane (a: V.t) (i: nat)
  : Lemma (requires i < 4) (ensures l64 (V.mask26 a) i == l64 a i % radix)
  = ()

let shl2_lane (a: V.t) (i: nat)
  : Lemma (requires i < 4 /\ l64 a i < pow2 61)
          (ensures l64 (V.shl64 a 2ul) i == 4 * l64 a i)
  = let x = l64 a i in
    assert_norm (pow2 2 == 4);
    assert_norm (4 * pow2 61 < pow2 64);
    assert (x * pow2 2 == x * 4);
    Math.swap_mul x 4;
    Math.small_mod (4 * x) (pow2 64)

let lin5 (x: nat) : Lemma (4 * x + x == 5 * x) = ()

let times5_lane (a: V.t) (i: nat)
  : Lemma (requires i < 4 /\ l64 a i < pow2 61)
          (ensures l64 (vtimes5 a) i == 5 * l64 a i)
  = assert_norm (5 * pow2 61 < pow2 64);
    shl2_lane a i;
    add_lane (V.shl64 a 2ul) a i;
    lin5 (l64 a i)

let col_lane (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4: V.t) (i: nat)
  : Lemma (requires i < 4 /\
                    l64 a0 i < pow2 28 /\ l64 a1 i < pow2 28 /\ l64 a2 i < pow2 28 /\
                    l64 a3 i < pow2 28 /\ l64 a4 i < pow2 28 /\
                    l64 b0 i < pow2 30 /\ l64 b1 i < pow2 30 /\ l64 b2 i < pow2 30 /\
                    l64 b3 i < pow2 30 /\ l64 b4 i < pow2 30)
          (ensures l64 (vcol a0 b0 a1 b1 a2 b2 a3 b3 a4 b4) i ==
                   l64 a0 i * l64 b0 i + l64 a1 i * l64 b1 i + l64 a2 i * l64 b2 i +
                   l64 a3 i * l64 b3 i + l64 a4 i * l64 b4 i)
  = let p0 = V.mul32 a0 b0 in
    let p1 = V.mul32 a1 b1 in
    let p2 = V.mul32 a2 b2 in
    let p3 = V.mul32 a3 b3 in
    let p4 = V.mul32 a4 b4 in
    mul_lane a0 b0 i; mul_lane a1 b1 i; mul_lane a2 b2 i; mul_lane a3 b3 i; mul_lane a4 b4 i;
    assert_norm (5 * pow2 58 < pow2 64);
    add_lane p0 p1 i;
    add_lane (V.add64 p0 p1) p2 i;
    add_lane (V.add64 (V.add64 p0 p1) p2) p3 i;
    add_lane (V.add64 (V.add64 (V.add64 p0 p1) p2) p3) p4 i

#pop-options

(** {2 A field element per lane}

    Five vectors are four field elements; [lv s k i] is limb [k] of the one
    in lane [i].  Total in both indices so that it can appear in a
    quantifier without a guard.  The predicates over all four lanes are
    opaque: the Pulse code passes them from lemma to lemma and never has to
    look inside. *)

let lv (s: Seq.seq V.t) (k: nat) (i: nat) : GTot nat =
  if k < Seq.length s then l64 (Seq.index s k) i else 0

let fl (s: Seq.seq V.t) (i: nat) : GTot nat =
  as_nat5 (lv s 0 i) (lv s 1 i) (lv s 2 i) (lv s 3 i) (lv s 4 i)

let lbounded (s: Seq.seq V.t) (i: nat) (n: nat) : prop =
  bounded5 (lv s 0 i) (lv s 1 i) (lv s 2 i) (lv s 3 i) (lv s 4 i) n

[@@"opaque_to_smt"]
let vbounded (s: Seq.seq V.t) (n: nat) : prop =
  forall (i: nat). i < 4 ==> lbounded s i n

(** The multiplier: five limbs, then four of them times five. *)
let has5_at (s: Seq.seq V.t) (i: nat) : prop =
  lv s 5 i == 5 * lv s 1 i /\ lv s 6 i == 5 * lv s 2 i /\
  lv s 7 i == 5 * lv s 3 i /\ lv s 8 i == 5 * lv s 4 i

[@@"opaque_to_smt"]
let vhas5 (s: Seq.seq V.t) : prop = forall (i: nat). i < 4 ==> has5_at s i

let product_at (d h r: Seq.seq V.t) (i: nat) : prop =
    lv d 0 i == d0 (lv h 0 i) (lv h 1 i) (lv h 2 i) (lv h 3 i) (lv h 4 i)
                   (lv r 0 i) (lv r 1 i) (lv r 2 i) (lv r 3 i) (lv r 4 i) /\
    lv d 1 i == d1 (lv h 0 i) (lv h 1 i) (lv h 2 i) (lv h 3 i) (lv h 4 i)
                   (lv r 0 i) (lv r 1 i) (lv r 2 i) (lv r 3 i) (lv r 4 i) /\
    lv d 2 i == d2 (lv h 0 i) (lv h 1 i) (lv h 2 i) (lv h 3 i) (lv h 4 i)
                   (lv r 0 i) (lv r 1 i) (lv r 2 i) (lv r 3 i) (lv r 4 i) /\
    lv d 3 i == d3 (lv h 0 i) (lv h 1 i) (lv h 2 i) (lv h 3 i) (lv h 4 i)
                   (lv r 0 i) (lv r 1 i) (lv r 2 i) (lv r 3 i) (lv r 4 i) /\
    lv d 4 i == d4 (lv h 0 i) (lv h 1 i) (lv h 2 i) (lv h 3 i) (lv h 4 i)
                   (lv r 0 i) (lv r 1 i) (lv r 2 i) (lv r 3 i) (lv r 4 i)

let chain_at (d h: Seq.seq V.t) (i: nat) : prop =
  chain (lv d 0 i) (lv d 1 i) (lv d 2 i) (lv d 3 i) (lv d 4 i)
        (lv h 0 i) (lv h 1 i) (lv h 2 i) (lv h 3 i) (lv h 4 i)

[@@"opaque_to_smt"]
let vis_product (d h r: Seq.seq V.t) : prop = forall (i: nat). i < 4 ==> product_at d h r i

[@@"opaque_to_smt"]
let vchain (d h: Seq.seq V.t) : prop = forall (i: nat). i < 4 ==> chain_at d h i

[@@"opaque_to_smt"]
let vmul_post (h r h': Seq.seq V.t) : prop =
  vbounded h' 27 /\
  (forall (i: nat). i < 4 ==> fl h' i % prime == (fl h i * fl r i) % prime)

(** What the code stores, by name. *)
let is_product (d h r: Seq.seq V.t) : prop =
  Seq.length d == 5 /\ Seq.length h == 5 /\ Seq.length r == 9 /\
  (Seq.index d 0 == vcol (Seq.index h 0) (Seq.index r 0) (Seq.index h 1) (Seq.index r 8) (Seq.index h 2) (Seq.index r 7)
                  (Seq.index h 3) (Seq.index r 6) (Seq.index h 4) (Seq.index r 5) /\
   Seq.index d 1 == vcol (Seq.index h 0) (Seq.index r 1) (Seq.index h 1) (Seq.index r 0) (Seq.index h 2) (Seq.index r 8)
                  (Seq.index h 3) (Seq.index r 7) (Seq.index h 4) (Seq.index r 6) /\
   Seq.index d 2 == vcol (Seq.index h 0) (Seq.index r 2) (Seq.index h 1) (Seq.index r 1) (Seq.index h 2) (Seq.index r 0)
                  (Seq.index h 3) (Seq.index r 8) (Seq.index h 4) (Seq.index r 7) /\
   Seq.index d 3 == vcol (Seq.index h 0) (Seq.index r 3) (Seq.index h 1) (Seq.index r 2) (Seq.index h 2) (Seq.index r 1)
                  (Seq.index h 3) (Seq.index r 0) (Seq.index h 4) (Seq.index r 8) /\
   Seq.index d 4 == vcol (Seq.index h 0) (Seq.index r 4) (Seq.index h 1) (Seq.index r 3) (Seq.index h 2) (Seq.index r 2)
                  (Seq.index h 3) (Seq.index r 1) (Seq.index h 4) (Seq.index r 0))

let is_carry (d h: Seq.seq V.t) : prop =
  Seq.length d == 5 /\ Seq.length h == 5 /\
  (let e0 = Seq.index d 0 in let e1 = Seq.index d 1 in let e2 = Seq.index d 2 in
   let e3 = Seq.index d 3 in let e4 = Seq.index d 4 in
   let x1 = cx1 e0 e1 in
   let x4 = cx4 e3 e4 in
   let x01 = cx01 e0 x4 in
   let x2 = cx2 e2 x1 in
   let x31 = cx31 e3 x2 in
   Seq.index h 0 == V.mask26 x01 /\
   Seq.index h 1 == cadd x1 x01 /\
   Seq.index h 2 == V.mask26 x2 /\
   Seq.index h 3 == V.mask26 x31 /\
   Seq.index h 4 == cadd x4 x31)

(** {2 The lemmas the Pulse code calls} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"

let product_lane (d h r: Seq.seq V.t) (i: nat)
  : Lemma (requires i < 4 /\ is_product d h r /\
                    lbounded h i 28 /\ lbounded r i 27 /\ has5_at r i)
          (ensures product_at d h r i /\ lbounded d i 60)
  = let h0 = lv h 0 i in let h1 = lv h 1 i in let h2 = lv h 2 i in
    let h3 = lv h 3 i in let h4 = lv h 4 i in
    let r0 = lv r 0 i in let r1 = lv r 1 i in let r2 = lv r 2 i in
    let r3 = lv r 3 i in let r4 = lv r 4 i in
    assert_norm (5 * pow2 27 < pow2 30);
    Math.pow2_lt_compat 30 27;
    col_lane (Seq.index h 0) (Seq.index r 0) (Seq.index h 1) (Seq.index r 8) (Seq.index h 2) (Seq.index r 7) (Seq.index h 3) (Seq.index r 6) (Seq.index h 4) (Seq.index r 5) i;
    col_lane (Seq.index h 0) (Seq.index r 1) (Seq.index h 1) (Seq.index r 0) (Seq.index h 2) (Seq.index r 8) (Seq.index h 3) (Seq.index r 7) (Seq.index h 4) (Seq.index r 6) i;
    col_lane (Seq.index h 0) (Seq.index r 2) (Seq.index h 1) (Seq.index r 1) (Seq.index h 2) (Seq.index r 0) (Seq.index h 3) (Seq.index r 8) (Seq.index h 4) (Seq.index r 7) i;
    col_lane (Seq.index h 0) (Seq.index r 3) (Seq.index h 1) (Seq.index r 2) (Seq.index h 2) (Seq.index r 1) (Seq.index h 3) (Seq.index r 0) (Seq.index h 4) (Seq.index r 8) i;
    col_lane (Seq.index h 0) (Seq.index r 4) (Seq.index h 1) (Seq.index r 3) (Seq.index h 2) (Seq.index r 2) (Seq.index h 3) (Seq.index r 1) (Seq.index h 4) (Seq.index r 0) i;
    times5_assoc h1 r4; times5_assoc h2 r3; times5_assoc h3 r2; times5_assoc h4 r1;
    times5_assoc h2 r4; times5_assoc h3 r3; times5_assoc h4 r2;
    times5_assoc h3 r4; times5_assoc h4 r3; times5_assoc h4 r4;
    mul_no_overflow27 h0 h1 h2 h3 h4 r0 r1 r2 r3 r4

let product_ok (d h r: Seq.seq V.t)
  : Lemma (requires is_product d h r /\ vbounded h 28 /\ vbounded r 27 /\ vhas5 r)
          (ensures vis_product d h r /\ vbounded d 60)
  = reveal_opaque (`%vbounded) (vbounded h 28);
    reveal_opaque (`%vbounded) (vbounded r 27);
    reveal_opaque (`%vbounded) (vbounded d 60);
    reveal_opaque (`%vhas5) (vhas5 r);
    reveal_opaque (`%vis_product) (vis_product d h r);
    let aux (i: nat) : Lemma (i < 4 ==> product_at d h r i /\ lbounded d i 60)
      = if i < 4 then product_lane d h r i in
    Classical.forall_intro aux

let carry_lane (d h: Seq.seq V.t) (i: nat)
  : Lemma (requires i < 4 /\ is_carry d h /\ lbounded d i 60)
          (ensures chain_at d h i)
  = let e0 = Seq.index d 0 in let e1 = Seq.index d 1 in let e2 = Seq.index d 2 in
    let e3 = Seq.index d 3 in let e4 = Seq.index d 4 in
    let x1 = cx1 e0 e1 in
    let x4 = cx4 e3 e4 in
    let x01 = cx01 e0 x4 in
    let x2 = cx2 e2 x1 in
    let x31 = cx31 e3 x2 in
    chain_fits60 (l64 e0 i) (l64 e1 i) (l64 e2 i) (l64 e3 i) (l64 e4 i);
    assert_norm (pow2 61 < pow2 64);
    assert_norm (pow2 39 < pow2 64);
    assert_norm (pow2 27 < pow2 64);
    assert_norm (pow2 36 < pow2 64);
    Math.pow2_lt_compat 61 35;
    Math.pow2_lt_compat 60 26;
    Math.pow2_lt_compat 61 60;
    shr_lane e0 i; add_lane e1 (vshr26 e0) i;
    shr_lane e3 i; add_lane e4 (vshr26 e3) i;
    mask_lane e0 i; shr_lane x4 i; times5_lane (vshr26 x4) i;
    add_lane (V.mask26 e0) (vtimes5 (vshr26 x4)) i;
    shr_lane x1 i; add_lane e2 (vshr26 x1) i;
    mask_lane e3 i; shr_lane x2 i; add_lane (V.mask26 e3) (vshr26 x2) i;
    mask_lane x01 i;
    mask_lane x1 i; shr_lane x01 i; add_lane (V.mask26 x1) (vshr26 x01) i;
    mask_lane x2 i;
    mask_lane x31 i;
    mask_lane x4 i; shr_lane x31 i; add_lane (V.mask26 x4) (vshr26 x31) i

let carry_ok (d h: Seq.seq V.t)
  : Lemma (requires is_carry d h /\ vbounded d 60)
          (ensures vchain d h)
  = reveal_opaque (`%vbounded) (vbounded d 60);
    reveal_opaque (`%vchain) (vchain d h);
    let aux (i: nat) : Lemma (i < 4 ==> chain_at d h i)
      = if i < 4 then carry_lane d h i in
    Classical.forall_intro aux

let mul_ok (h r d h': Seq.seq V.t)
  : Lemma (requires vbounded h 28 /\ vbounded r 27 /\ vis_product d h r /\ vchain d h')
          (ensures vmul_post h r h')
  = reveal_opaque (`%vbounded) (vbounded h 28);
    reveal_opaque (`%vbounded) (vbounded r 27);
    reveal_opaque (`%vbounded) (vbounded h' 27);
    reveal_opaque (`%vis_product) (vis_product d h r);
    reveal_opaque (`%vchain) (vchain d h');
    reveal_opaque (`%vmul_post) (vmul_post h r h');
    let aux (i: nat) : Lemma (i < 4 ==> lbounded h' i 27 /\
                                fl h' i % prime == (fl h i * fl r i) % prime)
      = if i < 4 then
          mul_reduce_ok27 (lv h 0 i) (lv h 1 i) (lv h 2 i) (lv h 3 i) (lv h 4 i)
                          (lv r 0 i) (lv r 1 i) (lv r 2 i) (lv r 3 i) (lv r 4 i)
                          (lv h' 0 i) (lv h' 1 i) (lv h' 2 i) (lv h' 3 i) (lv h' 4 i) in
    Classical.forall_intro aux

let vmul_post_bounded (h r h': Seq.seq V.t)
  : Lemma (requires vmul_post h r h') (ensures vbounded h' 27)
  = reveal_opaque (`%vmul_post) (vmul_post h r h')

#pop-options

(** {2 Multiplication, four lanes at once}

    The same two halves as [Hacl.Poly1305.Field.fmul], for the same reason. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

inline_for_extraction noextract
fn write5 (d: A.array V.t) (x0 x1 x2 x3 x4: V.t) (#vd: erased (Seq.seq V.t))
requires A.pts_to d vd ** pure (Seq.length vd == 5)
ensures exists* (vd': Seq.seq V.t). A.pts_to d vd' **
  pure (Seq.length vd' == 5 /\ Seq.index vd' 0 == x0 /\ Seq.index vd' 1 == x1 /\
        Seq.index vd' 2 == x2 /\ Seq.index vd' 3 == x3 /\ Seq.index vd' 4 == x4)
{
  A.pts_to_len d;
  A.((d.(0sz) <- x0));
  A.((d.(1sz) <- x1));
  A.((d.(2sz) <- x2));
  A.((d.(3sz) <- x3));
  A.((d.(4sz) <- x4));
  A.pts_to_len d;
}

inline_for_extraction noextract
fn vmul_limbs (d: A.array V.t) (h: A.array V.t) (r: A.array V.t)
              (#vd: erased (Seq.seq V.t))
              (#vh: erased (Seq.seq V.t)) (#vr: erased (Seq.seq V.t))
requires A.pts_to d vd ** A.pts_to h vh ** A.pts_to r vr **
         pure (Seq.length vd == 5 /\ Seq.length vh == 5 /\ Seq.length vr == 9)
ensures exists* (vd': Seq.seq V.t).
  A.pts_to d vd' ** A.pts_to h vh ** A.pts_to r vr ** pure (is_product vd' vh vr)
{
  A.pts_to_len d;
  A.pts_to_len h;
  A.pts_to_len r;
  let h0 = A.(h.(0sz));
  let h1 = A.(h.(1sz));
  let h2 = A.(h.(2sz));
  let h3 = A.(h.(3sz));
  let h4 = A.(h.(4sz));
  let r0 = A.(r.(0sz));
  let r1 = A.(r.(1sz));
  let r2 = A.(r.(2sz));
  let r3 = A.(r.(3sz));
  let r4 = A.(r.(4sz));
  let q1 = A.(r.(5sz));
  let q2 = A.(r.(6sz));
  let q3 = A.(r.(7sz));
  let q4 = A.(r.(8sz));
  write5 d (vcol h0 r0 h1 q4 h2 q3 h3 q2 h4 q1)
           (vcol h0 r1 h1 r0 h2 q4 h3 q3 h4 q2)
           (vcol h0 r2 h1 r1 h2 r0 h3 q4 h4 q3)
           (vcol h0 r3 h1 r2 h2 r1 h3 r0 h4 q4)
           (vcol h0 r4 h1 r3 h2 r2 h3 r1 h4 r0);
}

inline_for_extraction noextract
fn vcarry (h: A.array V.t) (d: A.array V.t)
          (#vh: erased (Seq.seq V.t)) (#vd: erased (Seq.seq V.t))
requires A.pts_to h vh ** A.pts_to d vd **
         pure (Seq.length vh == 5 /\ Seq.length vd == 5)
ensures exists* (vh': Seq.seq V.t). A.pts_to h vh' ** A.pts_to d vd ** pure (is_carry vd vh')
{
  A.pts_to_len h;
  A.pts_to_len d;
  let e0 = A.(d.(0sz));
  let e1 = A.(d.(1sz));
  let e2 = A.(d.(2sz));
  let e3 = A.(d.(3sz));
  let e4 = A.(d.(4sz));
  let x1 = cx1 e0 e1;
  let x4 = cx4 e3 e4;
  let x01 = cx01 e0 x4;
  let x2 = cx2 e2 x1;
  let x31 = cx31 e3 x2;
  write5 h (V.mask26 x01) (cadd x1 x01) (V.mask26 x2) (V.mask26 x31) (cadd x4 x31);
}

(** [h <- h * r], lane by lane. *)
inline_for_extraction noextract
fn vfmul (h: A.array V.t) (r: A.array V.t) (d: A.array V.t)
         (#vh: erased (Seq.seq V.t)) (#vr: erased (Seq.seq V.t))
         (#vd: erased (Seq.seq V.t))
requires A.pts_to h vh ** A.pts_to r vr ** A.pts_to d vd **
         pure (Seq.length vh == 5 /\ Seq.length vr == 9 /\ Seq.length vd == 5 /\
               vbounded vh 28 /\ vbounded vr 27 /\ vhas5 vr)
ensures exists* (vh': Seq.seq V.t) (vd': Seq.seq V.t).
  A.pts_to h vh' ** A.pts_to r vr ** A.pts_to d vd' **
  pure (Seq.length vd' == 5 /\ Seq.length vh' == 5 /\ vmul_post vh vr vh')
{
  vmul_limbs d h r;
  with vd'. assert (A.pts_to d vd');
  product_ok vd' vh vr;
  vcarry h d;
  with vh'. assert (A.pts_to h vh');
  carry_ok vd' vh';
  mul_ok vh vr vd' vh';
  A.pts_to_len h;
}

#pop-options

(** {2 Four blocks into four lanes}

    The bytes a register was loaded from are its sixty-four-bit lanes,
    little-endian; the unpacks pick lanes; and two lanes are a block. *)

let sig (j: nat) : nat = if j = 1 then 2 else if j = 2 then 1 else j

let blo (msg: Seq.seq S8.t) (b: nat { 16 * b + 16 <= Seq.length msg }) : GTot nat =
  le_nat (Seq.slice msg (16 * b) (16 * b + 8))

let bhi (msg: Seq.seq S8.t) (b: nat { 16 * b + 16 <= Seq.length msg }) : GTot nat =
  le_nat (Seq.slice msg (16 * b + 8) (16 * b + 16))

let in_window (msg: Seq.seq S8.t) (g: nat) (v0 v1: V.t) : prop =
  16 * g + 64 <= Seq.length msg /\
  V.vv v0 == Seq.slice msg (16 * g) (16 * g + 32) /\
  V.vv v1 == Seq.slice msg (16 * g + 32) (16 * g + 64)

(** Two words to five limbs, as [Hacl.Poly1305.Load.store_limbs] does it;
    [c] is [2^24] in every lane. *)
inline_for_extraction noextract
let mk0 (lo: V.t) : V.t = V.mask26 lo
inline_for_extraction noextract
let mk1 (lo: V.t) : V.t = V.mask26 (vshr26 lo)
inline_for_extraction noextract
let mk2 (lo hi: V.t) : V.t = V.add64 (V.shr64 lo 52ul) (V.mask26 (V.shl64 hi 12ul))
inline_for_extraction noextract
let mk3 (hi: V.t) : V.t = V.mask26 (V.shr64 hi 14ul)
inline_for_extraction noextract
let mk4 (hi c: V.t) : V.t = V.add64 (V.shr64 hi 40ul) c

let is24 (c: V.t) : prop = forall (i: nat). i < 4 ==> V.lane64 c i == pow2 24

let is_load (m: Seq.seq V.t) (v0 v1 c: V.t) : prop =
  Seq.length m == 5 /\
  (let lo = V.unpacklo64 v0 v1 in
   let hi = V.unpackhi64 v0 v1 in
   Seq.index m 0 == mk0 lo /\ Seq.index m 1 == mk1 lo /\ Seq.index m 2 == mk2 lo hi /\
   Seq.index m 3 == mk3 hi /\ Seq.index m 4 == mk4 hi c)

[@@"opaque_to_smt"]
let vload (m: Seq.seq V.t) (msg: Seq.seq S8.t) (g: nat) : prop =
  16 * g + 64 <= Seq.length msg /\ Seq.length m == 5 /\ vbounded m 26 /\
  fl m 0 == bv msg g /\ fl m 1 == bv msg (g + 2) /\
  fl m 2 == bv msg (g + 1) /\ fl m 3 == bv msg (g + 3)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let lane_le (x: V.t) (k: nat)
  : Lemma (requires k < 8)
          (ensures S32.v (V.lane x k) == le_nat (Seq.slice (V.vv x) (4 * k) (4 * k + 4)))
  = le_nat_bound (sub_block #S32.t 8 (V.vv x) k)

let lane64_le (x: V.t) (i: nat)
  : Lemma (requires i < 4)
          (ensures V.lane64 x i == le_nat (Seq.slice (V.vv x) (8 * i) (8 * i + 8)))
  = let s = V.vv x in
    let s8 = Seq.slice s (8 * i) (8 * i + 8) in
    lane_le x (2 * i);
    lane_le x (2 * i + 1);
    le_nat_split s8 4;
    Seq.slice_slice s (8 * i) (8 * i + 8) 0 4;
    Seq.slice_slice s (8 * i) (8 * i + 8) 4 8;
    assert_norm (pow2 (8 * 4) == pow2 32)

let lane64_lt (x: V.t) (i: nat)
  : Lemma (requires i < 4) (ensures V.lane64 x i < pow2 64)
  = let a = S32.v (V.lane x (2 * i)) in
    let b = S32.v (V.lane x (2 * i + 1)) in
    assert_norm (pow2 32 * pow2 32 == pow2 64);
    Math.lemma_mult_le_left (pow2 32) b (pow2 32 - 1)

let half_le (v: V.t) (msg: Seq.seq S8.t) (o: nat) (i: nat)
  : Lemma (requires i < 4 /\ o + 32 <= Seq.length msg /\ V.vv v == Seq.slice msg o (o + 32))
          (ensures V.lane64 v i == le_nat (Seq.slice msg (o + 8 * i) (o + 8 * i + 8)))
  = lane64_le v i;
    Seq.slice_slice msg o (o + 32) (8 * i) (8 * i + 8)

let gather_lane (msg: Seq.seq S8.t) (g: nat) (v0 v1: V.t) (j: nat)
  : Lemma (requires j < 4 /\ in_window msg g v0 v1)
          (ensures 16 * (g + sig j) + 16 <= Seq.length msg /\
                   l64 (V.unpacklo64 v0 v1) j == blo msg (g + sig j) /\
                   l64 (V.unpackhi64 v0 v1) j == bhi msg (g + sig j))
  = let o = 16 * g in
    half_le v0 msg o 0; half_le v0 msg o 1; half_le v0 msg o 2; half_le v0 msg o 3;
    half_le v1 msg (o + 32) 0; half_le v1 msg (o + 32) 1;
    half_le v1 msg (o + 32) 2; half_le v1 msg (o + 32) 3

let block_split (msg: Seq.seq S8.t) (b: nat)
  : Lemma (requires 16 * b + 16 <= Seq.length msg)
          (ensures blo msg b + pow2 64 * bhi msg b + pow2 128 == bv msg b)
  = let blk = Seq.slice msg (16 * b) (16 * b + 16) in
    le_nat_split blk 8;
    Seq.slice_slice msg (16 * b) (16 * b + 16) 0 8;
    Seq.slice_slice msg (16 * b) (16 * b + 16) 8 16;
    assert_norm (pow2 (8 * 8) == pow2 64);
    assert_norm (pow2 (8 * 16) == pow2 128)

let limbs_lane (lo hi c: V.t) (j: nat)
  : Lemma (requires j < 4 /\ l64 c j == pow2 24)
          (ensures (let a0 = l64 (mk0 lo) j in let a1 = l64 (mk1 lo) j in
                    let a2 = l64 (mk2 lo hi) j in let a3 = l64 (mk3 hi) j in
                    let a4 = l64 (mk4 hi c) j in
                    as_nat5 a0 a1 a2 a3 a4 == l64 lo j + pow2 64 * l64 hi j + pow2 128 /\
                    bounded5 a0 a1 a2 a3 a4 26))
  = let x = l64 lo j in
    let y = l64 hi j in
    lane64_lt lo j;
    lane64_lt hi j;
    load_limbs x y 1;
    Math.pow2_lt_compat 64 26;
    Math.pow2_modulo_modulo_lemma_1 (y * pow2 12) 26 64;
    Math.pow2_multiplication_modulo_lemma_2 y 26 12;
    add_lane (V.shr64 lo 52ul) (V.mask26 (V.shl64 hi 12ul)) j;
    add_lane (V.shr64 hi 40ul) c j

let load_ok (m: Seq.seq V.t) (v0 v1 c: V.t) (msg: Seq.seq S8.t) (g: nat)
  : Lemma (requires is_load m v0 v1 c /\ in_window msg g v0 v1 /\ is24 c)
          (ensures vload m msg g)
  = reveal_opaque (`%vload) (vload m msg g);
    reveal_opaque (`%vbounded) (vbounded m 26);
    let lo = V.unpacklo64 v0 v1 in
    let hi = V.unpackhi64 v0 v1 in
    let aux (j: nat) : Lemma (j < 4 ==> lbounded m j 26 /\ fl m j == bv msg (g + sig j))
      = if j < 4 then begin
          gather_lane msg g v0 v1 j;
          limbs_lane lo hi c j;
          block_split msg (g + sig j)
        end in
    Classical.forall_intro aux;
    aux 0; aux 1; aux 2; aux 3

#pop-options

(** {2 Adding, the multipliers, and the loop invariant} *)

let is_add (a' a b: Seq.seq V.t) : prop =
  Seq.length a' == 5 /\ Seq.length a == 5 /\ Seq.length b == 5 /\
  Seq.index a' 0 == V.add64 (Seq.index a 0) (Seq.index b 0) /\
  Seq.index a' 1 == V.add64 (Seq.index a 1) (Seq.index b 1) /\
  Seq.index a' 2 == V.add64 (Seq.index a 2) (Seq.index b 2) /\
  Seq.index a' 3 == V.add64 (Seq.index a 3) (Seq.index b 3) /\
  Seq.index a' 4 == V.add64 (Seq.index a 4) (Seq.index b 4)

[@@"opaque_to_smt"]
let vsum (a' a b: Seq.seq V.t) : prop =
  vbounded a' 28 /\ (forall (i: nat). i < 4 ==> fl a' i == fl a i + fl b i)

(** The multiplier's last four limbs are five times its limbs one to four. *)
let is_mult (m: Seq.seq V.t) : prop =
  Seq.length m == 9 /\
  Seq.index m 5 == vtimes5 (Seq.index m 1) /\ Seq.index m 6 == vtimes5 (Seq.index m 2) /\
  Seq.index m 7 == vtimes5 (Seq.index m 3) /\ Seq.index m 8 == vtimes5 (Seq.index m 4)

(** The same number in every lane. *)
let is_bc (m: Seq.seq V.t) (s: Seq.seq S64.t) : prop =
  Seq.length m >= 5 /\ Seq.length s >= 5 /\
  Seq.index m 0 == V.bcast64 (Seq.index s 0) /\ Seq.index m 1 == V.bcast64 (Seq.index s 1) /\
  Seq.index m 2 == V.bcast64 (Seq.index s 2) /\ Seq.index m 3 == V.bcast64 (Seq.index s 3) /\
  Seq.index m 4 == V.bcast64 (Seq.index s 4)

(** Four numbers, one per lane. *)
let is_set (m: Seq.seq V.t) (s0 s1 s2 s3: Seq.seq S64.t) : prop =
  Seq.length m >= 5 /\
  Seq.length s0 >= 5 /\ Seq.length s1 >= 5 /\ Seq.length s2 >= 5 /\ Seq.length s3 >= 5 /\
  Seq.index m 0 == V.set64 (Seq.index s0 0) (Seq.index s1 0) (Seq.index s2 0) (Seq.index s3 0) /\
  Seq.index m 1 == V.set64 (Seq.index s0 1) (Seq.index s1 1) (Seq.index s2 1) (Seq.index s3 1) /\
  Seq.index m 2 == V.set64 (Seq.index s0 2) (Seq.index s1 2) (Seq.index s2 2) (Seq.index s3 2) /\
  Seq.index m 3 == V.set64 (Seq.index s0 3) (Seq.index s1 3) (Seq.index s2 3) (Seq.index s3 3) /\
  Seq.index m 4 == V.set64 (Seq.index s0 4) (Seq.index s1 4) (Seq.index s2 4) (Seq.index s3 4)

[@@"opaque_to_smt"]
let vbc (m: Seq.seq V.t) (q: nat) : prop =
  Seq.length m == 9 /\ vbounded m 27 /\ vhas5 m /\
  (forall (i: nat). i < 4 ==> fl m i == q)

let zeros5 : Seq.seq S64.t = Seq.create 5 (S64.classify 0uL)

let pows (rr a2 a3 a4: nat) : prop =
  cong a2 (r2 rr) /\ cong a3 (r3 rr) /\ cong a4 (r4 rr)

(** The four accumulators, lanes in block order [0, 2, 1, 3]. *)
[@@"opaque_to_smt"]
let vinv (a: Seq.seq V.t) (msg: Seq.seq S8.t) (rr acc: nat) (g: nat) : prop =
  Seq.length a == 5 /\ vbounded a 28 /\ hinv msg rr acc g (fl a 0) (fl a 2) (fl a 1) (fl a 3)

let hs (a: Seq.seq V.t) (k: nat) : GTot nat = lv a k 0 + lv a k 1 + lv a k 2 + lv a k 3

let is_hsum (e: Seq.seq S64.t) (a: Seq.seq V.t) : prop =
  Seq.length e == 5 /\
  vv e 0 == hs a 0 /\ vv e 1 == hs a 1 /\ vv e 2 == hs a 2 /\ vv e 3 == hs a 3 /\ vv e 4 == hs a 4

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let bounded_weak (s: Seq.seq S64.t) (m n: nat)
  : Lemma (requires bounded s m /\ m <= n) (ensures bounded s n)
  = Math.pow2_le_compat n m

let same5 (a b: Seq.seq S64.t) (n: nat)
  : Lemma (requires Seq.length a == 5 /\ Seq.length b >= 5 /\ bounded b n /\
                    Seq.index a 0 == Seq.index b 0 /\ Seq.index a 1 == Seq.index b 1 /\
                    Seq.index a 2 == Seq.index b 2 /\ Seq.index a 3 == Seq.index b 3 /\
                    Seq.index a 4 == Seq.index b 4)
          (ensures feval a == feval b /\ bounded a n)
  = ()

let add_at (a' a b: Seq.seq V.t) (i: nat)
  : Lemma (requires i < 4 /\ is_add a' a b /\ lbounded a i 27 /\ lbounded b i 26)
          (ensures lbounded a' i 28 /\ fl a' i == fl a i + fl b i)
  = assert_norm (pow2 27 + pow2 26 < pow2 28);
    Math.pow2_lt_compat 64 28;
    add_lane (Seq.index a 0) (Seq.index b 0) i;
    add_lane (Seq.index a 1) (Seq.index b 1) i;
    add_lane (Seq.index a 2) (Seq.index b 2) i;
    add_lane (Seq.index a 3) (Seq.index b 3) i;
    add_lane (Seq.index a 4) (Seq.index b 4) i;
    add5_eval (lv a 0 i) (lv a 1 i) (lv a 2 i) (lv a 3 i) (lv a 4 i)
              (lv b 0 i) (lv b 1 i) (lv b 2 i) (lv b 3 i) (lv b 4 i)

let add_ok (a' a b: Seq.seq V.t)
  : Lemma (requires is_add a' a b /\ vbounded a 27 /\ vbounded b 26)
          (ensures vsum a' a b)
  = reveal_opaque (`%vsum) (vsum a' a b);
    reveal_opaque (`%vbounded) (vbounded a 27);
    reveal_opaque (`%vbounded) (vbounded b 26);
    reveal_opaque (`%vbounded) (vbounded a' 28);
    let aux (i: nat) : Lemma (i < 4 ==> lbounded a' i 28 /\ fl a' i == fl a i + fl b i)
      = if i < 4 then add_at a' a b i in
    Classical.forall_intro aux

let mult_ok (m: Seq.seq V.t)
  : Lemma (requires is_mult m /\ vbounded m 27) (ensures vhas5 m)
  = reveal_opaque (`%vhas5) (vhas5 m);
    reveal_opaque (`%vbounded) (vbounded m 27);
    let aux (i: nat) : Lemma (i < 4 ==> has5_at m i)
      = if i < 4 then begin
          assert (lbounded m i 27);
          Math.pow2_lt_compat 61 27;
          times5_lane (Seq.index m 1) i;
          times5_lane (Seq.index m 2) i;
          times5_lane (Seq.index m 3) i;
          times5_lane (Seq.index m 4) i
        end in
    Classical.forall_intro aux

let bc_ok (m: Seq.seq V.t) (s: Seq.seq S64.t)
  : Lemma (requires is_bc m s /\ is_mult m /\ bounded s 27)
          (ensures vbc m (feval s))
  = reveal_opaque (`%vbc) (vbc m (feval s));
    reveal_opaque (`%vbounded) (vbounded m 27);
    let aux (i: nat) : Lemma (i < 4 ==> lbounded m i 27 /\ fl m i == feval s)
      = () in
    Classical.forall_intro aux;
    mult_ok m

let vbc_elim (m: Seq.seq V.t) (q: nat)
  : Lemma (requires vbc m q) (ensures Seq.length m == 9 /\ vbounded m 27 /\ vhas5 m)
  = reveal_opaque (`%vbc) (vbc m q)

let set_ok (m: Seq.seq V.t) (s0 s1 s2 s3: Seq.seq S64.t)
  : Lemma (requires is_set m s0 s1 s2 s3 /\
                    bounded s0 27 /\ bounded s1 27 /\ bounded s2 27 /\ bounded s3 27)
          (ensures vbounded m 27 /\ fl m 0 == feval s0 /\ fl m 1 == feval s1 /\
                   fl m 2 == feval s2 /\ fl m 3 == feval s3)
  = reveal_opaque (`%vbounded) (vbounded m 27);
    let aux (i: nat) : Lemma (i < 4 ==> lbounded m i 27) = () in
    Classical.forall_intro aux

let set_mult_ok (m: Seq.seq V.t) (s0 s1 s2 s3: Seq.seq S64.t)
  : Lemma (requires is_set m s0 s1 s2 s3 /\ is_mult m /\
                    bounded s0 27 /\ bounded s1 27 /\ bounded s2 27 /\ bounded s3 27)
          (ensures vbounded m 27 /\ vhas5 m)
  = set_ok m s0 s1 s2 s3;
    mult_ok m

let pow_first (rr a: nat)
  : Lemma (requires a % prime == (rr * rr) % prime) (ensures cong a (r2 rr))
  = ()

let pow_next (rr a b c: nat)
  : Lemma (requires cong a b /\ c % prime == (a * rr) % prime) (ensures cong c (rr * b))
  = cong_mul a b rr rr;
    Math.swap_mul b rr

let pows_ok (rr a2 a3 a4: nat)
  : Lemma (requires a2 % prime == (rr * rr) % prime /\
                    a3 % prime == (a2 * rr) % prime /\
                    a4 % prime == (a3 * rr) % prime)
          (ensures pows rr a2 a3 a4)
  = pow_first rr a2;
    pow_next rr a2 (r2 rr) a3;
    pow_next rr a3 (r3 rr) a4

let lanes27 (s: Seq.seq V.t) (k: nat)
  : Lemma (requires vbounded s 27 /\ Seq.length s == 5 /\ k < 5)
          (ensures l64 (Seq.index s k) 0 < pow2 27 /\ l64 (Seq.index s k) 1 < pow2 27 /\
                   l64 (Seq.index s k) 2 < pow2 27 /\ l64 (Seq.index s k) 3 < pow2 27)
  = reveal_opaque (`%vbounded) (vbounded s 27);
    assert (lbounded s 0 27);
    assert (lbounded s 1 27);
    assert (lbounded s 2 27);
    assert (lbounded s 3 27)

#pop-options

let zeros_ok (_: unit)
  : Lemma (bounded zeros5 27 /\ feval zeros5 == 0 /\ Seq.length zeros5 == 5 /\
           Seq.index zeros5 0 == S64.classify 0uL /\ Seq.index zeros5 1 == S64.classify 0uL /\
           Seq.index zeros5 2 == S64.classify 0uL /\ Seq.index zeros5 3 == S64.classify 0uL /\
           Seq.index zeros5 4 == S64.classify 0uL)
  = let z = zeros5 in
    assert (Seq.index z 0 == S64.classify 0uL /\ Seq.index z 1 == S64.classify 0uL /\ Seq.index z 2 == S64.classify 0uL /\
            Seq.index z 3 == S64.classify 0uL /\ Seq.index z 4 == S64.classify 0uL);
    assert (vv z 0 == 0 /\ vv z 1 == 0 /\ vv z 2 == 0 /\ vv z 3 == 0 /\ vv z 4 == 0);
    assert_norm (as_nat5 0 0 0 0 0 == 0)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let init_ok (a hh m: Seq.seq V.t) (h: Seq.seq S64.t) (msg: Seq.seq S8.t) (rr acc: nat)
  : Lemma (requires Seq.length hh == 5 /\ is_set hh h zeros5 zeros5 zeros5 /\
                    bounded h 27 /\ feval h % prime == acc /\
                    vload m msg 0 /\ is_add a hh m)
          (ensures vinv a msg rr acc 4)
  = zeros_ok ();
    set_ok hh h zeros5 zeros5 zeros5;
    reveal_opaque (`%vload) (vload m msg 0);
    reveal_opaque (`%vinv) (vinv a msg rr acc 4);
    add_ok a hh m;
    reveal_opaque (`%vsum) (vsum a hh m);
    assert (fl a 0 == fl hh 0 + fl m 0);
    assert (fl a 1 == fl hh 1 + fl m 1);
    assert (fl a 2 == fl hh 2 + fl m 2);
    assert (fl a 3 == fl hh 3 + fl m 3);
    assert (fl hh 0 == feval h /\ fl hh 1 == 0 /\ fl hh 2 == 0 /\ fl hh 3 == 0);
    assert (fl m 0 == bv msg 0 /\ fl m 1 == bv msg 2 /\ fl m 2 == bv msg 1 /\ fl m 3 == bv msg 3);
    Math.lemma_mod_twice (feval h) prime;
    horner_init msg rr acc (feval h) (fl a 0) (fl a 2) (fl a 1) (fl a 3)

let step_ok (a a1 m a2 r4m: Seq.seq V.t) (msg: Seq.seq S8.t) (rr acc: nat) (g: nat) (q: nat)
  : Lemma (requires vinv a msg rr acc g /\ vmul_post a r4m a1 /\ vbc r4m q /\
                    cong q (r4 rr) /\ vload m msg g /\ is_add a2 a1 m)
          (ensures vinv a2 msg rr acc (g + 4))
  = reveal_opaque (`%vinv) (vinv a msg rr acc g);
    reveal_opaque (`%vinv) (vinv a2 msg rr acc (g + 4));
    vmul_post_bounded a r4m a1;
    reveal_opaque (`%vload) (vload m msg g);
    add_ok a2 a1 m;
    reveal_opaque (`%vsum) (vsum a2 a1 m);
    reveal_opaque (`%vmul_post) (vmul_post a r4m a1);
    reveal_opaque (`%vbc) (vbc r4m q);
    assert (fl r4m 0 == q /\ fl r4m 1 == q /\ fl r4m 2 == q /\ fl r4m 3 == q);
    assert (fl a2 0 == fl a1 0 + fl m 0 /\ fl a2 1 == fl a1 1 + fl m 1 /\
            fl a2 2 == fl a1 2 + fl m 2 /\ fl a2 3 == fl a1 3 + fl m 3);
    assert (fl a1 0 % prime == (fl a 0 * fl r4m 0) % prime /\
            fl a1 1 % prime == (fl a 1 * fl r4m 1) % prime /\
            fl a1 2 % prime == (fl a 2 * fl r4m 2) % prime /\
            fl a1 3 % prime == (fl a 3 * fl r4m 3) % prime);
    horner_step msg rr acc g q (fl a 0) (fl a 2) (fl a 1) (fl a 3)
                (fl a1 0) (fl a1 2) (fl a1 1) (fl a1 3)
                (fl a2 0) (fl a2 2) (fl a2 1) (fl a2 3)

let hsum_eval (e: Seq.seq S64.t) (a: Seq.seq V.t)
  : Lemma (requires is_hsum e a)
          (ensures feval e == fl a 0 + fl a 1 + fl a 2 + fl a 3)
  = add5_eval (lv a 0 0 + lv a 0 1 + lv a 0 2) (lv a 1 0 + lv a 1 1 + lv a 1 2)
              (lv a 2 0 + lv a 2 1 + lv a 2 2) (lv a 3 0 + lv a 3 1 + lv a 3 2)
              (lv a 4 0 + lv a 4 1 + lv a 4 2)
              (lv a 0 3) (lv a 1 3) (lv a 2 3) (lv a 3 3) (lv a 4 3);
    add5_eval (lv a 0 0 + lv a 0 1) (lv a 1 0 + lv a 1 1) (lv a 2 0 + lv a 2 1)
              (lv a 3 0 + lv a 3 1) (lv a 4 0 + lv a 4 1)
              (lv a 0 2) (lv a 1 2) (lv a 2 2) (lv a 3 2) (lv a 4 2);
    add5_eval (lv a 0 0) (lv a 1 0) (lv a 2 0) (lv a 3 0) (lv a 4 0)
              (lv a 0 1) (lv a 1 1) (lv a 2 1) (lv a 3 1) (lv a 4 1)

let hsum_bound (e: Seq.seq S64.t) (a: Seq.seq V.t)
  : Lemma (requires is_hsum e a /\ vbounded a 27) (ensures bounded e 59)
  = reveal_opaque (`%vbounded) (vbounded a 27);
    assert (lbounded a 0 27 /\ lbounded a 1 27 /\ lbounded a 2 27 /\ lbounded a 3 27);
    assert_norm (4 * pow2 27 < pow2 59)

let sacc_small (msg: Seq.seq S8.t) (rr acc: nat) (g: nat)
  : Lemma (requires 1 <= g /\ 16 * g <= Seq.length msg) (ensures sacc msg rr acc g < prime)
  = unfold_repeati_g (g - 1) (Spec.bstep msg 0 rr) acc

let final_ok (a rp a1: Seq.seq V.t) (e h': Seq.seq S64.t) (msg: Seq.seq S8.t) (acc: nat)
             (g: nat) (r4s r2s r3s rs: Seq.seq S64.t)
  : Lemma (requires vinv a msg (feval rs) acc g /\ 1 <= g /\
                    is_set rp r4s r2s r3s rs /\
                    bounded r4s 27 /\ bounded r2s 27 /\ bounded r3s 27 /\ bounded rs 27 /\
                    pows (feval rs) (feval r2s) (feval r3s) (feval r4s) /\
                    vmul_post a rp a1 /\ is_hsum e a1 /\ Seq.length h' == 5 /\
                    chain (vv e 0) (vv e 1) (vv e 2) (vv e 3) (vv e 4)
                          (vv h' 0) (vv h' 1) (vv h' 2) (vv h' 3) (vv h' 4))
          (ensures bounded h' 27 /\ feval h' % prime == sacc msg (feval rs) acc g)
  = let rr = feval rs in
    reveal_opaque (`%vinv) (vinv a msg rr acc g);
    set_ok rp r4s r2s r3s rs;
    vmul_post_bounded a rp a1;
    reveal_opaque (`%vmul_post) (vmul_post a rp a1);
    assert (fl a1 0 % prime == (fl a 0 * fl rp 0) % prime /\
            fl a1 1 % prime == (fl a 1 * fl rp 1) % prime /\
            fl a1 2 % prime == (fl a 2 * fl rp 2) % prime /\
            fl a1 3 % prime == (fl a 3 * fl rp 3) % prime);
    horner_final msg rr acc g (fl a 0) (fl a 2) (fl a 1) (fl a 3)
                 (fl rp 0) (fl rp 2) (fl rp 1) (fl rp 3)
                 (fl a1 0) (fl a1 2) (fl a1 1) (fl a1 3);
    hsum_eval e a1;
    hsum_bound e a1;
    carry_chain_cong (vv e 0) (vv e 1) (vv e 2) (vv e 3) (vv e 4)
                     (vv h' 0) (vv h' 1) (vv h' 2) (vv h' 3) (vv h' 4);
    carry_chain_bounds (vv e 0) (vv e 1) (vv e 2) (vv e 3) (vv e 4)
                       (vv h' 0) (vv h' 1) (vv h' 2) (vv h' 3) (vv h' 4);
    sacc_small msg rr acc g;
    Math.small_mod (sacc msg rr acc g) prime

#pop-options

let vinv_elim (a: Seq.seq V.t) (msg: Seq.seq S8.t) (rr acc: nat) (g: nat)
  : Lemma (requires vinv a msg rr acc g)
          (ensures Seq.length a == 5 /\ vbounded a 28 /\ 16 * g <= Seq.length msg)
  = reveal_opaque (`%vinv) (vinv a msg rr acc g)

(** [2^24] in every lane: the bit above a block, at limb four. *)
inline_for_extraction noextract
let c24 (_: unit) : Pure V.t (requires True) (ensures fun c -> is24 c)
  = let x = S64.classify 0x1000000uL in
    assert_norm (U64.v 0x1000000uL == pow2 24);
    V.bcast64 x

(** {2 The driver} *)

let as32 (s: Seq.seq S8.t { Seq.length s == 32 })
  : Pure (Seq.lseq S8.t 32) (requires True) (ensures fun r -> r == s)
  = s

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

inline_for_extraction noextract
fn write5s (d: A.array S64.t) (x0 x1 x2 x3 x4: S64.t) (#vd: erased (Seq.seq S64.t))
requires A.pts_to d vd ** pure (Seq.length vd == 5)
ensures exists* (vd': Seq.seq S64.t). A.pts_to d vd' **
  pure (Seq.length vd' == 5 /\ Seq.index vd' 0 == x0 /\ Seq.index vd' 1 == x1 /\
        Seq.index vd' 2 == x2 /\ Seq.index vd' 3 == x3 /\ Seq.index vd' 4 == x4)
{
  A.pts_to_len d;
  A.((d.(0sz) <- x0));
  A.((d.(1sz) <- x1));
  A.((d.(2sz) <- x2));
  A.((d.(3sz) <- x3));
  A.((d.(4sz) <- x4));
  A.pts_to_len d;
}

inline_for_extraction noextract
fn write9 (d: A.array V.t) (x0 x1 x2 x3 x4 x5 x6 x7 x8: V.t) (#vd: erased (Seq.seq V.t))
requires A.pts_to d vd ** pure (Seq.length vd == 9)
ensures exists* (vd': Seq.seq V.t). A.pts_to d vd' **
  pure (Seq.length vd' == 9 /\ Seq.index vd' 0 == x0 /\ Seq.index vd' 1 == x1 /\
        Seq.index vd' 2 == x2 /\ Seq.index vd' 3 == x3 /\ Seq.index vd' 4 == x4 /\
        Seq.index vd' 5 == x5 /\ Seq.index vd' 6 == x6 /\ Seq.index vd' 7 == x7 /\
        Seq.index vd' 8 == x8)
{
  A.pts_to_len d;
  A.((d.(0sz) <- x0));
  A.((d.(1sz) <- x1));
  A.((d.(2sz) <- x2));
  A.((d.(3sz) <- x3));
  A.((d.(4sz) <- x4));
  A.((d.(5sz) <- x5));
  A.((d.(6sz) <- x6));
  A.((d.(7sz) <- x7));
  A.((d.(8sz) <- x8));
  A.pts_to_len d;
}

(** The first five limbs of [s], into [d]. *)
inline_for_extraction noextract
fn copy5 (d: A.array S64.t) (s: A.array S64.t)
         (#vd: erased (Seq.seq S64.t)) (#vs: erased (Seq.seq S64.t))
requires A.pts_to d vd ** A.pts_to s vs **
         pure (Seq.length vd == 5 /\ Seq.length vs >= 5 /\ bounded vs 27)
ensures exists* (vd': Seq.seq S64.t). A.pts_to d vd' ** A.pts_to s vs **
  pure (Seq.length vd' == 5 /\ feval vd' == feval vs /\ bounded vd' 27 /\ bounded vd' 28)
{
  A.pts_to_len s;
  let x0 = A.(s.(0sz));
  let x1 = A.(s.(1sz));
  let x2 = A.(s.(2sz));
  let x3 = A.(s.(3sz));
  let x4 = A.(s.(4sz));
  write5s d x0 x1 x2 x3 x4;
  with vd'. assert (A.pts_to d vd');
  same5 vd' vs 27;
  bounded_weak vd' 27 28;
  A.pts_to_len d;
}

inline_for_extraction noextract
fn vadd5 (a: A.array V.t) (b: A.array V.t)
         (#va: erased (Seq.seq V.t)) (#vb: erased (Seq.seq V.t))
requires A.pts_to a va ** A.pts_to b vb ** pure (Seq.length va == 5 /\ Seq.length vb == 5)
ensures exists* (va': Seq.seq V.t). A.pts_to a va' ** A.pts_to b vb ** pure (is_add va' va vb)
{
  A.pts_to_len a;
  A.pts_to_len b;
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let a4 = A.(a.(4sz));
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  let b4 = A.(b.(4sz));
  write5 a (V.add64 a0 b0) (V.add64 a1 b1) (V.add64 a2 b2) (V.add64 a3 b3) (V.add64 a4 b4);
}

(** Blocks [g] to [g + 3], one per lane, as limbs: lanes [0, 2, 1, 3]. *)
inline_for_extraction noextract
fn load4 (m: A.array V.t) (msg: A.array S8.t) (o: SZ.t) (c: V.t) (g: erased nat)
         (#vm: erased (Seq.seq V.t)) (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
requires A.pts_to m vm ** A.pts_to msg #pm vmsg **
         pure (Seq.length vm == 5 /\ SZ.v o == 16 * g /\ 16 * g + 64 <= Seq.length vmsg /\
               is24 c)
ensures exists* (vm': Seq.seq V.t). A.pts_to m vm' ** A.pts_to msg #pm vmsg **
  pure (Seq.length vm' == 5 /\ vload vm' vmsg g)
{
  A.pts_to_len msg;
  let o1 = SZ.add o 32sz;
  let o2 = SZ.add o1 32sz;
  let b0 = Sub.sub msg o o1;
  let v0 = V.load b0 #(as32 (Seq.slice vmsg (SZ.v o) (SZ.v o1)));
  Sub.unsub_id msg (SZ.v o) (SZ.v o1) b0;
  let b1 = Sub.sub msg o1 o2;
  let v1 = V.load b1 #(as32 (Seq.slice vmsg (SZ.v o1) (SZ.v o2)));
  Sub.unsub_id msg (SZ.v o1) (SZ.v o2) b1;
  let lo = V.unpacklo64 v0 v1;
  let hi = V.unpackhi64 v0 v1;
  assert pure (V.vv v0 == Seq.slice vmsg (16 * g) (16 * g + 32));
  assert pure (V.vv v1 == Seq.slice vmsg (16 * g + 32) (16 * g + 64));
  write5 m (mk0 lo) (mk1 lo) (mk2 lo hi) (mk3 hi) (mk4 hi c);
  with vm'. assert (A.pts_to m vm');
  load_ok vm' v0 v1 c vmsg g;
  A.pts_to_len m;
}

(** The four lanes of [x], added up. *)
inline_for_extraction noextract
fn lane_sum (buf: A.array S64.t) (x: V.t) (#vb: erased (Seq.seq S64.t))
requires A.pts_to buf vb **
         pure (Seq.length vb == 4 /\ l64 x 0 < pow2 27 /\ l64 x 1 < pow2 27 /\
               l64 x 2 < pow2 27 /\ l64 x 3 < pow2 27)
returns s: S64.t
ensures exists* (vb': Seq.seq S64.t). A.pts_to buf vb' **
  pure (Seq.length vb' == 4 /\ S64.v s == l64 x 0 + l64 x 1 + l64 x 2 + l64 x 3)
{
  V.store64 buf x;
  A.pts_to_len buf;
  let a0 = A.(buf.(0sz));
  let a1 = A.(buf.(1sz));
  let a2 = A.(buf.(2sz));
  let a3 = A.(buf.(3sz));
  assert_norm (4 * pow2 27 < pow2 64);
  add2 (add2 (add2 a0 a1) a2) a3
}

inline_for_extraction noextract
fn hsum5 (e: A.array S64.t) (a: A.array V.t) (buf: A.array S64.t)
         (#ve: erased (Seq.seq S64.t)) (#va: erased (Seq.seq V.t))
         (#vb: erased (Seq.seq S64.t))
requires A.pts_to e ve ** A.pts_to a va ** A.pts_to buf vb **
         pure (Seq.length ve == 5 /\ Seq.length va == 5 /\ Seq.length vb == 4 /\
               vbounded va 27)
ensures exists* (ve': Seq.seq S64.t) (vb': Seq.seq S64.t).
  A.pts_to e ve' ** A.pts_to a va ** A.pts_to buf vb' **
  pure (Seq.length vb' == 4 /\ is_hsum ve' va)
{
  A.pts_to_len a;
  lanes27 va 0;
  lanes27 va 1;
  lanes27 va 2;
  lanes27 va 3;
  lanes27 va 4;
  let x0 = A.(a.(0sz));
  let s0 = lane_sum buf x0;
  let x1 = A.(a.(1sz));
  let s1 = lane_sum buf x1;
  let x2 = A.(a.(2sz));
  let s2 = lane_sum buf x2;
  let x3 = A.(a.(3sz));
  let s3 = lane_sum buf x3;
  let x4 = A.(a.(4sz));
  let s4 = lane_sum buf x4;
  write5s e s0 s1 s2 s3 s4;
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Absorb the longest prefix of [n] blocks that is a multiple of four,
    four lanes at a time, and say how many blocks that was.  [d] is
    scratch. *)
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_prologue "__attribute__((target(\"avx2\")))"]
fn absorb4 (h: A.array S64.t) (r: A.array S64.t) (d: A.array S64.t)
           (msg: A.array S8.t) (n: SZ.t)
           (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
           (#vd: erased (Seq.seq S64.t))
           (#pm: perm) (#vmsg: erased (Seq.seq S8.t)) (#acc: erased nat)
requires A.pts_to h vh ** A.pts_to r vr ** A.pts_to d vd ** A.pts_to msg #pm vmsg **
         pure (Seq.length vh == 5 /\ Seq.length vr == 9 /\ Seq.length vd == 5 /\
               bounded vh 27 /\ bounded vr 26 /\ has5 vr /\
               4 <= SZ.v n /\ 16 * SZ.v n <= Seq.length vmsg /\
               feval vh % prime == reveal acc)
returns g: SZ.t
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t).
  A.pts_to h vh' ** A.pts_to r vr ** A.pts_to d vd' ** A.pts_to msg #pm vmsg **
  pure (Seq.length vh' == 5 /\ Seq.length vd' == 5 /\ bounded vh' 27 /\
        SZ.v g <= SZ.v n /\
        feval vh' % prime == Spec.blocks_acc vmsg 0 (SZ.v g) (feval vr) (reveal acc))
{
  A.pts_to_len h;
  A.pts_to_len r;
  A.pts_to_len d;
  A.pts_to_len msg;
  bounded_weak vr 26 27;
  let zz : S64.t = S64.classify 0uL;
  (* r^2, r^3 and r^4, one at a time *)
  let mut p2 = [| zz; 5sz |];
  Mem.track p2;
  let mut p3 = [| zz; 5sz |];
  Mem.track p3;
  let mut p4 = [| zz; 5sz |];
  Mem.track p4;
  copy5 p2 r;
  fmul p2 r d;
  with vp2. assert (A.pts_to p2 vp2);
  copy5 p3 p2;
  fmul p3 r d;
  with vp3. assert (A.pts_to p3 vp3);
  copy5 p4 p3;
  fmul p4 r d;
  with vp4. assert (A.pts_to p4 vp4);
  pows_ok (feval vr) (feval vp2) (feval vp3) (feval vp4);
  (* the multipliers: r^4 in every lane, and r^4, r^2, r^3, r for the end *)
  let z = V.zero ();
  let mut q4 = [| z; 9sz |];
  Mem.track q4;
  let mut qp = [| z; 9sz |];
  Mem.track qp;
  let w0 = A.(p4.(0sz));
  let w1 = A.(p4.(1sz));
  let w2 = A.(p4.(2sz));
  let w3 = A.(p4.(3sz));
  let w4 = A.(p4.(4sz));
  let b0 = V.bcast64 w0;
  let b1 = V.bcast64 w1;
  let b2 = V.bcast64 w2;
  let b3 = V.bcast64 w3;
  let b4 = V.bcast64 w4;
  write9 q4 b0 b1 b2 b3 b4 (vtimes5 b1) (vtimes5 b2) (vtimes5 b3) (vtimes5 b4);
  with vq4. assert (A.pts_to q4 vq4);
  bc_ok vq4 vp4;
  let u0 = V.set64 w0 A.(p2.(0sz)) A.(p3.(0sz)) A.(r.(0sz));
  let u1 = V.set64 w1 A.(p2.(1sz)) A.(p3.(1sz)) A.(r.(1sz));
  let u2 = V.set64 w2 A.(p2.(2sz)) A.(p3.(2sz)) A.(r.(2sz));
  let u3 = V.set64 w3 A.(p2.(3sz)) A.(p3.(3sz)) A.(r.(3sz));
  let u4 = V.set64 w4 A.(p2.(4sz)) A.(p3.(4sz)) A.(r.(4sz));
  write9 qp u0 u1 u2 u3 u4 (vtimes5 u1) (vtimes5 u2) (vtimes5 u3) (vtimes5 u4);
  with vqp. assert (A.pts_to qp vqp);
  set_mult_ok vqp vp4 vp2 vp3 vr;
  (* the first four blocks, and the incoming accumulator in lane 0 *)
  let c = c24 ();
  let mut a = [| z; 5sz |];
  Mem.track a;
  let mut m = [| z; 5sz |];
  Mem.track m;
  let mut t = [| z; 5sz |];
  Mem.track t;
  let mut buf = [| zz; 4sz |];
  Mem.track buf;
  zeros_ok ();
  write5 a (V.set64 A.(h.(0sz)) zz zz zz) (V.set64 A.(h.(1sz)) zz zz zz)
           (V.set64 A.(h.(2sz)) zz zz zz) (V.set64 A.(h.(3sz)) zz zz zz)
           (V.set64 A.(h.(4sz)) zz zz zz);
  with vhh. assert (A.pts_to a vhh);
  load4 m msg 0sz c 0;
  with vm0. assert (A.pts_to m vm0);
  vadd5 a m;
  with va0. assert (A.pts_to a va0);
  init_ok va0 vhh vm0 vh vmsg (feval vr) (reveal acc);
  (* four blocks a trip *)
  let mut gi = 4sz;
  while (let g = !gi; SZ.lte 4sz (SZ.sub n g))
  invariant exists* (g: SZ.t) (va: Seq.seq V.t) (vm: Seq.seq V.t) (vt: Seq.seq V.t).
    pts_to gi g ** A.pts_to a va ** A.pts_to m vm ** A.pts_to t vt **
    A.pts_to q4 vq4 ** A.pts_to msg #pm vmsg **
    pure (4 <= SZ.v g /\ SZ.v g <= SZ.v n /\ Seq.length vm == 5 /\ Seq.length vt == 5 /\
          vinv va vmsg (feval vr) (reveal acc) (SZ.v g))
  decreases (SZ.v n - SZ.v (!gi))
  {
    let g = !gi;
    assert pure (SZ.v g + 4 <= SZ.v n);
    with va. assert (A.pts_to a va);
    vinv_elim va vmsg (feval vr) (reveal acc) (SZ.v g);
    vbc_elim vq4 (feval vp4);
    vfmul a q4 t;
    with va1. assert (A.pts_to a va1);
    Math.lemma_mult_le_right 16 (SZ.v g + 4) (SZ.v n);
    let o = SZ.mul 16sz g;
    load4 m msg o c (SZ.v g);
    with vm1. assert (A.pts_to m vm1);
    vadd5 a m;
    with va2. assert (A.pts_to a va2);
    step_ok va va1 vm1 va2 vq4 vmsg (feval vr) (reveal acc) (SZ.v g) (feval vp4);
    let g4 = SZ.add g 4sz;
    assert pure (SZ.v n - SZ.v g4 < SZ.v n - SZ.v g /\ 0 <= SZ.v n - SZ.v g4);
    gi := g4;
  };
  (* each lane times its own power of r, and the lanes added *)
  let g = !gi;
  with va. assert (A.pts_to a va);
  vinv_elim va vmsg (feval vr) (reveal acc) (SZ.v g);
  vfmul a qp t;
  with va1. assert (A.pts_to a va1);
  vmul_post_bounded va vqp va1;
  hsum5 d a buf;
  with ve. assert (A.pts_to d ve);
  hsum_bound ve va1;
  carry_chain_impl h d;
  with vh'. assert (A.pts_to h vh');
  final_ok va vqp va1 ve vh' vmsg (reveal acc) (SZ.v g) vp4 vp2 vp3 vr;
  Mem.wipe buf 4sz;
  Mem.wipe t 5sz;
  Mem.wipe m 5sz;
  Mem.wipe a 5sz;
  Mem.wipe qp 9sz;
  Mem.wipe q4 9sz;
  Mem.wipe p4 5sz;
  Mem.wipe p3 5sz;
  Mem.wipe p2 5sz;
  g
}

(** The four-lane path when the processor has AVX2 and the message is long
    enough to pay for the powers of [r] -- eight blocks, measured, with gcc
    and clang; nothing otherwise.  Compiled for the
    baseline target, so that the [supported] test runs everywhere. *)
fn absorb_vec (h: A.array S64.t) (r: A.array S64.t) (d: A.array S64.t)
              (msg: A.array S8.t) (n: SZ.t)
              (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
              (#vd: erased (Seq.seq S64.t))
              (#pm: perm) (#vmsg: erased (Seq.seq S8.t)) (#acc: erased nat)
requires A.pts_to h vh ** A.pts_to r vr ** A.pts_to d vd ** A.pts_to msg #pm vmsg **
         pure (Seq.length vh == 5 /\ Seq.length vr == 9 /\ Seq.length vd == 5 /\
               bounded vh 27 /\ bounded vr 26 /\ has5 vr /\
               16 * SZ.v n <= Seq.length vmsg /\
               feval vh % prime == reveal acc)
returns g: SZ.t
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t).
  A.pts_to h vh' ** A.pts_to r vr ** A.pts_to d vd' ** A.pts_to msg #pm vmsg **
  pure (Seq.length vh' == 5 /\ Seq.length vd' == 5 /\ bounded vh' 27 /\
        SZ.v g <= SZ.v n /\
        feval vh' % prime == Spec.blocks_acc vmsg 0 (SZ.v g) (feval vr) (reveal acc))
{
  if (SZ.lte 8sz n && V.supported ()) {
    absorb4 h r d msg n #vh #vr #vd #pm #vmsg #acc
  } else {
    A.pts_to_len h;
    A.pts_to_len d;
    repeati_g_zero (Spec.bstep vmsg 0 (feval vr)) (reveal acc);
    0sz
  }
}

#pop-options
