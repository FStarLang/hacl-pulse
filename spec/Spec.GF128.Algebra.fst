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

(** GF(2^128) is a field, and in particular its multiplication is
    commutative, associative and distributes over addition.

    [Spec.GF128.Poly] proves everything a {i single} GHASH multiply needs and
    nothing more, because nothing more was needed: the implementation ran one
    multiply per block and the specification was a fold over blocks.  Running
    four blocks at once is a different matter.  GHASH is Horner's rule,

    {[
      acc' = (((((acc + b0) * H) + b1) * H + b2) * H + b3) * H
    ]}

    and every multiply waits on the one before it, which on this hardware is
    around thirty cycles of pure latency per sixteen bytes.  The way out is
    the standard one:

    {[
      acc' = (acc + b0) * H^4 + b1 * H^3 + b2 * H^2 + b3 * H
    ]}

    where the four products are independent and can be in flight together.
    Turning the first line into the second is exactly associativity and
    distributivity, so they have to be proved.

    {2 How}

    The whole development rests on one fact that [Spec.GF128.Poly] already
    has, which is that the loop of SP 800-38D accumulates

    {[
      gmul x y == bsum (fun k -> if bit x k then y * x^k else 0) 128
    ]}

    -- a sum over the set bits of the {i first} operand of the second operand
    shifted.  Read that way [gmul] is visibly linear in [x], which is
    distributivity, and the only real work is to move a shift from one side
    to the other:

    {[
      gmul u (xt c j) == xt (gmul u c) j
    ]}

    which is true term by term because [xt] is linear and [xt (xt c i) j] is
    [xt c (i + j)].  That moves a shift out of the {i second} operand;
    commutativity is what lets it out of the first, and associativity is the
    two together.  No new reasoning about the reduction polynomial is needed
    anywhere -- [xt] carries all of it. *)
module Spec.GF128.Algebra

open Spec.Byte
open Spec.GF128
open Spec.CarryLess
open Spec.GF128.Poly

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 1 --ifuel 0 --z3rlimit 150"

(** {2 Addition} *)

let gadd_comm (a b: block) : Lemma (gadd a b == gadd b a)
  = Classical.forall_intro (gadd_bit a b);
    Classical.forall_intro (gadd_bit b a);
    bits_inj (gadd a b) (gadd b a)

let gadd_zero_left (a: block) : Lemma (gadd zero a == a)
  = gadd_comm zero a; gadd_zero a

(** {2 Multiplication by [x] is linear}

    [xtimes] is a shift and a conditional addition of the reduction constant,
    and the condition is the top bit, so both halves are linear. *)

let xtimes_gadd (a b: block)
  : Lemma (xtimes (gadd a b) == gadd (xtimes a) (xtimes b))
  = let aux (i: nat { i < 128 })
      : Lemma (bit (xtimes (gadd a b)) i ==
               bit (gadd (xtimes a) (xtimes b)) i)
      = xtimes_bit (gadd a b) i;
        xtimes_bit a i;
        xtimes_bit b i;
        gadd_bit (xtimes a) (xtimes b) i;
        gadd_bit a b 127;
        if i > 0 then gadd_bit a b (i - 1)
    in
    Classical.forall_intro aux;
    bits_inj (xtimes (gadd a b)) (gadd (xtimes a) (xtimes b))

let xtimes_zero (_: unit) : Lemma (xtimes zero == zero)
  = Classical.forall_intro (xtimes_bit zero);
    Classical.forall_intro zero_bit;
    bits_inj (xtimes zero) zero

(** {2 ... and so is repeating it} *)

let rec xt_gadd (a b: block) (j: nat)
  : Lemma (ensures xt (gadd a b) j == gadd (xt a j) (xt b j)) (decreases j)
  = if j = 0 then ()
    else begin
      xt_gadd a b (j - 1);
      xtimes_gadd (xt a (j - 1)) (xt b (j - 1))
    end

let rec xt_zero (j: nat) : Lemma (ensures xt zero j == zero) (decreases j)
  = if j = 0 then () else (xt_zero (j - 1); xtimes_zero ())

(** [c * x^i * x^j == c * x^(i+j)]. *)
let rec xt_add (c: block) (i j: nat)
  : Lemma (ensures xt (xt c i) j == xt c (i + j)) (decreases j)
  = if j = 0 then () else xt_add c i (j - 1)

(** {2 Sums of families} *)

let rec bsum_ext (f g: int -> block) (n: nat)
  : Lemma (requires forall (k: int). 0 <= k /\ k < n ==> f k == g k)
          (ensures bsum f n == bsum g n) (decreases n)
  = if n = 0 then () else bsum_ext f g (n - 1)

let rec xt_bsum (f: int -> block) (n: nat) (j: nat)
  : Lemma (ensures xt (bsum f n) j == bsum (fun k -> xt (f k) j) n)
          (decreases n)
  = if n = 0 then xt_zero j
    else begin
      xt_bsum f (n - 1) j;
      xt_gadd (f (n - 1)) (bsum f (n - 1)) j
    end

(** {2 Shifting a polynomial by one is multiplying its reduction by [x]}

    This is the identity the module docstring of [Spec.GF128.Poly] promises:
    reduction is linear, and [x^(k+1)] is [x^k] advanced once, so shifting the
    coefficient sequence up by one place and reducing gives the same block as
    reducing and then advancing once.  The one hypothesis is that the top
    coefficient of the window being reduced is zero, since the shift would
    otherwise push a live term past the end of the window and lose it.

    It is what makes a carry-less multiplier that omits the customary one-bit
    shift usable: such a multiplier returns the product polynomial shifted up
    by one, and this lemma says that reduces to [x] times the field product. *)

#push-options "--fuel 3 --ifuel 1"
let rec bsum_shift1 (g: int -> block) (n: nat)
  : Lemma (requires g 0 == zero)
          (ensures bsum g (n + 1) == bsum (fun k -> g (k + 1)) n)
          (decreases n)
  = if n = 0 then gadd_zero zero
    else bsum_shift1 g (n - 1)

let pmod_unfold (b: poly) (n: nat)
  : Lemma (pmod b n == bsum (fun k -> if pget b k then xpowi k else zero) n)
  = ()

let pmod_shift1 (a: poly) (n: pos)
  : Lemma (requires pget a (n - 1) == false)
          (ensures pmod (pshift a 1) n == xtimes (pmod a n))
  = let f (k: int) : block = if pget a k then xpowi k else zero in
    let g (k: int) : block = if pget a (k - 1) then xpowi k else zero in
    let h (k: int) : block = g (k + 1) in
    (* The left-hand side is [bsum g n]: shifting the coefficient sequence up
       by one place is the same as asking for the coefficient one lower. *)
    Classical.forall_intro (pshift_get a 1);
    pmod_unfold (pshift a 1) n;
    pmod_unfold a n;
    bsum_ext (fun k -> if pget (pshift a 1) k then xpowi k else zero) g n;
    (* [g 0] is zero because there is no coefficient below zero, so the sum
       may be reindexed: [bsum g n == bsum h (n - 1)]. *)
    bsum_shift1 g (n - 1);
    (* The right-hand side is [bsum h n] by linearity of [xtimes], and its
       top term is [g n], which the hypothesis makes zero. *)
    xt_bsum f n 1;
    let aux (k: nat) : Lemma (xt (f k) 1 == h k) = xtimes_zero () in
    Classical.forall_intro aux;
    bsum_ext (fun k -> xt (f k) 1) h n;
    gadd_zero_left (bsum h (n - 1))

#pop-options

(** {2 The product as a sum over the bits of the left operand}

    [accum] is what [gmul_loop] accumulates and [Spec.GF128.Poly] has already
    shown the loop computes it.  Rewriting it as a [bsum] is a change of
    notation, but it is the notation in which linearity is visible. *)

let afun (x y: block) : int -> block =
  fun k -> if pget (pbits x) k then xti y k else zero

let rec accum_bsum (x y: block) (n: nat { n <= 128 })
  : Lemma (ensures accum x y n == bsum (afun x y) n) (decreases n)
  = if n = 0 then ()
    else begin
      accum_bsum x y (n - 1);
      pbits_get x (n - 1);
      gadd_comm (accum x y (n - 1)) (xt y (n - 1));
      gadd_zero_left (bsum (afun x y) (n - 1))
    end

#push-options "--fuel 2"
let gmul_accum (x y: block) : Lemma (gmul x y == accum x y 128)
  = gmul_loop_accum x y 0
#pop-options

let gmul_bsum (x y: block) : Lemma (gmul x y == bsum (afun x y) 128)
  = gmul_accum x y; accum_bsum x y 128

(** {2 Distributivity}

    Immediate from the shape above: the family [afun] depends on [x] only
    through its bits, and those exclusive-or. *)

let afun_gadd_bit (a b c: block) (i: nat { i < 128 }) (k: int)
  : Lemma (bit (afun (gadd a b) c k) i == (bit (afun a c k) i <> bit (afun b c k) i))
  = pbits_get (gadd a b) k;
    pbits_get a k;
    pbits_get b k;
    zero_bit i;
    if 0 <= k && k < 128 then gadd_bit a b k

let gmul_gadd_left (a b c: block)
  : Lemma (gmul (gadd a b) c == gadd (gmul a c) (gmul b c))
  = gmul_bsum (gadd a b) c;
    gmul_bsum a c;
    gmul_bsum b c;
    Classical.forall_intro (gadd_bit a b);
    Classical.forall_intro (pbits_get (gadd a b));
    Classical.forall_intro (pbits_get a);
    Classical.forall_intro (pbits_get b);
    Classical.forall_intro zero_bit;
    let aux (i: nat { i < 128 })
      : Lemma (bit (bsum (afun (gadd a b) c) 128) i ==
               bit (gadd (bsum (afun a c) 128) (bsum (afun b c) 128)) i)
      = bsum_bit (afun (gadd a b) c) 128 i;
        bsum_bit (afun a c) 128 i;
        bsum_bit (afun b c) 128 i;
        gadd_bit (bsum (afun a c) 128) (bsum (afun b c) 128) i;
        xsum_xor (fun k -> bit (afun a c k) i) (fun k -> bit (afun b c k) i)
                 0 128;
        Classical.forall_intro (afun_gadd_bit a b c i);
        xsum_ext (fun k -> bit (afun (gadd a b) c k) i)
                 (fun k -> bit (afun a c k) i <> bit (afun b c k) i) 0 128
    in
    Classical.forall_intro aux;
    bits_inj (bsum (afun (gadd a b) c) 128)
             (gadd (bsum (afun a c) 128) (bsum (afun b c) 128))

let rec gmul_bsum_left (f: int -> block) (n: nat) (c: block)
  : Lemma (ensures gmul (bsum f n) c == bsum (fun k -> gmul (f k) c) n)
          (decreases n)
  = if n = 0 then gmul_zero c
    else begin
      gmul_bsum_left f (n - 1) c;
      gmul_gadd_left (f (n - 1)) (bsum f (n - 1)) c
    end

(** {2 Moving a shift out of the right operand}

    [gmul u (c * x^j) == (gmul u c) * x^j], term by term. *)

let gmul_xt_right (u c: block) (j: nat)
  : Lemma (gmul u (xt c j) == xt (gmul u c) j)
  = gmul_bsum u (xt c j);
    gmul_bsum u c;
    xt_bsum (afun u c) 128 j;
    let aux (k: int)
      : Lemma (0 <= k /\ k < 128 ==>
               afun u (xt c j) k == (fun k -> xt (afun u c k) j) k)
      = if 0 <= k && k < 128 then begin
          xt_add c j k;
          xt_add c k j;
          xt_zero j
        end
    in
    Classical.forall_intro aux;
    bsum_ext (afun u (xt c j)) (fun k -> xt (afun u c k) j) 128

(** {2 Commutativity}

    The convolution is symmetric, which is the sum read backwards.  Both the
    reversal and the sliding of the range are [Spec.CarryLess]'s; the only
    care needed is that the two ranges are different, so each is trimmed down
    to the span where the terms can be nonzero. *)

let xsum_window (g: int -> bool) (lo: int) (n: nat) (a: int) (m: nat)
  : Lemma (requires lo <= a /\ a + m <= lo + n /\
                    (forall (i: int). (i < a \/ a + m <= i) ==> g i == false))
          (ensures xsum g lo n == xsum g a m)
  = xsum_trim_hi g lo (a + m - lo) n;
    xsum_trim_lo g lo (a - lo) (a + m - lo)

let conv_comm (a b: poly) (k: int)
  : Lemma (requires Seq.length a == 128 /\ Seq.length b == 128)
          (ensures conv a b k == conv b a k)
  = let f : int -> bool = fun i -> pget a i && pget b (k - i) in
    let g : int -> bool = fun i -> pget b i && pget a (k - i) in
    xsum_rev f 0 128;
    xsum_shift (fun i -> f (0 + 128 - 1 - i)) 0 128 (127 - k);
    xsum_ext (fun i -> f (0 + 128 - 1 - (i + (127 - k)))) g (k - 127) 128;
    let lo = if k - 127 > 0 then k - 127 else 0 in
    let hi = if k + 1 < 128 then k + 1 else 128 in
    if lo < hi then begin
      xsum_window g (k - 127) 128 lo (hi - lo);
      xsum_window g 0 128 lo (hi - lo)
    end else begin
      xsum_zero g (k - 127) 128;
      xsum_zero g 0 128
    end

let gmul_comm (x y: block) : Lemma (gmul x y == gmul y x)
  = gmul_is_pmod x y;
    gmul_is_pmod y x;
    let aux (i: nat { i < 128 })
      : Lemma (bit (pmod (pmul (pbits x) (pbits y)) 256) i ==
               bit (pmod (pmul (pbits y) (pbits x)) 256) i)
      = pmod_bit (pmul (pbits x) (pbits y)) 256 i;
        pmod_bit (pmul (pbits y) (pbits x)) 256 i;
        Classical.forall_intro (pmul_get (pbits x) (pbits y));
        Classical.forall_intro (pmul_get (pbits y) (pbits x));
        Classical.forall_intro (conv_comm (pbits x) (pbits y));
        xsum_ext (fun k -> pget (pmul (pbits x) (pbits y)) k && bit (xpowi k) i)
                 (fun k -> pget (pmul (pbits y) (pbits x)) k && bit (xpowi k) i)
                 0 256
    in
    Classical.forall_intro aux;
    bits_inj (pmod (pmul (pbits x) (pbits y)) 256)
             (pmod (pmul (pbits y) (pbits x)) 256)

(** A shift comes out of either operand now. *)
let gmul_xt_left (b c: block) (j: nat)
  : Lemma (gmul (xt b j) c == xt (gmul b c) j)
  = gmul_comm (xt b j) c;
    gmul_xt_right c b j;
    gmul_comm c b

(** {2 Associativity} *)

let gmul_assoc (a b c: block)
  : Lemma (gmul (gmul a b) c == gmul a (gmul b c))
  = gmul_bsum a b;
    gmul_bsum_left (afun a b) 128 c;
    gmul_bsum a (gmul b c);
    let aux (k: int)
      : Lemma (0 <= k /\ k < 128 ==>
               (fun k -> gmul (afun a b k) c) k == afun a (gmul b c) k)
      = if 0 <= k && k < 128 then begin
          gmul_xt_left b c k;
          gmul_zero c
        end
    in
    Classical.forall_intro aux;
    bsum_ext (fun k -> gmul (afun a b k) c) (afun a (gmul b c)) 128

(** {2 What the four-way loop uses}

    Four turns of Horner's rule, rearranged into four products that depend on
    nothing but the accumulator four steps back.  The four multiplies can
    then be in flight together, which is the entire point of the exercise. *)

let gadd_assoc (a b c: block)
  : Lemma (gadd (gadd a b) c == gadd a (gadd b c))
  = Classical.forall_intro (gadd_bit (gadd a b) c);
    Classical.forall_intro (gadd_bit a b);
    Classical.forall_intro (gadd_bit a (gadd b c));
    Classical.forall_intro (gadd_bit b c);
    bits_inj (gadd (gadd a b) c) (gadd a (gadd b c))

let horner4 (a b0 b1 b2 b3 h h2 h3 h4: block)
  : Lemma (requires h2 == gmul h h /\ h3 == gmul h2 h /\ h4 == gmul h3 h)
          (ensures
            (let s1 = gmul (gadd a b0) h in
             let s2 = gmul (gadd s1 b1) h in
             let s3 = gmul (gadd s2 b2) h in
             gmul (gadd s3 b3) h ==
               gadd (gmul (gadd a b0) h4)
                    (gadd (gmul b1 h3)
                          (gadd (gmul b2 h2) (gmul b3 h)))))
  = let s1 = gmul (gadd a b0) h in
    let s2 = gmul (gadd s1 b1) h in
    let s3 = gmul (gadd s2 b2) h in
    gmul_gadd_left s3 b3 h;
    gmul_assoc (gadd s2 b2) h h;
    gmul_gadd_left s2 b2 h2;
    gmul_assoc (gadd s1 b1) h h2;
    gmul_comm h h2;
    gmul_gadd_left s1 b1 h3;
    gmul_assoc (gadd a b0) h h3;
    gmul_comm h h3;
    let p = gmul (gadd a b0) h4 in
    let q = gmul b1 h3 in
    let r = gmul b2 h2 in
    let t = gmul b3 h in
    gadd_assoc (gadd p q) r t;
    gadd_assoc p q (gadd r t)

#pop-options

(** {2 One reduction for four products}

    [Spec.GF128.Poly.gmul_three] is the shape a single multiply has in the
    implementation: a 256-bit carry-less product, then the high half folded
    back by two products with the reduction constant.  On this hardware the
    product is four [PCLMULQDQ]s and the fold is about forty shifts and
    exclusive-ors, so the reduction, not the multiplication, is most of the
    cost.

    It does not have to happen four times.  The 256-bit product is linear in
    each operand, so four products may be accumulated as two registers --- the
    sum of the low halves and the sum of the high halves --- and only that
    sum reduced.  Four multiplies then cost four products and {i one} fold
    rather than four, which is what [Hacl.AES.GF128.NI.gmul4_vec] does.

    Nothing here is about the reduction polynomial.  The only facts used are
    that [gmul] distributes over [gadd] on the left, which
    [Spec.GF128.Poly.gmul_split] turns into a statement about halves, and
    that exclusive-or may be regrouped. *)

let sum4 (a b c d: block) : block = gadd a (gadd b (gadd c d))

let sum4_bit (a b c d: block) (i: nat { i < 128 })
  : Lemma (bit (sum4 a b c d) i ==
           (((bit a i <> bit b i) <> bit c i) <> bit d i))
  = gadd_bit a (gadd b (gadd c d)) i;
    gadd_bit b (gadd c d) i;
    gadd_bit c d i

(** Four pairwise sums regrouped into two fourfold sums.  Pure exclusive-or:
    the solver sees eight booleans per bit and does the rest. *)
let regroup4 (u1 u2 u3 u4 w1 w2 w3 w4: block)
  : Lemma (sum4 (gadd u1 w1) (gadd u2 w2) (gadd u3 w3) (gadd u4 w4) ==
           gadd (sum4 u1 u2 u3 u4) (sum4 w1 w2 w3 w4))
  = let l = sum4 (gadd u1 w1) (gadd u2 w2) (gadd u3 w3) (gadd u4 w4) in
    let r = gadd (sum4 u1 u2 u3 u4) (sum4 w1 w2 w3 w4) in
    let aux (i: nat { i < 128 }) : Lemma (bit l i == bit r i)
      = sum4_bit (gadd u1 w1) (gadd u2 w2) (gadd u3 w3) (gadd u4 w4) i;
        gadd_bit u1 w1 i; gadd_bit u2 w2 i;
        gadd_bit u3 w3 i; gadd_bit u4 w4 i;
        gadd_bit (sum4 u1 u2 u3 u4) (sum4 w1 w2 w3 w4) i;
        sum4_bit u1 u2 u3 u4 i;
        sum4_bit w1 w2 w3 w4 i
    in
    Classical.forall_intro aux;
    bits_inj l r

(** A product by the reduction constant distributes over a fourfold sum. *)
let mul_r_sum4 (v1 v2 v3 v4: block)
  : Lemma (gmul (sum4 v1 v2 v3 v4) r_block ==
           sum4 (gmul v1 r_block) (gmul v2 r_block)
                (gmul v3 r_block) (gmul v4 r_block))
  = gmul_gadd_left v3 v4 r_block;
    gmul_gadd_left v2 (gadd v3 v4) r_block;
    gmul_gadd_left v1 (gadd v2 (gadd v3 v4)) r_block

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** Four multiplies, four carry-less products, one reduction.

    [u_i] and [v_i] are the halves of the *i*th 256-bit product, exactly as
    [Spec.GF128.Poly.halves] states them for a single multiply.  [p] and [q]
    are the halves of the sum of the four high halves times the reduction
    constant, and [pp] and [qq] of the second such product; [q] necessarily
    has degree at most six and [qq] is therefore zero, which is what
    [Spec.GF128.Poly.mul_r_two] says.

    The conclusion is the sum of the four field products, which is what
    [Spec.GF128.Algebra.horner4] leaves a four-block GHASH step needing. *)
let gmul_defer4 (x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 x4 y4 u4 v4
                 p q pp qq: block)
  : Lemma (requires halves x1 y1 u1 v1 /\ halves x2 y2 u2 v2 /\
                    halves x3 y3 u3 v3 /\ halves x4 y4 u4 v4 /\
                    halves (sum4 v1 v2 v3 v4) r_block p q /\
                    halves q r_block pp qq)
          (ensures sum4 (gmul x1 y1) (gmul x2 y2) (gmul x3 y3) (gmul x4 y4) ==
                   gadd (sum4 u1 u2 u3 u4) (gadd p pp))
  = gmul_split x1 y1 u1 v1;
    gmul_split x2 y2 u2 v2;
    gmul_split x3 y3 u3 v3;
    gmul_split x4 y4 u4 v4;
    regroup4 u1 u2 u3 u4
             (gmul v1 r_block) (gmul v2 r_block)
             (gmul v3 r_block) (gmul v4 r_block);
    mul_r_sum4 v1 v2 v3 v4;
    mul_r_two (sum4 v1 v2 v3 v4) p q pp qq

(** The same with the four products replaced by four arbitrary
    256-coefficient polynomials.  A multiplier that omits the customary
    one-bit shift produces the halves of the product {i shifted}, which is
    not a product of two blocks, so the deferral has to be stated at this
    generality to apply to it -- see [Spec.CLMUL.gmulx_three].  Nothing in
    the proof changes but the name of the splitting lemma. *)
let pmod_defer4 (a1 a2 a3 a4: poly)
                (u1 v1 u2 v2 u3 v3 u4 v4 p q pp qq: block)
  : Lemma (requires halvesp a1 u1 v1 /\ halvesp a2 u2 v2 /\
                    halvesp a3 u3 v3 /\ halvesp a4 u4 v4 /\
                    halves (sum4 v1 v2 v3 v4) r_block p q /\
                    halves q r_block pp qq)
          (ensures sum4 (pmod a1 256) (pmod a2 256)
                        (pmod a3 256) (pmod a4 256) ==
                   gadd (sum4 u1 u2 u3 u4) (gadd p pp))
  = psplit a1 u1 v1;
    psplit a2 u2 v2;
    psplit a3 u3 v3;
    psplit a4 u4 v4;
    regroup4 u1 u2 u3 u4
             (gmul v1 r_block) (gmul v2 r_block)
             (gmul v3 r_block) (gmul v4 r_block);
    mul_r_sum4 v1 v2 v3 v4;
    mul_r_two (sum4 v1 v2 v3 v4) p q pp qq

#pop-options

(** {2 Eight multiplies, one reduction}

    Everything above generalises, and the reason to want it is that the fold
    is a fixed cost per group rather than per block: a four-block turn of
    [Hacl.AES.GF128.NI.ghash_loop4_ni] is about two hundred instructions of
    which roughly forty are the one remaining reduction, so running eight
    blocks against eight powers of the hash key pays that forty once for a
    hundred and twenty-eight bytes instead of twice.

    None of it is new reasoning.  [sum8] is two [sum4]s added, and each of
    the three facts the eight-way deferral needs reduces to its four-way
    counterpart applied twice plus one regrouping of exclusive-ors. *)

let sum8 (a b c d e f g h: block) : block
  = gadd (sum4 a b c d) (sum4 e f g h)

(** The one genuinely new exclusive-or fact: four terms may be paired the
    other way round.  Eight booleans a bit, which the solver does itself. *)
let gadd_shuffle (a b c d: block)
  : Lemma (gadd (gadd a b) (gadd c d) == gadd (gadd a c) (gadd b d))
  = let l = gadd (gadd a b) (gadd c d) in
    let r = gadd (gadd a c) (gadd b d) in
    let aux (i: nat { i < 128 }) : Lemma (bit l i == bit r i)
      = gadd_bit (gadd a b) (gadd c d) i; gadd_bit a b i; gadd_bit c d i;
        gadd_bit (gadd a c) (gadd b d) i; gadd_bit a c i; gadd_bit b d i
    in
    Classical.forall_intro aux;
    bits_inj l r

let regroup8 (u1 u2 u3 u4 u5 u6 u7 u8 w1 w2 w3 w4 w5 w6 w7 w8: block)
  : Lemma (sum8 (gadd u1 w1) (gadd u2 w2) (gadd u3 w3) (gadd u4 w4)
                (gadd u5 w5) (gadd u6 w6) (gadd u7 w7) (gadd u8 w8) ==
           gadd (sum8 u1 u2 u3 u4 u5 u6 u7 u8)
                (sum8 w1 w2 w3 w4 w5 w6 w7 w8))
  = regroup4 u1 u2 u3 u4 w1 w2 w3 w4;
    regroup4 u5 u6 u7 u8 w5 w6 w7 w8;
    gadd_shuffle (sum4 u1 u2 u3 u4) (sum4 w1 w2 w3 w4)
                 (sum4 u5 u6 u7 u8) (sum4 w5 w6 w7 w8)

(** A product distributes over a fourfold sum, for any multiplier.  This is
    [mul_r_sum4] with the reduction constant generalised; the eight-way
    Horner step needs it at [h4] as well. *)
let mul_sum4 (v1 v2 v3 v4 c: block)
  : Lemma (gmul (sum4 v1 v2 v3 v4) c ==
           sum4 (gmul v1 c) (gmul v2 c) (gmul v3 c) (gmul v4 c))
  = gmul_gadd_left v3 v4 c;
    gmul_gadd_left v2 (gadd v3 v4) c;
    gmul_gadd_left v1 (gadd v2 (gadd v3 v4)) c

let mul_r_sum8 (v1 v2 v3 v4 v5 v6 v7 v8: block)
  : Lemma (gmul (sum8 v1 v2 v3 v4 v5 v6 v7 v8) r_block ==
           sum8 (gmul v1 r_block) (gmul v2 r_block)
                (gmul v3 r_block) (gmul v4 r_block)
                (gmul v5 r_block) (gmul v6 r_block)
                (gmul v7 r_block) (gmul v8 r_block))
  = gmul_gadd_left (sum4 v1 v2 v3 v4) (sum4 v5 v6 v7 v8) r_block;
    mul_sum4 v1 v2 v3 v4 r_block;
    mul_sum4 v5 v6 v7 v8 r_block

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** Eight multiplies, eight carry-less products, one reduction.  The
    statement and the proof are [gmul_defer4]'s with four replaced by
    eight throughout. *)
let gmul_defer8 (x1 y1 u1 v1 x2 y2 u2 v2 x3 y3 u3 v3 x4 y4 u4 v4
                 x5 y5 u5 v5 x6 y6 u6 v6 x7 y7 u7 v7 x8 y8 u8 v8
                 p q pp qq: block)
  : Lemma (requires halves x1 y1 u1 v1 /\ halves x2 y2 u2 v2 /\
                    halves x3 y3 u3 v3 /\ halves x4 y4 u4 v4 /\
                    halves x5 y5 u5 v5 /\ halves x6 y6 u6 v6 /\
                    halves x7 y7 u7 v7 /\ halves x8 y8 u8 v8 /\
                    halves (sum8 v1 v2 v3 v4 v5 v6 v7 v8) r_block p q /\
                    halves q r_block pp qq)
          (ensures sum8 (gmul x1 y1) (gmul x2 y2) (gmul x3 y3) (gmul x4 y4)
                        (gmul x5 y5) (gmul x6 y6) (gmul x7 y7) (gmul x8 y8) ==
                   gadd (sum8 u1 u2 u3 u4 u5 u6 u7 u8) (gadd p pp))
  = gmul_split x1 y1 u1 v1;
    gmul_split x2 y2 u2 v2;
    gmul_split x3 y3 u3 v3;
    gmul_split x4 y4 u4 v4;
    gmul_split x5 y5 u5 v5;
    gmul_split x6 y6 u6 v6;
    gmul_split x7 y7 u7 v7;
    gmul_split x8 y8 u8 v8;
    regroup8 u1 u2 u3 u4 u5 u6 u7 u8
             (gmul v1 r_block) (gmul v2 r_block)
             (gmul v3 r_block) (gmul v4 r_block)
             (gmul v5 r_block) (gmul v6 r_block)
             (gmul v7 r_block) (gmul v8 r_block);
    mul_r_sum8 v1 v2 v3 v4 v5 v6 v7 v8;
    mul_r_two (sum8 v1 v2 v3 v4 v5 v6 v7 v8) p q pp qq

(** And the eight-way deferral over arbitrary polynomials, which is what the
    shiftless multiplier needs. *)
let pmod_defer8 (a1 a2 a3 a4 a5 a6 a7 a8: poly)
                (u1 v1 u2 v2 u3 v3 u4 v4 u5 v5 u6 v6 u7 v7 u8 v8
                 p q pp qq: block)
  : Lemma (requires halvesp a1 u1 v1 /\ halvesp a2 u2 v2 /\
                    halvesp a3 u3 v3 /\ halvesp a4 u4 v4 /\
                    halvesp a5 u5 v5 /\ halvesp a6 u6 v6 /\
                    halvesp a7 u7 v7 /\ halvesp a8 u8 v8 /\
                    halves (sum8 v1 v2 v3 v4 v5 v6 v7 v8) r_block p q /\
                    halves q r_block pp qq)
          (ensures sum8 (pmod a1 256) (pmod a2 256) (pmod a3 256) (pmod a4 256)
                        (pmod a5 256) (pmod a6 256) (pmod a7 256) (pmod a8 256) ==
                   gadd (sum8 u1 u2 u3 u4 u5 u6 u7 u8) (gadd p pp))
  = psplit a1 u1 v1;
    psplit a2 u2 v2;
    psplit a3 u3 v3;
    psplit a4 u4 v4;
    psplit a5 u5 v5;
    psplit a6 u6 v6;
    psplit a7 u7 v7;
    psplit a8 u8 v8;
    regroup8 u1 u2 u3 u4 u5 u6 u7 u8
             (gmul v1 r_block) (gmul v2 r_block)
             (gmul v3 r_block) (gmul v4 r_block)
             (gmul v5 r_block) (gmul v6 r_block)
             (gmul v7 r_block) (gmul v8 r_block);
    mul_r_sum8 v1 v2 v3 v4 v5 v6 v7 v8;
    mul_r_two (sum8 v1 v2 v3 v4 v5 v6 v7 v8) p q pp qq

#pop-options

(** {2 Eight turns of Horner's rule}

    The powers are generated one multiplication at a time, so what the
    eight-way step needs -- that [h4] times the first four powers are the
    last four -- is not immediate and has to be walked up the chain. *)

let pow_mul4 (h h2 h3 h4 h5 h6 h7 h8: block)
  : Lemma (requires h2 == gmul h h /\ h3 == gmul h2 h /\ h4 == gmul h3 h /\
                    h5 == gmul h4 h /\ h6 == gmul h5 h /\ h7 == gmul h6 h /\
                    h8 == gmul h7 h)
          (ensures gmul h h4 == h5 /\ gmul h2 h4 == h6 /\
                   gmul h3 h4 == h7 /\ gmul h4 h4 == h8)
  = (* h * h4 = h4 * h = h5 *)
    gmul_comm h h4;
    (* h2 * h4 = (h * h) * h4 = h * (h * h4) = h * h5 = h5 * h = h6 *)
    gmul_assoc h h h4;
    gmul_comm h h5;
    (* h3 * h4 = (h2 * h) * h4 = h2 * (h * h4) = h2 * h5 = h * (h * h5)
                = h * h6 = h6 * h = h7 *)
    gmul_assoc h2 h h4;
    gmul_assoc h h h5;
    gmul_comm h h6;
    (* h4 * h4 = (h3 * h) * h4 = h3 * h5 = (h2 * h) * h5 = h2 * h6
                = (h * h) * h6 = h * h7 = h8 *)
    gmul_assoc h3 h h4;
    gmul_assoc h2 h h5;
    gmul_assoc h h h6;
    gmul_comm h h7

#push-options "--fuel 0 --ifuel 0 --z3rlimit 400"

(** Eight turns at once, as two fours.  The first four are [horner4], the
    second four are [horner4] again on the result, and the work is pushing
    the multiplication by [h4] through the first group's four terms, which
    raises each of their powers by four. *)
let horner8 (a b0 b1 b2 b3 b4 b5 b6 b7 h h2 h3 h4 h5 h6 h7 h8: block)
  : Lemma (requires h2 == gmul h h /\ h3 == gmul h2 h /\ h4 == gmul h3 h /\
                    h5 == gmul h4 h /\ h6 == gmul h5 h /\ h7 == gmul h6 h /\
                    h8 == gmul h7 h)
          (ensures
            (let s1 = gmul (gadd a b0) h in
             let s2 = gmul (gadd s1 b1) h in
             let s3 = gmul (gadd s2 b2) h in
             let s4 = gmul (gadd s3 b3) h in
             let s5 = gmul (gadd s4 b4) h in
             let s6 = gmul (gadd s5 b5) h in
             let s7 = gmul (gadd s6 b6) h in
             gmul (gadd s7 b7) h ==
               sum8 (gmul (gadd a b0) h8) (gmul b1 h7)
                    (gmul b2 h6) (gmul b3 h5)
                    (gmul b4 h4) (gmul b5 h3)
                    (gmul b6 h2) (gmul b7 h)))
  = let a0 = gadd a b0 in
    let s1 = gmul a0 h in
    let s2 = gmul (gadd s1 b1) h in
    let s3 = gmul (gadd s2 b2) h in
    let s4 = gmul (gadd s3 b3) h in
    horner4 a b0 b1 b2 b3 h h2 h3 h4;
    horner4 s4 b4 b5 b6 b7 h h2 h3 h4;
    (* The second group's leading term splits. *)
    gmul_gadd_left s4 b4 h4;
    (* ... and the first group's four terms each gain a power of four. *)
    mul_sum4 (gmul a0 h4) (gmul b1 h3) (gmul b2 h2) (gmul b3 h) h4;
    pow_mul4 h h2 h3 h4 h5 h6 h7 h8;
    gmul_assoc a0 h4 h4;
    gmul_assoc b1 h3 h4;
    gmul_assoc b2 h2 h4;
    gmul_assoc b3 h h4;
    (* One reassociation puts the eight terms in [sum8]'s shape. *)
    gadd_assoc (sum4 (gmul a0 h8) (gmul b1 h7) (gmul b2 h6) (gmul b3 h5))
               (gmul b4 h4)
               (gadd (gmul b5 h3) (gadd (gmul b6 h2) (gmul b7 h)))

#pop-options

(** {2 The powers of the hash key, as an array of bytes}

    The aggregated loops below consume four or eight blocks against the
    first four or eight powers of the hash key.  Computing them costs three
    or seven multiplications, which is why the aggregation used to begin
    only once there were two groups to pay for it; held in the expanded-key
    context instead, they are free, and the aggregation begins as soon as
    there is one group.

    The context holds them in the same pre-divided representation as the key
    itself -- [h^i / x] rather than [h^i] -- because that is the form
    [Hacl.AES.GF128.NI.gmul_vec] both consumes and produces.  The predicate
    is the recurrence rather than a closed form: each power is the one
    before it times the key, which is exactly what the loops need and
    exactly what the expansion establishes, one step at a time. *)

let hblk (v: Seq.seq elem) (i: nat) : GTot block =
  if 16 * i + 16 <= Seq.length v then Seq.slice v (16 * i) (16 * i + 16) else zero

let pow_step (v: Seq.seq elem) (i: pos) : prop =
  xtimes (hblk v i) == gmul (xtimes (hblk v (i - 1))) (xtimes (hblk v 0))

let powlen : nat = 128

let pows_ok (v: Seq.seq elem) : prop =
  Seq.length v == powlen /\
  pow_step v 1 /\ pow_step v 2 /\ pow_step v 3 /\ pow_step v 4 /\
  pow_step v 5 /\ pow_step v 6 /\ pow_step v 7

(** Advancing both sides of one step of the recurrence.

    The implementation's multiplier computes [gmul a (xtimes b)] -- the real
    product with one shift omitted -- so a chain of them starting at [h/x]
    gives [h^i/x] at every step.  This is the one line that says so, and it
    is what turns what the multiplier gives into what {!pow_step} asks
    for. *)
#push-options "--fuel 2 --ifuel 0"
let pow_adv (a b: block)
  : Lemma (xtimes (gmul a (xtimes b)) == gmul (xtimes a) (xtimes b))
  = gmul_xt_left a (xtimes b) 1
#pop-options
