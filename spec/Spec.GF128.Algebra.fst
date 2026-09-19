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
