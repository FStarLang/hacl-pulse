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

(** GCM's field multiplication as a polynomial product, modulo a polynomial.

    {2 What is being proved}

    [Spec.GF128.gmul] is SP 800-38D algorithm 1 written out: a hundred and
    twenty-eight iterations, each a shift of a byte string, a conditional
    exclusive-or with [0xe1 00 ... 00], and a conditional accumulation.  That
    is a fine specification and a fine portable implementation, and it is
    completely opaque to any argument about carry-less multiplication.

    This module says what algorithm 1 computes: the product of two
    polynomials over GF(2), reduced modulo [x^128 + x^7 + x^2 + x + 1].  With
    that in hand a [PCLMULQDQ] implementation has something to be proved
    against, because the instruction computes a polynomial product and
    nothing else.

    {2 How}

    The reduction is defined as the {i linear extension} of [x^i mod P]:
    [pmod a n] is the exclusive-or, over the set bits of [a], of [xpow i],
    where [xpow] is the same "shift and conditionally add [0xe1]" step that
    algorithm 1 uses to advance its running [v].  Defining it this way makes
    linearity true by construction and makes [pmod (pshift c 1) == xtimes
    (pmod c)] a restatement of [xpow (i+1) == xtimes (xpow i)], which is the
    definition.  No general theory of polynomial division is needed, and in
    particular nothing here needs [pmul] to be associative or commutative.

    The chain is then four steps, each an application of one lemma from
    [Spec.CarryLess]:

    - [gmul] is the accumulation [accum], by unrolling the loop;
    - [accum] is a sum over the bits of [x] of [xt y j], by definition;
    - [xt y j] is [pmod] of [y] shifted up by [j];
    - and [pmod] of a product is that sum, by exchanging two sums. *)
module Spec.GF128.Poly

open Spec.Byte
open Spec.GF128
open Spec.CarryLess

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module UInt = FStar.UInt
module U8 = FStar.UInt8

(** {2 A bit of a byte is a bit of a byte}

    [Spec.GF128.bit] extracts a bit arithmetically and [FStar.UInt] extracts
    one through a bit vector.  One induction connects them, and afterwards the
    whole of [FStar.UInt]'s bitwise theory -- in particular that the [i]-th
    bit of an exclusive-or is the exclusive-or of the [i]-th bits -- applies
    to blocks. *)

let rec nth_div_mod (#n: pos) (a: UInt.uint_t n) (i: nat { i < n })
  : Lemma (ensures UInt.nth a i == ((a / pow2 (n - 1 - i)) % 2 = 1))
          (decreases n)
  = if i = n - 1
    then begin
      assert_norm (pow2 0 == 1);
      Seq.lemma_index_app2 (UInt.to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i
    end
    else begin
      Seq.lemma_index_app1 (UInt.to_vec #(n - 1) (a / 2)) (Seq.create 1 (a % 2 = 1)) i;
      nth_div_mod #(n - 1) (a / 2) i;
      Math.division_multiplication_lemma a 2 (pow2 (n - 2 - i));
      Math.pow2_plus 1 (n - 2 - i)
    end

let bit_is_nth (a: block) (i: nat { i < 128 })
  : Lemma (bit a i == UInt.nth #8 (Seq.index a (i / 8)) (i % 8))
  = nth_div_mod #8 (Seq.index a (i / 8)) (i % 8)

(** Two blocks with the same bits are the same block. *)
let bits_inj (a b: block)
  : Lemma (requires forall (i: nat). i < 128 ==> bit a i == bit b i)
          (ensures a == b)
  = let aux (j: nat { j < 16 }) : Lemma (Seq.index a j == Seq.index b j)
      = let f (k: nat { k < 8 }) : Lemma (UInt.nth #8 (Seq.index a j) k ==
                                          UInt.nth #8 (Seq.index b j) k)
          = Math.lemma_mult_le_right 8 (j + 1) 16;
            Math.multiple_division_lemma j 8;
            Math.multiple_modulo_lemma j 8;
            Math.lemma_div_plus k j 8;
            Math.lemma_mod_plus k j 8;
            Math.small_division_lemma_1 k 8;
            Math.small_mod k 8;
            bit_is_nth a (j * 8 + k);
            bit_is_nth b (j * 8 + k)
        in
        FStar.Classical.forall_intro f;
        UInt.nth_lemma #8 (Seq.index a j) (Seq.index b j)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro a b

(** {2 The bits of the operations} *)

let gadd_bit (a b: block) (i: nat { i < 128 })
  : Lemma (bit (gadd a b) i == (bit a i <> bit b i))
  = bit_is_nth (gadd a b) i;
    bit_is_nth a i;
    bit_is_nth b i;
    xor_is_logxor (Seq.index a (i / 8)) (Seq.index b (i / 8))

let zero_bit (i: nat { i < 128 }) : Lemma (bit zero i == false) = ()

(** The reduction constant, [x^7 + x^2 + x + 1]. *)
let r_bit (i: nat { i < 128 })
  : Lemma (bit r_block i == (i = 0 || i = 1 || i = 2 || i = 7))
  = assert_norm (bit r_block 0 == true);
    assert_norm (bit r_block 1 == true);
    assert_norm (bit r_block 2 == true);
    assert_norm (bit r_block 3 == false);
    assert_norm (bit r_block 4 == false);
    assert_norm (bit r_block 5 == false);
    assert_norm (bit r_block 6 == false);
    assert_norm (bit r_block 7 == true);
    if i < 8 then () else Math.small_division_lemma_1 0 (pow2 (7 - i % 8))

(** {2 The shift}

    The byte string moves right, which in this bit numbering is multiplication
    by [x]: the coefficient of [x^i] becomes the coefficient of [x^(i+1)], and
    the coefficient of [x^127] falls off the end. *)

#push-options "--z3rlimit 200"

let shift_byte_bit (x: elem) (c: bool) (b: nat { b < 8 })
  : Lemma ((((if c then 128 else 0) + x / 2) / pow2 (7 - b)) % 2 =
             (if b = 0 then (if c then 1 else 0)
              else ((x / pow2 (8 - b)) % 2))
           == true)
  = let cv = if c then 1 else 0 in
    if b = 0
    then begin
      assert_norm (pow2 7 == 128);
      Math.lemma_div_lt x 8 1;
      Math.small_division_lemma_1 (x / 2) 128;
      Math.division_addition_lemma (x / 2) 128 cv;
      Math.small_mod cv 2
    end
    else begin
      Math.pow2_plus (7 - b) b;
      assert (pow2 7 == pow2 (7 - b) * pow2 b);
      Math.division_addition_lemma (x / 2) (pow2 (7 - b)) (cv * pow2 b);
      Math.division_multiplication_lemma x 2 (pow2 (7 - b));
      Math.pow2_plus 1 (7 - b);
      Math.lemma_mod_plus ((x / 2) / pow2 (7 - b)) (cv * pow2 (b - 1)) 2;
      Math.pow2_plus 1 (b - 1)
    end

let shift_bit (v: block) (i: nat { i < 128 })
  : Lemma (bit (shift_right_1 v) i == (i > 0 && bit v (i - 1)))
  = let j = i / 8 in
    let b = i % 8 in
    Math.euclidean_division_definition i 8;
    let c = if j = 0 then false else Seq.index v (j - 1) % 2 = 1 in
    assert (shift_byte v j == (if c then 128 else 0) + Seq.index v j / 2);
    shift_byte_bit (Seq.index v j) c b;
    if b = 0
    then begin
      if j = 0 then ()
      else begin
        assert_norm (pow2 0 == 1);
        Math.lemma_div_plus 7 (j - 1) 8;
        Math.lemma_mod_plus 7 (j - 1) 8;
        Math.small_division_lemma_1 7 8;
        Math.small_mod 7 8
      end
    end
    else begin
      Math.lemma_div_plus (b - 1) j 8;
      Math.lemma_mod_plus (b - 1) j 8;
      Math.small_division_lemma_1 (b - 1) 8;
      Math.small_mod (b - 1) 8
    end

#pop-options

(** {2 Multiplication by [x], modulo the field polynomial}

    Written to be {i syntactically} the step [gmul_loop] takes on its running
    [v], so that the unrolling below is a rewriting and not a proof. *)

let xtimes (v: block) : block =
  if Seq.index v (blocklen - 1) % 2 = 0
  then shift_right_1 v
  else gadd (shift_right_1 v) r_block

let top_bit (v: block) : Lemma (bit v 127 == (Seq.index v (blocklen - 1) % 2 = 1))
  = assert_norm (pow2 0 == 1)

let xtimes_bit (v: block) (i: nat { i < 128 })
  : Lemma (bit (xtimes v) i ==
             ((i > 0 && bit v (i - 1)) <>
              (bit v 127 && (i = 0 || i = 1 || i = 2 || i = 7))))
  = top_bit v;
    shift_bit v i;
    r_bit i;
    if Seq.index v (blocklen - 1) % 2 = 0 then () else gadd_bit (shift_right_1 v) r_block i

(** {2 Dividing by [x]}

    [xtimes] is a bijection -- [x] is invertible, the field polynomial having
    a constant term -- and its inverse is as cheap: shift the other way, and
    if the bit that falls off the {i bottom} is set, put [x^127] back and add
    the reduction constant divided by [x], which is [x^127 + x^6 + x^1 + 1].

    This is what lets a carry-less multiplier omit its one-bit shift: by
    [Spec.CLMUL.gmulx_three] such a multiplier computes [x] times the field
    product, so storing [xdiv h] in place of the hash key once, at setup,
    makes every later multiplication come out exact.  See the GHASH section
    of the README. *)

let shl_byte (a: block) (i: nat { i < blocklen }) : elem =
  let carry : elem = if i = blocklen - 1 then 0 else Seq.index a (i + 1) / 128 in
  (Seq.index a i % 128) * 2 + carry

let shift_left_1 (a: block) : block =
  Seq.init blocklen (fun i -> shl_byte a i)

#push-options "--z3rlimit 400"

let shl_byte_bit (x: elem) (c: bool) (b: nat { b < 8 })
  : Lemma (((((x % 128) * 2 + (if c then 1 else 0)) / pow2 (7 - b)) % 2 = 1)
           == (if b = 7 then c else ((x / pow2 (6 - b)) % 2 = 1)))
  = let cv = if c then 1 else 0 in
    let y = (x % 128) * 2 + cv in
    if b = 7
    then begin
      assert_norm (pow2 0 == 1);
      Math.lemma_mod_plus cv (x % 128) 2;
      Math.small_mod cv 2
    end
    else begin
      let n = 6 - b in
      Math.pow2_plus 1 n;
      Math.division_multiplication_lemma y 2 (pow2 n);
      Math.lemma_div_plus cv (x % 128) 2;
      Math.small_division_lemma_1 cv 2;
      assert (y / pow2 (7 - b) == (x % 128) / pow2 n);
      Math.pow2_plus n (b + 1);
      assert_norm (pow2 7 == 128);
      Math.euclidean_division_definition x 128;
      Math.lemma_div_plus (x % 128) (x / 128) (pow2 n) ;
      Math.pow2_double_mult (pow2 b);
      Math.lemma_mod_plus ((x % 128) / pow2 n) (pow2 b * (x / 128)) 2
    end

let shl_bit (a: block) (i: nat { i < 128 })
  : Lemma (bit (shift_left_1 a) i == (i < 127 && bit a (i + 1)))
  = let j = i / 8 in
    let b = i % 8 in
    Math.euclidean_division_definition i 8;
    let c = if j = blocklen - 1 then false
            else Seq.index a (j + 1) / 128 = 1 in
    Math.lemma_div_lt (Seq.index a (j + 1 - (if j = blocklen - 1 then 1 else 0))) 8 7;
    assert (shl_byte a j == (Seq.index a j % 128) * 2 + (if c then 1 else 0));
    shl_byte_bit (Seq.index a j) c b;
    if b = 7
    then begin
      if j = blocklen - 1 then ()
      else begin
        assert_norm (pow2 7 == 128);
        Math.lemma_div_plus 0 (j + 1) 8;
        Math.lemma_mod_plus 0 (j + 1) 8
      end
    end
    else begin
      Math.lemma_div_plus (b + 1) j 8;
      Math.lemma_mod_plus (b + 1) j 8;
      Math.small_division_lemma_1 (b + 1) 8;
      Math.small_mod (b + 1) 8
    end

#pop-options

(** [R / x == x^127 + x^6 + x^1 + 1]: byte 0 gets bits 0, 1 and 6, which is
    [0xc2], and byte 15 gets bit 127, which is [1]. *)
let rdiv_block : block =
  Seq.init blocklen (fun i -> (if i = 0 then 0xc2
                               else if i = blocklen - 1 then 1
                               else 0) <: elem)

#push-options "--z3rlimit 200"

let rdiv_bit (i: nat { i < 128 })
  : Lemma (bit rdiv_block i == (i = 0 || i = 1 || i = 6 || i = 127))
  = if i < 8
    then begin
      assert_norm (bit rdiv_block 0 == true);
      assert_norm (bit rdiv_block 1 == true);
      assert_norm (bit rdiv_block 2 == false);
      assert_norm (bit rdiv_block 3 == false);
      assert_norm (bit rdiv_block 4 == false);
      assert_norm (bit rdiv_block 5 == false);
      assert_norm (bit rdiv_block 6 == true);
      assert_norm (bit rdiv_block 7 == false)
    end
    else if i < 120 then Math.small_division_lemma_1 0 (pow2 (7 - i % 8))
    else begin
      assert_norm (bit rdiv_block 120 == false);
      assert_norm (bit rdiv_block 121 == false);
      assert_norm (bit rdiv_block 122 == false);
      assert_norm (bit rdiv_block 123 == false);
      assert_norm (bit rdiv_block 124 == false);
      assert_norm (bit rdiv_block 125 == false);
      assert_norm (bit rdiv_block 126 == false);
      assert_norm (bit rdiv_block 127 == true)
    end

#pop-options

let xdiv (v: block) : block =
  if bit v 0 then gadd (shift_left_1 v) rdiv_block else shift_left_1 v

let xdiv_bit (v: block) (j: nat { j < 128 })
  : Lemma (bit (xdiv v) j ==
             (if j = 127 then bit v 0
              else (j < 127 && bit v (j + 1)) <>
                   (bit v 0 && (j = 0 || j = 1 || j = 6))))
  = shl_bit v j;
    rdiv_bit j;
    if bit v 0 then gadd_bit (shift_left_1 v) rdiv_block j else ()

#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"

(** The point of it all: [xdiv] undoes [xtimes]. *)
let xtimes_xdiv (v: block) : Lemma (xtimes (xdiv v) == v)
  = let aux (i: nat { i < 128 }) : Lemma (bit (xtimes (xdiv v)) i == bit v i)
      = xtimes_bit (xdiv v) i;
        xdiv_bit v 127;
        if i > 0 then xdiv_bit v (i - 1) else ()
    in
    FStar.Classical.forall_intro aux;
    bits_inj (xtimes (xdiv v)) v

#pop-options

(** {2 The bits of a block, as a polynomial} *)

let pbits (a: block) : poly = Seq.init 128 (fun i -> bit a i)

let pbits_get (a: block) (i: int)
  : Lemma (pget (pbits a) i == (0 <= i && i < 128 && bit a i)) = ()

let pbits_len (a: block) : Lemma (Seq.length (pbits a) == 128) = ()

(** {2 [x^i] reduced, and the linear extension of it} *)

let one_block : block = Seq.init blocklen (fun j -> (if j = 0 then 128 else 0) <: elem)

let one_bit (i: nat { i < 128 }) : Lemma (bit one_block i == (i = 0))
  = if i < 8
    then begin
      assert_norm (bit one_block 0 == true);
      assert_norm (bit one_block 1 == false);
      assert_norm (bit one_block 2 == false);
      assert_norm (bit one_block 3 == false);
      assert_norm (bit one_block 4 == false);
      assert_norm (bit one_block 5 == false);
      assert_norm (bit one_block 6 == false);
      assert_norm (bit one_block 7 == false)
    end
    else Math.small_division_lemma_1 0 (pow2 (7 - i % 8))

let rec xpow (i: nat) : Tot block (decreases i) =
  if i = 0 then one_block else xtimes (xpow (i - 1))

let xpowi (k: int) : block = if k < 0 then zero else xpow k

(** Below the degree of the modulus, [x^i mod P] is [x^i]. *)
let rec xpow_mono (i: nat { i < 128 }) (k: nat { k < 128 })
  : Lemma (ensures bit (xpow i) k == (k = i)) (decreases i)
  = if i = 0 then one_bit k
    else begin
      xtimes_bit (xpow (i - 1)) k;
      xpow_mono (i - 1) 127;
      if k = 0 then () else xpow_mono (i - 1) (k - 1)
    end

(** {2 Exclusive-or of a family of blocks} *)

let rec bsum (f: int -> block) (n: nat) : Tot block (decreases n) =
  if n = 0 then zero else gadd (f (n - 1)) (bsum f (n - 1))

let rec bsum_bit (f: int -> block) (n: nat) (i: nat { i < 128 })
  : Lemma (ensures bit (bsum f n) i == xsum (fun k -> bit (f k) i) 0 n)
          (decreases n)
  = if n = 0 then zero_bit i
    else begin
      bsum_bit f (n - 1) i;
      gadd_bit (f (n - 1)) (bsum f (n - 1)) i
    end

(** The reduction: the exclusive-or, over the set bits of [a], of [x^k mod P].
    Linearity is not a lemma but the definition. *)
let pmod (a: poly) (n: nat) : block =
  bsum (fun k -> if pget a k then xpowi k else zero) n

let pmod_bit (a: poly) (n: nat) (i: nat { i < 128 })
  : Lemma (bit (pmod a n) i == xsum (fun k -> pget a k && bit (xpowi k) i) 0 n)
  = bsum_bit (fun k -> if pget a k then xpowi k else zero) n i;
    zero_bit i;
    xsum_ext (fun k -> bit (if pget a k then xpowi k else zero) i)
             (fun k -> pget a k && bit (xpowi k) i) 0 n

(** {2 [y] advanced [j] times}

    [xt y j] is [y * x^j] reduced, and is the running [v] of [gmul_loop]. *)

let rec xt (v: block) (j: nat) : Tot block (decreases j) =
  if j = 0 then v else xtimes (xt v (j - 1))

let xti (v: block) (j: int) : block = if j < 0 then zero else xt v j

(** The key step: [y * x^j] is the linear extension applied to [y] shifted,
    which is the same sum with [xpow] carrying the shift.

    The three cases are separate lemmas, and so is the unfolding of [xpowi]
    under the summation sign.  Written as one recursive function with the
    helpers nested it is a single query of several hundred thousand terms and
    takes the better part of an hour; split up it is under a minute. *)

#push-options "--z3rlimit 150 --fuel 1 --ifuel 0"

(** [x^(m+j) == x * x^(m+j-1)], at bit [0].  Below the summation range
    [m + j] may be zero, where the step does not hold and there is nothing to
    prove. *)
let xpow_step_zero (j: pos) (m: int)
  : Lemma (m + j >= 1 ==> bit (xpowi (m + j)) 0 == bit (xpowi (m + (j - 1))) 127)
  = if m + j >= 1 then xtimes_bit (xpow (m + (j - 1))) 0 else ()

let xpow_step_pos (j: pos) (i: nat { 0 < i /\ i < 128 }) (m: int)
  : Lemma (m + j >= 1 ==>
           bit (xpowi (m + j)) i ==
             (bit (xpowi (m + (j - 1))) (i - 1) <>
              (bit (xpowi (m + (j - 1))) 127 && (i = 1 || i = 2 || i = 7))))
  = if m + j >= 1 then xtimes_bit (xpow (m + (j - 1))) i else ()

(** The summand at [m], which is where the step above is used: below the
    range [pbits y] is zero and there is nothing to prove. *)
let xt_term_zero (y: block) (j: pos) (i: nat { i == 0 }) (m: int)
  : Lemma ((pget (pbits y) m && bit (xpowi (m + j)) i) ==
           (pget (pbits y) m && bit (xpowi (m + (j - 1))) 127))
  = if m >= 0 then xpow_step_zero j m else ()

let xt_term_pos (y: block) (j: pos) (i: nat { 0 < i /\ i < 128 }) (m: int)
  : Lemma ((pget (pbits y) m && bit (xpowi (m + j)) i) ==
           ((pget (pbits y) m && bit (xpowi (m + (j - 1))) (i - 1)) <>
            ((i = 1 || i = 2 || i = 7) &&
             (pget (pbits y) m && bit (xpowi (m + (j - 1))) 127))))
  = if m >= 0 then xpow_step_pos j i m else ()

(** At [j = 0] exactly one term of the sum survives. *)
let xt_bit_zero (y: block) (j: nat { j == 0 }) (i: nat { i < 128 })
  : Lemma (bit (xt y j) i ==
           xsum (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128)
  = let aux (m: int)
      : Lemma (0 <= m /\ m < 128 /\ m <> i ==>
               (pget (pbits y) m && bit (xpowi (m + j)) i) == false)
      = if 0 <= m && m < 128 then xpow_mono m i else ()
    in
    FStar.Classical.forall_intro aux;
    xpow_mono i i;
    xsum_one (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128 i

(** One unfolding of [xt], done here so that the two step lemmas below can
    run with no fuel at all: with fuel, [xpowi (m + j)] under a quantifier
    unfolds [xpow] for every [m] and the query never terminates. *)
let xt_unfold (y: block) (j: pos) : Lemma (xt y j == xtimes (xt y (j - 1))) = ()

#push-options "--fuel 0 --ifuel 0"

(** The step at bit [0], where the only contribution is the bit that wrapped
    round from the top. *)
let xt_bit_step_zero (y: block) (j: pos) (i: nat { i == 0 })
  : Lemma (requires bit (xt y (j - 1)) 127 ==
                    xsum (fun m -> pget (pbits y) m && bit (xpowi (m + (j - 1))) 127) 0 128)
          (ensures bit (xt y j) i ==
                   xsum (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128)
  = xt_unfold y j;
    FStar.Classical.forall_intro (xt_term_zero y j i);
    xtimes_bit (xt y (j - 1)) i;
    xsum_ext (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i)
             (fun m -> pget (pbits y) m && bit (xpowi (m + (j - 1))) 127) 0 128

(** The step above bit [0]: the shifted bit, plus the wrapped bit where the
    reduction constant has a term. *)
let xt_bit_step_pos (y: block) (j: pos) (i: nat { 0 < i /\ i < 128 })
  : Lemma (requires (bit (xt y (j - 1)) 127 ==
                     xsum (fun m -> pget (pbits y) m && bit (xpowi (m + (j - 1))) 127) 0 128) /\
                    (bit (xt y (j - 1)) (i - 1) ==
                     xsum (fun m -> pget (pbits y) m && bit (xpowi (m + (j - 1))) (i - 1)) 0 128))
          (ensures bit (xt y j) i ==
                   xsum (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128)
  = let rb = (i = 1 || i = 2 || i = 7) in
    xt_unfold y j;
    FStar.Classical.forall_intro (xt_term_pos y j i);
    xtimes_bit (xt y (j - 1)) i;
    xsum_ext (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i)
             (fun m -> (pget (pbits y) m && bit (xpowi (m + (j - 1))) (i - 1)) <>
                       (rb && (pget (pbits y) m && bit (xpowi (m + (j - 1))) 127)))
             0 128;
    xsum_xor (fun m -> pget (pbits y) m && bit (xpowi (m + (j - 1))) (i - 1))
             (fun m -> rb && (pget (pbits y) m && bit (xpowi (m + (j - 1))) 127))
             0 128;
    xsum_and rb (fun m -> pget (pbits y) m && bit (xpowi (m + (j - 1))) 127) 0 128

#pop-options

let rec xt_bit (y: block) (j: nat) (i: nat { i < 128 })
  : Lemma (ensures bit (xt y j) i ==
             xsum (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128)
          (decreases j)
  = if j = 0 then xt_bit_zero y j i
    else begin
      xt_bit y (j - 1) 127;
      if i = 0 then xt_bit_step_zero y j i
      else begin
        xt_bit y (j - 1) (i - 1);
        xt_bit_step_pos y j i
      end
    end

(** {2 The accumulation [gmul_loop] performs} *)

let rec accum (x y: block) (n: nat { n <= 128 }) : Tot block (decreases n) =
  if n = 0 then zero
  else begin
    let z = accum x y (n - 1) in
    if bit x (n - 1) then gadd z (xt y (n - 1)) else z
  end

let rec accum_bit (x y: block) (n: nat { n <= 128 }) (i: nat { i < 128 })
  : Lemma (ensures bit (accum x y n) i ==
             xsum (fun j -> pget (pbits x) j && bit (xti y j) i) 0 n)
          (decreases n)
  = if n = 0 then zero_bit i
    else begin
      accum_bit x y (n - 1) i;
      if bit x (n - 1) then gadd_bit (accum x y (n - 1)) (xt y (n - 1)) i else ()
    end

(** {2 Reduction of a shifted polynomial} *)

let pmod_shift_bit (y: block) (j: nat { j <= 128 }) (i: nat { i < 128 })
  : Lemma (bit (pmod (pshift (pbits y) j) 256) i == bit (xt y j) i)
  = let f : int -> bool = fun k -> pget (pbits y) (k - j) && bit (xpowi k) i in
    let g : int -> bool = fun m -> pget (pbits y) m && bit (xpowi (m + j)) i in
    pmod_bit (pshift (pbits y) j) 256 i;
    xsum_ext (fun k -> pget (pshift (pbits y) j) k && bit (xpowi k) i) f 0 256;
    xsum_shift f 0 256 j;
    xsum_ext (fun m -> f (m + j)) g (0 - j) 256;
    xsum_trim_lo g (0 - j) j 256;
    xsum_trim_hi g 0 128 (256 - j);
    xsum_ext g (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128;
    xt_bit y j i

let pmod_shift (y: block) (j: nat { j <= 128 })
  : Lemma (pmod (pshift (pbits y) j) 256 == xt y j)
  = FStar.Classical.forall_intro (pmod_shift_bit y j);
    bits_inj (pmod (pshift (pbits y) j) 256) (xt y j)

(** {2 Reduction of a product}

    Exchanging the two sums turns "reduce the product" into "for each bit of
    [x], reduce [y] shifted", which is exactly what the loop accumulates. *)

(** The term of the doubly-indexed sum: bit [j] of [x], bit [k - j] of [y],
    and bit [i] of [x^k] reduced. *)
let pterm (x y: block) (i: nat { i < 128 }) (j k: int) : bool =
  pget (pbits x) j && (pget (pbits y) (k - j) && bit (xpowi k) i)

(** For a fixed [k], the coefficient of the product times bit [i] of [x^k]. *)
let pmod_pmul_inner (x y: block) (i: nat { i < 128 }) (k: int)
  : Lemma ((pget (pmul (pbits x) (pbits y)) k && bit (xpowi k) i) ==
           xsum (fun j -> pterm x y i j k) 0 128)
  = pmul_get (pbits x) (pbits y) k;
    pbits_len x;
    conv_def (pbits x) (pbits y) k
             (fun j -> pget (pbits x) j && pget (pbits y) (k - j));
    xsum_and (bit (xpowi k) i)
             (fun j -> pget (pbits x) j && pget (pbits y) (k - j)) 0 128;
    xsum_ext (fun j -> bit (xpowi k) i &&
                       (pget (pbits x) j && pget (pbits y) (k - j)))
             (fun j -> pterm x y i j k) 0 128

(** For a fixed [j], the whole of [y] shifted up by [j] and reduced, which is
    [y] advanced [j] times. *)
let pmod_pmul_outer (x y: block) (i: nat { i < 128 }) (j: int)
  : Lemma (xsum (fun k -> pterm x y i j k) 0 256 ==
           (pget (pbits x) j && bit (xti y j) i))
  = xsum_ext (fun k -> pterm x y i j k)
             (fun k -> pget (pbits x) j &&
                       (pget (pbits y) (k - j) && bit (xpowi k) i)) 0 256;
    xsum_and (pget (pbits x) j)
             (fun k -> pget (pbits y) (k - j) && bit (xpowi k) i) 0 256;
    if 0 <= j && j < 128
    then begin
      pmod_bit (pshift (pbits y) j) 256 i;
      xsum_ext (fun k -> pget (pshift (pbits y) j) k && bit (xpowi k) i)
               (fun k -> pget (pbits y) (k - j) && bit (xpowi k) i) 0 256;
      pmod_shift y j
    end
    else ()

let pmod_pmul_bit (x y: block) (i: nat { i < 128 })
  : Lemma (bit (pmod (pmul (pbits x) (pbits y)) 256) i == bit (accum x y 128) i)
  = pmod_bit (pmul (pbits x) (pbits y)) 256 i;
    FStar.Classical.forall_intro (pmod_pmul_inner x y i);
    xsum_ext (fun k -> pget (pmul (pbits x) (pbits y)) k && bit (xpowi k) i)
             (fun k -> xsum (fun j -> pterm x y i j k) 0 128) 0 256;
    xsum_swap (pterm x y i) 0 128 0 256;
    FStar.Classical.forall_intro (pmod_pmul_outer x y i);
    xsum_ext (fun j -> xsum (fun k -> pterm x y i j k) 0 256)
             (fun j -> pget (pbits x) j && bit (xti y j) i) 0 128;
    accum_bit x y 128 i

let pmod_pmul (x y: block)
  : Lemma (pmod (pmul (pbits x) (pbits y)) 256 == accum x y 128)
  = FStar.Classical.forall_intro (pmod_pmul_bit x y);
    bits_inj (pmod (pmul (pbits x) (pbits y)) 256) (accum x y 128)

(** {2 Unrolling algorithm 1} *)

let rec gmul_loop_accum (x y: block) (i: nat { i <= 128 })
  : Lemma (ensures gmul_loop x (accum x y i) (xt y i) i == accum x y 128)
          (decreases (128 - i))
  = if i = 128 then () else gmul_loop_accum x y (i + 1)

(** {2 The theorem}

    GCM's field multiplication is the carry-less product of the two blocks'
    bit strings, reduced modulo [x^128 + x^7 + x^2 + x + 1]. *)

let gmul_is_pmod (x y: block)
  : Lemma (gmul x y == pmod (pmul (pbits x) (pbits y)) 256)
  = gmul_loop_accum x y 0;
    pmod_pmul x y

#pop-options

(** {2 Splitting a product, which is what a carry-less multiplier gives}

    A 128x128 carry-less multiplier produces 255 coefficients, and the
    hardware hands them over as two registers.  The bottom 128 of them are
    already the answer, because [x^k] for [k < 128] is its own reduction; the
    top 127 have to be brought down, and [x^128] is the reduction constant, so
    bringing them down is another multiplication by exactly that constant.

    [gmul_split] says this without ever constructing the two halves: it takes
    two blocks and the hypothesis that their bits {i are} the two halves,
    which is what an implementation can prove about its registers. *)

let pcoef (x y: block) (k: int) : bool = pget (pmul (pbits x) (pbits y)) k

let pterm2 (x y: block) (i: nat { i < 128 }) (k: int) : bool =
  pcoef x y k && bit (xpowi k) i

(** [x^n] advanced [m] more times is [x^(n+m)]. *)
let rec xpow_add (n m: nat)
  : Lemma (ensures xpow (n + m) == xt (xpow n) m) (decreases m)
  = if m = 0 then () else xpow_add n (m - 1)

(** [x^127] has only its top bit, so one more step is the reduction constant
    and nothing else: [x^128 == R]. *)
let xpow_128 (_: unit) : Lemma (xpow 128 == r_block)
  = let aux (i: nat { i < 128 }) : Lemma (bit (xpow 128) i == bit r_block i)
      = xtimes_bit (xpow 127) i;
        xpow_mono 127 127;
        (if i = 0 then () else xpow_mono 127 (i - 1));
        r_bit i
    in
    FStar.Classical.forall_intro aux;
    bits_inj (xpow 128) r_block

let xpow_high (m: nat { m < 128 }) : Lemma (xpowi (m + 128) == xti r_block m)
  = xpow_128 ();
    xpow_add 128 m

#push-options "--z3rlimit 150 --fuel 1 --ifuel 0"

(** Below [x^128] the reduction is the identity, so the bottom half of the
    product is read off unchanged. *)
let gmul_split_low (x y u: block) (i: nat { i < 128 })
  : Lemma (requires forall (k: nat). k < 128 ==> bit u k == pcoef x y k)
          (ensures xsum (fun k -> pterm2 x y i k) 0 128 == bit u i)
  = let aux (k: int)
      : Lemma (0 <= k /\ k < 128 /\ k <> i ==> pterm2 x y i k == false)
      = if 0 <= k && k < 128 then xpow_mono k i else ()
    in
    FStar.Classical.forall_intro aux;
    xpow_mono i i;
    xsum_one (fun k -> pterm2 x y i k) 0 128 i

(** Above it, the reduction of [x^(128+m)] is [R] advanced [m] times, so the
    top half is accumulated against [R] -- which is a multiplication by [R]. *)
let gmul_split_high (x y v: block) (i: nat { i < 128 })
  : Lemma (requires forall (k: nat). k < 128 ==> bit v k == pcoef x y (128 + k))
          (ensures xsum (fun k -> pterm2 x y i k) 128 128 ==
                   bit (gmul v r_block) i)
  = let aux (m: int)
      : Lemma (0 <= m /\ m < 128 ==>
               pterm2 x y i (m + 128) ==
                 (pget (pbits v) m && bit (xti r_block m) i))
      = if 0 <= m && m < 128 then xpow_high m else ()
    in
    FStar.Classical.forall_intro aux;
    xsum_shift (fun k -> pterm2 x y i k) 128 128 128;
    xsum_ext (fun m -> pterm2 x y i (m + 128))
             (fun m -> pget (pbits v) m && bit (xti r_block m) i) 0 128;
    accum_bit v r_block 128 i;
    pmod_pmul v r_block;
    gmul_is_pmod v r_block

let gmul_split_bit (x y u v: block) (i: nat { i < 128 })
  : Lemma (requires (forall (k: nat). k < 128 ==> bit u k == pcoef x y k) /\
                    (forall (k: nat). k < 128 ==> bit v k == pcoef x y (128 + k)))
          (ensures bit (gmul x y) i == (bit u i <> bit (gmul v r_block) i))
  = gmul_is_pmod x y;
    pmod_bit (pmul (pbits x) (pbits y)) 256 i;
    xsum_ext (fun k -> pget (pmul (pbits x) (pbits y)) k && bit (xpowi k) i)
             (fun k -> pterm2 x y i k) 0 256;
    xsum_split (fun k -> pterm2 x y i k) 0 128 128;
    gmul_split_low x y u i;
    gmul_split_high x y v i

(** {3 The same split over any polynomial at all}

    Nothing in the three lemmas above is about a product: they read the two
    halves of a 256-coefficient polynomial and reduce it.  Stating that
    separately is what lets the implementation drop the one-bit shift, whose
    effect is to hand the reduction a {i different} polynomial -- the product
    multiplied by [x] -- which is no longer of the form [pmul (pbits x)
    (pbits y)] for any pair of blocks.  See [pmod_shift1] in
    [Spec.GF128.Algebra] for what that costs, which is one factor of [x]. *)

let pterm_p (a: poly) (i: nat { i < 128 }) (k: int) : bool =
  pget a k && bit (xpowi k) i

let psplit_low (a: poly) (u: block) (i: nat { i < 128 })
  : Lemma (requires forall (k: nat). k < 128 ==> bit u k == pget a k)
          (ensures xsum (pterm_p a i) 0 128 == bit u i)
  = let aux (k: int)
      : Lemma (0 <= k /\ k < 128 /\ k <> i ==> pterm_p a i k == false)
      = if 0 <= k && k < 128 then xpow_mono k i else ()
    in
    FStar.Classical.forall_intro aux;
    xpow_mono i i;
    xsum_one (pterm_p a i) 0 128 i

let psplit_high (a: poly) (v: block) (i: nat { i < 128 })
  : Lemma (requires forall (k: nat). k < 128 ==> bit v k == pget a (128 + k))
          (ensures xsum (pterm_p a i) 128 128 == bit (gmul v r_block) i)
  = let aux (m: int)
      : Lemma (0 <= m /\ m < 128 ==>
               pterm_p a i (m + 128) ==
                 (pget (pbits v) m && bit (xti r_block m) i))
      = if 0 <= m && m < 128 then xpow_high m else ()
    in
    FStar.Classical.forall_intro aux;
    xsum_shift (pterm_p a i) 128 128 128;
    xsum_ext (fun m -> pterm_p a i (m + 128))
             (fun m -> pget (pbits v) m && bit (xti r_block m) i) 0 128;
    accum_bit v r_block 128 i;
    pmod_pmul v r_block;
    gmul_is_pmod v r_block

let psplit_bit (a: poly) (u v: block) (i: nat { i < 128 })
  : Lemma (requires (forall (k: nat). k < 128 ==> bit u k == pget a k) /\
                    (forall (k: nat). k < 128 ==> bit v k == pget a (128 + k)))
          (ensures bit (pmod a 256) i == (bit u i <> bit (gmul v r_block) i))
  = pmod_bit a 256 i;
    xsum_ext (fun k -> pget a k && bit (xpowi k) i) (pterm_p a i) 0 256;
    xsum_split (pterm_p a i) 0 128 128;
    psplit_low a u i;
    psplit_high a v i

let psplit (a: poly) (u v: block)
  : Lemma (requires (forall (k: nat). k < 128 ==> bit u k == pget a k) /\
                    (forall (k: nat). k < 128 ==> bit v k == pget a (128 + k)))
          (ensures pmod a 256 == gadd u (gmul v r_block))
  = let aux (i: nat { i < 128 })
      : Lemma (bit (pmod a 256) i == bit (gadd u (gmul v r_block)) i)
      = psplit_bit a u v i;
        gadd_bit u (gmul v r_block) i
    in
    FStar.Classical.forall_intro aux;
    bits_inj (pmod a 256) (gadd u (gmul v r_block))

(** The whole of the reduction step, as an implementation can use it: given
    the two halves of the carry-less product, the field product is the low
    half exclusive-ored with the high half times the reduction constant. *)
let gmul_split (x y u v: block)
  : Lemma (requires (forall (k: nat). k < 128 ==> bit u k == pcoef x y k) /\
                    (forall (k: nat). k < 128 ==> bit v k == pcoef x y (128 + k)))
          (ensures gmul x y == gadd u (gmul v r_block))
  = gmul_is_pmod x y;
    psplit (pmul (pbits x) (pbits y)) u v

(** The product of two blocks has degree at most 254, so its coefficient at
    255 -- the one the shift below would push out of range -- is zero. *)
let pcoef_top (x y: block) : Lemma (pcoef x y 255 == false)
  = pmul_get (pbits x) (pbits y) 255;
    conv_def (pbits x) (pbits y) 255 (fun _ -> false);
    xsum_zero (fun (_: int) -> false) 0 128

#pop-options

(** {2 The recursion closes after three steps}

    [gmul_split] turns one field multiplication into a low half plus another
    field multiplication, by the reduction constant.  That constant has
    degree seven, so the high half shrinks fast: after one step by [R] the
    remainder has degree at most six, and after a second it is gone
    altogether.  Three applications of the same routine therefore compute the
    whole product, with no separate reduction step to write or to verify. *)

let small_deg (a: block) = forall (k: nat). 6 < k /\ k < 128 ==> bit a k == false

(** The high half of anything times [R] has degree at most six. *)
let mul_r_high (a: block) (k: nat { 6 < k /\ k < 128 })
  : Lemma (pcoef a r_block (128 + k) == false)
  = let f : int -> bool =
      fun i -> pget (pbits a) i && pget (pbits r_block) (128 + k - i) in
    let aux (i: int) : Lemma (0 <= i /\ i < 128 ==> f i == false)
      = if 0 <= i && i < 128 && 128 + k - i < 128 then r_bit (128 + k - i)
        else ()
    in
    FStar.Classical.forall_intro aux;
    pmul_get (pbits a) (pbits r_block) (128 + k);
    conv_def (pbits a) (pbits r_block) (128 + k) f;
    xsum_ext f (fun _ -> false) 0 128;
    xsum_zero (fun _ -> false) 0 128

(** And the high half of a degree-six thing times [R] is nothing at all. *)
let mul_r_zero (a: block) (k: nat { k < 128 })
  : Lemma (requires small_deg a) (ensures pcoef a r_block (128 + k) == false)
  = let f : int -> bool =
      fun i -> pget (pbits a) i && pget (pbits r_block) (128 + k - i) in
    let aux (i: int) : Lemma (0 <= i /\ i < 128 ==> f i == false)
      = if 0 <= i && i < 128 && i > 6 && 128 + k - i < 128 then
          r_bit (128 + k - i)
        else ()
    in
    FStar.Classical.forall_intro aux;
    pmul_get (pbits a) (pbits r_block) (128 + k);
    conv_def (pbits a) (pbits r_block) (128 + k) f;
    xsum_ext f (fun _ -> false) 0 128;
    xsum_zero (fun _ -> false) 0 128

let zero_pmul (y: block) (k: int)
  : Lemma (pget (pmul (pbits zero) (pbits y)) k == false)
  = pmul_get (pbits zero) (pbits y) k;
    conv_def (pbits zero) (pbits y) k
      (fun j -> pget (pbits zero) j && pget (pbits y) (k - j));
    xsum_ext (fun j -> pget (pbits zero) j && pget (pbits y) (k - j))
             (fun _ -> false) 0 128;
    xsum_zero (fun _ -> false) 0 128

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let gmul_zero_bit (y: block) (i: nat { i < 128 })
  : Lemma (bit (gmul zero y) i == false)
  = FStar.Classical.forall_intro (zero_pmul y);
    gmul_is_pmod zero y;
    pmod_bit (pmul (pbits zero) (pbits y)) 256 i;
    xsum_ext (fun k -> pget (pmul (pbits zero) (pbits y)) k && bit (xpowi k) i)
             (fun _ -> false) 0 256;
    xsum_zero (fun _ -> false) 0 256

#pop-options

let gmul_zero (y: block) : Lemma (gmul zero y == zero)
  = FStar.Classical.forall_intro (gmul_zero_bit y);
    FStar.Classical.forall_intro zero_bit;
    bits_inj (gmul zero y) zero

let gadd_zero (a: block) : Lemma (gadd a zero == a)
  = FStar.Classical.forall_intro (gadd_bit a zero);
    bits_inj (gadd a zero) a

(** The same as [halves] below, but for the two halves of an arbitrary
    256-coefficient polynomial rather than of a product.  A multiplier that
    omits the customary one-bit shift produces the halves of the product
    {i shifted}, which is no longer a product of two blocks, so the reduction
    has to be stated at this generality to apply to it. *)
let halvesp (a: poly) (u v: block) =
  (forall (k: nat). k < 128 ==> bit u k == pget a k) /\
  (forall (k: nat). k < 128 ==> bit v k == pget a (128 + k))

let halves (x y u v: block) =
  (forall (k: nat). k < 128 ==> bit u k == pcoef x y k) /\
  (forall (k: nat). k < 128 ==> bit v k == pcoef x y (128 + k))

#push-options "--z3rlimit 200"

(** The reduction on its own: a product by [r_block] twice terminates,
    because [r_block] has degree seven, so the high half of [v1 * R] has
    degree at most six and {i its} high half is empty.

    This is stated separately from [gmul_three] below because it does not
    mention the operands at all --- it is a fact about one register and the
    reduction constant.  That is what lets several products be accumulated
    before anything is reduced: the sum of the high halves is reduced once
    rather than each high half separately.  See
    [Spec.GF128.Algebra.gmul_defer4]. *)
let mul_r_two (v1 u2 v2 u3 v3: block)
  : Lemma (requires halves v1 r_block u2 v2 /\ halves v2 r_block u3 v3)
          (ensures gmul v1 r_block == gadd u2 u3)
  = gmul_split v1 r_block u2 v2;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (mul_r_high v1));
    assert (small_deg v2);
    FStar.Classical.forall_intro
      (FStar.Classical.move_requires (mul_r_zero v2));
    FStar.Classical.forall_intro zero_bit;
    bits_inj v3 zero;
    gmul_split v2 r_block u3 v3;
    gmul_zero r_block;
    gadd_zero u3

(** The reduction of an arbitrary 256-coefficient polynomial, in the shape
    the implementation has it: its two halves plus the two rounds of
    multiplication by [R] that bring the high half down. *)
let pmod_three (a: poly) (u1 v1 u2 v2 u3 v3: block)
  : Lemma (requires halvesp a u1 v1 /\ halves v1 r_block u2 v2 /\
                    halves v2 r_block u3 v3)
          (ensures pmod a 256 == gadd u1 (gadd u2 u3))
  = psplit a u1 v1;
    mul_r_two v1 u2 v2 u3 v3

(** The whole multiplication, in the shape the implementation has it: three
    carry-less products, six registers, and the answer is the exclusive-or of
    the three low halves. *)
let gmul_three (x y u1 v1 u2 v2 u3 v3: block)
  : Lemma (requires halves x y u1 v1 /\ halves v1 r_block u2 v2 /\
                    halves v2 r_block u3 v3)
          (ensures gmul x y == gadd u1 (gadd u2 u3))
  = gmul_split x y u1 v1;
    mul_r_two v1 u2 v2 u3 v3

#pop-options

(** {2 Multiplying by the reduction constant is a shift}

    [gmul_three] above uses the general product three times, which is a fine
    way to state the reduction and an expensive way to compute it: the second
    and third products have [r_block] as an operand, and [r_block] is
    [x^7 + x^2 + x + 1] -- four set bits.  A product with it is therefore not
    a product at all but four copies of the other operand, shifted by nought,
    one, two and seven, added together.  That is what this section says, and
    it is what lets [Hacl.AES.GF128.NI] do two thirds of a GHASH multiply
    with shifts instead of with [PCLMULQDQ]. *)

(** A bit of a block at any index at all, [false] outside it, in the style of
    [Spec.CLMUL.lebiti]: it is what makes the statement below uniform in [k]
    rather than a list of boundary cases. *)
let bitk (a: block) (j: int) : bool = 0 <= j && j < 128 && bit a j

(** A sum over the range with at most one nonzero term. *)
let xsum_at (a: block) (j: int)
  : Lemma (xsum (fun i -> i = j && bitk a i) 0 128 == bitk a j)
  = if 0 <= j && j < 128
    then xsum_one (fun i -> i = j && bitk a i) 0 128 j
    else xsum_zero (fun i -> i = j && bitk a i) 0 128

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The coefficient of [x^k] in [a * R]: four bits of [a], and no summation
    left to do.  Compare [mul_r_high] and [mul_r_zero] above, which are the
    two special cases of this that [gmul_three] happened to need. *)
let mul_r_coef (a: block) (k: int)
  : Lemma (pcoef a r_block k ==
           (((bitk a k <> bitk a (k - 1)) <> bitk a (k - 2)) <> bitk a (k - 7)))
  = FStar.Classical.forall_intro r_bit;
    let g0 : int -> bool = fun i -> i = k && bitk a i in
    let g1 : int -> bool = fun i -> i = k - 1 && bitk a i in
    let g2 : int -> bool = fun i -> i = k - 2 && bitk a i in
    let g7 : int -> bool = fun i -> i = k - 7 && bitk a i in
    let g01 : int -> bool = fun i -> g0 i <> g1 i in
    let g012 : int -> bool = fun i -> g01 i <> g2 i in
    let f : int -> bool = fun i -> g012 i <> g7 i in
    pmul_get (pbits a) (pbits r_block) k;
    conv_def (pbits a) (pbits r_block) k f;
    xsum_xor g012 g7 0 128;
    xsum_xor g01 g2 0 128;
    xsum_xor g0 g1 0 128;
    xsum_at a k;
    xsum_at a (k - 1);
    xsum_at a (k - 2);
    xsum_at a (k - 7)

#pop-options
