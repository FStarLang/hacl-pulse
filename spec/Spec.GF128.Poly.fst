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
    which is the same sum with [xpow] carrying the shift. *)

#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"

let rec xt_bit (y: block) (j: nat) (i: nat { i < 128 })
  : Lemma (ensures bit (xt y j) i ==
             xsum (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128)
          (decreases j)
  = if j = 0
    then begin
      let aux (m: int)
        : Lemma (0 <= m /\ m < 128 /\ m <> i ==>
                 (pget (pbits y) m && bit (xpowi (m + j)) i) == false)
        = if 0 <= m && m < 128 then xpow_mono m i else ()
      in
      FStar.Classical.forall_intro aux;
      xpow_mono i i;
      xsum_one (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i) 0 128 i
    end
    else if i = 0
    then begin
      let e (m: int)
        : Lemma (m + j >= 1 ==>
                 bit (xpowi (m + j)) 0 == bit (xpowi (m + j - 1)) 127)
        = if m + j >= 1 then xtimes_bit (xpow (m + j - 1)) 0 else ()
      in
      FStar.Classical.forall_intro e;
      xtimes_bit (xt y (j - 1)) 0;
      xt_bit y (j - 1) 127;
      xsum_ext (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i)
               (fun m -> pget (pbits y) m && bit (xpowi (m + j - 1)) 127) 0 128
    end
    else begin
      let rb = (i = 1 || i = 2 || i = 7) in
      let e (m: int)
        : Lemma (m + j >= 1 ==>
                 bit (xpowi (m + j)) i ==
                   (bit (xpowi (m + j - 1)) (i - 1) <>
                    (bit (xpowi (m + j - 1)) 127 && rb)))
        = if m + j >= 1 then xtimes_bit (xpow (m + j - 1)) i else ()
      in
      FStar.Classical.forall_intro e;
      xtimes_bit (xt y (j - 1)) i;
      xt_bit y (j - 1) 127;
      xt_bit y (j - 1) (i - 1);
      xsum_ext (fun m -> pget (pbits y) m && bit (xpowi (m + j)) i)
               (fun m -> (pget (pbits y) m && bit (xpowi (m + j - 1)) (i - 1)) <>
                         (rb && (pget (pbits y) m && bit (xpowi (m + j - 1)) 127)))
               0 128;
      xsum_xor (fun m -> pget (pbits y) m && bit (xpowi (m + j - 1)) (i - 1))
               (fun m -> rb && (pget (pbits y) m && bit (xpowi (m + j - 1)) 127))
               0 128;
      xsum_and rb (fun m -> pget (pbits y) m && bit (xpowi (m + j - 1)) 127) 0 128
    end

#pop-options

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

#push-options "--z3rlimit 200"

let pmod_shift (y: block) (j: nat { j <= 128 })
  : Lemma (pmod (pshift (pbits y) j) 256 == xt y j)
  = let b = pbits y in
    let aux (i: nat { i < 128 })
      : Lemma (bit (pmod (pshift b j) 256) i == bit (xt y j) i)
      = let f : int -> bool = fun k -> pget b (k - j) && bit (xpowi k) i in
        let g : int -> bool = fun m -> pget b m && bit (xpowi (m + j)) i in
        pmod_bit (pshift b j) 256 i;
        xsum_ext (fun k -> pget (pshift b j) k && bit (xpowi k) i) f 0 256;
        xsum_shift f 0 256 j;
        xsum_ext (fun m -> f (m + j)) g (0 - j) 256;
        xsum_trim_lo g (0 - j) j 256;
        xsum_trim_hi g 0 128 (256 - j);
        xt_bit y j i
    in
    FStar.Classical.forall_intro aux;
    bits_inj (pmod (pshift b j) 256) (xt y j)

#pop-options

(** {2 Reduction of a product}

    Exchanging the two sums turns "reduce the product" into "for each bit of
    [x], reduce [y] shifted", which is exactly what the loop accumulates. *)

#push-options "--z3rlimit 400"

let pmod_pmul (x y: block)
  : Lemma (pmod (pmul (pbits x) (pbits y)) 256 == accum x y 128)
  = let a = pbits x in
    let b = pbits y in
    let aux (i: nat { i < 128 })
      : Lemma (bit (pmod (pmul a b) 256) i == bit (accum x y 128) i)
      = let h : int -> int -> bool =
          fun j k -> pget a j && (pget b (k - j) && bit (xpowi k) i) in
        pmod_bit (pmul a b) 256 i;
        FStar.Classical.forall_intro_2 (pmul_get a);
        let inner (k: int)
          : Lemma (pget (pmul a b) k && bit (xpowi k) i == xsum (fun j -> h j k) 0 128)
          = xsum_and (bit (xpowi k) i) (fun j -> pget a j && pget b (k - j)) 0 128;
            xsum_ext (fun j -> bit (xpowi k) i && (pget a j && pget b (k - j)))
                     (fun j -> h j k) 0 128
        in
        FStar.Classical.forall_intro inner;
        xsum_ext (fun k -> pget (pmul a b) k && bit (xpowi k) i)
                 (fun k -> xsum (fun j -> h j k) 0 128) 0 256;
        xsum_swap h 0 128 0 256;
        let outer (j: int)
          : Lemma (xsum (fun k -> h j k) 0 256 == (pget a j && bit (xti y j) i))
          = xsum_and (pget a j) (fun k -> pget b (k - j) && bit (xpowi k) i) 0 256;
            if 0 <= j && j < 128
            then begin
              pmod_bit (pshift b j) 256 i;
              xsum_ext (fun k -> pget (pshift b j) k && bit (xpowi k) i)
                       (fun k -> pget b (k - j) && bit (xpowi k) i) 0 256;
              pmod_shift y j
            end
            else ()
        in
        FStar.Classical.forall_intro outer;
        xsum_ext (fun j -> xsum (fun k -> h j k) 0 256)
                 (fun j -> pget a j && bit (xti y j) i) 0 128;
        accum_bit x y 128 i
    in
    FStar.Classical.forall_intro aux;
    bits_inj (pmod (pmul a b) 256) (accum x y 128)

#pop-options

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
