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

(** The little-endian bit view of a 128-bit register, and the four-way split
    that [PCLMULQDQ] imposes.

    {2 Two ways to number 128 bits}

    GCM numbers the bits of a block from the top of byte zero downwards:
    [Spec.GF128.bit a 0] is the high bit of [a.[0]].  A little-endian machine
    numbers the bits of a 128-bit integer from the low bit of byte zero
    upwards: that is [lebit] below.  The two orders are exact reverses of each
    other {i once the bytes have been reversed}, which is [bswap_lebit]: for
    every [k],

    {[
      lebit (bswap a) k == Spec.GF128.bit a (127 - k)
    ]}

    and that single fact is the reason every GHASH implementation on this
    hardware byte-reverses its operands on the way in.  Combined with
    [Spec.CarryLess.conv_rev] it turns the carry-less multiplier, which reads
    its operands little-endian, into a multiplier for GCM's polynomials.

    {2 Four multiplies}

    [PCLMULQDQ] multiplies one 64-bit lane by one 64-bit lane.  A 128x128
    product therefore takes four of them, and [conv_lanes] is the statement
    that assembling the four at offsets [0], [64], [64] and [128] gives the
    product: it is [Spec.CarryLess]'s bilinearity of [conv] applied twice on
    each side and nothing more. *)
module Spec.CLMUL

open Spec.Byte
open Spec.CarryLess
open Spec.GF128

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Poly = Spec.GF128.Poly

(** {2 The little-endian bit view} *)

(** Bit [k] of the block read as a 128-bit little-endian integer. *)
let lebit (a: block) (k: nat { k < 128 }) : bool =
  (Seq.index a (k / 8) / pow2 (k % 8)) % 2 = 1

(** The same at any index at all, which is what the instruction axioms are
    stated with: a shift then needs no side condition, because the bits that
    move in from outside are [false] by definition. *)
let lebiti (a: block) (k: int) : bool = 0 <= k && k < 128 && lebit a k

let lepoly (a: block) : poly = Seq.init 128 (fun k -> lebit a k)

let lepoly_geti (a: block) (k: int) : Lemma (pget (lepoly a) k == lebiti a k) = ()

let lepoly_get (a: block) (k: int)
  : Lemma (pget (lepoly a) k == (0 <= k && k < 128 && lebit a k)) = ()

let lepoly_len (a: block) : Lemma (Seq.length (lepoly a) == 128) = ()

(** The two numberings differ by reversing the bits within each byte, so
    every fact about [Spec.GF128.bit] transfers. *)
let lebit_is_bit (a: block) (k: nat { k < 128 })
  : Lemma (lebit a k == bit a (8 * (k / 8) + 7 - k % 8))
  = let q = k / 8 in
    let r = k % 8 in
    Math.lemma_div_plus (7 - r) q 8;
    Math.lemma_mod_plus (7 - r) q 8;
    Math.small_division_lemma_1 (7 - r) 8;
    Math.small_mod (7 - r) 8;
    Poly.nth_div_mod #8 (Seq.index a q) (7 - r)

let lexor (a b: block) (k: nat { k < 128 })
  : Lemma (lebit (gadd a b) k == (lebit a k <> lebit b k))
  = lebit_is_bit (gadd a b) k;
    lebit_is_bit a k;
    lebit_is_bit b k;
    Poly.gadd_bit a b (8 * (k / 8) + 7 - k % 8)

let lezero (k: nat { k < 128 }) : Lemma (lebit Spec.GF128.zero k == false) = ()

let lexori (a b: block) (k: int)
  : Lemma (lebiti (gadd a b) k == (lebiti a k <> lebiti b k))
  = if 0 <= k && k < 128 then lexor a b k else ()

(** [Spec.AES.xor_block] and [Spec.GF128.gadd] are the same function under two
    names; the AES side is what [Hacl.Vec128.vxor] is stated with. *)
let xor_is_gadd (a b: block)
  : Lemma (Spec.AES.xor_block a b == gadd a b)
  = Seq.lemma_eq_intro (Spec.AES.xor_block a b) (gadd a b)

(** Blocks with the same little-endian bits are the same block. *)
let lebits_inj (a b: block)
  : Lemma (requires forall (k: nat). k < 128 ==> lebit a k == lebit b k)
          (ensures a == b)
  = let aux (i: nat { i < 128 }) : Lemma (bit a i == bit b i)
      = Math.lemma_div_plus (7 - i % 8) (i / 8) 8;
        Math.lemma_mod_plus (7 - i % 8) (i / 8) 8;
        Math.small_division_lemma_1 (7 - i % 8) 8;
        Math.small_mod (7 - i % 8) 8;
        lebit_is_bit a (8 * (i / 8) + 7 - i % 8);
        lebit_is_bit b (8 * (i / 8) + 7 - i % 8)
    in
    FStar.Classical.forall_intro aux;
    Poly.bits_inj a b

(** {2 Byte reversal} *)

let bswap (a: block) : block =
  Seq.init blocklen (fun j -> Seq.index a (blocklen - 1 - j))

(** The whole point: reversing the bytes reverses the bit numbering. *)
let bswap_lebit (a: block) (k: nat { k < 128 })
  : Lemma (lebit (bswap a) k == bit a (127 - k))
  = let q = k / 8 in
    let r = k % 8 in
    Math.lemma_div_mod k 8;
    Math.small_division_lemma_1 (7 - r) 8;
    Math.small_mod (7 - r) 8;
    Math.lemma_div_plus (7 - r) (15 - q) 8;
    Math.lemma_mod_plus (7 - r) (15 - q) 8;
    assert (127 - k == (7 - r) + 8 * (15 - q))

let bswap_lepoly (a: block)
  : Lemma (peq (lepoly (bswap a)) (prev (Poly.pbits a) 128))
  = FStar.Classical.forall_intro (bswap_lebit a)

(** {2 The two lanes} *)

let lane (a: block) (hi: bool) : poly =
  Seq.init 64 (fun k -> lebit a (if hi then 64 + k else k))

let lane_get (a: block) (hi: bool) (k: int)
  : Lemma (pget (lane a hi) k ==
           (0 <= k && k < 64 && lebit a (if hi then 64 + k else k))) = ()

(** A register is its low lane plus its high lane shifted up by 64. *)
let lepoly_split (a: block)
  : Lemma (peq (lepoly a) (padd (lane a false) (pshift (lane a true) 64)))
  = ()

#push-options "--z3rlimit 200"

(** {2 The four-way product}

    This is exactly the shape of the code: four [clmul]s, the two middle ones
    added together and shifted up by eight bytes. *)
let conv_lanes (a b: block) (k: int)
  : Lemma (conv (lepoly a) (lepoly b) k ==
             (((conv (lane a false) (lane b false) k <>
                conv (lane a false) (lane b true) (k - 64)) <>
               (conv (lane a true) (lane b false) (k - 64) <>
                conv (lane a true) (lane b true) (k - 128)))))
  = let al = lane a false in
    let ah = pshift (lane a true) 64 in
    let bl = lane b false in
    let bh = pshift (lane b true) 64 in
    lepoly_split a;
    lepoly_split b;
    conv_peq (lepoly a) (padd al ah) (lepoly b) (padd bl bh) k 128;
    conv_add_left al ah (padd bl bh) k 128;
    conv_add_right al bl bh k;
    conv_add_right ah bl bh k;
    conv_shift_right al (lane b true) 64 k;
    conv_shift_left (lane a true) bl 64 k;
    conv_shift_left (lane a true) bh 64 k;
    conv_shift_right (lane a true) (lane b true) 64 (k - 64)

#pop-options

(** {2 The product, as the registers hold it}

    Byte reversal is its own inverse, so a block can be recovered from its
    reversed form; and the reversed operands' convolution is the true
    product read backwards from [254].  Together these say what the four
    [clmul]s compute in terms of the polynomials GCM cares about. *)

let bswap_involutive (a: block) : Lemma (bswap (bswap a) == a)
  = Seq.lemma_eq_intro (bswap (bswap a)) a

(** The mirror of [bswap_lebit]: the GCM bits of a reversed block are the
    little-endian bits of the original, backwards. *)
let bswap_bit (a: block) (j: nat { j < 128 })
  : Lemma (bit (bswap a) j == lebit a (127 - j))
  = bswap_lebit (bswap a) (127 - j);
    bswap_involutive a

#push-options "--z3rlimit 100"

(** What a 128x128 carry-less multiplier on the byte-reversed operands
    computes: coefficient [m] of it is coefficient [254 - m] of the product
    of the two GCM polynomials.  The one-off is Gueron's [>> 1]. *)
let bswap_conv (x y: block) (m: int)
  : Lemma (conv (lepoly (bswap x)) (lepoly (bswap y)) m ==
           pget (pmul (Poly.pbits x) (Poly.pbits y)) (254 - m))
  = bswap_lepoly x;
    bswap_lepoly y;
    conv_peq (lepoly (bswap x)) (prev (Poly.pbits x) 128)
             (lepoly (bswap y)) (prev (Poly.pbits y) 128) m 128;
    conv_rev (Poly.pbits x) (Poly.pbits y) m;
    pmul_get (Poly.pbits x) (Poly.pbits y) (254 - m)

#pop-options
