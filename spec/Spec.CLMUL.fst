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

(** Bit [k] of the block read as a 128-bit little-endian integer.

    Opaque, because this is the only place a division and a [pow2] appear:
    three lemmas below need the definition and every other proof in the
    library is far better off without it. *)
[@@"opaque_to_smt"]
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
  = reveal_opaque (`%lebit) lebit;
    let q = k / 8 in
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

let lezero (k: nat { k < 128 }) : Lemma (lebit Spec.GF128.zero k == false)
  = reveal_opaque (`%lebit) lebit

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
  = reveal_opaque (`%lebit) lebit;
    let q = k / 8 in
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

(** {2 The implementation, at the level of registers}

    Everything below is a statement about eight 128-bit values and nothing
    else, so the Pulse code that computes them has only to name its registers
    and to quote the instruction axioms.  The three stages are: four
    multiplies assembled into a 256-bit product; a one-bit left shift of that
    pair; and the byte reversal that turns it back into GCM's numbering. *)

(** Coefficient [m] of the product the multiplier actually computes. *)
let pprod (x y: block) (m: int) : bool =
  conv (lepoly (bswap x)) (lepoly (bswap y)) m

let is_lo (x y a: block) =
  forall (m: int). 0 <= m /\ m < 128 ==> lebiti a m == pprod x y m

let is_hi (x y a: block) =
  forall (m: int). 0 <= m /\ m < 128 ==> lebiti a m == pprod x y (m + 128)

let is_qlo (x y a: block) =
  forall (m: int). 0 <= m /\ m < 128 ==> lebiti a m == pprod x y (m - 1)

let is_qhi (x y a: block) =
  forall (m: int). 0 <= m /\ m < 128 ==> lebiti a m == pprod x y (m + 127)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 1"

(** {3 Stage one: four multiplies}

    [mid] is the two crossed products added; it contributes to the low
    register shifted up eight bytes and to the high register shifted down. *)

let lo_of_lanes (x y ll mid lo: block)
  : Lemma (requires
      (forall (k: int). lebiti ll k ==
         conv (lane (bswap x) false) (lane (bswap y) false) k) /\
      (forall (k: int). lebiti mid k ==
         (conv (lane (bswap x) false) (lane (bswap y) true) k <>
          conv (lane (bswap x) true) (lane (bswap y) false) k)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti lo k == (lebiti ll k <> lebiti mid (k - 64))))
    (ensures is_lo x y lo)
  = let aux (m: int) : Lemma (0 <= m /\ m < 128 ==> lebiti lo m == pprod x y m)
      = if 0 <= m && m < 128 then begin
          conv_lanes (bswap x) (bswap y) m;
          conv_zero_lo (lane (bswap x) true) (lane (bswap y) true) (m - 128)
        end else ()
    in
    FStar.Classical.forall_intro aux

let hi_of_lanes (x y hh mid hi: block)
  : Lemma (requires
      (forall (k: int). lebiti hh k ==
         conv (lane (bswap x) true) (lane (bswap y) true) k) /\
      (forall (k: int). lebiti mid k ==
         (conv (lane (bswap x) false) (lane (bswap y) true) k <>
          conv (lane (bswap x) true) (lane (bswap y) false) k)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti hi k == (lebiti hh k <> lebiti mid (k + 64))))
    (ensures is_hi x y hi)
  = let aux (m: int)
      : Lemma (0 <= m /\ m < 128 ==> lebiti hi m == pprod x y (m + 128))
      = if 0 <= m && m < 128 then begin
          conv_lanes (bswap x) (bswap y) (m + 128);
          conv_zero_hi (lane (bswap x) false) (lane (bswap y) false) (m + 128)
        end else ()
    in
    FStar.Classical.forall_intro aux

(** {3 Stage two: the one-bit left shift}

    The multiplier's result is one place short of the reversal GCM wants --
    this is the [>> 1] of [Spec.CarryLess.conv_rev] -- so the 256-bit pair is
    shifted up by one.  The hardware shifts 64-bit lanes, so each register
    needs the bit that falls out of its low lane carried into its high lane,
    and the low register needs its top bit carried into the high one. *)

(** The shift is pure index arithmetic, so it is proved about bit functions
    rather than about registers: nothing here needs to know that [flo] came
    out of a multiplier.  Keeping the polynomials out of these two queries is
    the difference between seconds and hours. *)
let bounded (f: int -> bool) = forall (k: int). (k < 0 \/ 128 <= k) ==> f k == false

#push-options "--fuel 0 --ifuel 0"

(** The whole of the case analysis, with no quantifier anywhere: it is
    handing the solver the four instantiations that matters, not the
    arithmetic, which is why these two are instant and the same reasoning
    inside a quantified context is not. *)

let step_lo (p flo fc fq: int -> bool) (m: nat { m < 128 })
  : Lemma (requires
      fq m == ((m % 64 >= 1 && flo (m - 1)) <> fc (m - 64)) /\
      (m < 64 ==> (m % 64 == m /\ fc (m - 64) == false)) /\
      (64 <= m ==> (m % 64 == m - 64 /\
                    fc (m - 64) == (m - 64 < 1 && flo (m - 1)))) /\
      (1 <= m ==> flo (m - 1) == p (m - 1)) /\ p (-1) == false)
    (ensures fq m == p (m - 1)) = ()

let step_hi (p flo fhi fc fd fq: int -> bool) (m: nat { m < 128 })
  : Lemma (requires
      fq m == (((m % 64 >= 1 && fhi (m - 1)) <> fd (m - 64)) <> fc (m + 64)) /\
      (m < 64 ==> (m % 64 == m /\ fd (m - 64) == false /\
                   fc (m + 64) == (m < 1 && flo (m + 127)))) /\
      (64 <= m ==> (m % 64 == m - 64 /\ fc (m + 64) == false /\
                    fd (m - 64) == (m - 64 < 1 && fhi (m - 1)))) /\
      (1 <= m ==> fhi (m - 1) == p (m + 127)) /\ flo 127 == p 127)
    (ensures fq m == p (m + 127)) = ()

#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"

let shift_lo_gen (p flo fc fq: int -> bool)
  : Lemma (requires
      bounded fc /\ p (-1) == false /\
      (forall (m: int). 0 <= m /\ m < 128 ==> flo m == p m) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fc k == (k % 64 + 63 < 64 && flo (k + 63))) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fq k == ((k % 64 >= 1 && flo (k - 1)) <> fc (k - 64))))
    (ensures forall (m: int). 0 <= m /\ m < 128 ==> fq m == p (m - 1))
  = let aux (m: int) : Lemma (0 <= m /\ m < 128 ==> fq m == p (m - 1))
      = if 0 <= m && m < 128 then begin
          assert (fq m == ((m % 64 >= 1 && flo (m - 1)) <> fc (m - 64)));
          assert (1 <= m ==> flo (m - 1) == p (m - 1));
          if m < 64 then begin
            Math.small_mod m 64;
            assert (fc (m - 64) == false)
          end else begin
            Math.small_mod (m - 64) 64;
            Math.lemma_mod_plus (m - 64) 1 64;
            assert (fc (m - 64) == (m - 64 < 1 && flo (m - 1)))
          end;
          step_lo p flo fc fq m
        end else ()
    in
    FStar.Classical.forall_intro aux

let shift_hi_gen (p flo fhi fc fd fq: int -> bool)
  : Lemma (requires
      bounded fc /\ bounded fd /\
      (forall (m: int). 0 <= m /\ m < 128 ==> flo m == p m) /\
      (forall (m: int). 0 <= m /\ m < 128 ==> fhi m == p (m + 128)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fc k == (k % 64 + 63 < 64 && flo (k + 63))) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fd k == (k % 64 + 63 < 64 && fhi (k + 63))) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fq k == (((k % 64 >= 1 && fhi (k - 1)) <> fd (k - 64)) <> fc (k + 64))))
    (ensures forall (m: int). 0 <= m /\ m < 128 ==> fq m == p (m + 127))
  = let aux (m: int) : Lemma (0 <= m /\ m < 128 ==> fq m == p (m + 127))
      = if 0 <= m && m < 128 then begin
          assert (fq m ==
            (((m % 64 >= 1 && fhi (m - 1)) <> fd (m - 64)) <> fc (m + 64)));
          assert (1 <= m ==> fhi (m - 1) == p (m + 127));
          assert (flo 127 == p 127);
          if m < 64 then begin
            Math.small_mod m 64;
            Math.lemma_mod_plus m 1 64;
            assert (fd (m - 64) == false);
            assert (fc (m + 64) == (m < 1 && flo (m + 127)))
          end else begin
            Math.small_mod (m - 64) 64;
            Math.lemma_mod_plus (m - 64) 1 64;
            assert (fc (m + 64) == false);
            assert (fd (m - 64) == (m - 64 < 1 && fhi (m - 1)))
          end;
          step_hi p flo fhi fc fd fq m
        end else ()
    in
    FStar.Classical.forall_intro aux

#pop-options

let shift_lo (x y lo c qlo: block)
  : Lemma (requires is_lo x y lo /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti c k == (k % 64 + 63 < 64 && lebiti lo (k + 63))) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti qlo k == ((k % 64 >= 1 && lebiti lo (k - 1)) <> lebiti c (k - 64))))
    (ensures is_qlo x y qlo)
  = conv_zero_lo (lepoly (bswap x)) (lepoly (bswap y)) (-1);
    shift_lo_gen (pprod x y) (lebiti lo) (lebiti c) (lebiti qlo)

let shift_hi (x y lo hi c d qhi: block)
  : Lemma (requires is_lo x y lo /\ is_hi x y hi /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti c k == (k % 64 + 63 < 64 && lebiti lo (k + 63))) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti d k == (k % 64 + 63 < 64 && lebiti hi (k + 63))) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti qhi k ==
           (((k % 64 >= 1 && lebiti hi (k - 1)) <> lebiti d (k - 64)) <>
            lebiti c (k + 64))))
    (ensures is_qhi x y qhi)
  = shift_hi_gen (pprod x y) (lebiti lo) (lebiti hi) (lebiti c) (lebiti d)
                 (lebiti qhi)

(** {3 Stage three: back to GCM's numbering}

    Reversing the bytes of the shifted pair, high register first, gives
    exactly the two halves [Spec.GF128.Poly.gmul_three] asks for. *)

let clmul_halves (x y qlo qhi: block)
  : Lemma (requires is_qlo x y qlo /\ is_qhi x y qhi)
          (ensures Poly.halves x y (bswap qhi) (bswap qlo))
  = let aux (k: nat { k < 128 })
      : Lemma (bit (bswap qhi) k == Poly.pcoef x y k /\
               bit (bswap qlo) k == Poly.pcoef x y (128 + k))
      = bswap_bit qhi k;
        bswap_bit qlo k;
        bswap_conv x y (254 - k);
        bswap_conv x y (126 - k)
    in
    FStar.Classical.forall_intro aux

#pop-options
