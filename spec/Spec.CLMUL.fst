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
module Alg = Spec.GF128.Algebra

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

(** Byte reversal is a permutation of the bytes and addition is bytewise, so
    the two commute.  This is what lets several carry-less products be
    accumulated in the multiplier's bit order and reversed once, which is
    the point of [Hacl.AES.GF128.NI.gmul4_vec]. *)
let bswap_gadd (a b: block)
  : Lemma (bswap (gadd a b) == gadd (bswap a) (bswap b))
  = Seq.lemma_eq_intro (bswap (gadd a b)) (gadd (bswap a) (bswap b))

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

(** {3 The same without the shift}

    The one-bit shift exists only to cancel the one-off in [bswap_conv].  If
    it is omitted the unshifted pair reverses to the two halves of the
    product polynomial {i shifted up by one place}, which is a polynomial of
    256 coefficients like any other but not the product of two blocks --
    hence [Poly.halvesp] rather than [Poly.halves]. *)

(** The product polynomial of two blocks, shifted up one place: what a
    multiplier without the shift leaves in its two registers. *)
let pshift1 (x y: block) : poly =
  pshift (pmul (Poly.pbits x) (Poly.pbits y)) 1

let clmul_halves_ns (x y lo hi: block)
  : Lemma (requires is_lo x y lo /\ is_hi x y hi)
          (ensures Poly.halvesp (pshift1 x y) (bswap hi) (bswap lo))
  = let pp = pmul (Poly.pbits x) (Poly.pbits y) in
    let aux (k: nat { k < 128 })
      : Lemma (bit (bswap hi) k == pget (pshift pp 1) k /\
               bit (bswap lo) k == pget (pshift pp 1) (128 + k))
      = bswap_bit hi k;
        bswap_bit lo k;
        bswap_conv x y (255 - k);
        bswap_conv x y (127 - k);
        pshift_get pp 1 k;
        pshift_get pp 1 (128 + k)
    in
    FStar.Classical.forall_intro aux

(** And so a multiplier without the shift computes [x] times the field
    product: the three low halves added together are [xtimes (gmul x y)].
    Pre-dividing one operand by [x] -- which costs one shift, once, at key
    setup -- therefore recovers the product exactly. *)

(** The bridge: the reduction of the shifted product is the field product of
    [x] with [y] advanced once.  Both halves of the identity are needed --
    [Spec.GF128.Algebra.pmod_shift1] to get [x] times the product, and
    [Spec.GF128.Algebra.gmul_xt_right] to move that [x] into the operand,
    where a key pre-divided once at setup cancels it. *)
#push-options "--fuel 2"
let pmodx (x y: block)
  : Lemma (Poly.pmod (pshift1 x y) 256 == gmul x (Poly.xtimes y))
  = Poly.pcoef_top x y;
    Alg.pmod_shift1 (pmul (Poly.pbits x) (Poly.pbits y)) 256;
    Poly.gmul_is_pmod x y;
    Alg.gmul_xt_right x y 1
#pop-options

let gmulx_three (x y u1 v1 u2 v2 u3 v3: block)
  : Lemma (requires Poly.halvesp (pshift1 x y) u1 v1 /\
                    Poly.halves v1 r_block u2 v2 /\
                    Poly.halves v2 r_block u3 v3)
          (ensures gmul x (Poly.xtimes y) == gadd u1 (gadd u2 u3))
  = Poly.pmod_three (pshift1 x y) u1 v1 u2 v2 u3 v3;
    pmodx x y

#pop-options

(** {2 Multiplying by the reduction constant without a multiplier}

    [Spec.GF128.Poly.mul_r_coef] says that a product with [r_block] is four
    shifted copies of the other operand added together.  On the register side
    a shift of a 128-bit value is not one instruction -- the shift units work
    on 64-bit lanes and there is no carry between them -- but it is two,
    which is still a great deal cheaper than [PCLMULQDQ].  This section
    proves the two shift recipes and then the reduction step itself. *)

(** The four bits of [f] that a multiply by [r_block] adds together. *)
let rxor (f: int -> bool) (k: int) : bool =
  ((f k <> f (k + 1)) <> f (k + 2)) <> f (k + 7)

#push-options "--fuel 0 --ifuel 0"

(** A full 128-bit right shift by [n], from a lane-wise right shift by [n] of
    the value and a lane-wise left shift by [64 - n] of the value with its
    lanes moved down one.  Exactly one of the two contributes at each bit, so
    the case analysis is purely boolean once the reindexing is discharged. *)
let shr_step (fa fh fs fq: int -> bool) (n k: int)
  : Lemma (requires
      (k % 64 >= 64 - n ==> fh (k - (64 - n)) == fa (k + n)) /\
      fs k == (k % 64 + n < 64 && fa (k + n)) /\
      fq k == (fs k <> ((k % 64 >= 64 - n) && fh (k - (64 - n)))))
    (ensures fq k == fa (k + n)) = ()

(** A full 128-bit left shift by [64 + m], from a lane-wise left shift by [m]
    of the value with its lanes moved up one.  There is no carry term because
    moving the lanes up has already zeroed the low lane. *)
let shl_step (fa fl fq: int -> bool) (m k: int)
  : Lemma (requires
      (k % 64 >= m ==> fl (k - m) == fa (k - 64 - m)) /\
      (k % 64 < m ==> fa (k - 64 - m) == false) /\
      fq k == ((k % 64 >= m) && fl (k - m)))
    (ensures fq k == fa (k - 64 - m)) = ()

#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"

let shr_gen (fa fh fs fq: int -> bool) (n: int)
  : Lemma (requires
      1 <= n /\ n < 64 /\
      (forall (k: int). 0 <= k /\ k < 128 ==> fh k == fa (k + 64)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fs k == (k % 64 + n < 64 && fa (k + n))) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fq k == (fs k <> ((k % 64 >= 64 - n) && fh (k - (64 - n))))))
    (ensures forall (k: int). 0 <= k /\ k < 128 ==> fq k == fa (k + n))
  = let aux (k: int) : Lemma (0 <= k /\ k < 128 ==> fq k == fa (k + n))
      = if 0 <= k && k < 128 then begin
          if k < 64 then Math.small_mod k 64
          else (Math.small_mod (k - 64) 64; Math.lemma_mod_plus (k - 64) 1 64);
          if k % 64 >= 64 - n then begin
            assert (0 <= k - (64 - n) /\ k - (64 - n) < 128);
            assert (fh (k - (64 - n)) == fa (k - (64 - n) + 64));
            assert (k - (64 - n) + 64 == k + n)
          end;
          shr_step fa fh fs fq n k
        end
    in FStar.Classical.forall_intro aux

let shl_gen (fa fl fq: int -> bool) (m: int)
  : Lemma (requires
      0 <= m /\ m < 64 /\ bounded fa /\
      (forall (k: int). 0 <= k /\ k < 128 ==> fl k == fa (k - 64)) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         fq k == ((k % 64 >= m) && fl (k - m))))
    (ensures forall (k: int). 0 <= k /\ k < 128 ==> fq k == fa (k - 64 - m))
  = let aux (k: int) : Lemma (0 <= k /\ k < 128 ==> fq k == fa (k - 64 - m))
      = if 0 <= k && k < 128 then begin
          if k < 64 then Math.small_mod k 64
          else (Math.small_mod (k - 64) 64; Math.lemma_mod_plus (k - 64) 1 64);
          if k % 64 >= m then begin
            assert (0 <= k - m /\ k - m < 128);
            assert (fl (k - m) == fa (k - m - 64));
            assert (k - m - 64 == k - 64 - m)
          end;
          shl_step fa fl fq m k
        end
    in FStar.Classical.forall_intro aux

#pop-options

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

(** The GCM bits of a reversed block, at any index at all.  This is
    [bswap_bit] again, extended past both ends where both sides are [false]
    for different reasons. *)
let bitk_bswap (a: block) (j: int)
  : Lemma (Poly.bitk (bswap a) j == lebiti a (127 - j))
  = if 0 <= j && j < 128 then (bswap_bit a j; lebit_is_bit a (127 - j))

(** The reduction step, in the little-endian numbering the registers use.
    [ua] is the low half and [wa] the high half of [a * R]; the caller has
    them as [rxor] of [a]'s bits at four offsets, which is what the shift
    recipes above deliver. *)
let mul_r_halves (a ua wa: block)
  : Lemma (requires
      (forall (k: int). 0 <= k /\ k < 128 ==> lebiti ua k == rxor (lebiti a) k) /\
      (forall (k: int). 0 <= k /\ k < 128 ==>
         lebiti wa k == rxor (lebiti a) (k - 128)))
    (ensures Poly.halves (bswap a) r_block (bswap ua) (bswap wa))
  = let aux (k: nat { k < 128 })
      : Lemma (bit (bswap ua) k == Poly.pcoef (bswap a) r_block k /\
               bit (bswap wa) k == Poly.pcoef (bswap a) r_block (128 + k))
      = bswap_bit ua k; lebit_is_bit ua (127 - k);
        bswap_bit wa k; lebit_is_bit wa (127 - k);
        Poly.mul_r_coef (bswap a) k;
        Poly.mul_r_coef (bswap a) (128 + k);
        bitk_bswap a k; bitk_bswap a (k - 1);
        bitk_bswap a (k - 2); bitk_bswap a (k - 7);
        bitk_bswap a (128 + k); bitk_bswap a (127 + k);
        bitk_bswap a (126 + k); bitk_bswap a (121 + k)
    in
    FStar.Classical.forall_intro aux

#pop-options

(** {2 Karatsuba, and the fold the group may defer}

    The multiplier above spends four carry-less multiplies per block: the two
    halves of the product, and the two crossed terms that make up [mid].  Only
    the sum of the crossed terms is ever used, and Karatsuba computes that sum
    with one multiply instead of two,

      [(x0 + x1) (y0 + y1) + x0 y0 + x1 y1  =  x0 y1 + x1 y0,]

    which over a field of characteristic two is exact, with no borrow to worry
    about and no wider intermediate: the fold that would normally be the price
    of Karatsuba is three exclusive-ors of registers already in hand.

    That saving pairs with a second one.  Assembling [mid] into the two halves
    costs a shift each way and two more exclusive-ors, and the bulk loop then
    throws the halves of eight blocks together anyway.  Since the assembly is
    linear in [mid], it commutes with that sum: accumulate the three raw
    registers across the group and assemble once at the end.  The lemmas below
    are what lets the implementation leave the per-block halves uncomputed —
    they exist only as the ghost blocks [kfold_lo] and [kfold_hi]. *)

(** Sixty-four bits up and sixty-four bits down.  A block is bytes and the
    little-endian numbering puts bit [k] in byte [k / 8], so the shift is a
    slice and a splice rather than any arithmetic. *)

let shl8 (a: block) : block =
  Seq.append (Seq.create 8 (0 <: elem)) (Seq.slice a 0 8)

let shr8 (a: block) : block =
  Seq.append (Seq.slice a 8 16) (Seq.create 8 (0 <: elem))

let shl8_bit (a: block) (k: nat { k < 128 })
  : Lemma (lebit (shl8 a) k == lebiti a (k - 64))
  = reveal_opaque (`%lebit) lebit;
    Math.lemma_div_lt_nat k 7 3;
    if k < 64 then
      Seq.lemma_index_app1 (Seq.create 8 (0 <: elem)) (Seq.slice a 0 8) (k / 8)
    else begin
      Seq.lemma_index_app2 (Seq.create 8 (0 <: elem)) (Seq.slice a 0 8) (k / 8);
      Math.lemma_div_plus (k - 64) 8 8;
      Math.lemma_mod_plus (k - 64) 8 8
    end

let shr8_bit (a: block) (k: nat { k < 128 })
  : Lemma (lebit (shr8 a) k == lebiti a (k + 64))
  = reveal_opaque (`%lebit) lebit;
    Math.lemma_div_lt_nat k 7 3;
    if k < 64 then begin
      Seq.lemma_index_app1 (Seq.slice a 8 16) (Seq.create 8 (0 <: elem)) (k / 8);
      Math.lemma_div_plus k 8 8;
      Math.lemma_mod_plus k 8 8
    end else
      Seq.lemma_index_app2 (Seq.slice a 8 16) (Seq.create 8 (0 <: elem)) (k / 8)

(** Both shifts are additive, which is the whole reason the fold may be put
    off: a sum of shifted blocks is the shift of the sum. *)

let shl8_gadd (a b: block)
  : Lemma (shl8 (gadd a b) == gadd (shl8 a) (shl8 b))
  = let aux (k: nat { k < 128 })
      : Lemma (lebit (shl8 (gadd a b)) k == lebit (gadd (shl8 a) (shl8 b)) k)
      = shl8_bit (gadd a b) k; shl8_bit a k; shl8_bit b k;
        lexori a b (k - 64); lexor (shl8 a) (shl8 b) k
    in
    FStar.Classical.forall_intro aux;
    lebits_inj (shl8 (gadd a b)) (gadd (shl8 a) (shl8 b))

let shr8_gadd (a b: block)
  : Lemma (shr8 (gadd a b) == gadd (shr8 a) (shr8 b))
  = let aux (k: nat { k < 128 })
      : Lemma (lebit (shr8 (gadd a b)) k == lebit (gadd (shr8 a) (shr8 b)) k)
      = shr8_bit (gadd a b) k; shr8_bit a k; shr8_bit b k;
        lexori a b (k + 64); lexor (shr8 a) (shr8 b) k
    in
    FStar.Classical.forall_intro aux;
    lebits_inj (shr8 (gadd a b)) (gadd (shr8 a) (shr8 b))

(** Recovering the crossed sum from the folded product: the two square terms
    are taken back out.  This too is linear in all three arguments, so it too
    may be put off until the end of a group -- which is what makes the
    Karatsuba form cheaper than the four-multiply one even when nothing is
    reused, rather than only in bulk. *)

let kmid (ll hh mf: block) : block = gadd mf (gadd ll hh)

let kmid_isbits (ll hh mf: block)
  : Lemma (forall (k: int). lebiti (kmid ll hh mf) k ==
             ((lebiti mf k <> lebiti ll k) <> lebiti hh k))
  = FStar.Classical.forall_intro (lexori ll hh);
    FStar.Classical.forall_intro (lexori mf (gadd ll hh))

let kmid_gadd (l1 h1 f1 l2 h2 f2: block)
  : Lemma (gadd (kmid l1 h1 f1) (kmid l2 h2 f2) ==
           kmid (gadd l1 l2) (gadd h1 h2) (gadd f1 f2))
  = let aux (k: nat { k < 128 })
      : Lemma (lebit (gadd (kmid l1 h1 f1) (kmid l2 h2 f2)) k ==
               lebit (kmid (gadd l1 l2) (gadd h1 h2) (gadd f1 f2)) k)
      = lexor (kmid l1 h1 f1) (kmid l2 h2 f2) k;
        kmid_isbits l1 h1 f1; kmid_isbits l2 h2 f2;
        kmid_isbits (gadd l1 l2) (gadd h1 h2) (gadd f1 f2);
        lexori l1 l2 k; lexori h1 h2 k; lexori f1 f2 k
    in
    FStar.Classical.forall_intro aux;
    lebits_inj (gadd (kmid l1 h1 f1) (kmid l2 h2 f2))
               (kmid (gadd l1 l2) (gadd h1 h2) (gadd f1 f2))

let kmid_sum4 (l1 h1 f1 l2 h2 f2 l3 h3 f3 l4 h4 f4: block)
  : Lemma (Alg.sum4 (kmid l1 h1 f1) (kmid l2 h2 f2)
                    (kmid l3 h3 f3) (kmid l4 h4 f4) ==
           kmid (Alg.sum4 l1 l2 l3 l4) (Alg.sum4 h1 h2 h3 h4)
                (Alg.sum4 f1 f2 f3 f4))
  = kmid_gadd l3 h3 f3 l4 h4 f4;
    kmid_gadd l2 h2 f2 (gadd l3 l4) (gadd h3 h4) (gadd f3 f4);
    kmid_gadd l1 h1 f1 (gadd l2 (gadd l3 l4)) (gadd h2 (gadd h3 h4))
              (gadd f2 (gadd f3 f4))

let kmid_sum8 (l1 h1 f1 l2 h2 f2 l3 h3 f3 l4 h4 f4
               l5 h5 f5 l6 h6 f6 l7 h7 f7 l8 h8 f8: block)
  : Lemma (Alg.sum8 (kmid l1 h1 f1) (kmid l2 h2 f2)
                    (kmid l3 h3 f3) (kmid l4 h4 f4)
                    (kmid l5 h5 f5) (kmid l6 h6 f6)
                    (kmid l7 h7 f7) (kmid l8 h8 f8) ==
           kmid (Alg.sum8 l1 l2 l3 l4 l5 l6 l7 l8)
                (Alg.sum8 h1 h2 h3 h4 h5 h6 h7 h8)
                (Alg.sum8 f1 f2 f3 f4 f5 f6 f7 f8))
  = kmid_sum4 l1 h1 f1 l2 h2 f2 l3 h3 f3 l4 h4 f4;
    kmid_sum4 l5 h5 f5 l6 h6 f6 l7 h7 f7 l8 h8 f8;
    kmid_gadd (Alg.sum4 l1 l2 l3 l4) (Alg.sum4 h1 h2 h3 h4)
              (Alg.sum4 f1 f2 f3 f4)
              (Alg.sum4 l5 l6 l7 l8) (Alg.sum4 h5 h6 h7 h8)
              (Alg.sum4 f5 f6 f7 f8)

(** The two halves of a product, as the three registers hold them. *)

let kfold_lo (ll mm: block) : block = gadd ll (shl8 mm)
let kfold_hi (hh mm: block) : block = gadd hh (shr8 mm)

(** Bit by bit, the assembled half is the raw half with the middle term
    shifted into place -- which is exactly the shape [lo_of_lanes] asks for,
    so the ghost block may be handed to it in place of a register. *)

let kfold_lo_bit (ll mm: block) (k: nat { k < 128 })
  : Lemma (lebit (kfold_lo ll mm) k == (lebiti ll k <> lebiti mm (k - 64)))
  = lexor ll (shl8 mm) k; shl8_bit mm k

let kfold_hi_bit (hh mm: block) (k: nat { k < 128 })
  : Lemma (lebit (kfold_hi hh mm) k == (lebiti hh k <> lebiti mm (k + 64)))
  = lexor hh (shr8 mm) k; shr8_bit mm k

let kfold_lo_isbits (ll mm: block)
  : Lemma (forall (k: int). 0 <= k /\ k < 128 ==>
             lebiti (kfold_lo ll mm) k == (lebiti ll k <> lebiti mm (k - 64)))
  = FStar.Classical.forall_intro (kfold_lo_bit ll mm)

let kfold_hi_isbits (hh mm: block)
  : Lemma (forall (k: int). 0 <= k /\ k < 128 ==>
             lebiti (kfold_hi hh mm) k == (lebiti hh k <> lebiti mm (k + 64)))
  = FStar.Classical.forall_intro (kfold_hi_bit hh mm)

(** A register holding the assembled half is that ghost block. *)

let kfold_lo_bits (ll mm v: block)
  : Lemma (requires forall (k: int). 0 <= k /\ k < 128 ==>
                      lebiti v k == (lebiti ll k <> lebiti mm (k - 64)))
          (ensures v == kfold_lo ll mm)
  = let aux (k: nat { k < 128 })
      : Lemma (lebit v k == lebit (kfold_lo ll mm) k)
      = kfold_lo_bit ll mm k
    in
    FStar.Classical.forall_intro aux;
    lebits_inj v (kfold_lo ll mm)

let kfold_hi_bits (hh mm v: block)
  : Lemma (requires forall (k: int). 0 <= k /\ k < 128 ==>
                      lebiti v k == (lebiti hh k <> lebiti mm (k + 64)))
          (ensures v == kfold_hi hh mm)
  = let aux (k: nat { k < 128 })
      : Lemma (lebit v k == lebit (kfold_hi hh mm) k)
      = kfold_hi_bit hh mm k
    in
    FStar.Classical.forall_intro aux;
    lebits_inj v (kfold_hi hh mm)

(** Assembling commutes with addition, one pair at a time and then over the
    four and the eight the bulk loops work in. *)

let kfold_lo_gadd (l1 m1 l2 m2: block)
  : Lemma (gadd (kfold_lo l1 m1) (kfold_lo l2 m2) ==
           kfold_lo (gadd l1 l2) (gadd m1 m2))
  = shl8_gadd m1 m2;
    let aux (k: nat { k < 128 })
      : Lemma (lebit (gadd (kfold_lo l1 m1) (kfold_lo l2 m2)) k ==
               lebit (kfold_lo (gadd l1 l2) (gadd m1 m2)) k)
      = lexor (kfold_lo l1 m1) (kfold_lo l2 m2) k;
        lexor l1 (shl8 m1) k; lexor l2 (shl8 m2) k;
        lexor (gadd l1 l2) (shl8 (gadd m1 m2)) k;
        lexor l1 l2 k; lexor (shl8 m1) (shl8 m2) k
    in
    FStar.Classical.forall_intro aux;
    lebits_inj (gadd (kfold_lo l1 m1) (kfold_lo l2 m2))
               (kfold_lo (gadd l1 l2) (gadd m1 m2))

let kfold_hi_gadd (h1 m1 h2 m2: block)
  : Lemma (gadd (kfold_hi h1 m1) (kfold_hi h2 m2) ==
           kfold_hi (gadd h1 h2) (gadd m1 m2))
  = shr8_gadd m1 m2;
    let aux (k: nat { k < 128 })
      : Lemma (lebit (gadd (kfold_hi h1 m1) (kfold_hi h2 m2)) k ==
               lebit (kfold_hi (gadd h1 h2) (gadd m1 m2)) k)
      = lexor (kfold_hi h1 m1) (kfold_hi h2 m2) k;
        lexor h1 (shr8 m1) k; lexor h2 (shr8 m2) k;
        lexor (gadd h1 h2) (shr8 (gadd m1 m2)) k;
        lexor h1 h2 k; lexor (shr8 m1) (shr8 m2) k
    in
    FStar.Classical.forall_intro aux;
    lebits_inj (gadd (kfold_hi h1 m1) (kfold_hi h2 m2))
               (kfold_hi (gadd h1 h2) (gadd m1 m2))

let kfold_lo_sum4 (l1 m1 l2 m2 l3 m3 l4 m4: block)
  : Lemma (Alg.sum4 (kfold_lo l1 m1) (kfold_lo l2 m2)
                    (kfold_lo l3 m3) (kfold_lo l4 m4) ==
           kfold_lo (Alg.sum4 l1 l2 l3 l4) (Alg.sum4 m1 m2 m3 m4))
  = kfold_lo_gadd l3 m3 l4 m4;
    kfold_lo_gadd l2 m2 (gadd l3 l4) (gadd m3 m4);
    kfold_lo_gadd l1 m1 (gadd l2 (gadd l3 l4)) (gadd m2 (gadd m3 m4))

let kfold_hi_sum4 (h1 m1 h2 m2 h3 m3 h4 m4: block)
  : Lemma (Alg.sum4 (kfold_hi h1 m1) (kfold_hi h2 m2)
                    (kfold_hi h3 m3) (kfold_hi h4 m4) ==
           kfold_hi (Alg.sum4 h1 h2 h3 h4) (Alg.sum4 m1 m2 m3 m4))
  = kfold_hi_gadd h3 m3 h4 m4;
    kfold_hi_gadd h2 m2 (gadd h3 h4) (gadd m3 m4);
    kfold_hi_gadd h1 m1 (gadd h2 (gadd h3 h4)) (gadd m2 (gadd m3 m4))

let kfold_lo_sum8 (l1 m1 l2 m2 l3 m3 l4 m4 l5 m5 l6 m6 l7 m7 l8 m8: block)
  : Lemma (Alg.sum8 (kfold_lo l1 m1) (kfold_lo l2 m2)
                    (kfold_lo l3 m3) (kfold_lo l4 m4)
                    (kfold_lo l5 m5) (kfold_lo l6 m6)
                    (kfold_lo l7 m7) (kfold_lo l8 m8) ==
           kfold_lo (Alg.sum8 l1 l2 l3 l4 l5 l6 l7 l8)
                    (Alg.sum8 m1 m2 m3 m4 m5 m6 m7 m8))
  = kfold_lo_sum4 l1 m1 l2 m2 l3 m3 l4 m4;
    kfold_lo_sum4 l5 m5 l6 m6 l7 m7 l8 m8;
    kfold_lo_gadd (Alg.sum4 l1 l2 l3 l4) (Alg.sum4 m1 m2 m3 m4)
                  (Alg.sum4 l5 l6 l7 l8) (Alg.sum4 m5 m6 m7 m8)

let kfold_hi_sum8 (h1 m1 h2 m2 h3 m3 h4 m4 h5 m5 h6 m6 h7 m7 h8 m8: block)
  : Lemma (Alg.sum8 (kfold_hi h1 m1) (kfold_hi h2 m2)
                    (kfold_hi h3 m3) (kfold_hi h4 m4)
                    (kfold_hi h5 m5) (kfold_hi h6 m6)
                    (kfold_hi h7 m7) (kfold_hi h8 m8) ==
           kfold_hi (Alg.sum8 h1 h2 h3 h4 h5 h6 h7 h8)
                    (Alg.sum8 m1 m2 m3 m4 m5 m6 m7 m8))
  = kfold_hi_sum4 h1 m1 h2 m2 h3 m3 h4 m4;
    kfold_hi_sum4 h5 m5 h6 m6 h7 m7 h8 m8;
    kfold_hi_gadd (Alg.sum4 h1 h2 h3 h4) (Alg.sum4 m1 m2 m3 m4)
                  (Alg.sum4 h5 h6 h7 h8) (Alg.sum4 m5 m6 m7 m8)

(** Byte reversal is additive too, so a sum of reversed blocks is the reversal
    of the sum.  The accumulators are stated reversed and the fold is not. *)

let bswap_sum4 (a b c d: block)
  : Lemma (Alg.sum4 (bswap a) (bswap b) (bswap c) (bswap d) ==
           bswap (Alg.sum4 a b c d))
  = bswap_gadd c d;
    bswap_gadd b (gadd c d);
    bswap_gadd a (gadd b (gadd c d))

let bswap_sum8 (a b c d e f g h: block)
  : Lemma (Alg.sum8 (bswap a) (bswap b) (bswap c) (bswap d)
                    (bswap e) (bswap f) (bswap g) (bswap h) ==
           bswap (Alg.sum8 a b c d e f g h))
  = bswap_sum4 a b c d;
    bswap_sum4 e f g h;
    bswap_gadd (Alg.sum4 a b c d) (Alg.sum4 e f g h)

let bswap_inj (a b: block)
  : Lemma (requires bswap a == bswap b) (ensures a == b)
  = bswap_involutive a; bswap_involutive b

(** {3 The Karatsuba identity}

    The folded operand's low lane is the sum of the two lanes it was built
    from: both sides are [Seq.init 64] over the same bits. *)

let fold_lane (a f: block)
  : Lemma (requires forall (k: int). 0 <= k /\ k < 128 ==>
                      lebiti f k == (lebiti a k <> lebiti a (k + 64)))
          (ensures lane f false == padd (lane a false) (lane a true))
  = Seq.lemma_eq_intro (lane f false) (padd (lane a false) (lane a true))

(** And the identity itself: the product of the folded operands, with the two
    square terms taken back out, is the sum of the crossed terms. *)

let kara_mid (al ah bl bh: poly) (k: int)
  : Lemma (requires Seq.length al == 64 /\ Seq.length ah == 64)
          (ensures ((conv (padd al ah) (padd bl bh) k <> conv al bl k) <>
                    conv ah bh k) ==
                   (conv al bh k <> conv ah bl k))
  = conv_add_left al ah (padd bl bh) k 64;
    conv_add_right al bl bh k;
    conv_add_right ah bl bh k

(** Specialised to the lanes of two registers, which is how the implementation
    meets it, and where the sixty-four-bit lengths are still in plain sight. *)

let kara_mid_lanes (xa yb: block) (k: int)
  : Lemma (((conv (padd (lane xa false) (lane xa true))
                  (padd (lane yb false) (lane yb true)) k <>
             conv (lane xa false) (lane yb false) k) <>
            conv (lane xa true) (lane yb true) k) ==
           (conv (lane xa false) (lane yb true) k <>
            conv (lane xa true) (lane yb false) k))
  = kara_mid (lane xa false) (lane xa true) (lane yb false) (lane yb true) k
