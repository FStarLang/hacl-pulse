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

(** Polynomials over GF(2), which is what a carry-less multiplier computes.

    {2 The representation}

    A polynomial is a sequence of bits whose index {i is} the exponent: index
    [i] holds the coefficient of [x^i].  Everything is read through [pget],
    which returns [false] outside the sequence and takes an [int] rather than
    a [nat], so no lemma in this file ever has a side condition about an index
    being in range.  Two polynomials that agree under [pget] everywhere are
    the same polynomial even if their sequences have different lengths; that
    is [peq], and it is what the lemmas conclude.

    {2 The sums}

    A carry-less product is a convolution, and a convolution is an
    exclusive-or over a range.  [xsum f lo n] is that: [f lo], ..., [f
    (lo+n-1)], combined with [<>].  Four small lemmas about it -- split off
    the bottom, shift the range, reverse the range, and drop zero terms -- are
    the whole of the work, and every algebraic fact below is one of them
    applied once.

    In particular the reflection identity that makes [PCLMULQDQ] usable for
    GHASH, which Gueron writes as [rev(a) * rev(b) == rev(a * b) >> 1], is
    here [conv_rev], and its proof is [xsum_rev] and nothing else. *)
module Spec.CarryLess

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

(** {2 Polynomials} *)

type poly = Seq.seq bool

(** The coefficient of [x^i], for any [i] at all. *)
let pget (a: poly) (i: int) : bool =
  if 0 <= i && i < Seq.length a then Seq.index a i else false

(** Equality of polynomials, as opposed to equality of representations. *)
let peq (a b: poly) = forall (i: int). pget a i == pget b i

let pzero (n: nat) : poly = Seq.create n false

let pzero_get (n: nat) (i: int) : Lemma (pget (pzero n) i == false) = ()

(** {2 Exclusive-or over a range}

    [xsum f lo n] is [f lo <> f (lo+1) <> ... <> f (lo+n-1)]. *)

let rec xsum (f: int -> bool) (lo: int) (n: nat) : Tot bool (decreases n) =
  if n = 0 then false else (f (lo + n - 1) <> xsum f lo (n - 1))

(** Only the values in range matter. *)
let rec xsum_ext (f g: int -> bool) (lo: int) (n: nat)
  : Lemma (requires forall (i: int). lo <= i /\ i < lo + n ==> f i == g i)
          (ensures xsum f lo n == xsum g lo n)
          (decreases n)
  = if n = 0 then () else xsum_ext f g lo (n - 1)

let rec xsum_zero (f: int -> bool) (lo: int) (n: nat)
  : Lemma (requires forall (i: int). lo <= i /\ i < lo + n ==> f i == false)
          (ensures xsum f lo n == false)
          (decreases n)
  = if n = 0 then () else xsum_zero f lo (n - 1)

(** Split off the {i bottom} term; the definition splits off the top one. *)
let rec xsum_cons (f: int -> bool) (lo: int) (n: nat { n > 0 })
  : Lemma (ensures xsum f lo n == (f lo <> xsum f (lo + 1) (n - 1)))
          (decreases n)
  = if n = 1 then () else xsum_cons f lo (n - 1)

(** Slide the range and the function together. *)
let rec xsum_shift (f: int -> bool) (lo: int) (n: nat) (d: int)
  : Lemma (ensures xsum f lo n == xsum (fun i -> f (i + d)) (lo - d) n)
          (decreases n)
  = if n = 0 then () else xsum_shift f lo (n - 1) d

(** {2 Trimming}

    Terms that are [false] may be dropped from either end. *)

let rec xsum_trim_hi (f: int -> bool) (lo: int) (m: nat) (n: nat { m <= n })
  : Lemma (requires forall (i: int). lo + m <= i /\ i < lo + n ==> f i == false)
          (ensures xsum f lo n == xsum f lo m)
          (decreases n)
  = if n = m then () else xsum_trim_hi f lo m (n - 1)

let rec xsum_trim_lo (f: int -> bool) (lo: int) (d: nat) (n: nat { d <= n })
  : Lemma (requires forall (i: int). lo <= i /\ i < lo + d ==> f i == false)
          (ensures xsum f lo n == xsum f (lo + d) (n - d))
          (decreases d)
  = if d = 0 then ()
    else begin
      xsum_cons f lo n;
      xsum_trim_lo f (lo + 1) (d - 1) (n - 1)
    end

(** {2 Reversal and linearity} *)

let rec xsum_rev (f: int -> bool) (lo: int) (n: nat)
  : Lemma (ensures xsum f lo n == xsum (fun i -> f (2 * lo + n - 1 - i)) lo n)
          (decreases n)
  = if n = 0
    then (xsum_zero f lo n; xsum_zero (fun i -> f (2 * lo + n - 1 - i)) lo n)
    else begin
      let g : int -> bool = fun i -> f (2 * lo + n - 1 - i) in
      let h : int -> bool = fun i -> g (2 * (lo + 1) + (n - 1) - 1 - i) in
      let fd : int -> bool = fun i -> f (i - 1) in
      xsum_cons g lo n;
      assert (xsum g lo n == (f (lo + n - 1) <> xsum g (lo + 1) (n - 1)));
      xsum_rev g (lo + 1) (n - 1);
      assert (xsum g (lo + 1) (n - 1) == xsum h (lo + 1) (n - 1));
      xsum_ext h fd (lo + 1) (n - 1);
      xsum_shift f lo (n - 1) (-1);
      xsum_ext (fun i -> f (i + (-1))) fd (lo + 1) (n - 1);
      assert (xsum fd (lo + 1) (n - 1) == xsum f lo (n - 1))
    end

(** A factor that does not depend on the summation index comes out. *)
let rec xsum_and (c: bool) (f: int -> bool) (lo: int) (n: nat)
  : Lemma (ensures xsum (fun i -> c && f i) lo n == (c && xsum f lo n))
          (decreases n)
  = if n = 0 then () else xsum_and c f lo (n - 1)

(** Exactly one term may be nonzero, and then the sum is that term. *)
let rec xsum_one (f: int -> bool) (lo: int) (n: nat) (j: int)
  : Lemma (requires lo <= j /\ j < lo + n /\
                    (forall (i: int). lo <= i /\ i < lo + n /\ i <> j ==> f i == false))
          (ensures xsum f lo n == f j)
          (decreases n)
  = if lo + n - 1 = j
    then xsum_zero f lo (n - 1)
    else xsum_one f lo (n - 1) j

let rec xsum_xor (f g: int -> bool) (lo: int) (n: nat)
  : Lemma (ensures xsum (fun i -> f i <> g i) lo n == (xsum f lo n <> xsum g lo n))
          (decreases n)
  = if n = 0 then () else xsum_xor f g lo (n - 1)

(** Two nested sums may be taken in either order. *)
let rec xsum_swap (h: int -> int -> bool) (lo1: int) (n1: nat) (lo2: int) (n2: nat)
  : Lemma (ensures xsum (fun j -> xsum (fun k -> h j k) lo2 n2) lo1 n1 ==
                   xsum (fun k -> xsum (fun j -> h j k) lo1 n1) lo2 n2)
          (decreases n1)
  = if n1 = 0
    then xsum_zero (fun k -> xsum (fun j -> h j k) lo1 n1) lo2 n2
    else begin
      let top = lo1 + n1 - 1 in
      xsum_swap h lo1 (n1 - 1) lo2 n2;
      xsum_xor (fun k -> h top k) (fun k -> xsum (fun j -> h j k) lo1 (n1 - 1)) lo2 n2;
      xsum_ext (fun k -> xsum (fun j -> h j k) lo1 n1)
               (fun k -> h top k <> xsum (fun j -> h j k) lo1 (n1 - 1))
               lo2 n2
    end

(** {2 The operations} *)

let padd (a b: poly) : poly =
  let n = if Seq.length a > Seq.length b then Seq.length a else Seq.length b in
  Seq.init n (fun i -> pget a i <> pget b i)

let padd_get (a b: poly) (i: int)
  : Lemma (pget (padd a b) i == (pget a i <> pget b i)) = ()

(** The convolution: the coefficient of [x^k] in [a * b].  The range is [a]'s
    length, since every other term has [pget a i == false]. *)
let conv (a b: poly) (k: int) : bool =
  xsum (fun i -> pget a i && pget b (k - i)) 0 (Seq.length a)

let pmul (a b: poly) : poly =
  Seq.init (Seq.length a + Seq.length b) (fun k -> conv a b k)

(** [pmul] is [conv] where it is defined, and [conv] is [false] elsewhere. *)
let pmul_get (a b: poly) (k: int)
  : Lemma (pget (pmul a b) k == conv a b k)
  = if 0 <= k && k < Seq.length a + Seq.length b then ()
    else xsum_zero (fun i -> pget a i && pget b (k - i)) 0 (Seq.length a)

(** The summation range may be widened to anything at least [a]'s length. *)
let conv_widen (a b: poly) (k: int) (n: nat { Seq.length a <= n })
  : Lemma (conv a b k == xsum (fun i -> pget a i && pget b (k - i)) 0 n)
  = xsum_trim_hi (fun i -> pget a i && pget b (k - i)) 0 (Seq.length a) n

(** Recognizing a convolution: any function agreeing with the summand on the
    range computes it.  This is the only reliable way to bring [conv] and a
    hand-written [xsum] into contact, because the solver sees two distinct
    closures otherwise. *)
let conv_def (a b: poly) (k: int) (f: int -> bool)
  : Lemma (requires forall (i: int). 0 <= i /\ i < Seq.length a ==>
                                    f i == (pget a i && pget b (k - i)))
          (ensures conv a b k == xsum f 0 (Seq.length a))
  = xsum_ext (fun i -> pget a i && pget b (k - i)) f 0 (Seq.length a)

(** The same over a wider range, the extra terms being zero. *)
let conv_def_n (a b: poly) (k: int) (f: int -> bool) (n: nat { Seq.length a <= n })
  : Lemma (requires forall (i: int). 0 <= i /\ i < n ==>
                                    f i == (pget a i && pget b (k - i)))
          (ensures conv a b k == xsum f 0 n)
  = conv_def a b k f;
    xsum_trim_hi f 0 (Seq.length a) n

(** {2 Shifting, which is multiplication by a monomial} *)

let pshift (a: poly) (d: nat) : poly =
  Seq.init (Seq.length a + d) (fun i -> pget a (i - d))

let pshift_get (a: poly) (d: nat) (i: int)
  : Lemma (pget (pshift a d) i == pget a (i - d)) = ()

(** {2 The convolution is bilinear}

    These four are what turns "multiply two 128-bit polynomials" into "call
    the 64x64 multiplier four times": split each operand into a low and a
    high half, and the product is four convolutions at three offsets. *)

(** Only the coefficients matter, not the representation. *)
let conv_peq (a a' b b': poly) (k: int) (n: nat)
  : Lemma (requires peq a a' /\ peq b b' /\
                    Seq.length a <= n /\ Seq.length a' <= n)
          (ensures conv a b k == conv a' b' k)
  = conv_widen a b k n;
    conv_widen a' b' k n;
    xsum_ext (fun i -> pget a i && pget b (k - i))
             (fun i -> pget a' i && pget b' (k - i)) 0 n

let conv_add_left (a1 a2 b: poly) (k: int) (n: nat)
  : Lemma (requires Seq.length a1 <= n /\ Seq.length a2 <= n /\
                    Seq.length (padd a1 a2) <= n)
          (ensures conv (padd a1 a2) b k == (conv a1 b k <> conv a2 b k))
  = let f1 : int -> bool = fun i -> pget a1 i && pget b (k - i) in
    let f2 : int -> bool = fun i -> pget a2 i && pget b (k - i) in
    FStar.Classical.forall_intro (padd_get a1 a2);
    conv_def_n a1 b k f1 n;
    conv_def_n a2 b k f2 n;
    conv_def_n (padd a1 a2) b k (fun i -> f1 i <> f2 i) n;
    xsum_xor f1 f2 0 n

(** On the right there is nothing to do: the summation range is [a]'s length
    either way. *)
let conv_add_right (a b1 b2: poly) (k: int)
  : Lemma (conv a (padd b1 b2) k == (conv a b1 k <> conv a b2 k))
  = let n = Seq.length a in
    let f1 : int -> bool = fun i -> pget a i && pget b1 (k - i) in
    let f2 : int -> bool = fun i -> pget a i && pget b2 (k - i) in
    FStar.Classical.forall_intro (padd_get b1 b2);
    conv_def a b1 k f1;
    conv_def a b2 k f2;
    conv_def a (padd b1 b2) k (fun i -> f1 i <> f2 i);
    xsum_xor f1 f2 0 n

let conv_shift_left (a b: poly) (d: nat) (k: int)
  : Lemma (conv (pshift a d) b k == conv a b (k - d))
  = let n = Seq.length a + d in
    let f : int -> bool = fun i -> pget a (i - d) && pget b (k - i) in
    let g : int -> bool = fun m -> pget a m && pget b (k - d - m) in
    conv_def (pshift a d) b k f;
    xsum_shift f 0 n d;
    xsum_ext (fun m -> f (m + d)) g (0 - d) n;
    xsum_trim_lo g (0 - d) d n;
    conv_def a b (k - d) g

let conv_shift_right (a b: poly) (d: nat) (k: int)
  : Lemma (conv a (pshift b d) k == conv a b (k - d))
  = let f : int -> bool = fun i -> pget a i && pget b (k - d - i) in
    conv_def a (pshift b d) k f;
    conv_def a b (k - d) f

(** {2 Reversal, and the identity that makes PCLMULQDQ usable}

    [prev a n] is [a] with its bottom [n] coefficients written backwards: the
    coefficient of [x^i] in the result is the coefficient of [x^(n-1-i)] in
    [a].  This is what a 128-bit register holds after the byte reversal that
    every GHASH implementation starts with, because GCM numbers the bits of a
    block the opposite way round from the way a little-endian machine numbers
    the bits of an integer.

    The identity is that reversing commutes with multiplication up to the one
    place the degrees do not line up: the product of two reversed degree-<128
    polynomials has, at [x^m], the coefficient the true product has at
    [x^(254-m)] -- one short of the [255-m] a clean reversal of a 256-bit
    value would give, which is the [>> 1] in Gueron's statement of it. *)

let prev (a: poly) (n: nat) : poly = Seq.init n (fun i -> pget a (n - 1 - i))

let prev_get (a: poly) (n: nat) (i: int)
  : Lemma (pget (prev a n) i == (if 0 <= i && i < n then pget a (n - 1 - i) else false))
  = ()

#push-options "--z3rlimit 100"

let conv_rev (a b: poly) (m: int)
  : Lemma (requires Seq.length a <= 128 /\ Seq.length b <= 128)
          (ensures conv (prev a 128) (prev b 128) m == conv a b (254 - m))
  = let ar = prev a 128 in
    let br = prev b 128 in
    let f : int -> bool = fun i -> pget ar i && pget br (m - i) in
    let g : int -> bool = fun p -> pget a p && pget b (254 - m - p) in
    conv_widen a b (254 - m) 128;
    assert (conv ar br m == xsum f 0 128);
    xsum_rev f 0 128;
    xsum_ext (fun i -> f (0 + 128 - 1 - i)) g 0 128

#pop-options
