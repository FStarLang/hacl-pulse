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

(** The eight-limb representation of [Spec.Curve25519]'s field.

    An element is eight natural numbers standing for
    [a0 + a1 2^32 + ... + a7 2^224].  Nothing here is a machine integer:
    this module is the arithmetic, and [Hacl.Curve25519.Field] will be the
    same arithmetic on [Hacl.Secret.UInt64.t].

    The part of that arithmetic which never mentions the prime -- the
    product, the carry chain, the bounds, the byte conversions -- now lives
    in [Spec.Bignum256], which P-256 shares.  This module [include]s it, so
    every name is still available here and no consumer noticed the move.
    What is left below is exactly the prime-specific half: folding column
    [k + 8] into column [k] with the constant [38], and subtracting the
    prime.

    {b Why thirty-two bits.}  The textbook representation of this field is
    five limbs of fifty-one bits, whose products need a hundred-and-two-bit
    accumulator; that is why HACL* has both a [_51] field over [uint128] and
    a [_64] one over assembly.  Custard now emits [unsigned __int128], so a
    column of products can be a hundred and twenty-eight bits wide, and the
    limb only has to be small enough that [nl] products fit there.
    Thirty-two is the largest such radix, and it makes everything else free:
    a limb is exactly four bytes, so loading and storing a field element is a
    byte shuffle with no bit extraction, and [2^256 = 2 * prime + 38] means
    the reduction constant is the single digit [38].  A column of eight
    products of thirty-three-bit limbs is under [2^69], and folding
    multiplies that by [38], so the widest intermediate is under [2^75] --
    fifty-three bits of headroom.

    A multiplication is sixty-four word multiplies.  Radix [2^51] would need
    twenty-five, but it would also need bit extraction on every load and
    store and a carry chain that is not a byte shuffle; sixty-four schoolbook
    products with no intermediate reduction is the trade this library makes.

    Everything below is stated on [Seq.seq nat] and proved by induction.  The
    alternative -- naming sixty-four products and handing them to the ring
    tactic, as [Spec.Poly1305.Field] does for twenty-five -- does not scale
    as well, and the sequence formulation is also the one the
    implementation's loops need. *)
module Spec.Curve25519.Field

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module S8 = Hacl.Secret.UInt8

open Hacl.Spec.Bytes

include Spec.Bignum256

let prime : pos = Spec.Curve25519.prime

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 Folding the top half down}

    [2^256 = 2 * prime + 38], so column [k + 8] is worth [38] units of
    column [k] plus [2 * prime] times its weight -- and the surplus is an
    exact multiple of the prime, so no [%] is needed anywhere. *)
let fold38 (c: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun k -> vat c k + 38 * vat c (k + nl))

let two_prime (_: unit) : Lemma (pow2 256 == 2 * prime + 38) =
  assert_norm (pow2 256 == 2 * (pow2 255 - 19) + 38)

let fold_ok (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw)
          (ensures eval c == eval (fold38 c) + 2 * prime * eval (Seq.slice c nl nw))
  = let u = Seq.slice c 0 nl in
    let w = Seq.slice c nl nw in
    eval_split c nl;
    Seq.lemma_eq_intro (fold38 c) (addw u (scale 38 w));
    eval_addw u (scale 38 w);
    eval_scale 38 w;
    two_prime ();
    assert (rad * nl == 256);
    Math.distributivity_add_left (2 * prime) 38 (eval w);
    Math.paren_mul_right 2 prime (eval w)

let fold_ble (c: Seq.seq nat) (cc: nat)
  : Lemma (requires ble c cc) (ensures ble (fold38 c) (39 * cc)) = ()


let carry_top (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then
    Seq.upd (Seq.upd s (nl - 1) (vat s (nl - 1) % base)) 0
            (vat s 0 + 38 * (vat s (nl - 1) / base))
  else s

let carry_top_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (carry_top s) == nl) = ()

let carry_top_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (carry_top s) + 2 * prime * (Seq.index s (nl - 1) / base) == eval s)
  = let q = Seq.index s (nl - 1) / base in
    let s1 = Seq.upd s (nl - 1) (Seq.index s (nl - 1) % base) in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % base);
    eval_upd s1 0 (Seq.index s 0 + 38 * q);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) base;
    Math.pow2_plus (rad * (nl - 1)) rad;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % base) (base * q);
    Math.paren_mul_right (pow2 (rad * (nl - 1))) base q;
    two_prime ();
    assert (rad * nl == 256);
    Math.distributivity_add_left (2 * prime) 38 q;
    Math.paren_mul_right 2 prime q

let carry_top_ble (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ chained s c d (nl - 1))
          (ensures ble (carry_top s) (base - 1 + 38 * ((c + d) / base)))
  = Math.lemma_div_le (Seq.index s (nl - 1)) (c + d) base

let carry_pass (s: Seq.seq nat) : Seq.seq nat = carry_top (carry_run s (nl - 1))

let carry_pass_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (carry_pass s) == nl)
  = carry_run_len s (nl - 1)

let carry_pass_mod (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (carry_pass s) % prime == eval s % prime)
  = carry_run_len s (nl - 1);
    carry_run_ok s (nl - 1);
    let r = carry_run s (nl - 1) in
    carry_top_ok r;
    let q = Seq.index r (nl - 1) / base in
    Math.paren_mul_right 2 q prime;
    Math.swap_mul 2 prime;
    Math.lemma_mod_plus (eval (carry_pass s)) (2 * q) prime

let carry_pass_ble (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures ble (carry_pass s) (base - 1 + 38 * ((c + d) / base)))
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    carry_top_ble (carry_run s (nl - 1)) c d


(** {2 Subtracting the prime}

    [2^255 = prime + 19], so clearing bit 255 and adding [19] subtracts one
    prime.  Applied twice to a number below [2^256] it lands below [2^255],
    and a third application decides the last conditional subtraction. *)

let hi255 (s: Seq.seq nat) : nat = vat s (nl - 1) / pow2 31

let fold255 (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then
    Seq.upd (Seq.upd s (nl - 1) (vat s (nl - 1) % pow2 31)) 0 (vat s 0 + 19 * hi255 s)
  else s

let fold255_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (fold255 s) == nl) = ()

let fold255_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (fold255 s) + prime * hi255 s == eval s)
  = let q = hi255 s in
    let s1 = Seq.upd s (nl - 1) (Seq.index s (nl - 1) % pow2 31) in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % pow2 31);
    eval_upd s1 0 (Seq.index s 0 + 19 * q);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) (pow2 31);
    Math.pow2_plus (rad * (nl - 1)) 31;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % pow2 31) (pow2 31 * q);
    Math.paren_mul_right (pow2 (rad * (nl - 1))) (pow2 31) q;
    assert (rad * (nl - 1) + 31 == 255);
    assert_norm (pow2 255 == prime + 19)

(** Masking off bit 255 is a reduction modulo [2^255], which is what
    decoding a public key asks for. *)
let mask255 (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then Seq.upd s (nl - 1) (vat s (nl - 1) % pow2 31) else s

let mask255_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures eval (mask255 s) == eval s % pow2 255 /\ bnd (mask255 s) base)
  = let q = Seq.index s (nl - 1) / pow2 31 in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % pow2 31);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) (pow2 31);
    Math.pow2_plus (rad * (nl - 1)) 31;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % pow2 31) (pow2 31 * q);
    Math.paren_mul_right (pow2 (rad * (nl - 1))) (pow2 31) q;
    assert (rad * (nl - 1) + 31 == 255);
    eval_at (mask255 s) (nl - 1);
    eval_bnd (Seq.slice (mask255 s) 0 (nl - 1));
    eval_zeros (Seq.slice (mask255 s) nl nl);
    Math.pow2_plus (rad * (nl - 1)) 31;
    Math.lemma_mult_le_left (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % pow2 31 + 1) (pow2 31);
    Math.lemma_mod_plus (eval (mask255 s)) q (pow2 255);
    Math.small_mod (eval (mask255 s)) (pow2 255)

(** {2 Eight primes}

    [fsub] adds a multiple of the prime before subtracting, so that no limb
    can go negative.  Four times [2 * prime] is the smallest one whose every
    limb dominates a limb of the subtrahend. *)


let twop : Seq.seq nat = Seq.upd (ones nl) 0 ((base - 38) <: nat)

let eightp : Seq.seq nat = scale 4 twop

let twop_ok (_: unit) : Lemma (eval twop == 2 * prime /\ Seq.length twop == nl)
  = eval_ones nl;
    eval_upd (ones nl) 0 ((base - 38) <: nat);
    assert (rad * nl == 256);
    two_prime ()

let eightp_ok (_: unit)
  : Lemma (eval eightp == 8 * prime /\ Seq.length eightp == nl /\
           (forall (i: nat). i < nl ==> 4 * (base - 38) <= Seq.index eightp i))
  = twop_ok ();
    eval_scale 4 twop;
    Math.paren_mul_right 4 2 prime

#pop-options

(** {2 The operations, as the implementation performs them}

    Everything from here down is stated so that a Pulse function can build a
    sequence and then apply exactly one lemma.  The bounds are the concrete
    ones: a field element in this library has every limb below [2^33], and
    each operation restores that with a fixed number of carry passes -- one
    for an addition, a subtraction or a multiplication by a small constant,
    two for a full multiplication. *)

module C = Spec.Curve25519

let lim : pos = pow2 33 - 1

let felem (s: Seq.seq nat) : prop = Seq.length s == nl /\ ble s lim

let fev (s: Seq.seq nat) : GTot C.elem = C.prime_gt_one (); eval s % prime

let ble_mono (s: Seq.seq nat) (c c': nat)
  : Lemma (requires ble s c /\ c <= c') (ensures ble s c') = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"

(** {3 Addition} *)

let fadd_spec (a b: Seq.seq nat) : Seq.seq nat = carry_pass (addw a b)

let fadd_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fadd_spec a b) /\ fev (fadd_spec a b) == C.fadd (fev a) (fev b))
  = addw_ble a b lim lim;
    addw_len a b;
    carry_pass_len (addw a b);
    carry_pass_ble (addw a b) (2 * lim) 4;
    assert_norm (2 * lim + 4 < base * 5);
    assert_norm (base - 1 + 38 * ((2 * lim + 4) / base) <= lim);
    ble_mono (carry_pass (addw a b)) (base - 1 + 38 * ((2 * lim + 4) / base)) lim;
    carry_pass_mod (addw a b);
    eval_addw a b;
    Math.lemma_mod_add_distr (eval a % prime) (eval b) prime;
    Math.lemma_mod_add_distr (eval b) (eval a) prime

let cancel (x y v: nat)
  : Lemma (requires x < prime /\ y < prime /\ v < prime /\
                    (x + v) % prime == (y + v) % prime)
          (ensures x == y)
  = Math.lemma_div_mod (x + v) prime;
    Math.lemma_div_mod (y + v) prime;
    div_le_of_lt (x + v) prime 1;
    div_le_of_lt (y + v) prime 1

let sub_mod_lemma (x a b: nat)
  : Lemma (requires x + b == a + 8 * prime)
          (ensures x % prime == C.fsub (a % prime) (b % prime))
  = C.prime_gt_one ();
    let u = a % prime in
    let v = b % prime in
    let y = C.fsub u v in
    Math.lemma_mod_plus a 8 prime;
    Math.lemma_mod_add_distr b x prime;
    Math.lemma_mod_add_distr (x % prime) b prime;
    assert ((x % prime + v) % prime == u);
    Math.lemma_mod_add_distr v (u + prime - v) prime;
    Math.lemma_mod_plus u 1 prime;
    assert ((y + v) % prime == u);
    cancel (x % prime) y v

(** {3 Subtraction}

    [eightp] dominates every limb of the subtrahend, so the difference is
    taken limb by limb without a borrow and without leaving the naturals. *)

let subw (a b: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun k -> if vat b k <= vat eightp k then vat a k + vat eightp k - vat b k else 0)

let subw_ok (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ ble a lim /\ Seq.length b == nl /\ ble b lim)
          (ensures eval (subw a b) + eval b == eval a + 8 * prime /\
                   ble (subw a b) (lim + 4 * (base - 1)))
  = eightp_ok ();
    assert (ble twop (base - 1));
    assert (forall (i: nat). i < nl ==> Seq.index eightp i == 4 * Seq.index twop i);
    Seq.lemma_eq_intro (addw (subw a b) b) (addw a eightp);
    eval_addw (subw a b) b;
    eval_addw a eightp

let fsub_spec (a b: Seq.seq nat) : Seq.seq nat = carry_pass (subw a b)

let fsub_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fsub_spec a b) /\ fev (fsub_spec a b) == C.fsub (fev a) (fev b))
  = subw_ok a b;
    carry_pass_len (subw a b);
    carry_pass_ble (subw a b) (lim + 4 * (base - 1)) 6;
    assert_norm (lim + 4 * (base - 1) + 6 < base * 7);
    assert_norm (base - 1 + 38 * ((lim + 4 * (base - 1) + 6) / base) <= lim);
    ble_mono (carry_pass (subw a b)) (base - 1 + 38 * ((lim + 4 * (base - 1) + 6) / base)) lim;
    carry_pass_mod (subw a b);
    sub_mod_lemma (eval (subw a b)) (eval a) (eval b)

(** {3 One carry pass, packaged}

    Every operation below is a few applications of this: from a bound [c] on
    the limbs, one pass leaves them under [c'], and the value is unchanged
    modulo the prime.  The witness [d] is the carry bound; the caller picks
    it, and [assert_norm] checks the two arithmetic side conditions. *)
let pass (s: Seq.seq nat) (c d c': nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1) /\
                    base - 1 + 38 * ((c + d) / base) <= c')
          (ensures Seq.length (carry_pass s) == nl /\ ble (carry_pass s) c' /\
                   eval (carry_pass s) % prime == eval s % prime)
  = carry_pass_len s;
    carry_pass_ble s c d;
    carry_pass_mod s

(** {3 Multiplication} *)

let fmul_spec (a b: Seq.seq nat) : Seq.seq nat =
  carry_pass (carry_pass (fold38 (part a b nl)))

let fold_mod (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw)
          (ensures eval (fold38 c) % prime == eval c % prime)
  = fold_ok c;
    Math.paren_mul_right 2 prime (eval (Seq.slice c nl nw));
    Math.swap_mul 2 prime;
    Math.paren_mul_right 2 (eval (Seq.slice c nl nw)) prime;
    Math.lemma_mod_plus (eval (fold38 c)) (2 * eval (Seq.slice c nl nw)) prime

let fmul_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fmul_spec a b) /\ fev (fmul_spec a b) == C.fmul (fev a) (fev b))
  = part_ble a b lim lim nl;
    part_len a b nl;
    let p = part a b nl in
    assert_norm (39 * (nl * (lim * lim)) <= pow2 75);
    fold_ble p (nl * (lim * lim));
    ble_mono (fold38 p) (39 * (nl * (lim * lim))) (pow2 75);
    let f = fold38 p in
    assert_norm (pow2 75 + (pow2 43 + pow2 28) < base * (pow2 43 + pow2 28 + 1));
    assert_norm (base - 1 + 38 * ((pow2 75 + (pow2 43 + pow2 28)) / base) <= pow2 49);
    pass f (pow2 75) (pow2 43 + pow2 28) (pow2 49);
    let g = carry_pass f in
    assert_norm (pow2 49 + (pow2 17 + pow2 2) < base * (pow2 17 + pow2 2 + 1));
    assert_norm (base - 1 + 38 * ((pow2 49 + (pow2 17 + pow2 2)) / base) <= lim);
    pass g (pow2 49) (pow2 17 + pow2 2) lim;
    fold_mod p;
    mul_ok a b;
    Math.lemma_mod_mul_distr_l (eval a) (eval b) prime;
    Math.lemma_mod_mul_distr_r (eval a % prime) (eval b) prime

(** {3 Multiplication by a small constant} *)

let fscale_spec (m: nat) (a: Seq.seq nat) : Seq.seq nat =
  carry_pass (scale m a)

let fscale_spec_ok (m: nat) (a: Seq.seq nat)
  : Lemma (requires felem a /\ m <= 121665)
          (ensures felem (fscale_spec m a) /\
                   fev (fscale_spec m a) == (m * eval a) % prime)
  = let s = scale m a in
    let aux (i: nat { i < nl }) : Lemma (Seq.index s i <= 121665 * lim) =
      Math.lemma_mult_le_left m (Seq.index a i) lim;
      Math.lemma_mult_le_right lim m 121665 in
    Classical.forall_intro aux;
    assert (ble s (121665 * lim));
    assert_norm (121665 * lim <= pow2 50);
    ble_mono s (121665 * lim) (pow2 50);
    assert_norm (pow2 50 + (pow2 18 + pow2 3) < base * (pow2 18 + pow2 3 + 1));
    assert_norm (base - 1 + 38 * ((pow2 50 + (pow2 18 + pow2 3)) / base) <= lim);
    pass s (pow2 50) (pow2 18 + pow2 3) lim;
    eval_scale m a


(** {3 Freezing}

    Reducing to the unique representative below the prime, which is what
    the caller sees on the way out.  The shape of the argument shrinks in
    four steps: from limbs under [2^33] to a genuine base-[2^32] number
    below [2^256], then two subtractions of the prime bring it below
    [2^255], and one conditional subtraction finishes. *)

let shaped (s: Seq.seq nat) (c0: nat) : prop =
  Seq.length s == nl /\ vat s 0 <= c0 /\
  (forall (k: nat). 0 < k /\ k < nl ==> vat s k < base)

let shaped_ble (s: Seq.seq nat) (c0: nat)
  : Lemma (requires shaped s c0 /\ base - 1 <= c0) (ensures ble s c0) = ()

let eval_shaped (s: Seq.seq nat) (c0: nat)
  : Lemma (requires shaped s c0) (ensures eval s <= c0 + pow2 256 - base)
  = let t = Seq.slice s 1 nl in
    let aux (i: nat { i < nl - 1 }) : Lemma (Seq.index t i < base) =
      Seq.lemma_index_slice s 1 nl i;
      assert (vat s (i + 1) < base) in
    Classical.forall_intro aux;
    assert (bnd t base);
    eval_bnd t;
    assert_norm (rad * (nl - 1) == 224);
    Math.lemma_mult_le_left base (eval t + 1) (pow2 224);
    Math.pow2_plus rad 224

(** One step: carry the whole number, then fold the overflow back in with
    the reduction constant, since [2^256 = 2 * prime + 38]. *)
let fstep (s: Seq.seq nat) : Seq.seq nat =
  let r = carry_low s in
  if Seq.length r = nl then Seq.upd r 0 (vat r 0 + 38 * carry_out s) else r

let fstep_val (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (fstep s) == eval (carry_low s) + 38 * carry_out s /\
                   eval (fstep s) % prime == eval s % prime)
  = carry_low_len s;
    carry_split_ok s;
    let r = carry_low s in
    let t = carry_out s in
    eval_upd r 0 (Seq.index r 0 + 38 * t);
    assert_norm (pow2 256 == 2 * prime + 38);
    Math.distributivity_add_left (2 * prime) 38 t;
    Math.paren_mul_right 2 prime t;
    Math.swap_mul 2 prime;
    Math.paren_mul_right 2 t prime;
    Math.lemma_mod_plus (eval (fstep s)) (2 * t) prime

let fstep_ok (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures shaped (fstep s) (base - 1 + 38 * d) /\
                   eval (fstep s) % prime == eval s % prime)
  = fstep_val s;
    carry_low_len s;
    carry_split_bnd s c d;
    Math.lemma_mult_le_right 38 (carry_out s) d

(** A pass leaves a shaped number: every limb but the lowest is a proper
    base-[2^32] digit, and the lowest has absorbed the wrap-around. *)
let carry_pass_shaped (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures shaped (carry_pass s) (base - 1 + 38 * ((c + d) / base)))
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    Math.lemma_div_le (Seq.index (carry_run s (nl - 1)) (nl - 1)) (c + d) base

(** [fstep] is nothing but [carry_pass] written the other way round: the
    wrap-around of the top limb and the fold of the overflow are the same
    multiplication by [38]. *)
let fstep_is_pass (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures fstep s == carry_pass s)
  = carry_run_len s (nl - 1);
    Seq.lemma_eq_intro (fstep s) (carry_pass s)

(** The last step lands inside base [2^32]: either nothing overflowed, or
    the overflow was one and what remained was tiny. *)
let fstep_last (s: Seq.seq nat)
  : Lemma (requires shaped s 4294967333)
          (ensures Seq.length (fstep s) == nl /\ bnd (fstep s) base /\
                   eval (fstep s) < pow2 256 /\
                   eval (fstep s) % prime == eval s % prime)
  = shaped_ble s 4294967333;
    assert_norm (4294967333 + 1 < base * 2);
    fstep_val s;
    carry_low_len s;
    carry_split_bnd s 4294967333 1;
    carry_split_ok s;
    eval_shaped s 4294967333;
    assert_norm (4294967333 + pow2 256 - base == pow2 256 + 37);
    let r = carry_low s in
    if carry_out s = 0 then begin
      Seq.lemma_eq_intro (fstep s) r;
      eval_bnd r;
      assert_norm (rad * nl == 256)
    end else begin
      assert (carry_out s == 1);
      assert (eval s == eval r + pow2 256);
      assert (eval r <= 37);
      assert (Seq.index r 0 <= eval r);
      assert (eval (fstep s) == eval r + 38);
      Math.pow2_lt_compat 256 7;
      assert_norm (pow2 7 == 128);
      assert (eval (fstep s) < pow2 256);
      assert (bnd (fstep s) base);
      ()
    end

let freeze_a (s: Seq.seq nat) : Seq.seq nat = fstep (fstep (fstep (fstep s)))

let freeze_a_ok (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures Seq.length (freeze_a s) == nl /\ bnd (freeze_a s) base /\
                   eval (freeze_a s) < pow2 256 /\
                   eval (freeze_a s) % prime == eval s % prime)
  = assert_norm (lim + 2 < base * 3);
    fstep_ok s lim 2;
    let x1 = fstep s in
    assert_norm (base - 1 + 38 * 2 == 4294967371);
    shaped_ble x1 4294967371;
    assert_norm (4294967371 + 1 < base * 2);
    fstep_ok x1 4294967371 1;
    let x2 = fstep x1 in
    assert_norm (base - 1 + 38 * 1 == 4294967333);
    shaped_ble x2 4294967333;
    fstep_ok x2 4294967333 1;
    fstep_last (fstep x2)

(** Four passes, which is what the implementation actually runs, together
    with the bound each one has to be given. *)
let freeze_a_alt (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures freeze_a s == carry_pass (carry_pass (carry_pass (carry_pass s))))
  = fstep_is_pass s;
    carry_pass_len s;
    fstep_is_pass (carry_pass s);
    carry_pass_len (carry_pass s);
    fstep_is_pass (carry_pass (carry_pass s));
    carry_pass_len (carry_pass (carry_pass s));
    fstep_is_pass (carry_pass (carry_pass (carry_pass s)))

let freeze_a_bounds (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures (let x1 = carry_pass s in
                    let x2 = carry_pass x1 in
                    let x3 = carry_pass x2 in
                    Seq.length x1 == nl /\ ble x1 4294967371 /\
                    Seq.length x2 == nl /\ ble x2 4294967333 /\
                    Seq.length x3 == nl /\ ble x3 4294967333))
  = assert_norm (lim + 2 < base * 3);
    assert_norm (base - 1 + 38 * ((lim + 2) / base) == 4294967371);
    pass s lim 2 4294967371;
    let x1 = carry_pass s in
    assert_norm (4294967371 + 1 < base * 2);
    assert_norm (base - 1 + 38 * ((4294967371 + 1) / base) == 4294967333);
    pass x1 4294967371 1 4294967333;
    let x2 = carry_pass x1 in
    assert_norm (4294967333 + 1 < base * 2);
    assert_norm (base - 1 + 38 * ((4294967333 + 1) / base) == 4294967333);
    pass x2 4294967333 1 4294967333

(** {3 Subtracting the prime once} *)

let red255 (s: Seq.seq nat) : Seq.seq nat = carry_low (fold255 s)

let hi255_bit (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures hi255 s == eval s / pow2 255)
  = eval_bnd s;
    assert_norm (rad * nl == 256);
    assert_norm (rad * (nl - 1) == 224);
    Math.lemma_div_lt (eval s) 256 224;
    eval_digit s (nl - 1);
    Math.small_mod (eval s / pow2 224) base;
    Math.division_multiplication_lemma (eval s) (pow2 224) (pow2 31);
    Math.pow2_plus 224 31

let red255_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures Seq.length (red255 s) == nl /\ bnd (red255 s) base /\
                   eval (red255 s) == eval s - prime * (eval s / pow2 255))
  = hi255_bit s;
    fold255_ok s;
    let f = fold255 s in
    assert (Seq.length f == nl);
    assert (ble f (base + 18));
    assert_norm (base + 18 + 1 < base * 2);
    eval_bnd s;
    assert_norm (rad * nl == 256);
    carry_out_zero f;
    carry_split_ok f;
    carry_split_bnd f (base + 18) 1;
    carry_low_len f

let freeze_b (s: Seq.seq nat) : Seq.seq nat = red255 (red255 s)

let freeze_b_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ eval s < pow2 256)
          (ensures Seq.length (freeze_b s) == nl /\ bnd (freeze_b s) base /\
                   eval (freeze_b s) < pow2 255 /\
                   eval (freeze_b s) % prime == eval s % prime)
  = red255_ok s;
    let y = red255 s in
    red255_ok y;
    assert_norm (pow2 255 == prime + 19);
    assert_norm (pow2 256 == 2 * pow2 255);
    assert_norm (pow2 1 == 2);
    Math.pow2_lt_compat 255 6;
    assert_norm (pow2 6 == 64);
    let q0 = eval s / pow2 255 in
    let q1 = eval y / pow2 255 in
    Math.lemma_div_lt_nat (eval s) 256 255;
    Math.lemma_div_mod (eval s) (pow2 255);
    if q0 = 0 then assert (eval y == eval s) else assert (eval y == eval s - prime);
    assert (eval y < pow2 255 + 19);
    Math.lemma_div_lt_nat (eval y) 256 255;
    Math.lemma_div_mod (eval y) (pow2 255);
    Math.swap_mul prime q0;
    Math.swap_mul prime q1;
    Math.lemma_mod_sub (eval s) prime q0;
    Math.lemma_mod_sub (eval y) prime q1;
    if q1 = 0 then begin
      assert (eval (freeze_b s) == eval y);
      assert (eval (freeze_b s) < pow2 255)
    end else begin
      assert (eval (freeze_b s) == eval y - prime);
      assert (eval (freeze_b s) < pow2 255)
    end

(** {3 The conditional last subtraction} *)

let add19 (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then Seq.upd s 0 (vat s 0 + 19) else s

let freeze_w (y: Seq.seq nat) : Seq.seq nat = carry_low (add19 y)

let freeze_spec (s: Seq.seq nat) : Seq.seq nat =
  let y = freeze_b (freeze_a s) in
  let w = freeze_w y in
  if hi255 w = 1 then mask255 w else y

let freeze_w_ok (y: Seq.seq nat)
  : Lemma (requires Seq.length y == nl /\ bnd y base /\ eval y < pow2 255)
          (ensures Seq.length (freeze_w y) == nl /\ bnd (freeze_w y) base /\
                   hi255 (freeze_w y) <= 1)
  = let a = add19 y in
    assert (ble a (base + 18));
    assert_norm (base + 18 + 1 < base * 2);
    assert_norm (pow2 255 == prime + 19);
    assert_norm (pow2 256 == 2 * pow2 255);
    eval_upd y 0 (Seq.index y 0 + 19);
    assert_norm (pow2 (rad * 0) == 1);
    carry_out_zero a;
    carry_split_ok a;
    carry_split_bnd a (base + 18) 1;
    carry_low_len a;
    hi255_bit (carry_low a);
    Math.lemma_div_lt_nat (eval (carry_low a)) 256 255;
    assert_norm (pow2 1 == 2)

let freeze_spec_ok (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures Seq.length (freeze_spec s) == nl /\ bnd (freeze_spec s) base /\
                   eval (freeze_spec s) == eval s % prime)
  = freeze_a_ok s;
    freeze_b_ok (freeze_a s);
    let y = freeze_b (freeze_a s) in
    let a = add19 y in
    assert (Seq.length a == nl);
    assert (ble a (base + 18));
    assert_norm (base + 18 + 1 < base * 2);
    eval_upd y 0 (Seq.index y 0 + 19);
    assert_norm (pow2 (rad * 0) == 1);
    assert_norm (pow2 255 == prime + 19);
    assert_norm (pow2 256 == 2 * pow2 255);
    carry_out_zero a;
    carry_split_ok a;
    carry_split_bnd a (base + 18) 1;
    carry_low_len a;
    let w = freeze_w y in
    hi255_bit w;
    Math.lemma_div_lt_nat (eval w) 256 255;
    if hi255 w = 1 then begin
      mask255_ok w;
      Math.lemma_mod_sub (eval w) (pow2 255) 1;
      Math.small_mod (eval w - pow2 255) (pow2 255);
      Math.lemma_mod_sub (eval y) prime 1;
      Math.small_mod (eval y - prime) prime
    end else
      Math.small_mod (eval y) prime

#pop-options

