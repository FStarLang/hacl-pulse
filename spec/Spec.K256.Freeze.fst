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

(** Reducing a lazy field element to its canonical representative.

    Every other operation on the radix-52 field leaves a number that is
    congruent to the right answer and has limbs below [2^53]; this is the
    one that produces the representative below the prime, and it is the
    only place the modulus is compared against rather than folded through.
    Only [fstore] and the equality tests need it.

    At radix [2^51] this is nearly free: five proper digits already put a
    number below [2^255], which is [prime + 19], so one conditional
    subtraction finishes the job.  Here five proper digits only put it
    below [2^260], which is {e sixteen} primes above the modulus, and the
    tail is correspondingly longer:

    - one carry chain, which leaves limbs zero to three proper and the top
      limb below [2^53];
    - a fold of everything above bit 256 -- that is, of the top limb's top
      five bits -- back into limb zero against [cf1 = 2^32 + 977], which
      is the constant for [2^256] rather than the [cf] for [2^260];
    - a second carry chain, after which the top limb is at most [2^48];
    - and only then the conditional subtraction, which has to fire both
      when the top limb reached [2^48] exactly and when the number is
      below [2^256] but still at or above the prime.

    That last step is libsecp256k1's, and the two conditions are handled
    by one branch: adding [cf1] and masking the top limb back to
    forty-eight bits subtracts exactly one prime in both cases.

    The arithmetic here is stated with literal weights rather than with
    [pow2].  Z3 sees [pow2 104 * x] as a nonlinear product and
    [20282409603651670423947251286016 * x] as a linear one, and the
    comparison against the prime is a lexicographic argument over four
    limbs that is trivial for the linear solver and hopeless for the
    nonlinear one.  {!ev5} is the bridge. *)
module Spec.K256.Freeze

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical

include Spec.K256.Columns

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

(** {2 The modulus at bit 256}

    [cf] folds bit [260] because the representation is five fifty-two-bit
    limbs; [cf1] folds bit [256] because the {e number} is two hundred and
    fifty-six bits.  They differ by the factor of sixteen between the two,
    and this is the only place the second one is needed. *)

let hib : (n: pos { n == pow2 48 }) =
  assert_norm (pow2 48 == 281474976710656); 281474976710656

let cf1 : (n: pos { n == pow2 32 + 977 }) =
  assert_norm (pow2 32 + 977 == 4294968273); 4294968273

let one_prime (_: unit) : Lemma (pow2 256 == prime + cf1) =
  assert_norm (pow2 256 == (pow2 256 - pow2 32 - 977) + pow2 32 + 977)

(** {2 The five limbs, weighed by literals} *)

let w1 : pos = 4503599627370496
let w2 : pos = 20282409603651670423947251286016
let w3 : pos = 91343852333181432387730302044767688728495783936
let w4 : pos = 411376139330301510538742295639337626245683966408394965837152256

#push-options "--fuel 8 --ifuel 8 --z3rlimit 400"

let ev5 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval s == vat s 0 + w1 * vat s 1 + w2 * vat s 2 +
                             w3 * vat s 3 + w4 * vat s 4)
  = assert_norm (nl == 5);
    let t1 = Seq.slice s 1 5 in
    let t2 = Seq.slice s 2 5 in
    let t3 = Seq.slice s 3 5 in
    let t4 = Seq.slice s 4 5 in
    Seq.lemma_eq_intro (Seq.slice t1 1 4) t2;
    Seq.lemma_eq_intro (Seq.slice t2 1 3) t3;
    Seq.lemma_eq_intro (Seq.slice t3 1 2) t4;
    assert (eval t4 == vat s 4);
    assert (eval t3 == vat s 3 + base * eval t4);
    assert (eval t2 == vat s 2 + base * eval t3);
    assert (eval t1 == vat s 1 + base * eval t2);
    assert (eval s == vat s 0 + base * eval t1);
    Math.distributivity_add_right base (vat s 3) (base * vat s 4);
    Math.paren_mul_right base base (vat s 4);
    Math.distributivity_add_right base (vat s 2) (base * vat s 3 + base * (base * vat s 4));
    Math.distributivity_add_right base (base * vat s 3) (base * (base * vat s 4));
    Math.paren_mul_right base base (vat s 3);
    Math.paren_mul_right base (base * base) (vat s 4);
    Math.distributivity_add_right base (vat s 1)
      (base * vat s 2 + (base * base) * vat s 3 + (base * (base * base)) * vat s 4);
    Math.distributivity_add_right base (base * vat s 2)
      ((base * base) * vat s 3 + (base * (base * base)) * vat s 4);
    Math.distributivity_add_right base ((base * base) * vat s 3)
      ((base * (base * base)) * vat s 4);
    Math.paren_mul_right base base (vat s 2);
    Math.paren_mul_right base (base * base) (vat s 3);
    Math.paren_mul_right base (base * (base * base)) (vat s 4);
    assert_norm (base * base == w2);
    assert_norm (base * (base * base) == w3);
    assert_norm (base * (base * (base * base)) == w4);
    assert_norm (base == w1)

#pop-options

(** {2 Folding bit 256 down}

    The twin of [Spec.K256.Field52.carry_top], one power of two lower:
    that one moves what sits above bit [260] and pays sixteen primes for
    it, this one moves what sits above bit [256] and pays one. *)

let top48 (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then
    Seq.upd (Seq.upd s (nl - 1) (vat s (nl - 1) % hib)) 0
            (vat s 0 + cf1 * (vat s (nl - 1) / hib))
  else s

let top48_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (top48 s) == nl) = ()

let top48_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (top48 s) + prime * (Seq.index s (nl - 1) / hib) == eval s)
  = let q = Seq.index s (nl - 1) / hib in
    let s1 = Seq.upd s (nl - 1) (Seq.index s (nl - 1) % hib) in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % hib);
    eval_upd s1 0 (Seq.index s 0 + cf1 * q);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) hib;
    assert (rad * (nl - 1) == 208);
    Math.pow2_plus 208 48;
    Math.distributivity_add_right (pow2 208) (Seq.index s (nl - 1) % hib) (hib * q);
    Math.paren_mul_right (pow2 208) hib q;
    one_prime ();
    Math.distributivity_add_left prime cf1 q

(** {2 The three steps before the comparison} *)

let step1 (s: Seq.seq nat) : Seq.seq nat = carry_run s (nl - 1)
let step2 (s: Seq.seq nat) : Seq.seq nat = top48 (step1 s)
let step3 (s: Seq.seq nat) : Seq.seq nat = carry_run (step2 s) (nl - 1)

(** After the first chain: four proper digits and a top limb that has
    taken on at most two units of carry. *)
let step1_ble (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures Seq.length (step1 s) == nl /\ eval (step1 s) == eval s /\
                   (forall (i: nat). i < nl - 1 ==> vat (step1 s) i < base) /\
                   vat (step1 s) (nl - 1) <= lim + 2)
  = assert_norm (nl == 5);
    assert_norm (lim + 2 < base * 3);
    carry_run_chained s lim 2 (nl - 1);
    carry_run_len s (nl - 1);
    carry_run_ok s (nl - 1)

(** After the fold: the top limb is short, and limb zero has taken on at
    most thirty-two units of [cf1]. *)
let step2_ble (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures Seq.length (step2 s) == nl /\
                   eval (step2 s) % prime == eval s % prime /\
                   vat (step2 s) 0 <= base - 1 + 32 * cf1 /\
                   (forall (i: nat). 0 < i /\ i < nl - 1 ==> vat (step2 s) i < base) /\
                   vat (step2 s) (nl - 1) < hib)
  = assert_norm (nl == 5);
    step1_ble s;
    let r = step1 s in
    assert_norm (lim + 2 < hib * 33);
    div_le_of_lt (lim + 2) hib 32;
    Math.lemma_div_le (vat r (nl - 1)) (lim + 2) hib;
    Math.lemma_mult_le_right cf1 (vat r (nl - 1) / hib) 32;
    top48_ok r;
    top48_len r;
    Math.swap_mul prime (Seq.index r (nl - 1) / hib);
    Math.lemma_mod_plus (eval (top48 r)) (Seq.index r (nl - 1) / hib) prime

let four_digits (q: Seq.seq nat)
  : Lemma (requires vat q 0 < base /\ vat q 1 < base /\ vat q 2 < base /\ vat q 3 < base)
          (ensures forall (i: nat). i < nl - 1 ==> vat q i < base)
  = assert_norm (nl == 5)

(** After the second chain: four proper digits and a top limb that is at
    most [2^48].  It can be [2^48] exactly -- the fold leaves a little
    more than [2^256] behind -- which is what the conditional subtraction
    is for. *)
let step3_ble (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures Seq.length (step3 s) == nl /\
                   eval (step3 s) % prime == eval s % prime /\
                   (forall (i: nat). i < nl - 1 ==> vat (step3 s) i < base) /\
                   vat (step3 s) (nl - 1) <= hib)
  = assert_norm (nl == 5);
    step2_ble s;
    let r = step2 s in
    assert_norm (base - 1 + 32 * cf1 < base * 2);
    run4 r;
    Math.lemma_div_le (vat r 0) (base - 1 + 32 * cf1) base;
    div_le_of_lt (base - 1 + 32 * cf1) base 1;
    carry_run_len r (nl - 1);
    carry_run_ok r (nl - 1);
    let q = step3 s in
    assert (vat q 0 < base /\ vat q 1 < base /\ vat q 2 < base /\ vat q 3 < base);
    four_digits q

#pop-options

(** {2 The conditional subtraction}

    Two conditions, one branch.  The number is at or above the prime
    either because the second chain pushed the top limb up to [2^48] -- in
    which case it is at or above [2^256] and certainly above the prime --
    or because it is below [2^256] and still no smaller than the prime,
    which at this width means the top limb is [2^48 - 1], the three in the
    middle are full, and limb zero has reached [pl0].

    Adding [cf1] to limb zero, carrying, and masking the top limb back to
    forty-eight bits subtracts exactly one prime in both cases: the carry
    reaches the top limb in the second case precisely because the middle
    limbs are full, and in the first case the top limb was already there.
    [2^48] times limb four's weight is [2^256], which is [prime + cf1], so
    what the mask removes and what the addition put in differ by the
    modulus. *)

#push-options "--fuel 1 --ifuel 2 --z3rlimit 300"

(** The shape the three steps leave behind, and the only precondition the
    tail has. *)
let proper (s: Seq.seq nat) : prop =
  Seq.length s == nl /\
  (forall (i: nat). i < nl - 1 ==> vat s i < base) /\ vat s (nl - 1) <= hib

let over (s: Seq.seq nat) : bool =
  (vat s (nl - 1) >= hib) ||
  (vat s (nl - 1) = hib - 1 && vat s 3 = base - 1 && vat s 2 = base - 1 &&
   vat s 1 = base - 1 && vat s 0 >= pl0)

let bump (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then Seq.upd s 0 (vat s 0 + cf1) else s

let fin (s: Seq.seq nat) : Seq.seq nat =
  let t = if over s then carry_run (bump s) (nl - 1) else s in
  if Seq.length t = nl then Seq.upd t (nl - 1) (vat t (nl - 1) % hib) else t

(** The prime, as the linear combination [ev5] produces. *)
let prime_lin (_: unit)
  : Lemma (prime == pl0 + w1 * (base - 1) + w2 * (base - 1) + w3 * (base - 1) +
                    w4 * (hib - 1))
  = assert_norm (prime == 4503595332402223 +
                   w1 * 4503599627370495 + w2 * 4503599627370495 +
                   w3 * 4503599627370495 + w4 * 281474976710655);
    assert_norm (pl0 == 4503595332402223);
    assert_norm (base - 1 == 4503599627370495);
    assert_norm (hib - 1 == 281474976710655)

(** Below the prime, and the tail does nothing. *)
let not_over_lt (s: Seq.seq nat)
  : Lemma (requires proper s /\ not (over s))
          (ensures fin s == s /\ eval s < prime)
  = assert_norm (nl == 5);
    Seq.lemma_eq_intro (Seq.upd s (nl - 1) (vat s (nl - 1) % hib)) s;
    ev5 s;
    prime_lin ();
    assert_norm (base == w1)

(** At or above the prime, and the tail subtracts exactly one. *)
let over_sub (s: Seq.seq nat)
  : Lemma (requires proper s /\ over s)
          (ensures proper (fin s) /\ vat (fin s) (nl - 1) <= 1 /\
                   eval (fin s) + prime == eval s /\ eval (fin s) < prime)
  = assert_norm (nl == 5);
    assert_norm (base - 1 + cf1 < base * 2);
    assert_norm (pl0 + cf1 == base);
    let b = bump s in
    run4 b;
    Math.lemma_div_le (vat b 0) (base - 1 + cf1) base;
    div_le_of_lt (base - 1 + cf1) base 1;
    let r = carry_run b (nl - 1) in
    carry_run_len b (nl - 1);
    carry_run_ok b (nl - 1);
    eval_upd s 0 (vat s 0 + cf1);
    assert (eval b == eval s + cf1);
    assert (vat r (nl - 1) >= hib);
    assert (vat r (nl - 1) <= hib + 1);
    Math.small_div (vat r (nl - 1) - hib) hib;
    Math.lemma_div_plus (vat r (nl - 1) - hib) 1 hib;
    Math.lemma_mod_plus (vat r (nl - 1) - hib) 1 hib;
    Math.small_mod (vat r (nl - 1) - hib) hib;
    eval_upd r (nl - 1) (vat r (nl - 1) % hib);
    assert (rad * (nl - 1) == 208);
    assert_norm (pow2 208 == w4);
    assert_norm (w4 * hib == pow2 256);
    one_prime ();
    Math.distributivity_sub_right w4 (vat r (nl - 1)) hib;
    ev5 (fin s);
    prime_lin ();
    assert_norm (base == w1)

#pop-options

(** {2 Freezing} *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"

let freeze_spec (s: Seq.seq nat) : Seq.seq nat = fin (step3 s)

let freeze_ok (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures felem (freeze_spec s) /\ proper (freeze_spec s) /\
                   vat (freeze_spec s) (nl - 1) < hib /\
                   eval (freeze_spec s) < prime /\
                   eval (freeze_spec s) == fev s)
  = assert_norm (nl == 5);
    assert_norm (hib <= lim);
    assert_norm (base - 1 <= lim);
    step3_ble s;
    let r = step3 s in
    assert (proper r);
    if over r then begin
      over_sub r;
      Math.lemma_mod_plus (eval (freeze_spec s)) 1 prime;
      Math.small_mod (eval (freeze_spec s)) prime
    end
    else begin
      not_over_lt r;
      Math.small_mod (eval (freeze_spec s)) prime
    end

#pop-options

(** {2 The shape the implementation runs}

    The code cannot branch on a secret, so it always adds [cf1 * x] and
    always carries, with [x] the zero-or-one the mask produced.  When [x]
    is zero both are no-ops -- the number is already made of proper digits
    -- which is what makes the branch-free form agree with {!fin}. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"

let carry_id (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\
                    (forall (i: nat). i < nl - 1 ==> vat s i < base))
          (ensures carry_run s (nl - 1) == s)
  = assert_norm (nl == 5);
    run4 s;
    carry_run_len s (nl - 1);
    Seq.lemma_eq_intro (carry_run s (nl - 1)) s

let finx (s: Seq.seq nat) (x: nat) : Seq.seq nat =
  if Seq.length s = nl then
    let t = carry_run (Seq.upd s 0 (vat s 0 + cf1 * x)) (nl - 1) in
    if Seq.length t = nl then Seq.upd t (nl - 1) (vat t (nl - 1) % hib) else t
  else s

let fin_uniform (s: Seq.seq nat) (x: nat)
  : Lemma (requires proper s /\ x == (if over s then 1 else 0))
          (ensures fin s == finx s x)
  = assert_norm (nl == 5);
    if over s then ()
    else begin
      Seq.lemma_eq_intro (Seq.upd s 0 (vat s 0 + cf1 * 0)) s;
      carry_id s
    end

#pop-options

(** {2 Canonical five-limb numbers}

    A [proper] sequence is bounded by [base] in every limb -- the top one
    only reaches [2^48] -- so it is the sequence of radix-[2^52] digits of
    its own value, and two proper sequences with the same value are the
    same sequence.  That is what turns a limb-by-limb comparison into a
    comparison of field elements, and it is the only thing [feq] needs
    beyond [freeze]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let proper_bnd (s: Seq.seq nat)
  : Lemma (requires proper s) (ensures bnd s base)
  = assert_norm (nl == 5);
    assert_norm (hib < base)

let proper_uniq (s t: Seq.seq nat)
  : Lemma (requires proper s /\ proper t /\ eval s == eval t)
          (ensures s == t)
  = proper_bnd s; proper_bnd t;
    let aux (k: nat { k < nl }) : Lemma (Seq.index s k == Seq.index t k) =
      eval_digit s k; eval_digit t k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s t

(** {2 Constants}

    A number below [2^256] written out in five limbs.  The precomputed
    curve constants are given this way, and [limbs_of_ok] is what says the
    literals in [Hacl.K256.Tables] denote the number they should. *)

let limbs_of (x: nat) : Seq.lseq nat nl =
  Seq.init #nat nl (fun i -> x / pow2 (rad * i) % base)

let limbs_of_ok (x: nat)
  : Lemma (requires x < pow2 256)
          (ensures eval (limbs_of x) == x /\ bnd (limbs_of x) base /\
                   ble (limbs_of x) lim)
  = assert_norm (rad * nl == 260);
    Math.pow2_le_compat 260 256;
    assert_norm (base - 1 <= lim);
    Seq.init_index nl (fun i -> x / pow2 (rad * i) % base);
    Spec.Bignum52.Window.eval_windows x (limbs_of x)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let limbs_index (x: nat) (k: nat { k < nl })
  : Lemma (Seq.index (limbs_of x) k == x / pow2 (rad * k) % base)
  = Seq.init_index nl (fun i -> x / pow2 (rad * i) % base)

#pop-options
