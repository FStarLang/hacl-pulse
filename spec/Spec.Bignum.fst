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

(** A number of any length, as limbs of thirty-two bits.

    This is the specification side of the arbitrary-precision bignum: what
    it means for a sequence of limbs to denote a number, and the six or
    seven facts about that meaning which the implementation loops need.

    {b Why thirty-two bits.}  The product of two limbs plus two more limbs
    is at most [(2^32-1)^2 + 2*(2^32-1) = 2^64 - 1], so a schoolbook inner
    step is exact in a [uint64] with not one bit to spare.  That is the
    largest radix with that property, and it is the reason the limb type is
    [Hacl.Secret.UInt32] and the accumulator type [Hacl.Secret.UInt64].
    (Custard has no [uint128], so radix 2^64 is not on the table; see
    {!Spec.Bignum256}, which makes the opposite trade for the curves, where
    the length is known and the reduction matters more than the memory.)

    {b Everything here is relational.}  There is deliberately no [add_spec]
    returning a sequence.  An implementation of addition says

    {[ eval vres + carry * pow2 (32 * n) == eval va + eval vb ]}

    which is the whole contract, is what a caller wants to hear, and needs
    no lemma connecting it to a second definition of addition.  So this
    module defines exactly one function on sequences -- [eval] -- and the
    operations appear only in the postconditions of the code.

    Limbs are [nat], not machine words: {!Hacl.Impl.Limb32.vals} is what
    turns an array of [Hacl.Secret.UInt32] into a sequence of [nat], and
    every statement below is about the mathematical value. *)
module Spec.Bignum

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

(** Bits per limb. *)
let rad : pos = 32

let base : pos = pow2 rad

(** The weight of limb [k].  Spelled out rather than written [pow2 (rad *
    k)] at every use, because the two forms do not match syntactically and
    Pulse's resource matcher is syntactic. *)
let wt (k: nat) : pos = pow2 (rad * k)

let wt_zero () : Lemma (wt 0 == 1) = ()

let wt_succ (k: nat) : Lemma (wt (k + 1) == base * wt k) =
  Math.pow2_plus rad (rad * k)

let wt_add (i j: nat) : Lemma (wt i * wt j == wt (i + j)) =
  Math.pow2_plus (rad * i) (rad * j)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 Viewing a sequence as a number}

    Limb zero is least significant, which is the convention of every
    bignum in the library and of the C API. *)

let rec eval (s: Seq.seq nat) : Tot nat (decreases Seq.length s) =
  let n = Seq.length s in
  if n = 0 then 0
  else Seq.index s 0 + base * eval (Seq.slice s 1 n)

(** Limb [i], or zero past the end.  Lets a short sequence be read at the
    indices of a longer one without a case split at every use. *)
let vat (s: Seq.seq nat) (i: nat) : nat =
  if i < Seq.length s then Seq.index s i else 0

let eval_empty (s: Seq.seq nat) : Lemma (requires Seq.length s == 0) (ensures eval s == 0) = ()

(** Cutting a number in two.  Almost everything below is a corollary. *)
let rec eval_split (s: Seq.seq nat) (k: nat { k <= Seq.length s })
  : Lemma (ensures eval s == eval (Seq.slice s 0 k) +
                             wt k * eval (Seq.slice s k (Seq.length s)))
          (decreases k)
  = let n = Seq.length s in
    if k = 0 then Seq.lemma_eq_intro (Seq.slice s 0 n) s
    else begin
      let t = Seq.slice s 1 n in
      let p = Seq.slice s 0 k in
      eval_split t (k - 1);
      Seq.lemma_eq_intro (Seq.slice t 0 (k - 1)) (Seq.slice p 1 k);
      Seq.lemma_eq_intro (Seq.slice t (k - 1) (n - 1)) (Seq.slice s k n);
      assert (eval p == Seq.index s 0 + base * eval (Seq.slice t 0 (k - 1)));
      assert (eval s == Seq.index s 0 + base * eval t);
      Math.pow2_plus rad (rad * (k - 1));
      Math.paren_mul_right base (wt (k - 1)) (eval (Seq.slice s k n))
    end

let rec eval_zeros (s: Seq.seq nat)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> Seq.index s i == 0)
          (ensures eval s == 0)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      assert (forall (i: nat). i < n - 1 ==> Seq.index (Seq.slice s 1 n) i == Seq.index s (i + 1));
      eval_zeros (Seq.slice s 1 n)
    end

(** The step of every loop that walks a bignum from the bottom: one more
    limb weighs [wt j]. *)
let eval_snoc (s: Seq.seq nat) (j: nat { j < Seq.length s })
  : Lemma (eval (Seq.slice s 0 (j + 1)) ==
           eval (Seq.slice s 0 j) + wt j * Seq.index s j)
  = eval_split (Seq.slice s 0 (j + 1)) j;
    Seq.lemma_eq_intro (Seq.slice (Seq.slice s 0 (j + 1)) 0 j) (Seq.slice s 0 j);
    let one = Seq.slice (Seq.slice s 0 (j + 1)) j (j + 1) in
    assert (Seq.length one == 1);
    assert (Seq.index one 0 == Seq.index s j);
    eval_zeros (Seq.slice one 1 1);
    assert (eval one == Seq.index s j)

(** Zeros on the top do not count. *)
let eval_pad (s: Seq.seq nat) (k: nat { k <= Seq.length s })
  : Lemma (requires forall (i: nat). k <= i /\ i < Seq.length s ==> Seq.index s i == 0)
          (ensures eval s == eval (Seq.slice s 0 k))
  = eval_split s k;
    eval_zeros (Seq.slice s k (Seq.length s))

let eval_full (s: Seq.seq nat)
  : Lemma (eval (Seq.slice s 0 (Seq.length s)) == eval s)
  = Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s

(** {2 Well-formedness}

    A limb sequence is {i normal} when every limb is a real limb.  This is
    the only invariant an array of [Hacl.Secret.UInt32] can violate, and it
    cannot: [vals] of a [uint32] array is normal by construction.  The
    predicate is still worth naming, because the statements below are about
    arbitrary [nat] sequences. *)

let bnd (s: Seq.seq nat) (c: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i < c

let norm (s: Seq.seq nat) : prop = bnd s base

(** A normal sequence of [n] limbs denotes a number below [base^n]: the
    representation is not redundant. *)
let rec eval_bnd (s: Seq.seq nat)
  : Lemma (requires norm s)
          (ensures eval s < wt (Seq.length s))
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let t = Seq.slice s 1 n in
      assert (norm t);
      eval_bnd t;
      Math.pow2_plus rad (rad * (n - 1));
      Math.lemma_mult_le_left base (eval t + 1) (wt (n - 1))
    end

let eval_bnd_prefix (s: Seq.seq nat) (k: nat { k <= Seq.length s })
  : Lemma (requires norm s) (ensures eval (Seq.slice s 0 k) < wt k)
  = eval_bnd (Seq.slice s 0 k)

(** {2 Reading and writing one limb} *)

let eval_at (s: Seq.seq nat) (k: nat { k < Seq.length s })
  : Lemma (eval s == eval (Seq.slice s 0 k) +
                     wt k * (Seq.index s k +
                             base * eval (Seq.slice s (k + 1) (Seq.length s))))
  = let n = Seq.length s in
    eval_split s k;
    Seq.lemma_eq_intro (Seq.slice (Seq.slice s k n) 1 (n - k)) (Seq.slice s (k + 1) n)

(** Additive, so that both sides stay a [nat] and no subtraction has to be
    justified at the use site. *)
let eval_upd (s: Seq.seq nat) (k: nat { k < Seq.length s }) (x: nat)
  : Lemma (eval (Seq.upd s k x) + wt k * Seq.index s k ==
           eval s + wt k * x)
  = let n = Seq.length s in
    let t = Seq.upd s k x in
    eval_at s k;
    eval_at t k;
    Seq.lemma_eq_intro (Seq.slice t 0 k) (Seq.slice s 0 k);
    Seq.lemma_eq_intro (Seq.slice t (k + 1) n) (Seq.slice s (k + 1) n);
    Math.distributivity_add_right (wt k) (Seq.index s k)
      (base * eval (Seq.slice s (k + 1) n));
    Math.distributivity_add_right (wt k) x
      (base * eval (Seq.slice s (k + 1) n))

(** Writing limb [k] does not disturb the number denoted by the limbs below
    it, which is what the accumulating loops need in order to keep their
    invariant about a prefix. *)
let eval_upd_above (s: Seq.seq nat) (k: nat { k < Seq.length s }) (x: nat)
                   (j: nat { j <= k })
  : Lemma (eval (Seq.slice (Seq.upd s k x) 0 j) == eval (Seq.slice s 0 j))
  = Seq.lemma_eq_intro (Seq.slice (Seq.upd s k x) 0 j) (Seq.slice s 0 j)

let eval_upd_below (s: Seq.seq nat) (k: nat { k < Seq.length s }) (x: nat)
                   (j: nat { k < j /\ j <= Seq.length s })
  : Lemma (eval (Seq.slice (Seq.upd s k x) 0 j) + wt k * Seq.index s k ==
           eval (Seq.slice s 0 j) + wt k * x)
  = Seq.lemma_eq_intro (Seq.slice (Seq.upd s k x) 0 j) (Seq.upd (Seq.slice s 0 j) k x);
    eval_upd (Seq.slice s 0 j) k x

(** {2 Comparison}

    The constant-time comparisons scan from the bottom and keep one mask.
    Their correctness is this lemma: for normal sequences, the ordering of
    the first [j+1] limbs is decided by limb [j], falling back on the first
    [j] limbs when limb [j] ties. *)

let eval_lt_snoc (a b: Seq.seq nat) (j: nat)
  : Lemma (requires norm a /\ norm b /\ j < Seq.length a /\ j < Seq.length b)
          (ensures (eval (Seq.slice a 0 (j + 1)) < eval (Seq.slice b 0 (j + 1))) <==>
                   (Seq.index a j < Seq.index b j \/
                    (Seq.index a j == Seq.index b j /\
                     eval (Seq.slice a 0 j) < eval (Seq.slice b 0 j))))
  = eval_snoc a j;
    eval_snoc b j;
    eval_bnd_prefix a j;
    eval_bnd_prefix b j;
    let wa = wt j * Seq.index a j in
    let wb = wt j * Seq.index b j in
    if Seq.index a j < Seq.index b j then begin
      Math.lemma_mult_le_left (wt j) (Seq.index a j + 1) (Seq.index b j);
      assert (wa + wt j <= wb)
    end else if Seq.index b j < Seq.index a j then begin
      Math.lemma_mult_le_left (wt j) (Seq.index b j + 1) (Seq.index a j);
      assert (wb + wt j <= wa)
    end else ()

(** Equality of numbers is equality of limbs, again because the
    representation is not redundant. *)
let rec eval_eq (a b: Seq.seq nat)
  : Lemma (requires norm a /\ norm b /\ Seq.length a == Seq.length b)
          (ensures (eval a == eval b) <==> Seq.equal a b)
          (decreases Seq.length a)
  = let n = Seq.length a in
    if n = 0 then Seq.lemma_eq_intro a b
    else begin
      let ta = Seq.slice a 1 n in
      let tb = Seq.slice b 1 n in
      eval_eq ta tb;
      if eval a = eval b then begin
        Math.lemma_mod_plus_distr_r (Seq.index a 0) (base * eval ta) base;
        Math.lemma_mod_plus_distr_r (Seq.index b 0) (base * eval tb) base;
        Math.multiple_modulo_lemma (eval ta) base;
        Math.multiple_modulo_lemma (eval tb) base;
        Math.small_mod (Seq.index a 0) base;
        Math.small_mod (Seq.index b 0) base;
        assert (Seq.index a 0 == Seq.index b 0);
        assert (Seq.equal ta tb);
        Seq.lemma_eq_intro a (Seq.cons (Seq.index a 0) ta);
        Seq.lemma_eq_intro b (Seq.cons (Seq.index b 0) tb);
        assert (forall (i: nat). i < n ==> Seq.index a i == Seq.index b i);
        Seq.lemma_eq_intro a b
      end else if Seq.equal a b then Seq.lemma_eq_elim a b
    end

(** {2 Modular addition and subtraction}

    [add_mod] adds, subtracts the modulus, and keeps whichever of the two
    results did not go negative.  Which one that is can be read off the
    borrow, and this is the arithmetic behind that. *)

let sum_mod_cases (x y m: nat)
  : Lemma (requires x < m /\ y < m)
          (ensures (if x + y < m then (x + y) % m == x + y
                                 else (x + y) % m == x + y - m))
  = if x + y < m then Math.small_mod (x + y) m
    else begin
      Math.lemma_mod_sub (x + y) m 1;
      Math.small_mod (x + y - m) m
    end

let diff_mod_cases (x y m: nat)
  : Lemma (requires x < m /\ y < m)
          (ensures (if y <= x then (x - y) % m == x - y
                              else (x - y) % m == x - y + m))
  = if y <= x then Math.small_mod (x - y) m
    else begin
      Math.lemma_mod_plus (x - y) 1 m;
      Math.small_mod (x - y + m) m
    end

#pop-options

(** {2 Powers}

    Exponentiation walks the exponent's bits from the top, squaring at every
    step and multiplying in the base when the bit is set.  These three
    lemmas are all the arithmetic that step needs. *)

#push-options "--fuel 1 --ifuel 1"

let rec pw (a: nat) (k: nat) : Tot nat (decreases k) =
  if k = 0 then 1 else a * pw a (k - 1)

let rec pw_add (a: nat) (m n: nat)
  : Lemma (ensures pw a (m + n) == pw a m * pw a n) (decreases m)
  = if m = 0 then ()
    else begin
      pw_add a (m - 1) n;
      Math.paren_mul_right a (pw a (m - 1)) (pw a n)
    end

(** One step down the exponent: the bits above position [i] are twice the
    bits above position [i+1], plus the bit at [i] itself. *)
let pw_step (a: nat) (e: nat) (b: nat { b < 2 })
  : Lemma (pw a (e + e + b) == (pw a e * pw a e) * (if b = 0 then 1 else a))
  = pw_add a e e;
    pw_add a (e + e) b

#pop-options
