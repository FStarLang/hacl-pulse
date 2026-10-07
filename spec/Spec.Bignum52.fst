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

(** Five limbs of fifty-two bits: the arithmetic that does not mention a
    prime.

    The radix-52 twin of {!Spec.Bignum51}, and word for word the same
    induction: the schoolbook product, the carry chain and the bounds
    bookkeeping on [Seq.seq nat].  As the header of that module says, the
    two are deliberately separate rather than one module parameterized by
    the radix, because everything downstream discharges its bounds with
    [assert_norm]s that do not mention [rad] symbolically.  This is the
    third copy of the argument and the last one worth making by hand.

    {b Why fifty-two bits, and why five limbs for a 256-bit prime.}
    secp256k1's prime is [2^256 - 2^32 - 977].  Four sixty-four-bit limbs
    hold it exactly, which is why the shared Montgomery core does; but a
    full limb leaves no room to accumulate, so every limb product has to be
    split into a low and a high column and added into two accumulators, and
    [Hacl_K256_Field_fmul] came out at four hundred and forty-seven
    instructions for sixteen multiplications.  Five fifty-two-bit limbs
    waste twenty bits of space and buy back all of that: a column of the
    schoolbook product is a sum of five products of numbers below [2^52],
    so it is below [2^106.4] and it simply accumulates, with no carry
    between limbs and no splitting, inside a [Hacl.Secret.UInt128].
    Twenty-five multiplications, each one [mul_wide] and one [add].

    Fifty-two rather than fifty-one or fifty-three is what makes the fold
    cheap.  [nl * rad] is [260], and

      [2^260 = 16 * 2^256 = 16 * (prime + 2^32 + 977) = 16 * prime + 2^36 + 15632],

    so [2^260] is congruent to [2^36 + 15632], a thirty-seven-bit constant.
    Folding the top four columns of a product down is therefore eight
    multiplications by a constant that fits in a word, with no carry chain
    between them -- see [Hacl.K256.Field52] for why the fold is split into
    a low and a high half of each column.  Fifty-three bits would make a
    column [2^108.4], still safe, but the fold constant would be [2^40]-ish
    and the top limb would no longer be reachable with one narrowing; fifty
    -one would need six limbs.

    Unlike the radix-51 case the top limb is a full fifty-two bits, so an
    element is below [2^260] rather than below the prime: this is a lazy
    representation, and nothing reduces to the canonical range until
    [freeze] is asked for it.  That is the whole point -- the ladder never
    asks. *)
module Spec.Bignum52

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module Classical = FStar.Classical

(** Bits per limb, limbs per element, columns in a product. *)
let rad : pos = 52
let nl : pos = 5
let nw : pos = 9

let base : pos = pow2 rad

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 Viewing a sequence as a number} *)

let rec eval (s: Seq.seq nat) : Tot nat (decreases Seq.length s) =
  let n = Seq.length s in
  if n = 0 then 0
  else Seq.index s 0 + base * eval (Seq.slice s 1 n)

let vat (s: Seq.seq nat) (i: nat) : nat =
  if i < Seq.length s then Seq.index s i else 0

let eval_empty (s: Seq.seq nat) : Lemma (requires Seq.length s == 0) (ensures eval s == 0) = ()

(** Cutting a number in two: the low [k] limbs weigh [2^(rad k)] less than
    the rest.  This one lemma gives the reduction, the carry chain and the
    row lemma below. *)
let rec eval_split (s: Seq.seq nat) (k: nat { k <= Seq.length s })
  : Lemma (ensures eval s == eval (Seq.slice s 0 k) +
                             pow2 (rad * k) * eval (Seq.slice s k (Seq.length s)))
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
      Math.paren_mul_right base (pow2 (rad * (k - 1))) (eval (Seq.slice s k n))
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

(** Appending a limb on the right adds its weighted value. *)
let eval_snoc (s: Seq.seq nat) (j: nat { j < Seq.length s })
  : Lemma (eval (Seq.slice s 0 (j + 1)) ==
           eval (Seq.slice s 0 j) + pow2 (rad * j) * Seq.index s j)
  = eval_split (Seq.slice s 0 (j + 1)) j;
    Seq.lemma_eq_intro (Seq.slice (Seq.slice s 0 (j + 1)) 0 j) (Seq.slice s 0 j);
    let one = Seq.slice (Seq.slice s 0 (j + 1)) j (j + 1) in
    assert (Seq.length one == 1);
    assert (Seq.index one 0 == Seq.index s j);
    eval_zeros (Seq.slice one 1 1);
    assert (eval one == Seq.index s j)

(** Zeros on the right do not change the value. *)
let eval_pad (s: Seq.seq nat) (k: nat { k <= Seq.length s })
  : Lemma (requires forall (i: nat). k <= i /\ i < Seq.length s ==> Seq.index s i == 0)
          (ensures eval s == eval (Seq.slice s 0 k))
  = eval_split s k;
    eval_zeros (Seq.slice s k (Seq.length s))

(** {2 Bounds} *)

let bnd (s: Seq.seq nat) (c: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i < c

let rec eval_bnd (s: Seq.seq nat)
  : Lemma (requires bnd s base)
          (ensures eval s < pow2 (rad * Seq.length s))
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let t = Seq.slice s 1 n in
      assert (bnd t base);
      eval_bnd t;
      Math.pow2_plus rad (rad * (n - 1));
      Math.lemma_mult_le_left base (eval t + 1) (pow2 (rad * (n - 1)))
    end

(** {2 Pointwise operations} *)

let addw (x y: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat (Seq.length x) (fun i -> Seq.index x i + vat y i)

let rec eval_addw (x y: Seq.seq nat)
  : Lemma (requires Seq.length y <= Seq.length x)
          (ensures eval (addw x y) == eval x + eval y)
          (decreases Seq.length x)
  = let n = Seq.length x in
    let m = Seq.length y in
    if n = 0 then ()
    else if m = 0 then Seq.lemma_eq_intro (addw x y) x
    else begin
      Seq.lemma_eq_intro (Seq.slice (addw x y) 1 n) (addw (Seq.slice x 1 n) (Seq.slice y 1 m));
      eval_addw (Seq.slice x 1 n) (Seq.slice y 1 m);
      Math.distributivity_add_right base (eval (Seq.slice x 1 n)) (eval (Seq.slice y 1 m))
    end

let scale (c: nat) (x: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat (Seq.length x) (fun i -> c * Seq.index x i)

let rec eval_scale (c: nat) (x: Seq.seq nat)
  : Lemma (ensures eval (scale c x) == c * eval x) (decreases Seq.length x)
  = let n = Seq.length x in
    if n = 0 then ()
    else begin
      Seq.lemma_eq_intro (Seq.slice (scale c x) 1 n) (scale c (Seq.slice x 1 n));
      eval_scale c (Seq.slice x 1 n);
      Math.distributivity_add_right c (Seq.index x 0) (base * eval (Seq.slice x 1 n));
      Math.paren_mul_right c base (eval (Seq.slice x 1 n));
      Math.paren_mul_right base c (eval (Seq.slice x 1 n))
    end

(** {2 One limb of the left operand}

    [rowj a b i j] is the contribution of [a_i] times the first [j] limbs of
    [b], laid out in a [nw]-column accumulator: it is zero everywhere except
    at columns [i] to [i + j - 1]. *)
let rowj (a b: Seq.seq nat) (i j: nat) : Seq.seq nat =
  Seq.init #nat nw (fun k -> if i <= k && k - i < j then vat a i * vat b (k - i) else 0)

let row (a b: Seq.seq nat) (i: nat) : Seq.seq nat = rowj a b i nl

let rowj_step (a b: Seq.seq nat) (i: nat) (j: nat { i + j < nw })
  : Lemma (rowj a b i (j + 1) ==
           Seq.upd (rowj a b i j) (i + j) (vat a i * vat b j))
  = Seq.lemma_eq_intro (rowj a b i (j + 1))
                       (Seq.upd (rowj a b i j) (i + j) (vat a i * vat b j))

let eval_row (a b: Seq.seq nat) (i: nat { i < nl })
  : Lemma (requires Seq.length b == nl)
          (ensures eval (row a b i) == vat a i * (pow2 (rad * i) * eval b))
  = let r = row a b i in
    eval_split r i;
    eval_zeros (Seq.slice r 0 i);
    let suf = Seq.slice r i nw in
    eval_pad suf nl;
    Seq.lemma_eq_intro (Seq.slice suf 0 nl) (scale (vat a i) b);
    eval_scale (vat a i) b

(** {2 The schoolbook product} *)

let mul_step (a b: Seq.seq nat) (i: nat) (acc: Seq.seq nat) : Seq.seq nat =
  addw acc (row a b i)

let zerow : Seq.seq nat = Seq.create nw 0

let part (a b: Seq.seq nat) (i: nat) : Seq.seq nat =
  Loops.repeati i (mul_step a b) zerow

let rec part_len (a b: Seq.seq nat) (i: nat)
  : Lemma (ensures Seq.length (part a b i) == nw) (decreases i)
  = if i = 0 then () else part_len a b (i - 1)

let rec eval_part (a b: Seq.seq nat) (i: nat { i <= nl })
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl)
          (ensures eval (part a b i) == eval (Seq.slice a 0 i) * eval b)
          (decreases i)
  = if i = 0 then (Seq.lemma_eq_intro (Seq.slice a 0 0) (Seq.empty #nat); eval_zeros zerow)
    else begin
      eval_part a b (i - 1);
      part_len a b (i - 1);
      eval_addw (part a b (i - 1)) (row a b (i - 1));
      eval_row a b (i - 1);
      eval_snoc a (i - 1);
      Math.distributivity_add_left (eval (Seq.slice a 0 (i - 1)))
                                   (pow2 (rad * (i - 1)) * Seq.index a (i - 1)) (eval b);
      Math.paren_mul_right (pow2 (rad * (i - 1))) (Seq.index a (i - 1)) (eval b);
      Math.paren_mul_right (Seq.index a (i - 1)) (pow2 (rad * (i - 1))) (eval b);
      Math.swap_mul (pow2 (rad * (i - 1))) (Seq.index a (i - 1))
    end

let mul_ok (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl)
          (ensures eval (part a b nl) == eval a * eval b)
  = eval_part a b nl;
    Seq.lemma_eq_intro (Seq.slice a 0 nl) a

(** {2 Bounds on the product} *)

let ble (s: Seq.seq nat) (c: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i <= c

let vat_ble (s: Seq.seq nat) (c: nat) (i: nat)
  : Lemma (requires ble s c) (ensures vat s i <= c) = ()

let scale_ble (c: nat) (x: Seq.seq nat) (cx: nat)
  : Lemma (requires ble x cx) (ensures ble (scale c x) (c * cx))
  = let aux (i: nat { i < Seq.length x }) : Lemma (Seq.index (scale c x) i <= c * cx) =
      Math.lemma_mult_le_left c (Seq.index x i) cx in
    Classical.forall_intro aux

let rowj_ble (a b: Seq.seq nat) (ca cb: nat) (i j: nat)
  : Lemma (requires ble a ca /\ ble b cb) (ensures ble (rowj a b i j) (ca * cb))
  = let aux (k: nat { k < nw }) : Lemma (Seq.index (rowj a b i j) k <= ca * cb) =
      if i <= k && k - i < j then Math.lemma_mult_le_left ca (vat b (k - i)) cb
      else () in
    Classical.forall_intro aux

let rec part_ble (a b: Seq.seq nat) (ca cb: nat) (i: nat)
  : Lemma (requires ble a ca /\ ble b cb)
          (ensures ble (part a b i) (i * (ca * cb)))
          (decreases i)
  = if i = 0 then ()
    else begin
      part_ble a b ca cb (i - 1);
      part_len a b (i - 1);
      rowj_ble a b ca cb (i - 1) nl;
      Math.distributivity_add_left (i - 1) 1 (ca * cb)
    end

(** {2 The carry chain} *)

let eval_at (s: Seq.seq nat) (k: nat { k < Seq.length s })
  : Lemma (eval s == eval (Seq.slice s 0 k) +
                     pow2 (rad * k) * (Seq.index s k +
                                       base * eval (Seq.slice s (k + 1) (Seq.length s))))
  = let n = Seq.length s in
    eval_split s k;
    Seq.lemma_eq_intro (Seq.slice (Seq.slice s k n) 1 (n - k)) (Seq.slice s (k + 1) n)

(** Additive, so that everything stays a [nat]. *)
let eval_ge (s: Seq.seq nat) (k: nat { k < Seq.length s })
  : Lemma (Seq.index s k <= eval s)
  = eval_at s k;
    Math.pow2_le_compat (rad * k) 0;
    assert_norm (pow2 0 == 1)

let eval_upd (s: Seq.seq nat) (k: nat { k < Seq.length s }) (x: nat)
  : Lemma (eval (Seq.upd s k x) + pow2 (rad * k) * Seq.index s k ==
           eval s + pow2 (rad * k) * x)
  = let n = Seq.length s in
    let t = Seq.upd s k x in
    eval_at s k;
    eval_at t k;
    Seq.lemma_eq_intro (Seq.slice t 0 k) (Seq.slice s 0 k);
    Seq.lemma_eq_intro (Seq.slice t (k + 1) n) (Seq.slice s (k + 1) n);
    Math.distributivity_add_right (pow2 (rad * k)) (Seq.index s k)
      (base * eval (Seq.slice s (k + 1) n));
    Math.distributivity_add_right (pow2 (rad * k)) x
      (base * eval (Seq.slice s (k + 1) n))

let carry_step (k: nat) (s: Seq.seq nat) : Seq.seq nat =
  if k + 1 < Seq.length s then
    Seq.upd (Seq.upd s k (vat s k % base)) (k + 1) (vat s (k + 1) + vat s k / base)
  else s

let carry_step_len (k: nat) (s: Seq.seq nat)
  : Lemma (Seq.length (carry_step k s) == Seq.length s) = ()

let carry_step_ok (k: nat) (s: Seq.seq nat)
  : Lemma (ensures eval (carry_step k s) == eval s)
  = if k + 1 < Seq.length s then begin
      let s1 = Seq.upd s k (Seq.index s k % base) in
      eval_upd s k (Seq.index s k % base);
      eval_upd s1 (k + 1) (Seq.index s (k + 1) + Seq.index s k / base);
      Math.pow2_plus (rad * k) rad;
      Math.euclidean_division_definition (Seq.index s k) base;
      Math.distributivity_add_right (pow2 (rad * (k + 1)))
        (Seq.index s (k + 1)) (Seq.index s k / base);
      Math.paren_mul_right (pow2 (rad * k)) base (Seq.index s k / base)
    end
    else ()

let carry_run (s: Seq.seq nat) (k: nat) : Seq.seq nat = Loops.repeati k carry_step s

let rec carry_run_len (s: Seq.seq nat) (k: nat)
  : Lemma (ensures Seq.length (carry_run s k) == Seq.length s) (decreases k)
  = if k = 0 then () else carry_run_len s (k - 1)

let rec carry_run_ok (s: Seq.seq nat) (k: nat)
  : Lemma (ensures eval (carry_run s k) == eval s) (decreases k)
  = if k = 0 then ()
    else (carry_run_ok s (k - 1); carry_step_ok (k - 1) (carry_run s (k - 1)))

let chained (s: Seq.seq nat) (c d: nat) (k: nat) : prop =
  (forall (i: nat). i < k /\ i < Seq.length s ==> Seq.index s i < base) /\
  (k < Seq.length s ==> Seq.index s k <= c + d) /\
  (forall (i: nat). k < i /\ i < Seq.length s ==> Seq.index s i <= c)

let div_le_of_lt (x: nat) (b: pos) (m: nat)
  : Lemma (requires x < b * (m + 1)) (ensures x / b <= m)
  = Math.lemma_div_mod x b;
    if x / b > m then Math.lemma_mult_le_right b (m + 1) (x / b)

let rec carry_run_chained (s: Seq.seq nat) (c d: nat) (k: nat)
  : Lemma (requires ble s c /\ c + d < base * (d + 1) /\ k < Seq.length s)
          (ensures chained (carry_run s k) c d k)
          (decreases k)
  = if k = 0 then ()
    else begin
      carry_run_chained s c d (k - 1);
      carry_run_len s (k - 1);
      let r = carry_run s (k - 1) in
      Math.lemma_div_le (Seq.index r (k - 1)) (c + d) base;
      div_le_of_lt (c + d) base d
    end

(** A run of [k] steps touches indices [0] through [k] and nothing above
    them, which is what lets a run be started on a sequence whose top limb
    is known to be zero and have that fact survive. *)
let rec carry_run_above (s: Seq.seq nat) (k: nat) (i: nat)
  : Lemma (requires k < i /\ i < Seq.length s)
          (ensures vat (carry_run s k) i == vat s i)
          (decreases k)
  = if k = 0 then ()
    else begin
      carry_run_above s (k - 1) i;
      carry_run_len s (k - 1)
    end

(** The carry that lands on a limb which started at zero.  {!carry_run_chained}
    bounds the limb the run stops on by [c + d] because it may have had [c]
    in it to begin with; when it began empty the bound is the incoming carry
    alone, and [d] is a great deal smaller than [c].  This is what makes a
    product's upper half fold: the four upper columns carry into a fifth
    limb that was not there, and that limb is the only thing the reduction
    constant has to multiply. *)
let carry_run_top (s: Seq.seq nat) (c d: nat) (k: pos)
  : Lemma (requires ble s c /\ c + d < base * (d + 1) /\
                    k < Seq.length s /\ Seq.index s k == 0)
          (ensures (let r = carry_run s k in
                    Seq.length r == Seq.length s /\
                    (forall (i: nat). i < k ==> vat r i < base) /\
                    vat r k <= d))
  = carry_run_chained s c d (k - 1);
    carry_run_len s (k - 1);
    carry_run_len s k;
    carry_run_above s (k - 1) k;
    let r = carry_run s (k - 1) in
    Math.lemma_div_le (Seq.index r (k - 1)) (c + d) base;
    div_le_of_lt (c + d) base d

(** {2 Reading a limb off the number} *)

let eval_digit (s: Seq.seq nat) (k: nat { k < Seq.length s })
  : Lemma (requires bnd s base)
          (ensures (eval s / pow2 (rad * k)) % base == Seq.index s k)
  = let n = Seq.length s in
    eval_at s k;
    let p = Seq.slice s 0 k in
    eval_bnd p;
    Math.lemma_div_plus (eval p) (Seq.index s k + base * eval (Seq.slice s (k + 1) n))
                        (pow2 (rad * k));
    Math.small_div (eval p) (pow2 (rad * k));
    Math.lemma_mod_plus (Seq.index s k) (eval (Seq.slice s (k + 1) n)) base;
    Math.small_mod (Seq.index s k) base

(** {2 Splitting off the top carry} *)

let carry_low (s: Seq.seq nat) : Seq.seq nat =
  let r = carry_run s (nl - 1) in
  if Seq.length r = nl then Seq.upd r (nl - 1) (vat r (nl - 1) % base) else r

let carry_out (s: Seq.seq nat) : nat =
  vat (carry_run s (nl - 1)) (nl - 1) / base

let carry_low_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (carry_low s) == nl)
  = carry_run_len s (nl - 1)

let carry_split_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval s == eval (carry_low s) + pow2 260 * carry_out s)
  = carry_run_len s (nl - 1);
    carry_run_ok s (nl - 1);
    let r = carry_run s (nl - 1) in
    eval_upd r (nl - 1) (Seq.index r (nl - 1) % base);
    Math.euclidean_division_definition (Seq.index r (nl - 1)) base;
    Math.pow2_plus (rad * (nl - 1)) rad;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index r (nl - 1) % base) (base * (Seq.index r (nl - 1) / base));
    Math.paren_mul_right (pow2 (rad * (nl - 1))) base (Seq.index r (nl - 1) / base);
    assert (rad * nl == 260)

let carry_split_bnd (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures bnd (carry_low s) base /\ carry_out s <= d)
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    Math.lemma_div_le (Seq.index (carry_run s (nl - 1)) (nl - 1)) (c + d) base;
    div_le_of_lt (c + d) base d

let carry_out_zero (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ eval s < pow2 260)
          (ensures carry_out s == 0)
  = carry_split_ok s

(** {2 An all-ones number} *)

let ones (n: nat) : Seq.seq nat = Seq.create n ((base - 1) <: nat)

let rec eval_ones (n: nat)
  : Lemma (ensures eval (ones n) == pow2 (rad * n) - 1) (decreases n)
  = if n = 0 then ()
    else begin
      Seq.lemma_eq_intro (Seq.slice (ones n) 1 n) (ones (n - 1));
      eval_ones (n - 1);
      Math.pow2_plus rad (rad * (n - 1));
      Math.distributivity_sub_right base (pow2 (rad * (n - 1))) 1
    end

(** {2 What the loops need} *)

let addw_ble (x y: Seq.seq nat) (cx cy: nat)
  : Lemma (requires ble x cx /\ ble y cy) (ensures ble (addw x y) (cx + cy)) = ()

let addw_len (x y: Seq.seq nat)
  : Lemma (Seq.length (addw x y) == Seq.length x) = ()

let addw_rowj_step (x a b: Seq.seq nat) (i: nat) (j: nat { i + j < nw })
  : Lemma (requires Seq.length x == nw)
          (ensures addw x (rowj a b i (j + 1)) ==
                   Seq.upd (addw x (rowj a b i j)) (i + j)
                           (Seq.index (addw x (rowj a b i j)) (i + j) + vat a i * vat b j))
  = Seq.lemma_eq_intro (addw x (rowj a b i (j + 1)))
      (Seq.upd (addw x (rowj a b i j)) (i + j)
               (Seq.index (addw x (rowj a b i j)) (i + j) + vat a i * vat b j))

let part_step (a b: Seq.seq nat) (i: nat)
  : Lemma (part a b (i + 1) == addw (part a b i) (row a b i)) = ()

let rowj_zero (a b: Seq.seq nat) (i: nat)
  : Lemma (rowj a b i 0 == zerow)
  = Seq.lemma_eq_intro (rowj a b i 0) zerow

#pop-options
