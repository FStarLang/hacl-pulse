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
(** A 256-bit number as four limbs of sixty-four bits, and everything true
    of that representation that does not mention a modulus.

    This is the arithmetic core shared by P-256 and secp256k1.  It is the
    same architecture as {!Spec.Bignum256} -- a schoolbook product held in
    unreduced columns, a carry chain, and the bounds bookkeeping around
    both -- at four times the radix and half the limb count, which is a
    quarter of the limb products.

    {b Why a product is split.}  A column of the schoolbook has to hold
    [nl] limb products.  At thirty-two bits that is eight products of just
    under [2^64], comfortably inside a hundred and twenty-eight; at
    sixty-four bits one product already fills a hundred and twenty-eight
    bits and four of them would need a hundred and thirty.

    So a product is not put in one column.  [a_i * b_j] is [plo] of it at
    column [i + j] and [phi] of it at column [i + j + 1], which is the same
    number -- [plo x + base * phi x == x] -- laid out so that no column ever
    holds more than [nl] halves below [base] and [nl] halves below [base].
    A column of a finished product is under [2^67], and the machine still
    gets both halves of a sixty-four by sixty-four multiply for the price of
    one instruction.

    Everything downstream is unchanged by the split, because everything
    downstream is stated with [eval] and [eval] cannot see it.

    {b No bytes here.}  {!Spec.Bignum256}'s little-endian byte layer is for
    Curve25519 and Ed25519 and stays with them.  P-256 and secp256k1
    serialise big-endian, which is {!Spec.Field4}'s business.

    Limbs are [nat] here, not machine words: every lemma is about the
    mathematical value, and the implementation separately shows its
    [Hacl.Secret.UInt64] limbs have these values. *)
module Spec.Bignum4

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module Loops = Hacl.Spec.Loops

(** Bits per limb, limbs per element, columns in a product.

    [nw] is [2 nl] rather than [2 nl - 1]: the top limb product puts its
    high half one column above where its low half went. *)
let rad : pos = 64
let nl : pos = 4
let nw : pos = 8

let base : pos = pow2 rad

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"

(** {2 Viewing a sequence as a number} *)

let rec eval (s: Seq.seq nat) : Tot nat (decreases Seq.length s) =
  let n = Seq.length s in
  if n = 0 then 0
  else Seq.index s 0 + base * eval (Seq.slice s 1 n)

let vat (s: Seq.seq nat) (i: nat) : nat =
  if i < Seq.length s then Seq.index s i else 0

let eval_empty (s: Seq.seq nat) : Lemma (requires Seq.length s == 0) (ensures eval s == 0) = ()

(** Cutting a number in two: the low [k] limbs weigh [2^(rad k)] less than
    the rest. *)
let rec eval_split (s: Seq.seq nat) (k: nat { k <= Seq.length s })
  : Lemma (ensures eval s == eval (Seq.slice s 0 k) +
                             pow2 (rad * k) * eval (Seq.slice s k (Seq.length s)))
          (decreases k)
  = let n = Seq.length s in
    if k = 0 then Seq.lemma_eq_intro (Seq.slice s 0 n) s
    else begin
      let t = Seq.slice s 1 n in
      eval_split t (k - 1);
      Seq.lemma_eq_intro (Seq.slice t 0 (k - 1)) (Seq.slice (Seq.slice s 0 k) 1 k);
      Seq.lemma_eq_intro (Seq.slice t (k - 1) (n - 1)) (Seq.slice s k n);
      Math.pow2_plus rad (rad * (k - 1));
      Math.distributivity_add_right base (eval (Seq.slice t 0 (k - 1)))
        (pow2 (rad * (k - 1)) * eval (Seq.slice s k n));
      Math.paren_mul_right base (pow2 (rad * (k - 1))) (eval (Seq.slice s k n))
    end

let rec eval_zeros (s: Seq.seq nat)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> Seq.index s i == 0)
          (ensures eval s == 0)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let t = Seq.slice s 1 n in
      assert (forall (i: nat). i < n - 1 ==> Seq.index t i == Seq.index s (i + 1));
      eval_zeros t
    end

(** Appending a limb on the right adds its weighted value. *)
let eval_snoc (s: Seq.seq nat) (j: nat { j < Seq.length s })
  : Lemma (eval (Seq.slice s 0 (j + 1)) ==
           eval (Seq.slice s 0 j) + pow2 (rad * j) * Seq.index s j)
  = let p = Seq.slice s 0 (j + 1) in
    eval_split p j;
    Seq.lemma_eq_intro (Seq.slice p 0 j) (Seq.slice s 0 j);
    Seq.lemma_eq_intro (Seq.slice p j (j + 1)) (Seq.create 1 (Seq.index s j));
    assert (eval (Seq.slice p j (j + 1)) == Seq.index s j)

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

(** {2 The two halves of a product}

    [plo] and [phi] are the two words a sixty-four by sixty-four multiply
    returns.  Nothing below cares that they came from a multiply; all that
    is used is that they put the number back together. *)

let plo (x: nat) : nat = x % base
let phi (x: nat) : nat = x / base

let split_ok (x: nat) : Lemma (plo x + base * phi x == x)
  = Math.euclidean_division_definition x base

let plo_lt (x: nat) : Lemma (plo x < base) = ()

(** A half is a proper limb whenever the product came from proper limbs. *)
let phi_le (x: nat) (c: nat)
  : Lemma (requires x <= c * c /\ c < base) (ensures phi x <= c)
  = Math.lemma_div_le x (c * c) base;
    Math.lemma_mult_le_right c c (base - 1);
    if c * c / base > c then Math.lemma_mult_le_right base (c + 1) (c * c / base)

(** Interleaving two sequences of the same length, the second weighing one
    limb more: this is what the split does to a whole row. *)
let rec eval_lohi (x y: Seq.seq nat)
  : Lemma (requires Seq.length x == Seq.length y)
          (ensures eval (Seq.init #nat (Seq.length x)
                           (fun j -> Seq.index x j + base * Seq.index y j)) ==
                   eval x + base * eval y)
          (decreases Seq.length x)
  = let n = Seq.length x in
    let z = Seq.init #nat n (fun j -> Seq.index x j + base * Seq.index y j) in
    if n = 0 then ()
    else begin
      let x' = Seq.slice x 1 n in
      let y' = Seq.slice y 1 n in
      let zt = Seq.slice z 1 n in
      Seq.lemma_eq_intro zt
        (Seq.init #nat (Seq.length x') (fun j -> Seq.index x' j + base * Seq.index y' j));
      eval_lohi x' y';
      assert (Seq.length z == n);
      assert (eval z == Seq.index z 0 + base * eval zt);
      assert (Seq.index z 0 == Seq.index x 0 + base * Seq.index y 0);
      assert (eval zt == eval x' + base * eval y');
      assert (eval x == Seq.index x 0 + base * eval x');
      assert (eval y == Seq.index y 0 + base * eval y');
      Math.distributivity_add_right base (eval x') (base * eval y');
      Math.distributivity_add_right base (Seq.index y 0) (base * eval y');
      assert (eval z == eval x + base * eval y);
      Seq.lemma_eq_intro z (Seq.init #nat (Seq.length x)
                              (fun j -> Seq.index x j + base * Seq.index y j))
    end

(** {2 A row: one multiplier against a whole number}

    [srow n u b i j] is [u] times the first [j] limbs of [b], laid out in an
    [n]-column accumulator starting at column [i].  Each product contributes
    twice: its low half at column [i + j'] and its high half at column
    [i + j' + 1].  The implementation's inner loop adds one product at a
    time, so it needs the [j]-indexed family and not just the complete row.

    Both the schoolbook product and the Montgomery reduction are rows in
    this sense -- the first with [u = a_i] and the second with [u] the digit
    that kills a limb -- so the whole of the split lives here. *)

let srow (n: nat) (u: nat) (b: Seq.seq nat) (i j: nat) : Seq.seq nat =
  Seq.init #nat n (fun k ->
    (if i <= k && k - i < j then plo (u * vat b (k - i)) else 0) +
    (if i + 1 <= k && k - i - 1 < j then phi (u * vat b (k - i - 1)) else 0))

let srow_len (n: nat) (u: nat) (b: Seq.seq nat) (i j: nat)
  : Lemma (Seq.length (srow n u b i j) == n) = ()

(** Adding the [j]-th product touches two columns, both additively: column
    [i + j] already holds the high half of the previous product. *)
let srow_step (n: nat) (u: nat) (b: Seq.seq nat) (i: nat) (j: nat { i + j + 1 < n })
  : Lemma (srow n u b i (j + 1) ==
           Seq.upd (Seq.upd (srow n u b i j) (i + j)
                      (Seq.index (srow n u b i j) (i + j) + plo (u * vat b j)))
                   (i + j + 1)
                   (Seq.index (srow n u b i j) (i + j + 1) + phi (u * vat b j)))
  = Seq.lemma_eq_intro (srow n u b i (j + 1))
      (Seq.upd (Seq.upd (srow n u b i j) (i + j)
                  (Seq.index (srow n u b i j) (i + j) + plo (u * vat b j)))
               (i + j + 1)
               (Seq.index (srow n u b i j) (i + j + 1) + phi (u * vat b j)))

let srow_zero (n: nat) (u: nat) (b: Seq.seq nat) (i: nat)
  : Lemma (srow n u b i 0 == Seq.create n 0)
  = Seq.lemma_eq_intro (srow n u b i 0) (Seq.create n 0)

(** The two halves of a row, before they are put in their columns. *)
let slomap (u: nat) (b: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun j -> plo (u * vat b j))

let shimap (u: nat) (b: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun j -> phi (u * vat b j))

let slomap_ok (u: nat) (b: Seq.seq nat)
  : Lemma (requires Seq.length b == nl)
          (ensures eval (slomap u b) + base * eval (shimap u b) == u * eval b)
  = let l = slomap u b in
    let h = shimap u b in
    eval_lohi l h;
    let comb = Seq.init #nat (Seq.length l)
                 (fun j -> Seq.index l j + base * Seq.index h j) in
    let aux (j: nat { j < nl })
      : Lemma (Seq.index comb j == Seq.index (scale u b) j)
      = split_ok (u * vat b j) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro comb (scale u b);
    eval_scale u b

(** The low halves and the high halves, each shifted into place.  Named
    separately so that the proof below works on small terms. *)

let lorowf (n: nat) (u: nat) (b: Seq.seq nat) (i: nat) : Seq.seq nat =
  Seq.init #nat n (fun k -> if i <= k && k - i < nl then plo (u * vat b (k - i)) else 0)

let hirowf (n: nat) (u: nat) (b: Seq.seq nat) (i: nat) : Seq.seq nat =
  Seq.init #nat n (fun k -> if i + 1 <= k && k - i - 1 < nl
                            then phi (u * vat b (k - i - 1)) else 0)

let srow_split (n: nat) (u: nat) (b: Seq.seq nat) (i: nat)
  : Lemma (srow n u b i nl == addw (lorowf n u b i) (hirowf n u b i))
  = Seq.lemma_eq_intro (srow n u b i nl) (addw (lorowf n u b i) (hirowf n u b i))

let slorow_eval (n: nat) (u: nat) (b: Seq.seq nat) (i: nat { i + nl <= n })
  : Lemma (requires Seq.length b == nl)
          (ensures eval (lorowf n u b i) == pow2 (rad * i) * eval (slomap u b))
  = let r = lorowf n u b i in
    eval_split r i;
    eval_zeros (Seq.slice r 0 i);
    let suf = Seq.slice r i n in
    eval_pad suf nl;
    Seq.lemma_eq_intro (Seq.slice suf 0 nl) (slomap u b)

let shirow_eval (n: nat) (u: nat) (b: Seq.seq nat) (i: nat { i + nl + 1 <= n })
  : Lemma (requires Seq.length b == nl)
          (ensures eval (hirowf n u b i) == pow2 (rad * (i + 1)) * eval (shimap u b))
  = let r = hirowf n u b i in
    eval_split r (i + 1);
    eval_zeros (Seq.slice r 0 (i + 1));
    let suf = Seq.slice r (i + 1) n in
    eval_pad suf nl;
    Seq.lemma_eq_intro (Seq.slice suf 0 nl) (shimap u b)

(** Shifting the high halves one column up is multiplying them by the
    base, which is exactly what [slomap_ok] undoes. *)
let srow_arith (i lo hi: nat)
  : Lemma (pow2 (rad * i) * lo + pow2 (rad * (i + 1)) * hi ==
           pow2 (rad * i) * (lo + base * hi))
  = Math.distributivity_add_right (pow2 (rad * i)) lo (base * hi);
    Math.paren_mul_right (pow2 (rad * i)) base hi;
    assert (rad * (i + 1) == rad * i + rad);
    Math.pow2_plus (rad * i) rad

let eval_srow (n: nat) (u: nat) (b: Seq.seq nat) (i: nat { i + nl + 1 <= n })
  : Lemma (requires Seq.length b == nl)
          (ensures eval (srow n u b i nl) == pow2 (rad * i) * (u * eval b))
  = srow_split n u b i;
    eval_addw (lorowf n u b i) (hirowf n u b i);
    slorow_eval n u b i;
    shirow_eval n u b i;
    slomap_ok u b;
    srow_arith i (eval (slomap u b)) (eval (shimap u b))

(** {2 One limb of the left operand}

    The schoolbook's row is a [srow] whose multiplier is a limb of [a]. *)

let rowj (a b: Seq.seq nat) (i j: nat) : Seq.seq nat = srow nw (vat a i) b i j

let row (a b: Seq.seq nat) (i: nat) : Seq.seq nat = rowj a b i nl

let rowj_step (a b: Seq.seq nat) (i: nat) (j: nat { i + j + 1 < nw })
  : Lemma (rowj a b i (j + 1) ==
           Seq.upd (Seq.upd (rowj a b i j) (i + j)
                      (Seq.index (rowj a b i j) (i + j) + plo (vat a i * vat b j)))
                   (i + j + 1)
                   (Seq.index (rowj a b i j) (i + j + 1) + phi (vat a i * vat b j)))
  = srow_step nw (vat a i) b i j

let eval_row (a b: Seq.seq nat) (i: nat { i < nl })
  : Lemma (requires Seq.length b == nl)
          (ensures eval (row a b i) == vat a i * (pow2 (rad * i) * eval b))
  = eval_srow nw (vat a i) b i;
    Math.paren_mul_right (pow2 (rad * i)) (vat a i) (eval b);
    Math.swap_mul (pow2 (rad * i)) (vat a i);
    Math.paren_mul_right (vat a i) (pow2 (rad * i)) (eval b)

(** {2 The schoolbook product} *)

let mul_step (a b: Seq.seq nat) (i: nat) (acc: Seq.seq nat) : Seq.seq nat =
  addw acc (row a b i)

let zerow : Seq.seq nat = Seq.create nw 0

let part (a b: Seq.seq nat) (i: nat) : Seq.seq nat =
  Loops.repeati i (mul_step a b) zerow

let rec part_len (a b: Seq.seq nat) (i: nat)
  : Lemma (ensures Seq.length (part a b i) == nw) (decreases i)
  = if i = 0 then () else part_len a b (i - 1)

(** [part a b i] is the product of [b] by the low [i] limbs of [a]. *)
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

(** {2 Bounds on the product}

    [bnd] is strict because that is what a machine-integer bound looks like;
    for the accumulator a non-strict bound composes better.  A column of a
    row holds one low half and one high half, and both are proper limbs, so
    a row is bounded by twice a limb and a whole product by [2 nl] of
    them. *)
let ble (s: Seq.seq nat) (c: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i <= c

let vat_ble (s: Seq.seq nat) (c: nat) (i: nat)
  : Lemma (requires ble s c) (ensures vat s i <= c) = ()

let scale_ble (c: nat) (x: Seq.seq nat) (cx: nat)
  : Lemma (requires ble x cx) (ensures ble (scale c x) (c * cx))
  = let aux (i: nat { i < Seq.length x }) : Lemma (Seq.index (scale c x) i <= c * cx) =
      Math.lemma_mult_le_left c (Seq.index x i) cx in
    Classical.forall_intro aux

(** A column holds one low half and one high half, and both are proper
    limbs. *)
let srow_ble (n: nat) (u: nat) (b: Seq.seq nat) (i j: nat)
  : Lemma (requires u <= base - 1 /\ ble b (base - 1))
          (ensures ble (srow n u b i j) (2 * (base - 1)))
  = let aux (k: nat { k < n }) : Lemma (Seq.index (srow n u b i j) k <= 2 * (base - 1)) =
      if i + 1 <= k && k - i - 1 < j then begin
        Math.lemma_mult_le_left u (vat b (k - i - 1)) (base - 1);
        Math.lemma_mult_le_right (base - 1) u (base - 1);
        phi_le (u * vat b (k - i - 1)) (base - 1)
      end else () in
    Classical.forall_intro aux

let rowj_ble (a b: Seq.seq nat) (i j: nat)
  : Lemma (requires ble a (base - 1) /\ ble b (base - 1))
          (ensures ble (rowj a b i j) (2 * (base - 1)))
  = srow_ble nw (vat a i) b i j

let rec part_ble (a b: Seq.seq nat) (i: nat)
  : Lemma (requires ble a (base - 1) /\ ble b (base - 1))
          (ensures ble (part a b i) (i * (2 * (base - 1))))
          (decreases i)
  = if i = 0 then ()
    else begin
      part_ble a b (i - 1);
      part_len a b (i - 1);
      rowj_ble a b (i - 1) nl;
      Math.distributivity_add_left (i - 1) 1 (2 * (base - 1))
    end

(** {2 The carry chain} *)

(** [eval] in terms of the limb at [k] and the two pieces around it. *)
let eval_at (s: Seq.seq nat) (k: nat { k < Seq.length s })
  : Lemma (eval s == eval (Seq.slice s 0 k) +
                     pow2 (rad * k) * (Seq.index s k +
                                       base * eval (Seq.slice s (k + 1) (Seq.length s))))
  = let n = Seq.length s in
    eval_split s k;
    Seq.lemma_eq_intro (Seq.slice (Seq.slice s k n) 1 (n - k)) (Seq.slice s (k + 1) n)

(** Additive, so that everything stays a [nat]. *)
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

(** Move the top of limb [k] into limb [k + 1].  Total on every [k] so that
    it can be handed to [repeati] unrefined. *)
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

(** A whole pass: limbs [0] to [k - 1] carry into their neighbour. *)
let carry_run (s: Seq.seq nat) (k: nat) : Seq.seq nat = Loops.repeati k carry_step s

let rec carry_run_len (s: Seq.seq nat) (k: nat)
  : Lemma (ensures Seq.length (carry_run s k) == Seq.length s) (decreases k)
  = if k = 0 then () else carry_run_len s (k - 1)

let rec carry_run_ok (s: Seq.seq nat) (k: nat)
  : Lemma (ensures eval (carry_run s k) == eval s) (decreases k)
  = if k = 0 then ()
    else (carry_run_ok s (k - 1); carry_step_ok (k - 1) (carry_run s (k - 1)))

(** The invariant of the chain: everything below [k] is a proper limb, [k]
    itself has absorbed a carry, and everything above is untouched. *)
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
(** {2 Reading a limb off the number}

    What the store loop needs: with every limb a proper one, limb [k] is
    digit [k] of the value in base [2^64]. *)
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

(** {2 Splitting off the top carry}

    [carry_pass] folds the carry out of the top limb back down, which is what
    an arithmetic operation wants.  The final reduction wants the carry
    itself, so that it can decide how many primes to subtract. *)

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
          (ensures eval s == eval (carry_low s) + pow2 256 * carry_out s)
  = carry_run_len s (nl - 1);
    carry_run_ok s (nl - 1);
    let r = carry_run s (nl - 1) in
    eval_upd r (nl - 1) (Seq.index r (nl - 1) % base);
    Math.euclidean_division_definition (Seq.index r (nl - 1)) base;
    Math.pow2_plus (rad * (nl - 1)) rad;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index r (nl - 1) % base) (base * (Seq.index r (nl - 1) / base));
    Math.paren_mul_right (pow2 (rad * (nl - 1))) base (Seq.index r (nl - 1) / base);
    assert (rad * nl == 256)

let carry_split_bnd (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures bnd (carry_low s) base /\ carry_out s <= d)
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    Math.lemma_div_le (Seq.index (carry_run s (nl - 1)) (nl - 1)) (c + d) base;
    div_le_of_lt (c + d) base d

let carry_out_zero (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ eval s < pow2 256)
          (ensures carry_out s == 0)
  = carry_split_ok s


(** {2 What the loops need}

    Small lemmas stated in exactly the shape the implementation's invariants
    take, so that no arithmetic happens inside a Pulse block. *)

let addw_ble (x y: Seq.seq nat) (cx cy: nat)
  : Lemma (requires ble x cx /\ ble y cy) (ensures ble (addw x y) (cx + cy)) = ()

let addw_len (x y: Seq.seq nat)
  : Lemma (Seq.length (addw x y) == Seq.length x) = ()

(** Adding the [j]-th product of row [i] to the accumulator is two updates,
    the low half at column [i + j] and the high half at column [i + j + 1].
    Both are additive: neither column is known to be zero, because the
    previous product left its high half in the first of them. *)
(** {3 Accumulating a row}

    The implementation never builds a row on its own: it adds one product
    at a time into an accumulator that already holds something.  These are
    the three facts that loop needs -- that it starts where it started,
    that one product is two column updates, and that a column has not grown
    by more than one low half and one high half. *)

let addw_srow_zero (x: Seq.seq nat) (n: nat) (u: nat) (b: Seq.seq nat) (i: nat)
  : Lemma (requires Seq.length x == n) (ensures addw x (srow n u b i 0) == x)
  = srow_zero n u b i;
    Seq.lemma_eq_intro (addw x (srow n u b i 0)) x

let addw_srow_step (x: Seq.seq nat) (n: nat) (u: nat) (b: Seq.seq nat)
                   (i: nat) (j: nat { i + j + 1 < n })
  : Lemma (requires Seq.length x == n)
          (ensures (let y = addw x (srow n u b i j) in
                    addw x (srow n u b i (j + 1)) ==
                    Seq.upd (Seq.upd y (i + j)
                               (Seq.index y (i + j) + plo (u * vat b j)))
                            (i + j + 1)
                            (Seq.index y (i + j + 1) + phi (u * vat b j))))
  = let y = addw x (srow n u b i j) in
    Seq.lemma_eq_intro (addw x (srow n u b i (j + 1)))
      (Seq.upd (Seq.upd y (i + j) (Seq.index y (i + j) + plo (u * vat b j)))
               (i + j + 1) (Seq.index y (i + j + 1) + phi (u * vat b j)))

let addw_srow_ble (x b: Seq.seq nat) (n u i j c: nat)
  : Lemma (requires Seq.length x == n /\ ble x c /\ u <= base - 1 /\ ble b (base - 1))
          (ensures ble (addw x (srow n u b i j)) (c + 2 * (base - 1)))
  = srow_ble n u b i j;
    addw_ble x (srow n u b i j) c (2 * (base - 1))

let addw_rowj_step (x a b: Seq.seq nat) (i: nat) (j: nat { i + j + 1 < nw })
  : Lemma (requires Seq.length x == nw)
          (ensures (let y = addw x (rowj a b i j) in
                    addw x (rowj a b i (j + 1)) ==
                    Seq.upd (Seq.upd y (i + j)
                               (Seq.index y (i + j) + plo (vat a i * vat b j)))
                            (i + j + 1)
                            (Seq.index y (i + j + 1) + phi (vat a i * vat b j))))
  = let y = addw x (rowj a b i j) in
    Seq.lemma_eq_intro (addw x (rowj a b i (j + 1)))
      (Seq.upd (Seq.upd y (i + j) (Seq.index y (i + j) + plo (vat a i * vat b j)))
               (i + j + 1) (Seq.index y (i + j + 1) + phi (vat a i * vat b j)))

let part_step (a b: Seq.seq nat) (i: nat)
  : Lemma (part a b (i + 1) == addw (part a b i) (row a b i)) = ()

let rowj_zero (a b: Seq.seq nat) (i: nat)
  : Lemma (rowj a b i 0 == zerow)
  = srow_zero nw (vat a i) b i

(** {2 An all-ones number}

    The largest value the representation holds, which is what a
    subtraction has to dominate and what a mask produces. *)

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
#pop-options
