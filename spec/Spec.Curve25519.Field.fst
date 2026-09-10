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

(** The sixteen-limb representation of [Spec.Curve25519]'s field.

    An element is sixteen natural numbers standing for
    [a0 + a1 2^16 + ... + a15 2^240].  Nothing here is a machine integer:
    this module is the arithmetic, and [Hacl.Curve25519.Field] will be the
    same arithmetic on [Hacl.Secret.UInt64.t].

    {b Why sixteen bits.}  The textbook representation of this field is five
    limbs of fifty-one bits, whose products need a hundred-and-two-bit
    accumulator; that is why HACL* has both a [_51] field over
    [uint128] and a [_64] one over assembly.  Custard emits no
    hundred-and-twenty-eight-bit type, so the limb has to be small enough
    that a product and a column of products stay inside [uint64].  Sixteen is
    the choice that makes everything else free: a limb is exactly two bytes,
    so loading and storing a field element is a byte shuffle with no bit
    extraction, and [2^256 = 2 * prime + 38] means the reduction constant is
    the single digit [38].  A column of sixteen products of eighteen-bit
    limbs is under [2^40], and folding multiplies that by [38], so the widest
    intermediate is under [2^46] -- seventeen bits of headroom.

    The cost is that a multiplication is two hundred and fifty-six word
    multiplies rather than twenty-five.  That is the price of not having a
    hundred-and-twenty-eight-bit integer, and it is paid in the one place
    where this library is not competitive with HACL*.

    Everything below is stated on [Seq.seq nat] and proved by induction.  The
    alternative -- naming two hundred and fifty-six products and handing them
    to the ring tactic, as [Spec.Poly1305.Field] does for twenty-five -- does
    not scale, and the sequence formulation is also the one the
    implementation's loops need. *)
module Spec.Curve25519.Field

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module S8 = Hacl.Secret.UInt8

open Hacl.Spec.Bytes

let prime : pos = Spec.Curve25519.prime

(** Bits per limb, limbs per element, columns in a product. *)
let rad : pos = 16
let nl : pos = 16
let nw : pos = 31

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
    at columns [i] to [i + j - 1].  The implementation's inner loop adds one
    product at a time, so it needs the [j]-indexed family and not just the
    complete row. *)
let rowj (a b: Seq.seq nat) (i j: nat) : Seq.seq nat =
  Seq.init #nat nw (fun k -> if i <= k && k - i < j then vat a i * vat b (k - i) else 0)

let row (a b: Seq.seq nat) (i: nat) : Seq.seq nat = rowj a b i nl

(** Adding the [j]-th product is an update of column [i + j]: the column was
    zero, because [rowj _ _ i j] stops just short of it. *)
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
    for the accumulator a non-strict bound composes better, since the column
    of [i] products is bounded by [i] times the bound on one. *)
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

(** {2 Folding the top half down}

    [2^256 = 2 * prime + 38], so column [k + 16] is worth [38] units of
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

(** A whole pass: limbs [0] to [nl - 2] carry into their neighbour, then the
    top limb carries round into limb [0] multiplied by [38]. *)
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

(** {2 Reading a limb off the number}

    What the store loop needs: with every limb a proper one, limb [k] is
    digit [k] of the value in base [2^16]. *)
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

(** {2 Subtracting the prime}

    [2^255 = prime + 19], so clearing bit 255 and adding [19] subtracts one
    prime.  Applied twice to a number below [2^256] it lands below [2^255],
    and a third application decides the last conditional subtraction. *)

let hi255 (s: Seq.seq nat) : nat = vat s (nl - 1) / pow2 15

let fold255 (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then
    Seq.upd (Seq.upd s (nl - 1) (vat s (nl - 1) % pow2 15)) 0 (vat s 0 + 19 * hi255 s)
  else s

let fold255_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (fold255 s) == nl) = ()

let fold255_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (fold255 s) + prime * hi255 s == eval s)
  = let q = hi255 s in
    let s1 = Seq.upd s (nl - 1) (Seq.index s (nl - 1) % pow2 15) in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % pow2 15);
    eval_upd s1 0 (Seq.index s 0 + 19 * q);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) (pow2 15);
    Math.pow2_plus (rad * (nl - 1)) 15;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % pow2 15) (pow2 15 * q);
    Math.paren_mul_right (pow2 (rad * (nl - 1))) (pow2 15) q;
    assert (rad * (nl - 1) + 15 == 255);
    assert_norm (pow2 255 == prime + 19)

(** Masking off bit 255 is a reduction modulo [2^255], which is what
    decoding a public key asks for. *)
let mask255 (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then Seq.upd s (nl - 1) (vat s (nl - 1) % pow2 15) else s

let mask255_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures eval (mask255 s) == eval s % pow2 255 /\ bnd (mask255 s) base)
  = let q = Seq.index s (nl - 1) / pow2 15 in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % pow2 15);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) (pow2 15);
    Math.pow2_plus (rad * (nl - 1)) 15;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % pow2 15) (pow2 15 * q);
    Math.paren_mul_right (pow2 (rad * (nl - 1))) (pow2 15) q;
    assert (rad * (nl - 1) + 15 == 255);
    eval_at (mask255 s) (nl - 1);
    eval_bnd (Seq.slice (mask255 s) 0 (nl - 1));
    eval_zeros (Seq.slice (mask255 s) nl nl);
    Math.pow2_plus (rad * (nl - 1)) 15;
    Math.lemma_mult_le_left (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % pow2 15 + 1) (pow2 15);
    Math.lemma_mod_plus (eval (mask255 s)) q (pow2 255);
    Math.small_mod (eval (mask255 s)) (pow2 255)

(** {2 Bytes}

    A limb is exactly two bytes, so both directions are stated relationally
    on whatever the loop happens to have built. *)

#push-options "--fuel 4"
let rec eval_bytes (b: Seq.seq S8.t) (s: Seq.seq nat)
  : Lemma (requires Seq.length b == 2 * Seq.length s /\
                    (forall (k: nat). k < Seq.length s ==>
                       Seq.index s k == S8.v (Seq.index b (2 * k)) +
                                        256 * S8.v (Seq.index b (2 * k + 1))))
          (ensures eval s == le_nat b)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      le_nat_split b 2;
      let hd = Seq.slice b 0 2 in
      let tl = Seq.slice b 2 (2 * n) in
      assert (le_nat hd == S8.v (Seq.index b 0) + 256 * S8.v (Seq.index b 1));
      eval_bytes tl (Seq.slice s 1 n)
    end
#pop-options

let store_ok (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\ bnd s base /\
                    (forall (k: nat). k < nl ==>
                       S8.v (Seq.index b (2 * k)) == Seq.index s k % 256 /\
                       S8.v (Seq.index b (2 * k + 1)) == Seq.index s k / 256))
          (ensures b == nat_to_le 32 (eval s))
  = let v = eval s in
    let aux (i: nat { i < 32 }) : Lemma (Seq.index b i == Seq.index (nat_to_le 32 v) i) =
      let k = i / 2 in
      eval_digit s k;
      nat_to_le_index 32 v i;
      Math.pow2_plus (rad * k) 8;
      if i % 2 = 0 then begin
        assert (8 * i == rad * k);
        Math.pow2_modulo_modulo_lemma_1 (v / pow2 (rad * k)) 8 rad
      end else begin
        assert (8 * i == rad * k + 8);
        Math.pow2_modulo_division_lemma_1 (v / pow2 (rad * k)) 8 rad;
        Math.division_multiplication_lemma v (pow2 (rad * k)) (pow2 8)
      end;
      S8.v_extensional (Seq.index b i) (Seq.index (nat_to_le 32 v) i) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro b (nat_to_le 32 v)

(** {2 What the loops need}

    Three small lemmas stated in exactly the shape the implementation's
    invariants take, so that no arithmetic happens inside a Pulse block. *)

let addw_ble (x y: Seq.seq nat) (cx cy: nat)
  : Lemma (requires ble x cx /\ ble y cy) (ensures ble (addw x y) (cx + cy)) = ()

let addw_len (x y: Seq.seq nat)
  : Lemma (Seq.length (addw x y) == Seq.length x) = ()

(** Adding the [j]-th product of row [i] to the accumulator is an update of
    column [i + j], because that column is still zero. *)
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

(** {2 Eight primes}

    [fsub] adds a multiple of the prime before subtracting, so that no limb
    can go negative.  Four times [2 * prime] is the smallest one whose every
    limb dominates a limb of the subtrahend. *)

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
    ones: a field element in this library has every limb below [2^17], and
    each operation restores that with a fixed number of carry passes -- one
    for an addition or a subtraction, two for a multiplication by a small
    constant, three for a full multiplication. *)

module C = Spec.Curve25519

let lim : pos = pow2 17 - 1

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
  carry_pass (carry_pass (carry_pass (fold38 (part a b nl))))

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
    assert_norm (39 * (nl * (lim * lim)) <= pow2 44);
    fold_ble p (nl * (lim * lim));
    ble_mono (fold38 p) (39 * (nl * (lim * lim))) (pow2 44);
    let f = fold38 p in
    assert_norm (pow2 44 + (pow2 28 + pow2 13) < base * (pow2 28 + pow2 13 + 1));
    assert_norm (base - 1 + 38 * ((pow2 44 + (pow2 28 + pow2 13)) / base) <= pow2 34);
    pass f (pow2 44) (pow2 28 + pow2 13) (pow2 34);
    let g = carry_pass f in
    assert_norm (pow2 34 + (pow2 18 + pow2 4) < base * (pow2 18 + pow2 4 + 1));
    assert_norm (base - 1 + 38 * ((pow2 34 + (pow2 18 + pow2 4)) / base) <= pow2 24);
    pass g (pow2 34) (pow2 18 + pow2 4) (pow2 24);
    let h = carry_pass g in
    assert_norm (pow2 24 + 257 < base * 258);
    assert_norm (base - 1 + 38 * ((pow2 24 + 257) / base) <= lim);
    pass h (pow2 24) 257 lim;
    fold_mod p;
    mul_ok a b;
    Math.lemma_mod_mul_distr_l (eval a) (eval b) prime;
    Math.lemma_mod_mul_distr_r (eval a % prime) (eval b) prime

(** {3 Multiplication by a small constant} *)

let fscale_spec (m: nat) (a: Seq.seq nat) : Seq.seq nat =
  carry_pass (carry_pass (scale m a))

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
    assert_norm (121665 * lim <= pow2 34);
    ble_mono s (121665 * lim) (pow2 34);
    assert_norm (pow2 34 + (pow2 18 + pow2 4) < base * (pow2 18 + pow2 4 + 1));
    assert_norm (base - 1 + 38 * ((pow2 34 + (pow2 18 + pow2 4)) / base) <= pow2 24);
    pass s (pow2 34) (pow2 18 + pow2 4) (pow2 24);
    let g = carry_pass s in
    assert_norm (pow2 24 + 257 < base * 258);
    assert_norm (base - 1 + 38 * ((pow2 24 + 257) / base) <= lim);
    pass g (pow2 24) 257 lim;
    eval_scale m a


(** {3 Freezing}

    Reducing to the unique representative below the prime, which is what
    the caller sees on the way out.  The shape of the argument shrinks in
    four steps: from limbs under [2^17] to a genuine base-[2^16] number
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
    assert_norm (rad * (nl - 1) == 240);
    Math.lemma_mult_le_left base (eval t + 1) (pow2 240);
    Math.pow2_plus rad 240

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
    base-[2^16] digit, and the lowest has absorbed the wrap-around. *)
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

(** The last step lands inside base [2^16]: either nothing overflowed, or
    the overflow was one and what remained was tiny. *)
let fstep_last (s: Seq.seq nat)
  : Lemma (requires shaped s 65573)
          (ensures Seq.length (fstep s) == nl /\ bnd (fstep s) base /\
                   eval (fstep s) < pow2 256 /\
                   eval (fstep s) % prime == eval s % prime)
  = shaped_ble s 65573;
    assert_norm (65573 + 1 < base * 2);
    fstep_val s;
    carry_low_len s;
    carry_split_bnd s 65573 1;
    carry_split_ok s;
    eval_shaped s 65573;
    assert_norm (65573 + pow2 256 - base == pow2 256 + 37);
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
    assert_norm (base - 1 + 38 * 2 == 65611);
    shaped_ble x1 65611;
    assert_norm (65611 + 1 < base * 2);
    fstep_ok x1 65611 1;
    let x2 = fstep x1 in
    assert_norm (base - 1 + 38 * 1 == 65573);
    shaped_ble x2 65573;
    fstep_ok x2 65573 1;
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
                    Seq.length x1 == nl /\ ble x1 65611 /\
                    Seq.length x2 == nl /\ ble x2 65573 /\
                    Seq.length x3 == nl /\ ble x3 65573))
  = assert_norm (lim + 2 < base * 3);
    assert_norm (base - 1 + 38 * ((lim + 2) / base) == 65611);
    pass s lim 2 65611;
    let x1 = carry_pass s in
    assert_norm (65611 + 1 < base * 2);
    assert_norm (base - 1 + 38 * ((65611 + 1) / base) == 65573);
    pass x1 65611 1 65573;
    let x2 = carry_pass x1 in
    assert_norm (65573 + 1 < base * 2);
    assert_norm (base - 1 + 38 * ((65573 + 1) / base) == 65573);
    pass x2 65573 1 65573

(** {3 Subtracting the prime once} *)

let red255 (s: Seq.seq nat) : Seq.seq nat = carry_low (fold255 s)

let hi255_bit (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures hi255 s == eval s / pow2 255)
  = eval_bnd s;
    assert_norm (rad * nl == 256);
    assert_norm (rad * (nl - 1) == 240);
    Math.lemma_div_lt (eval s) 256 240;
    eval_digit s (nl - 1);
    Math.small_mod (eval s / pow2 240) base;
    Math.division_multiplication_lemma (eval s) (pow2 240) (pow2 15);
    Math.pow2_plus 240 15

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
