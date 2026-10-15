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

(** Montgomery reduction on [Spec.Bignum4]'s four limbs, for an arbitrary
    odd modulus.

    Curve25519's prime has a shape -- [2^256 = 2 * prime + 38] -- that turns
    reduction into adding thirty-eight times the top half to the bottom.
    P-256's prime has a shape too, but exploiting it would mean a second
    reduction path for every modulus that has none.  And the P-256 *group
    order*, which needs exactly the same arithmetic for ECDSA, has no shape
    at all.  So both of P-256's moduli use the one method that does not care
    what the modulus looks like.

    {b The method.}  Write [R = 2^256].  Instead of [a * b mod m] the
    library computes [a * b * R^-1 mod m], and keeps every value multiplied
    by [R].  Then [(aR)(bR)R^-1 = (ab)R], so the representation is
    preserved, and the reduction itself is a loop of four steps each costing
    one multiply-accumulate of the modulus.  Step [i] picks the unique
    [u < 2^64] making limb [i] of the accumulator divisible by [2^64], adds
    [u * m * 2^(64 i)] -- which changes nothing modulo [m] -- and carries
    limb [i] into limb [i + 1], leaving limb [i] zero.  After four steps the
    bottom four limbs are zero and dropping them is division by [R].

    {b The split.}  At sixty-four bits a single product [u * m_j] is a
    hundred and twenty-eight bits wide, so it cannot be added into one
    column of the accumulator.  It is added as [Spec.Bignum4.srow] adds a
    schoolbook row: the low half at column [i + j] and the high half at
    column [i + j + 1].  The multiplier happens to be the digit that kills a
    limb rather than a limb of the left operand, but nothing else differs,
    so the whole of the layout argument is inherited.

    {b Why the whole thing fits in a 128-bit word.}  The accumulator starts
    as an unreduced product with columns below [2^67].  Each step adds two
    halves below [2^64] to a limb and carries in less than [2^9], so four
    steps cannot push a limb past [2^69].  That is comfortably inside the
    [2^72] ceiling the bound chain is stated with, and no intermediate
    normalisation is needed anywhere, which is why the loop body is three
    lines.

    {b What the caller must supply.}  The modulus as four proper limbs, and
    [mu], the negated inverse of its bottom limb modulo [2^64].  Both are
    compile-time constants in every instance, so [mont_ok] is discharged
    once by [assert_norm] and never thought about again.

    The modulus is an ordinary argument rather than a module parameter
    because F* has no module functors and a type class over a *value* would
    be worse than passing it; the implementation passes the corresponding
    slice. *)
module Spec.Montgomery4

open Spec.Bignum4

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops

(** This module is arithmetic-heavy, and the default SMT encoding boxes
    every integer operation, which hides the structure of the products from
    Z3's arithmetic solver.  Encoding linear arithmetic natively and leaving
    only the nonlinear operators wrapped is measurably faster here. *)
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"

(** {2 The modulus}

    [mu] is the constant with [m0 * mu = -1 mod 2^64], which exists exactly
    when the modulus is odd. *)

let mont_ok (ms: Seq.seq nat) (mu: nat) : prop =
  Seq.length ms == nl /\ ble ms (base - 1) /\
  mu < base /\ (Seq.index ms 0 * mu + 1) % base == 0

(** The digit that zeroes limb [i]. *)
let mdigit (mu: nat) (i: nat) (t: Seq.seq nat) : nat = (vat t i * mu) % base

(** The heart of it: [a + ((a * mu) mod 2^64) * m0] is divisible by [2^64],
    for any [a] at all -- limb [i] does not have to be a proper limb first,
    which is what lets the whole reduction run without normalising. *)
let mdigit_kills (ms: Seq.seq nat) (mu: nat) (a: nat)
  : Lemma (requires mont_ok ms mu)
          (ensures (a + ((a * mu) % base) * Seq.index ms 0) % base == 0)
  = let m0 = Seq.index ms 0 in
    let u = (a * mu) % base in
    Math.lemma_mod_mul_distr_l (a * mu) m0 base;
    assert (u * m0 % base == a * mu * m0 % base);
    Math.lemma_mod_add_distr a (u * m0) base;
    Math.lemma_mod_add_distr a (a * mu * m0) base;
    assert ((a + u * m0) % base == (a + a * mu * m0) % base);
    Math.paren_mul_right a mu m0;
    Math.swap_mul mu m0;
    Math.distributivity_add_right a 1 (m0 * mu);
    assert (a + a * mu * m0 == a * (1 + m0 * mu));
    Math.lemma_div_mod (m0 * mu + 1) base;
    let z = (m0 * mu + 1) / base in
    assert (1 + m0 * mu == base * z);
    Math.paren_mul_right a base z;
    Math.swap_mul a base;
    Math.paren_mul_right base a z;
    Math.cancel_mul_mod (a * z) base

(** {2 One step} *)

let mstep (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat) : Seq.seq nat =
  carry_step i (addw t (srow (Seq.length t) (mdigit mu i t) ms i nl))

let mstep_len (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat)
  : Lemma (Seq.length (mstep ms mu i t) == Seq.length t) = ()

(** The value grows by an exact multiple of the modulus, so nothing is lost
    and no [%] appears until the very end. *)
let mstep_eval (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat)
  : Lemma (requires i + nl + 1 <= Seq.length t /\ Seq.length ms == nl)
          (ensures eval (mstep ms mu i t) ==
                   eval t + pow2 (rad * i) * mdigit mu i t * eval ms)
  = let u = mdigit mu i t in
    let e = srow (Seq.length t) u ms i nl in
    carry_step_ok i (addw t e);
    eval_addw t e;
    eval_srow (Seq.length t) u ms i;
    Math.paren_mul_right (pow2 (rad * i)) u (eval ms)

(** Limb [i] becomes zero and the limbs below it are untouched. *)
let mstep_low (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat) (j: nat)
  : Lemma (requires i + 1 < Seq.length t /\ j <= i)
          (ensures vat (mstep ms mu i t) j ==
                   (if j < i then Seq.index t j
                    else (Seq.index t i + plo (mdigit mu i t * vat ms 0)) % base))
  = let u = mdigit mu i t in
    let e = srow (Seq.length t) u ms i nl in
    let s = addw t e in
    assert (Seq.index s j == Seq.index t j + vat e j);
    assert (vat e j == (if j < i then 0 else plo (u * vat ms 0)));
    let s1 = Seq.upd s i (vat s i % base) in
    assert (Seq.length s == Seq.length t);
    assert (mstep ms mu i t == Seq.upd s1 (i + 1) (vat s (i + 1) + vat s i / base));
    assert (Seq.index s1 j == (if j < i then Seq.index s j else vat s i % base))

let mstep_zero (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat)
  : Lemma (requires mont_ok ms mu /\ i + 1 < Seq.length t /\
                    (forall (j: nat). j < i ==> vat t j == 0))
          (ensures (forall (j: nat). j <= i ==> vat (mstep ms mu i t) j == 0))
  = let u = mdigit mu i t in
    mdigit_kills ms mu (vat t i);
    assert (vat ms 0 == Seq.index ms 0);
    Math.lemma_mod_add_distr (Seq.index t i) (u * Seq.index ms 0) base;
    introduce forall (j: nat). j <= i ==> vat (mstep ms mu i t) j == 0
    with introduce _ ==> _
    with (mstep_low ms mu i t j; if j < i then assert (vat t j == 0))

(** {3 The bound}

    A limb grows by at most two halves, each below [2^64], from the
    multiply-accumulate, and by at most [2^9] from the incoming carry, so
    [2^66] of headroom per step is generous.  Four steps from a product's
    [2^67] therefore stay under [2^69]. *)
let mstep_ble (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat) (c: nat)
  : Lemma (requires mont_ok ms mu /\ ble t c /\ c <= pow2 72)
          (ensures ble (mstep ms mu i t) (c + pow2 66))
  = let u = mdigit mu i t in
    let e = srow (Seq.length t) u ms i nl in
    let s = addw t e in
    srow_ble (Seq.length t) u ms i nl;
    assert_norm (2 * (base - 1) < pow2 65);
    assert (ble s (c + pow2 65));
    assert_norm (pow2 72 + pow2 65 < base * (pow2 9 + 1));
    let aux (k: nat { k < Seq.length s }) : Lemma (Seq.index (mstep ms mu i t) k <= c + pow2 66) =
      if k = i then assert_norm (base <= pow2 66)
      else if k = i + 1 && i + 1 < Seq.length s then begin
        div_le_of_lt (Seq.index s i) base (pow2 9);
        assert_norm (pow2 65 + pow2 9 <= pow2 66)
      end
      else assert_norm (pow2 65 <= pow2 66) in
    Classical.forall_intro aux

(** {2 The loop} *)

let mrun (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat) : Seq.seq nat =
  Loops.repeati k (mstep ms mu) t

let mrun_zero (ms: Seq.seq nat) (mu: nat) (t: Seq.seq nat)
  : Lemma (mrun ms mu 0 t == t) = ()

let mrun_unfold (ms: Seq.seq nat) (mu: nat) (k: pos) (t: Seq.seq nat)
  : Lemma (mrun ms mu k t == mstep ms mu (k - 1) (mrun ms mu (k - 1) t))
  = Loops.unfold_repeati k (mstep ms mu) t

let rec mrun_len (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat)
  : Lemma (ensures Seq.length (mrun ms mu k t) == Seq.length t) (decreases k)
  = if k = 0 then () else (mrun_unfold ms mu k t; mrun_len ms mu (k - 1) t)

let rec mrun_ble (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat) (c: nat)
  : Lemma (requires mont_ok ms mu /\ ble t c /\ c + k * pow2 66 <= pow2 72)
          (ensures ble (mrun ms mu k t) (c + k * pow2 66))
          (decreases k)
  = if k = 0 then ()
    else begin
      mrun_unfold ms mu k t;
      Math.lemma_mult_le_right (pow2 66) (k - 1) k;
      mrun_ble ms mu (k - 1) t c;
      mstep_ble ms mu (k - 1) (mrun ms mu (k - 1) t) (c + (k - 1) * pow2 66);
      Math.distributivity_add_left (k - 1) 1 (pow2 66)
    end

let rec mrun_eval (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat)
  : Lemma (requires Seq.length ms == nl /\ k + nl < Seq.length t /\ 0 < eval ms)
          (ensures eval (mrun ms mu k t) % eval ms == eval t % eval ms)
          (decreases k)
  = if k = 0 then ()
    else begin
      mrun_unfold ms mu k t;
      mrun_len ms mu (k - 1) t;
      mrun_eval ms mu (k - 1) t;
      let s = mrun ms mu (k - 1) t in
      mstep_eval ms mu (k - 1) s;
      let q = pow2 (rad * (k - 1)) * mdigit mu (k - 1) s in
      Math.paren_mul_right (pow2 (rad * (k - 1))) (mdigit mu (k - 1) s) (eval ms);
      Math.lemma_mod_plus (eval s) q (eval ms)
    end

let rec mrun_low (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat)
  : Lemma (requires mont_ok ms mu /\ k < Seq.length t)
          (ensures (forall (j: nat). j < k ==> vat (mrun ms mu k t) j == 0))
          (decreases k)
  = if k = 0 then ()
    else begin
      mrun_unfold ms mu k t;
      mrun_len ms mu (k - 1) t;
      mrun_low ms mu (k - 1) t;
      mstep_zero ms mu (k - 1) (mrun ms mu (k - 1) t)
    end

(** {2 The reduction}

    [t] has [2 nl + 1] columns -- one more than a product needs, so that the
    answer, which can be as large as [2 m], still has a top limb to land in.
    After [nl] steps the bottom [nl] limbs are zero, so the value is [R]
    times the value of what is left, and dropping them is the division. *)

let ncol : pos = 2 * nl + 1

let mreduce (ms: Seq.seq nat) (mu: nat) (t: Seq.seq nat { Seq.length t == ncol })
  : Seq.seq nat
  = mrun_len ms mu nl t;
    Seq.slice (mrun ms mu nl t) nl ncol

let mreduce_len (ms: Seq.seq nat) (mu: nat) (t: Seq.seq nat { Seq.length t == ncol })
  : Lemma (ensures Seq.length (mreduce ms mu t) == nl + 1)
  = mrun_len ms mu nl t

let mreduce_ble (ms: Seq.seq nat) (mu: nat) (t: Seq.seq nat { Seq.length t == ncol }) (c: nat)
  : Lemma (requires mont_ok ms mu /\ ble t c /\
                    c + nl * pow2 66 <= pow2 72)
          (ensures ble (mreduce ms mu t) (c + nl * pow2 66))
  = mrun_ble ms mu nl t c; mrun_len ms mu nl t

(** The defining property: [R] times the answer is congruent to the input,
    and equals it exactly as integers. *)
let mreduce_ok (ms: Seq.seq nat) (mu: nat) (t: Seq.seq nat { Seq.length t == ncol })
  : Lemma (requires mont_ok ms mu /\ 0 < eval ms)
          (ensures pow2 256 * eval (mreduce ms mu t) % eval ms == eval t % eval ms /\
                   Seq.length (mreduce ms mu t) == nl + 1)
  = let r = mrun ms mu nl t in
    mrun_len ms mu nl t;
    mrun_low ms mu nl t;
    mrun_eval ms mu nl t;
    eval_split r nl;
    eval_zeros (Seq.slice r 0 nl);
    assert (rad * nl == 256)

(** {3 How much the modulus was added}

    Step [i] adds at most [(2^64 - 1) m 2^(64 i)], and those weights sum to
    [R - 1].  So a reduction of a value below [m R] is below [2 m] -- which
    is why one conditional subtraction at the end suffices and no other
    normalisation is ever needed. *)
let pow_step (k: pos)
  : Lemma (pow2 (rad * (k - 1)) * base == pow2 (rad * k))
  = Math.pow2_plus (rad * (k - 1)) rad;
    assert (rad * k == rad * (k - 1) + rad)

let rec mrun_add (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat)
  : Lemma (requires Seq.length ms == nl /\ k + nl < Seq.length t)
          (ensures eval (mrun ms mu k t) <= eval t + (pow2 (rad * k) - 1) * eval ms)
          (decreases k)
  = if k = 0 then ()
    else begin
      mrun_unfold ms mu k t;
      mrun_len ms mu (k - 1) t;
      mrun_add ms mu (k - 1) t;
      let s = mrun ms mu (k - 1) t in
      mstep_eval ms mu (k - 1) s;
      let w = pow2 (rad * (k - 1)) in
      let u = mdigit mu (k - 1) s in
      let m = eval ms in
      Math.paren_mul_right w u m;
      Math.lemma_mult_le_right m u (base - 1);
      Math.lemma_mult_le_left w (u * m) ((base - 1) * m);
      Math.paren_mul_right w (base - 1) m;
      Math.distributivity_sub_left w 1 m;
      Math.distributivity_sub_left (w * base) 1 m;
      Math.distributivity_sub_left w (w * base) m;
      pow_step k
    end

#push-options "--fuel 0 --ifuel 0 --z3rlimit 5"
let mreduce_bound (r: pos) (m: pos) (t y v: int)
  : Lemma (requires v == r * y /\ v <= t + (r - 1) * m /\ t < m * r)
          (ensures y < 2 * m)
  = Math.distributivity_sub_left r 1 m;
    Math.swap_mul m r;
    if y >= 2 * m then begin
      Math.lemma_mult_le_left r (2 * m) y;
      Math.paren_mul_right r 2 m;
      Math.swap_mul r 2
    end
#pop-options

let mreduce_lt (ms: Seq.seq nat) (mu: nat) (t: Seq.seq nat { Seq.length t == ncol }) (m: pos)
  : Lemma (requires mont_ok ms mu /\ eval ms == m /\
                    eval t < m * pow2 256)
          (ensures eval (mreduce ms mu t) < 2 * m)
  = let r = mrun ms mu nl t in
    mrun_len ms mu nl t;
    mrun_low ms mu nl t;
    eval_split r nl;
    eval_zeros (Seq.slice r 0 nl);
    assert_norm (rad * nl == 256);
    let y = eval (mreduce ms mu t) in
    assert (eval r == pow2 256 * y);
    mrun_add ms mu nl t;
    mreduce_bound (pow2 256) m (eval t) y (eval r)

#pop-options
