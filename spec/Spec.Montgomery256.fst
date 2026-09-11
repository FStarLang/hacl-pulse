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

(** Montgomery reduction on [Spec.Bignum256]'s sixteen limbs, for an
    arbitrary odd modulus.

    Curve25519's prime has a shape -- [2^256 = 2 * prime + 38] -- that turns
    reduction into adding thirty-eight times the top half to the bottom.
    P-256's prime has a shape too, but one that only pays off with 32-bit
    limbs; with sixteen-bit limbs it buys nothing.  And the P-256 *group
    order*, which needs exactly the same arithmetic for ECDSA, has no shape
    at all.  So both of P-256's moduli use the one method that does not care
    what the modulus looks like.

    {b The method.}  Write [R = 2^256].  Instead of [a * b mod m] the
    library computes [a * b * R^-1 mod m], and keeps every value multiplied
    by [R].  Then [(aR)(bR)R^-1 = (ab)R], so the representation is
    preserved, and the reduction itself is a loop of sixteen steps each
    costing one multiply-accumulate of the modulus.  Step [i] picks the
    unique [u < 2^16] making limb [i] of the accumulator divisible by
    [2^16], adds [u * m * 2^(16 i)] -- which changes nothing modulo [m] --
    and carries limb [i] into limb [i + 1], leaving limb [i] zero.  After
    sixteen steps the bottom sixteen limbs are zero and dropping them is
    division by [R].

    {b Why the whole thing fits in a 64-bit word.}  The accumulator starts
    as an unreduced product with columns below [2^36].  Each step adds at
    most [(2^16 - 1)^2 < 2^32] to a limb and carries in less than [2^25], so
    sixteen steps cannot push a limb past [2^38].  No intermediate
    normalisation is needed anywhere, which is why the loop body is three
    lines.

    {b What the caller must supply.}  The modulus as sixteen proper limbs,
    and [mu], the negated inverse of its bottom limb modulo [2^16].  Both
    are compile-time constants in every instance, so [mont_ok] is discharged
    once by [assert_norm] and never thought about again.

    The modulus is an ordinary argument rather than a module parameter
    because F* has no module functors and a type class over a *value* would
    be worse than passing it; the implementation passes the corresponding
    slice. *)
module Spec.Montgomery256

open Spec.Bignum256

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops

#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"

(** {2 Embedding a short number at a limb offset}

    Step [i] adds [u * m] starting at limb [i].  [emb n i s] is [s] placed
    at offset [i] inside [n] limbs, so that the addition is an ordinary
    pointwise [addw]. *)

let emb (n i: nat) (s: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat n (fun k -> if i <= k && k < i + Seq.length s then Seq.index s (k - i) else 0)

let emb_len (n i: nat) (s: Seq.seq nat) : Lemma (Seq.length (emb n i s) == n) = ()

let emb_ble (n i: nat) (s: Seq.seq nat) (c: nat)
  : Lemma (requires ble s c) (ensures ble (emb n i s) c) = ()

let eval_emb (n i: nat) (s: Seq.seq nat)
  : Lemma (requires i + Seq.length s <= n)
          (ensures eval (emb n i s) == pow2 (rad * i) * eval s)
  = let e = emb n i s in
    let hi = Seq.slice e i n in
    eval_split e i;
    eval_zeros (Seq.slice e 0 i);
    Seq.lemma_eq_intro (Seq.slice hi 0 (Seq.length s)) s;
    eval_pad hi (Seq.length s)

(** {2 The modulus}

    [mu] is the constant with [m0 * mu = -1 mod 2^16], which exists exactly
    when the modulus is odd. *)

let mont_ok (ms: Seq.seq nat) (mu: nat) : prop =
  Seq.length ms == nl /\ ble ms (base - 1) /\
  mu < base /\ (Seq.index ms 0 * mu + 1) % base == 0

(** The digit that zeroes limb [i]. *)
let mdigit (mu: nat) (i: nat) (t: Seq.seq nat) : nat = (vat t i * mu) % base

(** The heart of it: [a + ((a * mu) mod 2^16) * m0] is divisible by [2^16],
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
  carry_step i (addw t (emb (Seq.length t) i (scale (mdigit mu i t) ms)))

let mstep_len (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat)
  : Lemma (Seq.length (mstep ms mu i t) == Seq.length t) = ()

(** The value grows by an exact multiple of the modulus, so nothing is lost
    and no [%] appears until the very end. *)
let mstep_eval (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat)
  : Lemma (requires i + nl <= Seq.length t /\ Seq.length ms == nl)
          (ensures eval (mstep ms mu i t) ==
                   eval t + pow2 (rad * i) * mdigit mu i t * eval ms)
  = let u = mdigit mu i t in
    let e = emb (Seq.length t) i (scale u ms) in
    carry_step_ok i (addw t e);
    eval_addw t e;
    eval_emb (Seq.length t) i (scale u ms);
    eval_scale u ms;
    Math.paren_mul_right (pow2 (rad * i)) u (eval ms)

(** Limb [i] becomes zero and the limbs below it are untouched. *)
let mstep_zero (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat)
  : Lemma (requires mont_ok ms mu /\ i + 1 < Seq.length t /\
                    (forall (j: nat). j < i ==> vat t j == 0))
          (ensures (forall (j: nat). j <= i ==> vat (mstep ms mu i t) j == 0))
  = let u = mdigit mu i t in
    let e = emb (Seq.length t) i (scale u ms) in
    let s = addw t e in
    mdigit_kills ms mu (vat t i);
    assert (Seq.index s i == Seq.index t i + u * Seq.index ms 0);
    assert (Seq.index s i % base == 0)

(** {3 The bound}

    A limb grows by at most [(2^16 - 1)^2] from the multiply-accumulate and
    by at most [2^25] from the incoming carry, so [2^33] of headroom per
    step is generous.  Sixteen steps from a product's [2^36] therefore stay
    under [2^38]. *)
let mstep_ble (ms: Seq.seq nat) (mu: nat) (i: nat) (t: Seq.seq nat) (c: nat)
  : Lemma (requires mont_ok ms mu /\ ble t c /\ c <= pow2 40)
          (ensures ble (mstep ms mu i t) (c + pow2 33))
  = let u = mdigit mu i t in
    let e = emb (Seq.length t) i (scale u ms) in
    let s = addw t e in
    scale_ble u ms (base - 1);
    emb_ble (Seq.length t) i (scale u ms) (u * (base - 1));
    assert_norm (base - 1 < base);
    Math.lemma_mult_le_right (base - 1) u (base - 1);
    assert (ble e ((base - 1) * (base - 1)));
    assert_norm ((base - 1) * (base - 1) < pow2 32);
    assert (ble s (c + pow2 32));
    assert_norm (pow2 40 + pow2 32 < base * (pow2 25 + 1));
    let aux (k: nat { k < Seq.length s }) : Lemma (Seq.index (mstep ms mu i t) k <= c + pow2 33) =
      if k = i then assert_norm (base <= pow2 33)
      else if k = i + 1 && i + 1 < Seq.length s then begin
        div_le_of_lt (Seq.index s i) base (pow2 25);
        assert_norm (pow2 32 + pow2 25 <= pow2 33)
      end
      else assert_norm (pow2 32 <= pow2 33) in
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
  : Lemma (requires mont_ok ms mu /\ ble t c /\ c + k * pow2 33 <= pow2 40)
          (ensures ble (mrun ms mu k t) (c + k * pow2 33))
          (decreases k)
  = if k = 0 then ()
    else begin
      mrun_unfold ms mu k t;
      Math.lemma_mult_le_right (pow2 33) (k - 1) k;
      mrun_ble ms mu (k - 1) t c;
      mstep_ble ms mu (k - 1) (mrun ms mu (k - 1) t) (c + (k - 1) * pow2 33);
      Math.distributivity_add_left (k - 1) 1 (pow2 33)
    end

let rec mrun_eval (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat)
  : Lemma (requires Seq.length ms == nl /\ k + nl <= Seq.length t /\ 0 < eval ms)
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
                    c + nl * pow2 33 <= pow2 40)
          (ensures ble (mreduce ms mu t) (c + nl * pow2 33))
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

    Step [i] adds at most [(2^16 - 1) m 2^(16 i)], and those weights sum to
    [R - 1].  So a reduction of a value below [m R] is below [2 m] -- which
    is why one conditional subtraction at the end suffices and no other
    normalisation is ever needed. *)
let rec mrun_add (ms: Seq.seq nat) (mu: nat) (k: nat) (t: Seq.seq nat)
  : Lemma (requires Seq.length ms == nl /\ k + nl <= Seq.length t)
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
      Math.pow2_plus rad (rad * (k - 1));
      assert (rad * k == rad + rad * (k - 1));
      assert (w * base == pow2 (rad * k))
    end

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
    Math.distributivity_sub_left (pow2 256) 1 m;
    if y >= 2 * m then Math.lemma_mult_le_left (pow2 256) (2 * m) y

#pop-options
