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

(** Arithmetic modulo the group order, at the limb level.

    Ed25519 has a second modulus besides the field's: the order [q] of the
    prime-order subgroup, which is where the [S] half of a signature lives.
    Two things have to happen mod [q] -- a 512-bit hash output has to be
    reduced, and one product [k s] has to be formed -- and neither is
    performance-critical next to a scalar multiplication.

    So this module does the simplest thing that is constant time and cheap
    to prove: everything is *bitwise*.  Reduction is 512 steps of
    [acc := 2 acc + bit mod q], and multiplication is 256 steps of
    [acc := 2 acc mod q] with a conditional [acc := acc + a mod q].  Each
    step is a shift or an addition over sixteen limbs followed by one
    conditional subtraction of [q], so the entire module is built out of
    exactly two primitives, and both of them are the carry chain that
    [Spec.Curve25519.Field] already has lemmas for.

    The conditional subtraction is done by *adding* [2^256 - q] and looking
    at the carry out, which is why [Spec.Curve25519.Field.carry_out] is
    the only thing this needs beyond [carry_low]: [a >= q] exactly when
    [a + (2^256 - q)] overflows, and the low limbs are then [a - q]
    already.  No comparison and no borrow chain has to be written down. *)
module Spec.Ed25519.Scalar

open Hacl.Spec.Bytes

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module Loops = Hacl.Spec.Loops
module F = Spec.Curve25519.Field
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let q : pos = Spec.Ed25519.q

let q_bound (_: unit) : Lemma (0 < q /\ 2 * q + 1 < pow2 256 /\ q < pow2 255) =
  assert_norm (2 * (pow2 252 + 27742317777372353535851937790883648493) + 1 < pow2 256);
  assert_norm (pow2 252 + 27742317777372353535851937790883648493 < pow2 255)

(** {2 Limbs of a constant} *)

let limbs_of (x: nat) : Seq.lseq nat F.nl =
  Seq.init #nat F.nl (fun i -> x / pow2 (F.rad * i) % F.base)

(** The general fact that a base-[2^rad] digit expansion evaluates back to
    the number it came from. *)
#push-options "--z3rlimit 300"
let rec eval_limbs (x: nat) (s: Seq.seq nat)
  : Lemma (requires x < pow2 (F.rad * Seq.length s) /\
                    (forall (k: nat). k < Seq.length s ==>
                       Seq.index s k == x / pow2 (F.rad * k) % F.base))
          (ensures F.eval s == x)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let t = Seq.slice s 1 n in
      let y = x / F.base in
      assert (F.base == pow2 F.rad);
      assert (F.rad * n == F.rad + F.rad * (n - 1));
      Math.pow2_plus F.rad (F.rad * (n - 1));
      Math.lemma_div_lt_nat x (F.rad * n) F.rad;
      assert (y < pow2 (F.rad * (n - 1)));
      let aux (k: nat { k < n - 1 })
        : Lemma (Seq.index t k == y / pow2 (F.rad * k) % F.base)
        = assert (Seq.index t k == Seq.index s (k + 1));
          assert (F.rad * (k + 1) == F.rad + F.rad * k);
          Math.pow2_plus F.rad (F.rad * k);
          Math.division_multiplication_lemma x F.base (pow2 (F.rad * k)) in
      Classical.forall_intro aux;
      assert (forall (k: nat). k < Seq.length t ==>
                Seq.index t k == y / pow2 (F.rad * k) % F.base);
      eval_limbs y t;
      assert (F.eval t == y);
      assert (F.eval s == Seq.index s 0 + F.base * y);
      assert (Seq.index s 0 == x % F.base);
      Math.euclidean_division_definition x F.base
    end
#pop-options

let limbs_of_ok (x: nat)
  : Lemma (requires x < pow2 256)
          (ensures F.eval (limbs_of x) == x /\ F.bnd (limbs_of x) F.base)
  = assert (F.rad * F.nl == 256);
    eval_limbs x (limbs_of x)

(** {2 The two primitives} *)

(** A limbwise addition followed by one carry pass: the low sixteen limbs
    and the carry out.  Both arguments proper, so every column is below
    [2 base - 1] and one pass normalises it. *)
let addc (a b: Seq.seq nat) : Seq.seq nat = F.carry_low (F.addw a b)
let addc_out (a b: Seq.seq nat) : nat = F.carry_out (F.addw a b)

let addc_ok (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == F.nl /\ Seq.length b == F.nl /\
                    F.bnd a F.base /\ F.bnd b F.base)
          (ensures Seq.length (addc a b) == F.nl /\ F.bnd (addc a b) F.base /\
                   addc_out a b <= 1 /\
                   F.eval a + F.eval b == F.eval (addc a b) + pow2 256 * addc_out a b)
  = let s = F.addw a b in
    F.eval_addw a b;
    assert (F.ble a (F.base - 1));
    assert (F.ble b (F.base - 1));
    F.addw_ble a b (F.base - 1) (F.base - 1);
    assert_norm (2 * F.base - 2 + 1 < F.base * 2);
    F.carry_split_bnd s (2 * F.base - 2) 1;
    F.carry_low_len s;
    F.carry_split_ok s

(** A doubling with a bit shifted in: limbwise [2 a_i], the bit added to
    limb zero, then the same carry pass.  Columns reach [2 base - 1] here,
    so the chain needs two units of headroom rather than one. *)
let dbl_add (a: Seq.seq nat) (b: nat { b < 2 }) : Seq.seq nat =
  F.carry_low (F.addw (F.scale 2 a) (Seq.create 1 b))

let dbl_add_ok (a: Seq.seq nat) (b: nat { b < 2 })
  : Lemma (requires Seq.length a == F.nl /\ F.bnd a F.base /\ 2 * F.eval a + b < pow2 256)
          (ensures Seq.length (dbl_add a b) == F.nl /\ F.bnd (dbl_add a b) F.base /\
                   F.eval (dbl_add a b) == 2 * F.eval a + b)
  = let x = F.scale 2 a in
    let y : Seq.seq nat = Seq.create 1 b in
    let s = F.addw x y in
    F.eval_scale 2 a;
    F.eval_addw x y;
    F.eval_empty (Seq.slice y 1 1);
    assert (F.eval y == b);
    F.scale_ble 2 a (F.base - 1);
    assert (F.ble y 1);
    F.addw_ble x y (2 * F.base - 2) 1;
    assert_norm (2 * F.base - 1 + 2 < F.base * 3);
    F.carry_split_bnd s (2 * F.base - 1) 2;
    F.carry_low_len s;
    F.carry_split_ok s;
    F.carry_out_zero s

(** {2 Conditional subtraction}

    [a >= q] iff [a + (2^256 - q)] carries out of the top, and then the low
    limbs already hold [a - q].  So the whole reduction is one addition and
    one select on the carry bit. *)

let qc : Seq.lseq nat F.nl = q_bound (); limbs_of (pow2 256 - q)

let qc_ok (_: unit) : Lemma (F.eval qc == pow2 256 - q /\ F.bnd qc F.base) =
  q_bound ();
  limbs_of_ok (pow2 256 - q)

let csub_q (a: Seq.seq nat) : Seq.seq nat =
  if addc_out a qc = 1 then addc a qc else a

let csub_q_ok (a: Seq.seq nat)
  : Lemma (requires Seq.length a == F.nl /\ F.bnd a F.base /\ F.eval a < 2 * q)
          (ensures Seq.length (csub_q a) == F.nl /\ F.bnd (csub_q a) F.base /\
                   F.eval (csub_q a) == F.eval a % q)
  = q_bound ();
    qc_ok ();
    addc_ok a qc;
    let c = addc_out a qc in
    if c = 1 then begin
      assert (F.eval (addc a qc) == F.eval a - q);
      Math.lemma_mod_plus (F.eval a - q) 1 q;
      Math.small_mod (F.eval a - q) q
    end else begin
      assert (F.eval a + pow2 256 - q == F.eval (addc a qc));
      F.eval_bnd (addc a qc);
      assert (F.eval (addc a qc) < pow2 256);
      Math.small_mod (F.eval a) q
    end

(** {2 The three operations} *)

let zero : Seq.lseq nat F.nl = limbs_of 0

let zero_ok (_: unit) : Lemma (F.eval zero == 0 /\ F.bnd zero F.base) =
  limbs_of_ok 0

(** [(2 a + b) mod q]. *)
let qdbl_add (a: Seq.seq nat) (b: nat { b < 2 }) : Seq.seq nat = csub_q (dbl_add a b)

let qdbl_add_ok (a: Seq.seq nat) (b: nat { b < 2 })
  : Lemma (requires Seq.length a == F.nl /\ F.bnd a F.base /\ F.eval a < q)
          (ensures Seq.length (qdbl_add a b) == F.nl /\ F.bnd (qdbl_add a b) F.base /\
                   F.eval (qdbl_add a b) == (2 * F.eval a + b) % q /\
                   F.eval (qdbl_add a b) < q)
  = q_bound ();
    dbl_add_ok a b;
    csub_q_ok (dbl_add a b)

(** [(a + b) mod q]. *)
let qadd (a b: Seq.seq nat) : Seq.seq nat = csub_q (addc a b)

let qadd_ok (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == F.nl /\ Seq.length b == F.nl /\
                    F.bnd a F.base /\ F.bnd b F.base /\ F.eval a < q /\ F.eval b < q)
          (ensures Seq.length (qadd a b) == F.nl /\ F.bnd (qadd a b) F.base /\
                   F.eval (qadd a b) == (F.eval a + F.eval b) % q /\
                   F.eval (qadd a b) < q)
  = q_bound ();
    addc_ok a b;
    assert (F.eval a + F.eval b < pow2 256);
    F.eval_bnd (addc a b);
    csub_q_ok (addc a b)

(** {2 Reduction of a wide value}

    [reduce x] is [x mod q] for any [x] below [2^512], read one bit at a
    time from the top.  The invariant is that after [i] steps the
    accumulator holds the top [i] bits of [x] reduced. *)

let bit_of (x: nat) (i: nat) : nat = (x / pow2 i) % 2

(** [x / 2^i] is twice [x / 2^(i+1)] plus bit [i]: the induction step of
    every bitwise loop here. *)
let bit_split (x: nat) (i: nat)
  : Lemma (x / pow2 i == 2 * (x / pow2 (i + 1)) + bit_of x i)
  = Math.pow2_plus i 1;
    Math.division_multiplication_lemma x (pow2 i) 2;
    Math.euclidean_division_definition (x / pow2 i) 2

let reduce_step (x: nat) (i: nat) (acc: Seq.seq nat) : Seq.seq nat =
  if i < 512 then qdbl_add acc (bit_of x (511 - i)) else acc

let reduce (x: nat) : Seq.seq nat = Loops.repeati 512 (reduce_step x) zero

let rec reduce_at (x: nat) (i: nat)
  : Lemma (requires x < pow2 512 /\ i <= 512)
          (ensures (let r = Loops.repeati i (reduce_step x) zero in
                    Seq.length r == F.nl /\ F.bnd r F.base /\ F.eval r < q /\
                    F.eval r == (x / pow2 (512 - i)) % q))
          (decreases i)
  = q_bound ();
    if i = 0 then begin
      zero_ok ();
      Loops.repeati_zero (reduce_step x) zero;
      Math.small_div x (pow2 512);
      Math.small_mod 0 q
    end else begin
      reduce_at x (i - 1);
      Loops.unfold_repeati (i - 1) (reduce_step x) zero;
      let p = Loops.repeati (i - 1) (reduce_step x) zero in
      let b = bit_of x (512 - i) in
      qdbl_add_ok p b;
      bit_split x (512 - i);
      Math.lemma_mod_mul_distr_r 2 (x / pow2 (513 - i)) q;
      Math.lemma_mod_add_distr b (2 * (x / pow2 (513 - i))) q
    end

let reduce_ok (x: nat)
  : Lemma (requires x < pow2 512)
          (ensures Seq.length (reduce x) == F.nl /\ F.bnd (reduce x) F.base /\
                   F.eval (reduce x) < q /\ F.eval (reduce x) == x % q)
  = reduce_at x 512;
    assert_norm (pow2 0 == 1)

(** {2 Multiplication}

    Horner over the 256 bits of the multiplier, most significant first.  The
    conditional addition is a [select] on the bit, so that the
    implementation may compile it to a mask. *)

let qsel (b: nat { b < 2 }) (x y: Seq.seq nat) : Seq.seq nat = if b = 1 then y else x

let qmul_step (a: Seq.seq nat) (n: nat) (i: nat) (acc: Seq.seq nat) : Seq.seq nat =
  if i < 256 then
    let acc = qdbl_add acc 0 in
    qsel (bit_of n (255 - i)) acc (qadd acc a)
  else acc

let qmul (a: Seq.seq nat) (n: nat) : Seq.seq nat =
  Loops.repeati 256 (qmul_step a n) zero

let rec qmul_at (a: Seq.seq nat) (n: nat) (i: nat)
  : Lemma (requires Seq.length a == F.nl /\ F.bnd a F.base /\ F.eval a < q /\
                    n < pow2 256 /\ i <= 256)
          (ensures (let r = Loops.repeati i (qmul_step a n) zero in
                    Seq.length r == F.nl /\ F.bnd r F.base /\ F.eval r < q /\
                    F.eval r == (F.eval a * (n / pow2 (256 - i))) % q))
          (decreases i)
  = q_bound ();
    if i = 0 then begin
      zero_ok ();
      Loops.repeati_zero (qmul_step a n) zero;
      Math.small_div n (pow2 256);
      Math.small_mod 0 q
    end else begin
      qmul_at a n (i - 1);
      Loops.unfold_repeati (i - 1) (qmul_step a n) zero;
      let p = Loops.repeati (i - 1) (qmul_step a n) zero in
      let hi = n / pow2 (257 - i) in
      let b = bit_of n (256 - i) in
      qdbl_add_ok p 0;
      let d = qdbl_add p 0 in
      Math.lemma_mod_mul_distr_r 2 (F.eval a * hi) q;
      Math.paren_mul_right 2 (F.eval a) hi;
      Math.swap_mul 2 (F.eval a);
      Math.paren_mul_right (F.eval a) 2 hi;
      assert (F.eval d == (F.eval a * (2 * hi)) % q);
      bit_split n (256 - i);
      if b = 1 then begin
        qadd_ok d a;
        Math.lemma_mod_add_distr (F.eval a) (F.eval a * (2 * hi)) q;
        Math.distributivity_add_right (F.eval a) (2 * hi) 1
      end else ()
    end

let qmul_ok (a: Seq.seq nat) (n: nat)
  : Lemma (requires Seq.length a == F.nl /\ F.bnd a F.base /\ F.eval a < q /\ n < pow2 256)
          (ensures Seq.length (qmul a n) == F.nl /\ F.bnd (qmul a n) F.base /\
                   F.eval (qmul a n) < q /\ F.eval (qmul a n) == (F.eval a * n) % q)
  = qmul_at a n 256;
    assert_norm (pow2 0 == 1)

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"

(** {2 Reading a bit out of a representation}

    Two facts the implementation needs and nothing else does: bit [i] of a
    limb sequence is bit [i mod rad] of limb [i / rad], and bit [i] of a
    byte string is bit [i mod 8] of byte [i / 8].  Both are the same
    argument -- [eval_digit] or its little-endian twin, then a division of
    a residue. *)

(** [(y / 2^j) mod 2] does not change when [y] is first cut down to [w]
    bits, as long as [j < w]. *)
let bit_of_residue (y: nat) (j: nat) (w: nat)
  : Lemma (requires j < w) (ensures bit_of ((y % pow2 w) / pow2 j) 0 == bit_of y j)
  = Math.pow2_modulo_division_lemma_1 y j w;
    assert_norm (pow2 1 == 2);
    Math.pow2_modulo_modulo_lemma_1 (y / pow2 j) 1 (w - j)

let eval_bit (s: Seq.seq nat) (i: nat)
  : Lemma (requires F.bnd s F.base /\ i < F.rad * Seq.length s)
          (ensures bit_of (F.eval s) i ==
                   bit_of (Seq.index s (i / F.rad) / pow2 (i % F.rad)) 0)
  = let k = i / F.rad in
    let j = i % F.rad in
    Math.lemma_div_mod i F.rad;
    F.div_le_of_lt i F.rad (Seq.length s - 1);
    assert (k < Seq.length s);
    assert (i == F.rad * k + j);
    F.eval_digit s k;
    Math.pow2_plus (F.rad * k) j;
    Math.division_multiplication_lemma (F.eval s) (pow2 (F.rad * k)) (pow2 j);
    assert (F.base == pow2 F.rad);
    bit_of_residue (F.eval s / pow2 (F.rad * k)) j F.rad

let le_nat_digit (b: Seq.seq S8.t) (k: nat { k < Seq.length b })
  : Lemma ((le_nat b / pow2 (8 * k)) % 256 == S8.v (Seq.index b k))
  = let n = Seq.length b in
    le_nat_split b k;
    le_nat_bound (Seq.slice b 0 k);
    Math.lemma_div_plus (le_nat (Seq.slice b 0 k)) (le_nat (Seq.slice b k n)) (pow2 (8 * k));
    Math.small_div (le_nat (Seq.slice b 0 k)) (pow2 (8 * k));
    le_nat_cons b k;
    Math.lemma_mod_plus (S8.v (Seq.index b k)) (le_nat (Seq.slice b (k + 1) n)) 256;
    Math.small_mod (S8.v (Seq.index b k)) 256

let le_nat_bit (b: Seq.seq S8.t) (i: nat)
  : Lemma (requires i < 8 * Seq.length b)
          (ensures bit_of (le_nat b) i ==
                   bit_of (S8.v (Seq.index b (i / 8)) / pow2 (i % 8)) 0)
  = let k = i / 8 in
    let j = i % 8 in
    Math.lemma_div_mod i 8;
    F.div_le_of_lt i 8 (Seq.length b - 1);
    assert (k < Seq.length b);
    le_nat_digit b k;
    Math.pow2_plus (8 * k) j;
    Math.division_multiplication_lemma (le_nat b) (pow2 (8 * k)) (pow2 j);
    assert_norm (pow2 8 == 256);
    bit_of_residue (le_nat b / pow2 (8 * k)) j 8

#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 Two facts for the implementation}

    A proper limb sequence is *determined* by its value, so an
    implementation never has to produce [limbs_of x] structurally: it is
    enough to produce sixteen limbs below the base that evaluate to [x].
    And the limbs of [2^256 - q] are named, so that a table of literals can
    be checked against them one entry at a time rather than by evaluating
    [eval] on a sixteen-element spine. *)

let limbs_unique (s: Seq.seq nat) (x: nat)
  : Lemma (requires Seq.length s == F.nl /\ F.bnd s F.base /\ F.eval s == x)
          (ensures s == limbs_of x)
  = let aux (k: nat { k < F.nl }) : Lemma (Seq.index s k == Seq.index (limbs_of x) k) =
      F.eval_digit s k;
      Seq.init_index F.nl (fun i -> x / pow2 (F.rad * i) % F.base) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s (limbs_of x)

let qc_index (k: nat { k < F.nl })
  : Lemma (Seq.index qc k == (pow2 256 - q) / pow2 (F.rad * k) % F.base)
  = q_bound ();
    Seq.init_index F.nl (fun i -> (pow2 256 - q) / pow2 (F.rad * i) % F.base)

let zero_index (k: nat { k < F.nl }) : Lemma (Seq.index zero k == 0) =
  Seq.init_index F.nl (fun i -> 0 / pow2 (F.rad * i) % F.base)

#pop-options
