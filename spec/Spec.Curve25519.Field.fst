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

(** The five-limb representation of [Spec.Curve25519]'s field.

    An element is five natural numbers standing for
    [a0 + a1 2^51 + ... + a4 2^204].  Nothing here is a machine integer:
    this module is the arithmetic, and [Hacl.Curve25519.Field] will be the
    same arithmetic on [Hacl.Secret.UInt64.t].

    The part of that arithmetic which never mentions the prime -- the
    product, the carry chain, the bounds -- lives in [Spec.Bignum51], which
    this module [include]s, so every name is available here.  What is left
    below is the prime-specific half: folding column [k + 5] into column [k]
    with the constant [19], subtracting the prime, and the byte conversions.

    {b Why fifty-one bits.}  [nl * rad] is [255], and [2^255 = prime + 19]:
    the reduction constant is a single digit, the carry out of the top limb
    subtracts exactly one prime, and a multiplication is twenty-five limb
    products rather than the sixty-four this library used when its limbs
    were thirty-two bits wide.  A column of five products of fifty-two-bit
    limbs is under [2^107], and folding multiplies that by twenty, so the
    widest intermediate is under [2^111] -- seventeen bits of headroom in a
    [Hacl.Secret.UInt128].

    {b The bytes.}  A limb is no longer a whole number of bytes, so the
    encoding is no longer a shuffle.  Rather than prove a second byte layer,
    both conversions go through the thirty-two-bit representation of
    [Spec.Bignum256], whose byte layer is already proved, and the bit
    repacking between the two representations is stated with the windows of
    [Spec.Bignum51.Window] and [Spec.Bignum256.Window].  {!load_ok} and
    {!store_ok} at the bottom of this file are the whole of it. *)
module Spec.Curve25519.Field

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module Classical = FStar.Classical
module S8 = Hacl.Secret.UInt8
module B32 = Spec.Bignum256
module W32 = Spec.Bignum256.Window
module W = Spec.Bignum51.Window

open Hacl.Spec.Bytes

include Spec.Bignum51

let prime : pos = Spec.Curve25519.prime

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 Folding the top half down}

    [2^255 = prime + 19], so column [k + 5] is worth [19] units of column
    [k] plus one prime times its weight -- and the surplus is an exact
    multiple of the prime, so no [%] is needed anywhere. *)
let fold19 (c: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun k -> vat c k + 19 * vat c (k + nl))

let one_prime (_: unit) : Lemma (pow2 255 == prime + 19) =
  assert_norm (pow2 255 == (pow2 255 - 19) + 19)

let fold_ok (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw)
          (ensures eval c == eval (fold19 c) + prime * eval (Seq.slice c nl nw))
  = let u = Seq.slice c 0 nl in
    let w = Seq.slice c nl nw in
    eval_split c nl;
    Seq.lemma_eq_intro (fold19 c) (addw u (scale 19 w));
    eval_addw u (scale 19 w);
    eval_scale 19 w;
    one_prime ();
    assert (rad * nl == 255);
    Math.distributivity_add_left prime 19 (eval w)

let fold_ble (c: Seq.seq nat) (cc: nat)
  : Lemma (requires ble c cc) (ensures ble (fold19 c) (20 * cc)) = ()


let carry_top (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then
    Seq.upd (Seq.upd s (nl - 1) (vat s (nl - 1) % base)) 0
            (vat s 0 + 19 * (vat s (nl - 1) / base))
  else s

let carry_top_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (carry_top s) == nl) = ()

let carry_top_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (carry_top s) + prime * (Seq.index s (nl - 1) / base) == eval s)
  = let q = Seq.index s (nl - 1) / base in
    let s1 = Seq.upd s (nl - 1) (Seq.index s (nl - 1) % base) in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % base);
    eval_upd s1 0 (Seq.index s 0 + 19 * q);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) base;
    Math.pow2_plus (rad * (nl - 1)) rad;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % base) (base * q);
    Math.paren_mul_right (pow2 (rad * (nl - 1))) base q;
    one_prime ();
    assert (rad * nl == 255);
    Math.distributivity_add_left prime 19 q

let carry_top_ble (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ chained s c d (nl - 1))
          (ensures ble (carry_top s) (base - 1 + 19 * ((c + d) / base)))
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
    Math.swap_mul prime q;
    Math.lemma_mod_plus (eval (carry_pass s)) q prime

let carry_pass_ble (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures ble (carry_pass s) (base - 1 + 19 * ((c + d) / base)))
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    carry_top_ble (carry_run s (nl - 1)) c d


let shaped (s: Seq.seq nat) (c0: nat) : prop =
  Seq.length s == nl /\ vat s 0 <= c0 /\
  (forall (k: nat). 0 < k /\ k < nl ==> vat s k < base)

let shaped_ble (s: Seq.seq nat) (c0: nat)
  : Lemma (requires shaped s c0 /\ base - 1 <= c0) (ensures ble s c0) = ()

let eval_shaped (s: Seq.seq nat) (c0: nat)
  : Lemma (requires shaped s c0) (ensures eval s <= c0 + pow2 255 - base)
  = let t = Seq.slice s 1 nl in
    let aux (i: nat { i < nl - 1 }) : Lemma (Seq.index t i < base) =
      Seq.lemma_index_slice s 1 nl i;
      assert (vat s (i + 1) < base) in
    Classical.forall_intro aux;
    assert (bnd t base);
    eval_bnd t;
    assert_norm (rad * (nl - 1) == 204);
    Math.lemma_mult_le_left base (eval t + 1) (pow2 204);
    Math.pow2_plus rad 204

(** A pass leaves a shaped number: every limb but the lowest is a proper
    base-[2^51] digit, and the lowest has absorbed the wrap-around. *)
let carry_pass_shaped (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures shaped (carry_pass s) (base - 1 + 19 * ((c + d) / base)))
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    Math.lemma_div_le (Seq.index (carry_run s (nl - 1)) (nl - 1)) (c + d) base

(** {2 Eight primes}

    [fsub] adds a multiple of the prime before subtracting, so that no limb
    can go negative.  Eight primes is the smallest one whose every limb
    dominates a limb of the subtrahend. *)

let bm19 : (n: nat { n == base - 19 }) =
  assert_norm (base - 19 == 2251799813685229); 2251799813685229

let onep : Seq.seq nat = Seq.upd (ones nl) 0 bm19

let eightp : Seq.seq nat = scale 8 onep

let onep_ok (_: unit) : Lemma (eval onep == prime /\ Seq.length onep == nl)
  = eval_ones nl;
    eval_upd (ones nl) 0 bm19;
    assert (rad * nl == 255);
    one_prime ()

let eightp_ok (_: unit)
  : Lemma (eval eightp == 8 * prime /\ Seq.length eightp == nl /\
           (forall (i: nat). i < nl ==> Seq.index eightp i == 8 * Seq.index onep i))
  = onep_ok ();
    eval_scale 8 onep

#pop-options

(** {2 The operations, as the implementation performs them}

    Everything from here down is stated so that a Pulse function can build a
    sequence and then apply exactly one lemma.  The bounds are the concrete
    ones: a field element in this library has every limb below [2^52], and
    each operation restores that with a fixed number of carry passes -- one
    for an addition, a subtraction or a multiplication by a small constant,
    two for a full multiplication. *)

module C = Spec.Curve25519

let lim : pos = pow2 52 - 1

let felem (s: Seq.seq nat) : prop = Seq.length s == nl /\ ble s lim

let fev (s: Seq.seq nat) : GTot C.elem = C.prime_gt_one (); eval s % prime

let ble_mono (s: Seq.seq nat) (c c': nat)
  : Lemma (requires ble s c /\ c <= c') (ensures ble s c') = ()

#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"

(** {3 One carry pass, packaged}

    Every operation below is a few applications of this: from a bound [c] on
    the limbs, one pass leaves them under [c'], and the value is unchanged
    modulo the prime.  The witness [d] is the carry bound; the caller picks
    it, and [assert_norm] checks the two arithmetic side conditions. *)
let pass (s: Seq.seq nat) (c d c': nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1) /\
                    base - 1 + 19 * ((c + d) / base) <= c')
          (ensures Seq.length (carry_pass s) == nl /\ ble (carry_pass s) c' /\
                   eval (carry_pass s) % prime == eval s % prime)
  = carry_pass_len s;
    carry_pass_ble s c d;
    carry_pass_mod s

(** {3 Addition} *)

let fadd_spec (a b: Seq.seq nat) : Seq.seq nat = carry_pass (addw a b)

let fadd_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fadd_spec a b) /\ fev (fadd_spec a b) == C.fadd (fev a) (fev b))
  = addw_ble a b lim lim;
    addw_len a b;
    assert_norm (2 * lim + 4 < base * 5);
    assert_norm (base - 1 + 19 * ((2 * lim + 4) / base) <= lim);
    pass (addw a b) (2 * lim) 4 lim;
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
                   ble (subw a b) (lim + 8 * (base - 1)))
  = eightp_ok ();
    assert (ble onep (base - 1));
    assert_norm (lim <= 8 * (base - 19));
    assert (forall (i: nat). i < nl ==> Seq.index onep i >= base - 19);
    Seq.lemma_eq_intro (addw (subw a b) b) (addw a eightp);
    eval_addw (subw a b) b;
    eval_addw a eightp

let fsub_spec (a b: Seq.seq nat) : Seq.seq nat = carry_pass (subw a b)

let fsub_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fsub_spec a b) /\ fev (fsub_spec a b) == C.fsub (fev a) (fev b))
  = subw_ok a b;
    assert_norm (lim + 8 * (base - 1) + 10 < base * 11);
    assert_norm (base - 1 + 19 * ((lim + 8 * (base - 1) + 10) / base) <= lim);
    pass (subw a b) (lim + 8 * (base - 1)) 10 lim;
    sub_mod_lemma (eval (subw a b)) (eval a) (eval b)

(** {3 Multiplication} *)

(** The last, partial pass.  {!carry_pass_shaped} says a full pass leaves
    every limb but the lowest a proper base-[2^51] digit, so all that is
    left to do is move limb zero's overflow into limb one -- one step of
    the chain rather than a second pass over all five limbs.  That is what
    lets [fmul] run a single carry chain, and it is why the bound below is
    kept as [20 * (nl * (lim * lim))] rather than rounded up to [2^111]:
    the rounding would put [19] times the top carry over [2^64] and the
    chain could no longer be carried in a word. *)
let carry_fix (s: Seq.seq nat) : Seq.seq nat = carry_step 0 s

let carry_fix_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures Seq.length (carry_fix s) == nl /\ eval (carry_fix s) == eval s)
  = carry_step_ok 0 s

let carry_fix_ble (s: Seq.seq nat) (c0: nat)
  : Lemma (requires shaped s c0) (ensures ble (carry_fix s) (base - 1 + c0 / base))
  = Math.lemma_div_le (vat s 0) c0 base

let fmul_spec (a b: Seq.seq nat) : Seq.seq nat =
  carry_fix (carry_pass (fold19 (part a b nl)))

let fold_mod (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw)
          (ensures eval (fold19 c) % prime == eval c % prime)
  = fold_ok c;
    Math.swap_mul prime (eval (Seq.slice c nl nw));
    Math.lemma_mod_plus (eval (fold19 c)) (eval (Seq.slice c nl nw)) prime

let fmul_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fmul_spec a b) /\ fev (fmul_spec a b) == C.fmul (fev a) (fev b))
  = part_ble a b lim lim nl;
    part_len a b nl;
    let p = part a b nl in
    fold_ble p (nl * (lim * lim));
    let f = fold19 p in
    assert_norm (20 * (nl * (lim * lim)) + pow2 60 < base * (pow2 60 + 1));
    carry_pass_shaped f (20 * (nl * (lim * lim))) (pow2 60);
    carry_pass_len f;
    carry_pass_mod f;
    let g = carry_pass f in
    let c0 = base - 1 + 19 * ((20 * (nl * (lim * lim)) + pow2 60) / base) in
    carry_fix_ble g c0;
    carry_fix_ok g;
    assert_norm (base - 1 + (base - 1 + 19 * ((20 * (nl * (lim * lim)) + pow2 60) / base)) / base <= lim);
    ble_mono (carry_fix g) (base - 1 + c0 / base) lim;
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
    assert_norm (121665 * lim <= pow2 69);
    ble_mono s (121665 * lim) (pow2 69);
    assert_norm (pow2 69 + (pow2 18 + pow2 6) < base * (pow2 18 + pow2 6 + 1));
    assert_norm (base - 1 + 19 * ((pow2 69 + (pow2 18 + pow2 6)) / base) <= lim);
    pass s (pow2 69) (pow2 18 + pow2 6) lim;
    eval_scale m a


(** {3 Freezing}

    Reducing to the unique representative below the prime, which is what
    the caller sees on the way out.  Four carry passes bring the limbs from
    under [2^52] to genuine base-[2^51] digits, at which point the value is
    already below [2^255] because [nl * rad] is [255]; one conditional
    subtraction finishes. *)

(** One step: carry the whole number, then fold the overflow back in with
    the reduction constant, since [2^255 = prime + 19]. *)
let fstep (s: Seq.seq nat) : Seq.seq nat =
  let r = carry_low s in
  if Seq.length r = nl then Seq.upd r 0 (vat r 0 + 19 * carry_out s) else r

let fstep_val (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (fstep s) == eval (carry_low s) + 19 * carry_out s /\
                   eval (fstep s) % prime == eval s % prime)
  = carry_low_len s;
    carry_split_ok s;
    let r = carry_low s in
    let t = carry_out s in
    eval_upd r 0 (Seq.index r 0 + 19 * t);
    one_prime ();
    Math.distributivity_add_left prime 19 t;
    Math.swap_mul prime t;
    Math.lemma_mod_plus (eval (fstep s)) t prime

let fstep_ok (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures shaped (fstep s) (base - 1 + 19 * d) /\
                   eval (fstep s) % prime == eval s % prime)
  = fstep_val s;
    carry_low_len s;
    carry_split_bnd s c d;
    Math.lemma_mult_le_right 19 (carry_out s) d

(** [fstep] is nothing but [carry_pass] written the other way round: the
    wrap-around of the top limb and the fold of the overflow are the same
    multiplication by [19]. *)
let fstep_is_pass (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures fstep s == carry_pass s)
  = carry_run_len s (nl - 1);
    Seq.lemma_eq_intro (fstep s) (carry_pass s)

(** The last step lands inside base [2^51]: either nothing overflowed, or
    the overflow was one and what remained was tiny. *)
let fstep_last (s: Seq.seq nat)
  : Lemma (requires shaped s (base + 18))
          (ensures Seq.length (fstep s) == nl /\ bnd (fstep s) base /\
                   eval (fstep s) < pow2 255 /\
                   eval (fstep s) % prime == eval s % prime)
  = shaped_ble s (base + 18);
    assert_norm (base + 18 + 1 < base * 2);
    fstep_val s;
    carry_low_len s;
    carry_split_bnd s (base + 18) 1;
    carry_split_ok s;
    eval_shaped s (base + 18);
    let r = carry_low s in
    if carry_out s = 0 then begin
      Seq.lemma_eq_intro (fstep s) r;
      eval_bnd r;
      assert (rad * nl == 255)
    end else begin
      assert (carry_out s == 1);
      assert (eval s == eval r + pow2 255);
      assert (eval r <= 18);
      eval_ge r 0; eval_ge r 1; eval_ge r 2; eval_ge r 3; eval_ge r 4;
      assert_norm (nl == 5);
      assert (forall (k: nat). k < nl ==> Seq.index r k <= 18);
      assert_norm (18 + 19 < base);
      assert (Seq.equal (fstep s) (Seq.upd r 0 (Seq.index r 0 + 19)));
      assert (eval (fstep s) == eval r + 19);
      Math.pow2_lt_compat 255 6;
      assert_norm (pow2 6 == 64);
      assert (eval (fstep s) < pow2 255);
      assert (bnd (fstep s) base)
    end

let freeze_a (s: Seq.seq nat) : Seq.seq nat = fstep (fstep (fstep (fstep s)))

let freeze_a_ok (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures Seq.length (freeze_a s) == nl /\ bnd (freeze_a s) base /\
                   eval (freeze_a s) < pow2 255 /\
                   eval (freeze_a s) % prime == eval s % prime)
  = assert_norm (lim + 2 < base * 3);
    fstep_ok s lim 2;
    let x1 = fstep s in
    assert_norm (base - 1 + 19 * 2 == base + 37);
    shaped_ble x1 (base + 37);
    assert_norm (base + 37 + 1 < base * 2);
    fstep_ok x1 (base + 37) 1;
    let x2 = fstep x1 in
    assert_norm (base - 1 + 19 * 1 == base + 18);
    shaped_ble x2 (base + 18);
    fstep_ok x2 (base + 18) 1;
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
                    Seq.length x1 == nl /\ ble x1 (base + 37) /\
                    Seq.length x2 == nl /\ ble x2 (base + 18) /\
                    Seq.length x3 == nl /\ ble x3 (base + 18)))
  = assert_norm (lim + 2 < base * 3);
    assert_norm (base - 1 + 19 * ((lim + 2) / base) == base + 37);
    pass s lim 2 (base + 37);
    let x1 = carry_pass s in
    assert_norm (base + 37 + 1 < base * 2);
    assert_norm (base - 1 + 19 * ((base + 37 + 1) / base) == base + 18);
    pass x1 (base + 37) 1 (base + 18);
    let x2 = carry_pass x1 in
    assert_norm (base + 18 + 1 < base * 2);
    assert_norm (base - 1 + 19 * ((base + 18 + 1) / base) == base + 18);
    pass x2 (base + 18) 1 (base + 18)

(** {3 The conditional last subtraction}

    After {!freeze_a} the value is below [2^255 = prime + 19], so at most
    one prime has to come off.  Adding [19] and carrying decides it: the
    carry out of the top limb is one exactly when the value was at least
    the prime, and what the carry chain left behind is then the answer. *)

let add19 (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then Seq.upd s 0 (vat s 0 + 19) else s

let freeze_w (y: Seq.seq nat) : Seq.seq nat = carry_low (add19 y)

let freeze_spec (s: Seq.seq nat) : Seq.seq nat =
  let y = freeze_a s in
  if carry_out (add19 y) = 1 then freeze_w y else y

let freeze_step (y: Seq.seq nat)
  : Lemma (requires Seq.length y == nl /\ bnd y base /\ eval y < pow2 255)
          (ensures (let a = add19 y in
                    Seq.length (freeze_w y) == nl /\ bnd (freeze_w y) base /\
                    carry_out a <= 1 /\
                    eval (freeze_w y) + pow2 255 * carry_out a == eval y + 19))
  = let a = add19 y in
    assert (ble a (base + 18));
    assert_norm (base + 18 + 1 < base * 2);
    eval_upd y 0 (Seq.index y 0 + 19);
    assert_norm (pow2 (rad * 0) == 1);
    carry_split_ok a;
    carry_split_bnd a (base + 18) 1;
    carry_low_len a

let freeze_spec_ok (s: Seq.seq nat)
  : Lemma (requires felem s)
          (ensures Seq.length (freeze_spec s) == nl /\ bnd (freeze_spec s) base /\
                   eval (freeze_spec s) == eval s % prime)
  = freeze_a_ok s;
    let y = freeze_a s in
    freeze_step y;
    let w = freeze_w y in
    one_prime ();
    assert_norm (prime > 19);
    if carry_out (add19 y) = 1 then begin
      assert (eval w == eval y - prime);
      assert (eval y < prime + 19);
      Math.small_mod (eval y - prime) prime;
      Math.lemma_mod_sub (eval y) prime 1
    end else begin
      assert (eval w == eval y + 19);
      eval_bnd w;
      assert (rad * nl == 255);
      Math.small_mod (eval y) prime
    end

#pop-options

(** {2 Bytes}

    Both directions go through the thirty-two-bit representation of
    [Spec.Bignum256]: a limb there is exactly four bytes, so its byte layer
    is a shuffle and is already proved.  What is left is the bit repacking
    between the two representations, and that is two applications of
    [eval_windows] -- the limbs of either representation are the successive
    windows of the value, and a sequence of windows evaluates to the value
    it came from.

    The implementation obtains the windows themselves from the *other*
    representation's limbs with [eval_win] and [eval_win2]; those are used
    at the call site rather than here, because the offsets differ from limb
    to limb and naming eight of them would be longer than using them. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"

(** The two [win]s are the same function, one written in each module. *)
let win_eq (v: nat) (a w: nat) : Lemma (W.win v a w == W32.win v a w) = ()

(** Bit [255] of a thirty-two-bit number lives in limb [7], and clearing it
    is the reduction modulo [2^255] that decoding a public key performs. *)
let mask255_32 (u: Seq.seq nat) : Seq.seq nat =
  if Seq.length u = 8 then Seq.upd u 7 (B32.vat u 7 % pow2 31) else u

let mask255_32_ok (u: Seq.seq nat)
  : Lemma (requires Seq.length u == 8 /\ B32.bnd u B32.base)
          (ensures B32.eval (mask255_32 u) == B32.eval u % pow2 255 /\
                   B32.bnd (mask255_32 u) B32.base)
  = let q = Seq.index u 7 / pow2 31 in
    B32.eval_upd u 7 (Seq.index u 7 % pow2 31);
    Math.euclidean_division_definition (Seq.index u 7) (pow2 31);
    Math.pow2_plus (B32.rad * 7) 31;
    Math.distributivity_add_right (pow2 (B32.rad * 7))
      (Seq.index u 7 % pow2 31) (pow2 31 * q);
    Math.paren_mul_right (pow2 (B32.rad * 7)) (pow2 31) q;
    assert (B32.rad * 7 + 31 == 255);
    B32.eval_at (mask255_32 u) 7;
    B32.eval_bnd (Seq.slice (mask255_32 u) 0 7);
    B32.eval_zeros (Seq.slice (mask255_32 u) 8 8);
    Math.lemma_mult_le_left (pow2 (B32.rad * 7))
      (Seq.index u 7 % pow2 31 + 1) (pow2 31);
    Math.lemma_mod_plus (B32.eval (mask255_32 u)) q (pow2 255);
    Math.small_mod (B32.eval (mask255_32 u)) (pow2 255)

(** Loading: the five fifty-one-bit limbs are the successive windows of the
    thirty-two-bit number the bytes decode to. *)
let load_ok (v: nat) (s: Seq.seq nat)
  : Lemma (requires v < pow2 255 /\ Seq.length s == nl /\
                    (forall (k: nat). k < nl ==> Seq.index s k == W32.win v (rad * k) rad))
          (ensures eval s == v /\ bnd s base)
  = assert (rad * nl == 255);
    W.eval_windows v s

(** {2 Constants}

    A number below [2^255] written out in five limbs.  The precomputed
    curve constants are given this way, and [limbs_of_ok] is what says the
    literals in [Hacl.Ed25519.Tables] denote the number they should. *)

let limbs_of (x: nat) : Seq.lseq nat nl =
  Seq.init #nat nl (fun i -> x / pow2 (rad * i) % base)

let limbs_of_ok (x: nat)
  : Lemma (requires x < pow2 255)
          (ensures eval (limbs_of x) == x /\ bnd (limbs_of x) base)
  = assert_norm (rad * nl == 255);
    Seq.init_index nl (fun i -> x / pow2 (rad * i) % base);
    W.eval_windows x (limbs_of x)

(** Two bounded five-limb sequences with the same value are the same
    sequence: each limb is a digit of the value. *)
let limbs_unique (s: Seq.seq nat) (x: nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ eval s == x)
          (ensures s == limbs_of x)
  = let aux (k: nat { k < nl }) : Lemma (Seq.index s k == Seq.index (limbs_of x) k) =
      eval_digit s k;
      Seq.init_index nl (fun i -> x / pow2 (rad * i) % base) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s (limbs_of x)

let limbs_index (x: nat) (k: nat { k < nl })
  : Lemma (Seq.index (limbs_of x) k == x / pow2 (rad * k) % base)
  = Seq.init_index nl (fun i -> x / pow2 (rad * i) % base)

(** Storing: the eight thirty-two-bit limbs are the successive windows of
    the fifty-one-bit number, and [Spec.Bignum256] turns those into bytes. *)
let store_ok (v: nat) (u: Seq.seq nat)
  : Lemma (requires v < pow2 256 /\ Seq.length u == 8 /\
                    (forall (j: nat). j < 8 ==> Seq.index u j == W.win v (B32.rad * j) B32.rad))
          (ensures B32.eval u == v /\ B32.bnd u B32.base)
  = assert (B32.rad * 8 == 256);
    W32.eval_windows v u

#pop-options
