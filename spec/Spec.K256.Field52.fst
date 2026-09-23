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

(** The five-limb representation of secp256k1's field.

    An element is five natural numbers standing for
    [a0 + a1 2^52 + ... + a4 2^208].  Nothing here is a machine integer:
    this module is the arithmetic, and [Hacl.K256.Field52] will be the same
    arithmetic on [Hacl.Secret.UInt64.t].

    The part that never mentions the prime -- the product, the carry chain,
    the bounds -- is [Spec.Bignum52], which this module [include]s, so every
    name from it is available here.  What is left below is the
    prime-specific half: folding column [k + 5] into column [k], subtracting
    a multiple of the prime, and reducing to the canonical representative.

    This is the exact counterpart of {!Spec.Curve25519.Field}, which does
    the same job at radix [2^51] for [2^255 - 19], and the two should be
    read side by side.  Two things differ, and both come from the size of
    the reduction constant.

    {b The constant.}  [nl * rad] is [260] and

      [2^260 = 16 * 2^256 = 16 * (prime + 2^32 + 977) = 16 * prime + 2^36 + 15632],

    so [cf = 2^36 + 15632] here where Curve25519 has [19].  Folding
    therefore discards sixteen primes at a time rather than one, which costs
    nothing -- [fold_ok] subtracts an exact multiple either way.  What it
    does cost is headroom: a column of the schoolbook product is a sum of
    five products of numbers below [2^53], so it is below [2^108.4], and
    [cf] times that would be [2^144.4].  Curve25519 can fold a whole column
    because nineteen times [2^107] still fits; here the column has to be
    carried down to a proper digit before it is multiplied.  That is why
    {!fold} below takes an already-carried upper half, and why
    [Hacl.K256.Field52] will interleave the carry with the fold in the
    manner of libsecp256k1's [field_5x52_int128_impl.h] rather than
    computing the whole product first.

    {b The top limb.}  At radix [2^51] the number [2^255] is one prime plus
    nineteen, so a carry out of the top limb is worth a single fold.  Here
    the same is true of [2^260] and [cf], and nothing is different -- but
    an element is below [2^260] and the prime is below [2^256], so being
    reduced is no longer implied by having five proper digits.  {!freeze}
    has to do the extra work, and the sixteen primes that [2^260] hides
    mean it does it with five conditional subtractions' worth of slack
    rather than one.

    {b Lazy.}  As at radix [2^51], no operation reduces to the canonical
    range; a limb below [2^53] is the whole invariant, and only [freeze]
    ever produces a number below the prime. *)
module Spec.K256.Field52

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module Classical = FStar.Classical
module K = Spec.K256

include Spec.Bignum52

let prime : pos = K.prime

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 Folding the top half down}

    [2^260 = 16 * prime + cf], so column [k + 5] is worth [cf] units of
    column [k] plus sixteen primes times its weight -- and the surplus is an
    exact multiple of the prime, so no [%] appears anywhere. *)

let cf : (n: pos { n == pow2 36 + 15632 }) =
  assert_norm (pow2 36 + 15632 == 68719492368); 68719492368

let sixteen_primes (_: unit) : Lemma (pow2 260 == 16 * prime + cf) =
  assert_norm (pow2 260 == 16 * (pow2 256 - pow2 32 - 977) + pow2 36 + 15632)

let fold (c: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun k -> vat c k + cf * vat c (k + nl))

let fold_ok (c: Seq.seq nat)
  : Lemma (requires Seq.length c == 2 * nl)
          (ensures eval c == eval (fold c) + 16 * prime * eval (Seq.slice c nl (2 * nl)))
  = let u = Seq.slice c 0 nl in
    let w = Seq.slice c nl (2 * nl) in
    eval_split c nl;
    Seq.lemma_eq_intro (fold c) (addw u (scale cf w));
    eval_addw u (scale cf w);
    eval_scale cf w;
    sixteen_primes ();
    assert (rad * nl == 260);
    Math.distributivity_add_left (16 * prime) cf (eval w)

let fold_ble (c: Seq.seq nat) (cu cw: nat)
  : Lemma (requires Seq.length c == 2 * nl /\
                    (forall (i: nat). i < nl ==> vat c i <= cu) /\
                    (forall (i: nat). nl <= i /\ i < 2 * nl ==> vat c i <= cw))
          (ensures ble (fold c) (cu + cf * cw))
  = let aux (i: nat { i < nl }) : Lemma (Seq.index (fold c) i <= cu + cf * cw) =
      Math.lemma_mult_le_right cf (vat c (i + nl)) cw in
    Classical.forall_intro aux

let fold_mod (c: Seq.seq nat)
  : Lemma (requires Seq.length c == 2 * nl)
          (ensures eval (fold c) % prime == eval c % prime)
  = fold_ok c;
    Math.paren_mul_right 16 prime (eval (Seq.slice c nl (2 * nl)));
    Math.swap_mul prime (16 * eval (Seq.slice c nl (2 * nl)));
    Math.lemma_mod_plus (eval (fold c)) (16 * eval (Seq.slice c nl (2 * nl))) prime

(** {2 The carry pass}

    Identical to the radix-51 one with [cf] in place of nineteen: run the
    chain to the top, keep the top limb's low digit, and fold its overflow
    back into limb zero. *)

let carry_top (s: Seq.seq nat) : Seq.seq nat =
  if Seq.length s = nl then
    Seq.upd (Seq.upd s (nl - 1) (vat s (nl - 1) % base)) 0
            (vat s 0 + cf * (vat s (nl - 1) / base))
  else s

let carry_top_len (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl) (ensures Seq.length (carry_top s) == nl) = ()

let carry_top_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures eval (carry_top s) + 16 * prime * (Seq.index s (nl - 1) / base) == eval s)
  = let q = Seq.index s (nl - 1) / base in
    let s1 = Seq.upd s (nl - 1) (Seq.index s (nl - 1) % base) in
    eval_upd s (nl - 1) (Seq.index s (nl - 1) % base);
    eval_upd s1 0 (Seq.index s 0 + cf * q);
    Math.euclidean_division_definition (Seq.index s (nl - 1)) base;
    Math.pow2_plus (rad * (nl - 1)) rad;
    Math.distributivity_add_right (pow2 (rad * (nl - 1)))
      (Seq.index s (nl - 1) % base) (base * q);
    Math.paren_mul_right (pow2 (rad * (nl - 1))) base q;
    sixteen_primes ();
    assert (rad * nl == 260);
    Math.distributivity_add_left (16 * prime) cf q

let carry_top_ble (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ chained s c d (nl - 1))
          (ensures ble (carry_top s) (base - 1 + cf * ((c + d) / base)))
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
    Math.paren_mul_right 16 prime q;
    Math.swap_mul prime (16 * q);
    Math.lemma_mod_plus (eval (carry_pass s)) (16 * q) prime

let carry_pass_ble (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures ble (carry_pass s) (base - 1 + cf * ((c + d) / base)))
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    carry_top_ble (carry_run s (nl - 1)) c d

(** {2 Shaped numbers}

    What a pass leaves behind: four proper digits and a low limb that has
    absorbed the wrap-around. *)

let shaped (s: Seq.seq nat) (c0: nat) : prop =
  Seq.length s == nl /\ vat s 0 <= c0 /\
  (forall (k: nat). 0 < k /\ k < nl ==> vat s k < base)

let shaped_ble (s: Seq.seq nat) (c0: nat)
  : Lemma (requires shaped s c0 /\ base - 1 <= c0) (ensures ble s c0) = ()

let eval_shaped (s: Seq.seq nat) (c0: nat)
  : Lemma (requires shaped s c0) (ensures eval s <= c0 + pow2 260 - base)
  = let t = Seq.slice s 1 nl in
    let aux (i: nat { i < nl - 1 }) : Lemma (Seq.index t i < base) =
      Seq.lemma_index_slice s 1 nl i;
      assert (vat s (i + 1) < base) in
    Classical.forall_intro aux;
    assert (bnd t base);
    eval_bnd t;
    assert_norm (rad * (nl - 1) == 208);
    Math.lemma_mult_le_left base (eval t + 1) (pow2 208);
    Math.pow2_plus rad 208

let carry_pass_shaped (s: Seq.seq nat) (c d: nat)
  : Lemma (requires Seq.length s == nl /\ ble s c /\ c + d < base * (d + 1))
          (ensures shaped (carry_pass s) (base - 1 + cf * ((c + d) / base)))
  = carry_run_chained s c d (nl - 1);
    carry_run_len s (nl - 1);
    Math.lemma_div_le (Seq.index (carry_run s (nl - 1)) (nl - 1)) (c + d) base

(** {2 Sixty-four primes}

    [fsub] adds a multiple of the prime before subtracting, so that no limb
    can go negative.  The top limb of the prime is only [2^48 - 1] -- the
    prime is below [2^256] where an element is below [2^260] -- so the
    multiple has to be large enough that even that limb dominates a limb of
    the subtrahend.  Sixty-four is the smallest power of two that does, and
    a power of two is what makes the implementation a shift.

    Curve25519's counterpart is eight primes, and the difference is exactly
    the four bits [2^260] has over [2^256]. *)

let pl0 : (n: nat { n == base - pow2 32 - 977 }) =
  assert_norm (base - pow2 32 - 977 == 4503595332402223); 4503595332402223

let pl4 : (n: nat { n == pow2 48 - 1 }) =
  assert_norm (pow2 48 - 1 == 281474976710655); 281474976710655

let onep : Seq.seq nat = Seq.upd (Seq.upd (ones nl) 0 pl0) (nl - 1) pl4

let p64 : Seq.seq nat = scale 64 onep

let onep_ok (_: unit) : Lemma (eval onep == prime /\ Seq.length onep == nl)
  = eval_ones nl;
    let s1 = Seq.upd (ones nl) 0 pl0 in
    eval_upd (ones nl) 0 pl0;
    eval_upd s1 (nl - 1) pl4;
    assert (rad * nl == 260);
    assert_norm (rad * (nl - 1) == 208);
    assert_norm (pow2 260 - 1 - (base - 1 - pl0) - pow2 208 * (base - 1 - pl4) ==
                 pow2 256 - pow2 32 - 977)

let p64_ok (_: unit)
  : Lemma (eval p64 == 64 * prime /\ Seq.length p64 == nl /\
           (forall (i: nat). i < nl ==> Seq.index p64 i == 64 * Seq.index onep i))
  = onep_ok ();
    eval_scale 64 onep

(** The three distinct limbs of [p64], as the literals the implementation
    adds.  Curve25519's counterpart has two, because at radix [2^51] every
    limb of the prime but the lowest is all ones; here the top one is short
    as well. *)
let p64_index (i: nat { i < nl })
  : Lemma (Seq.index p64 i ==
             (if i = 0 then 288230101273742272
              else if i = nl - 1 then 18014398509481920
              else 288230376151711680))
  = assert_norm (64 * pl0 == 288230101273742272);
    assert_norm (64 * pl4 == 18014398509481920);
    assert_norm (64 * (base - 1) == 288230376151711680)

#pop-options

(** {2 The operations, as the implementation performs them}

    A field element here has every limb below [2^53], and each operation
    restores that.  An addition, a subtraction or a negation costs one carry
    pass; a multiplication is the interleaved chain of [fmul_spec]. *)

let lim : pos = pow2 53 - 1

let felem (s: Seq.seq nat) : prop = Seq.length s == nl /\ ble s lim

let fev (s: Seq.seq nat) : GTot K.felem = eval s % prime

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
                    base - 1 + cf * ((c + d) / base) <= c')
          (ensures Seq.length (carry_pass s) == nl /\ ble (carry_pass s) c' /\
                   eval (carry_pass s) % prime == eval s % prime)
  = carry_pass_len s;
    carry_pass_ble s c d;
    carry_pass_mod s

(** {3 Addition} *)

let fadd_spec (a b: Seq.seq nat) : Seq.seq nat = carry_pass (addw a b)

let fadd_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fadd_spec a b) /\ fev (fadd_spec a b) == K.fadd (fev a) (fev b))
  = addw_ble a b lim lim;
    addw_len a b;
    assert_norm (2 * lim + 5 < base * 6);
    assert_norm (base - 1 + cf * ((2 * lim + 5) / base) <= lim);
    pass (addw a b) (2 * lim) 5 lim;
    eval_addw a b;
    Math.lemma_mod_add_distr (eval a % prime) (eval b) prime;
    Math.lemma_mod_add_distr (eval b) (eval a) prime

(** {3 Subtraction}

    [p64] dominates every limb of the subtrahend, so the difference is taken
    limb by limb without a borrow and without leaving the naturals. *)

let cancel (x y v: nat)
  : Lemma (requires x < prime /\ y < prime /\ v < prime /\
                    (x + v) % prime == (y + v) % prime)
          (ensures x == y)
  = Math.lemma_div_mod (x + v) prime;
    Math.lemma_div_mod (y + v) prime;
    div_le_of_lt (x + v) prime 1;
    div_le_of_lt (y + v) prime 1

let sub_mod_lemma (x a b: nat)
  : Lemma (requires x + b == a + 64 * prime)
          (ensures x % prime == K.fsub (a % prime) (b % prime))
  = let u = a % prime in
    let v = b % prime in
    let y = K.fsub u v in
    Math.lemma_mod_plus a 64 prime;
    Math.lemma_mod_add_distr b x prime;
    Math.lemma_mod_add_distr (x % prime) b prime;
    assert ((x % prime + v) % prime == u);
    Math.lemma_mod_add_distr v (u + prime - v) prime;
    Math.lemma_mod_plus u 1 prime;
    assert ((y + v) % prime == u);
    cancel (x % prime) y v

let subw (a b: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun k -> if vat b k <= vat p64 k then vat a k + vat p64 k - vat b k else 0)

let subw_ok (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ ble a lim /\ Seq.length b == nl /\ ble b lim)
          (ensures eval (subw a b) + eval b == eval a + 64 * prime /\
                   ble (subw a b) (lim + 64 * (base - 1)))
  = p64_ok ();
    assert (ble onep (base - 1));
    assert_norm (lim <= 64 * pl4);
    assert (forall (i: nat). i < nl ==> Seq.index onep i >= pl4);
    Seq.lemma_eq_intro (addw (subw a b) b) (addw a p64);
    eval_addw (subw a b) b;
    eval_addw a p64

let fsub_spec (a b: Seq.seq nat) : Seq.seq nat = carry_pass (subw a b)

let fsub_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fsub_spec a b) /\ fev (fsub_spec a b) == K.fsub (fev a) (fev b))
  = subw_ok a b;
    assert_norm (lim + 64 * (base - 1) + 66 < base * 67);
    assert_norm (base - 1 + cf * ((lim + 64 * (base - 1) + 66) / base) <= lim);
    pass (subw a b) (lim + 64 * (base - 1)) 66 lim;
    sub_mod_lemma (eval (subw a b)) (eval a) (eval b)

(** {3 Negation}

    [fneg] is [fsub] from zero, but the zero is not stored: the limbs of
    [p64] are the whole of the minuend. *)

let negw (a: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun k -> if vat a k <= vat p64 k then vat p64 k - vat a k else 0)

let negw_ok (a: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ ble a lim)
          (ensures eval (negw a) + eval a == 64 * prime /\ ble (negw a) (64 * (base - 1)))
  = p64_ok ();
    assert (ble onep (base - 1));
    assert_norm (lim <= 64 * pl4);
    assert (forall (i: nat). i < nl ==> Seq.index onep i >= pl4);
    Seq.lemma_eq_intro (addw (negw a) a) p64;
    eval_addw (negw a) a

let fneg_spec (a: Seq.seq nat) : Seq.seq nat = carry_pass (negw a)

let fneg_spec_ok (a: Seq.seq nat)
  : Lemma (requires felem a)
          (ensures felem (fneg_spec a) /\ fev (fneg_spec a) == K.fneg (fev a))
  = negw_ok a;
    assert_norm (64 * (base - 1) + 64 < base * 65);
    assert_norm (base - 1 + cf * ((64 * (base - 1) + 64) / base) <= lim);
    pass (negw a) (64 * (base - 1)) 64 lim;
    Seq.lemma_eq_intro (subw (Seq.create nl 0) a) (negw a);
    sub_mod_lemma (eval (negw a)) 0 (eval a);
    eval_zeros (Seq.create nl 0)

#pop-options

(** {3 Multiplication}

    The schoolbook product is nine columns, each a sum of five products of
    numbers below [2^53] and so below [2^108.4].  Curve25519 folds such a
    column by multiplying it whole by nineteen; here the constant is [2^36]
    and that would need [2^144].  So the upper four columns are carried into
    proper digits first, and it is those -- and the one small limb the carry
    spills into -- that the reduction constant multiplies.

    {!carry_run_top} is the lemma that makes this pay.  A run of four steps
    over [w5] stops on a limb that began at zero, so the bound on it is the
    incoming carry, [2^57], rather than the [2^108.4] a column starts at;
    [cf] times [2^57] is [2^93], which is nineteen bits inside a
    [Hacl.Secret.UInt128], and every other fold term is below [2^88].

    Two carry passes then restore the invariant.  The first is an ordinary
    one and leaves a shaped number whose low limb is below [2^93]; the
    second is where {!pass_shaped} is needed, because the uniform bound of
    {!pass} would carry that [2^93] all the way round again and give
    [2^76], and a third and a fourth pass would be wanted.  Knowing that
    only limb zero is large, the carry dies out after two limbs: the chain
    of bounds is [2^93], [2^53], [2^52], [2^52], [2^52], the overflow out of
    the top is one, and limb zero comes back at [base - 1 + cf], comfortably
    inside [2^53]. *)

let w5 (c: Seq.seq nat) : Seq.seq nat =
  if Seq.length c = nw then Seq.append (Seq.slice c nl nw) (Seq.create 1 0)
  else Seq.create nl 0

let hi (c: Seq.seq nat) : Seq.seq nat = carry_run (w5 c) (nl - 1)

let prep (c: Seq.seq nat) : Seq.seq nat =
  if Seq.length c = nw then Seq.append (Seq.slice c 0 nl) (hi c)
  else Seq.create (2 * nl) 0

let w5_ok (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw)
          (ensures Seq.length (w5 c) == nl /\ eval (w5 c) == eval (Seq.slice c nl nw) /\
                   vat (w5 c) (nl - 1) == 0)
  = Seq.lemma_eq_intro (Seq.slice (w5 c) 0 (nl - 1)) (Seq.slice c nl nw);
    eval_pad (w5 c) (nl - 1)

let prep_len (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw) (ensures Seq.length (prep c) == 2 * nl)
  = w5_ok c; carry_run_len (w5 c) (nl - 1)

let prep_ok (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw) (ensures eval (prep c) == eval c)
  = w5_ok c;
    carry_run_len (w5 c) (nl - 1);
    carry_run_ok (w5 c) (nl - 1);
    prep_len c;
    eval_split (prep c) nl;
    eval_split c nl;
    Seq.lemma_eq_intro (Seq.slice (prep c) 0 nl) (Seq.slice c 0 nl);
    Seq.lemma_eq_intro (Seq.slice (prep c) nl (2 * nl)) (hi c)

(** The bound on the carried upper half: four proper digits and a fifth
    limb holding no more than the carry that reached it. *)
let dhi : pos = pow2 57

let prep_ble (c: Seq.seq nat) (cu: nat)
  : Lemma (requires Seq.length c == nw /\ ble c cu /\ cu + dhi < base * (dhi + 1))
          (ensures (forall (i: nat). i < nl ==> vat (prep c) i <= cu) /\
                   (forall (i: nat). nl <= i /\ i < 2 * nl ==> vat (prep c) i <= dhi))
  = w5_ok c;
    assert (ble (w5 c) cu);
    carry_run_top (w5 c) cu dhi (nl - 1);
    carry_run_len (w5 c) (nl - 1);
    prep_len c;
    let h = hi c in
    let u = Seq.slice c 0 nl in
    assert_norm (base <= dhi);
    let aux (i: nat { nl <= i /\ i < 2 * nl }) : Lemma (vat (prep c) i <= dhi) =
      Seq.lemma_index_app2 u h i in
    Classical.forall_intro aux;
    let aux2 (i: nat { i < nl }) : Lemma (vat (prep c) i <= cu) =
      Seq.lemma_index_app1 u h i in
    Classical.forall_intro aux2

(** {3 The carry pass on a shaped number}

    [shchain c0 k] is the bound on limb [k] once the chain has reached it,
    starting from a shaped number whose low limb is at most [c0]: each step
    divides what is left by the base and adds a full digit. *)

let rec shchain (c0: nat) (k: nat) : Tot nat (decreases k) =
  if k = 0 then c0 else base - 1 + shchain c0 (k - 1) / base

#push-options "--fuel 2 --z3rlimit 400"

let rec carry_run_shaped (s: Seq.seq nat) (c0: nat) (k: nat)
  : Lemma (requires shaped s c0 /\ k < nl)
          (ensures (let r = carry_run s k in
                    Seq.length r == nl /\
                    (forall (i: nat). i < k ==> vat r i < base) /\
                    vat r k <= shchain c0 k /\
                    (forall (i: nat). k < i /\ i < nl ==> vat r i < base)))
          (decreases k)
  = carry_run_len s k;
    if k = 0 then ()
    else begin
      carry_run_shaped s c0 (k - 1);
      carry_run_len s (k - 1);
      let r = carry_run s (k - 1) in
      assert (carry_run s k == carry_step (k - 1) r);
      assert (shchain c0 k == base - 1 + shchain c0 (k - 1) / base);
      Math.lemma_div_le (vat r (k - 1)) (shchain c0 (k - 1)) base
    end

#pop-options

#push-options "--fuel 1 --z3rlimit 400"

let pass_shaped (s: Seq.seq nat) (c0 c0': nat)
  : Lemma (requires shaped s c0 /\
                    base - 1 + cf * (shchain c0 (nl - 1) / base) <= c0')
          (ensures shaped (carry_pass s) c0' /\
                   eval (carry_pass s) % prime == eval s % prime)
  = carry_run_shaped s c0 (nl - 1);
    carry_run_len s (nl - 1);
    let r = carry_run s (nl - 1) in
    Math.lemma_div_le (vat r (nl - 1)) (shchain c0 (nl - 1)) base;
    Math.lemma_mult_le_right cf (vat r (nl - 1) / base) (shchain c0 (nl - 1) / base);
    let r1 = Seq.upd r (nl - 1) (vat r (nl - 1) % base) in
    assert (carry_pass s == Seq.upd r1 0 (vat r 0 + cf * (vat r (nl - 1) / base)));
    assert (Seq.length (carry_pass s) == nl);
    assert (vat (carry_pass s) 0 <= base - 1 + cf * (shchain c0 (nl - 1) / base));
    assert (forall (k: nat). 0 < k /\ k < nl ==> vat (carry_pass s) k < base);
    carry_pass_mod s

#pop-options

(** {3 Multiplication, assembled} *)

let colb : pos = nl * (lim * lim)

let fmul_spec (a b: Seq.seq nat) : Seq.seq nat =
  carry_pass (carry_pass (fold (prep (part a b nl))))

#push-options "--fuel 2 --z3rlimit 400"

let fmul_spec_ok (a b: Seq.seq nat)
  : Lemma (requires felem a /\ felem b)
          (ensures felem (fmul_spec a b) /\ fev (fmul_spec a b) == K.fmul (fev a) (fev b))
  = part_ble a b lim lim nl;
    part_len a b nl;
    let p = part a b nl in
    assert_norm (colb + dhi < base * (dhi + 1));
    prep_ble p colb;
    prep_len p;
    prep_ok p;
    let q = prep p in
    fold_ble q colb dhi;
    fold_mod q;
    let f = fold q in
    let c1 = colb + cf * dhi in
    assert_norm (colb + cf * dhi + dhi < base * (dhi + 1));
    carry_pass_shaped f c1 dhi;
    carry_pass_len f;
    carry_pass_mod f;
    let c0 = base - 1 + cf * ((c1 + dhi) / base) in
    let g = carry_pass f in
    assert_norm (base - 1 + cf * (shchain (base - 1 + cf * ((colb + cf * dhi + dhi) / base))
                                          (nl - 1) / base) <= lim);
    pass_shaped g c0 lim;
    shaped_ble (carry_pass g) lim;
    mul_ok a b;
    Math.lemma_mod_mul_distr_l (eval a) (eval b) prime;
    Math.lemma_mod_mul_distr_r (eval a % prime) (eval b) prime

#pop-options
