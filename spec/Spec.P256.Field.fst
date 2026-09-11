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

(** P-256's arithmetic in sixteen limbs, in Montgomery form.

    [Spec.Montgomery256] does the reduction for an arbitrary odd modulus;
    this module is the operations built on it -- addition, subtraction,
    negation, multiplication, and the byte conversions -- stated once over a
    general modulus so that P-256's field prime and its group order are two
    instances of the same code, [fmod] and [qmod], at the bottom of the
    file.

    {b The representation.}  A residue [x] is stored as the sixteen proper
    limbs of [x R mod m], where [R = 2^256].  [mmul] computes
    [a b R^-1 mod m], so it maps [(xR, yR)] to [(xy)R]: the factor survives
    multiplication, and addition and subtraction never noticed it.  Entering
    the representation is [mmul x r2] and leaving it is [mmul x one].

    {b Everything is fully reduced.}  Each operation ends with one
    conditional subtraction and a value is therefore always below its
    modulus.  Curve25519 can afford to be lazy because its reduction
    constant is [38]; here the slack would have to be threaded through
    [mreduce]'s bound, and an extra carry pass per operation is far cheaper
    than that proof.  Being canonical also makes equality of residues
    equality of limbs, which is what the curve's point comparison and
    ECDSA's final check need.

    {b No borrows anywhere.}  Every conditional subtraction is done by
    *adding* the two's complement and reading the carry out.  That is why
    the modulus bundle carries [nm = 2^256 - m] alongside [m]: it turns the
    one operation that would need a borrow chain into one that needs only
    the [addw] and [carry_run] that [Spec.Bignum256] already proves
    everything about. *)
module Spec.P256.Field

open Spec.Bignum256
open Spec.Montgomery256
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module P = Spec.P256

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"

(** {2 A modulus and its companions}

    Five sequences and a word.  All six are compile-time constants in both
    instances, so [modulus_ok] is discharged once by [assert_norm] and never
    appears in a running proof. *)

noeq type modulus = {
  m: pos;               (** the modulus *)
  ms: Seq.seq nat;      (** its limbs *)
  nm: Seq.seq nat;      (** the limbs of [2^256 - m]: subtracting by adding *)
  r1: Seq.seq nat;      (** the limbs of [R mod m], which is [1] in Montgomery form *)
  r2: Seq.seq nat;      (** the limbs of [R^2 mod m], for entering Montgomery form *)
  mu: nat;              (** [-m^-1 mod 2^16] *)
  ri: nat;              (** any [R^-1 mod m]; only ever used to cancel an [R] *)
}

let modulus_ok (d: modulus) : prop =
  mont_ok d.ms d.mu /\ eval d.ms == d.m /\ 1 < d.m /\ d.m < pow2 256 /\
  Seq.length d.nm == nl /\ bnd d.nm base /\ eval d.nm == pow2 256 - d.m /\
  Seq.length d.r1 == nl /\ bnd d.r1 base /\ eval d.r1 == pow2 256 % d.m /\
  Seq.length d.r2 == nl /\ bnd d.r2 base /\ eval d.r2 == pow2 256 * pow2 256 % d.m /\
  pow2 256 * d.ri % d.m == 1

(** A residue: sixteen proper limbs holding a value below the modulus. *)
let res (d: modulus) (s: Seq.seq nat) : prop =
  Seq.length s == nl /\ bnd s base /\ eval s < d.m

(** [s] represents [x] in Montgomery form. *)
let mform (d: modulus) (x: nat) (s: Seq.seq nat) : prop =
  res d s /\ eval s == x * pow2 256 % d.m

(** {2 Building a modulus bundle from its number}

    Rather than write five sequences of sixteen literals per modulus and
    prove each one's [eval], the limbs are read off the number itself.  The
    implementation will of course carry the literals; the specification
    only has to say what they mean. *)

let limbs_n (x: nat) (n: nat) : Seq.seq nat =
  Seq.init #nat n (fun i -> x / pow2 (rad * i) % base)

let rec limbs_n_eval (x: nat) (n: nat)
  : Lemma (ensures Seq.length (limbs_n x n) == n /\ bnd (limbs_n x n) base /\
                   eval (limbs_n x n) == x % pow2 (rad * n))
          (decreases n)
  = if n = 0 then ()
    else begin
      limbs_n_eval (x / base) (n - 1);
      let t = Seq.slice (limbs_n x n) 1 n in
      let aux (i: nat { i < n - 1 })
        : Lemma (Seq.index t i == Seq.index (limbs_n (x / base) (n - 1)) i)
        = Math.pow2_plus rad (rad * i);
          Math.division_multiplication_lemma x base (pow2 (rad * i)) in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro t (limbs_n (x / base) (n - 1));
      Math.pow2_plus rad (rad * (n - 1));
      Math.modulo_division_lemma x base (pow2 (rad * (n - 1)));
      Math.euclidean_division_definition (x % pow2 (rad * n)) base;
      Math.pow2_modulo_modulo_lemma_1 x rad (rad * n)
    end

let limbs (x: nat) : Seq.seq nat = limbs_n x nl

let limbs_ok (x: nat)
  : Lemma (requires x < pow2 256)
          (ensures Seq.length (limbs x) == nl /\ bnd (limbs x) base /\
                   eval (limbs x) == x)
  = limbs_n_eval x nl;
    assert_norm (rad * nl == 256);
    Math.small_mod x (pow2 256)

(** A modulus bundle is determined by three numbers: the modulus, the
    Montgomery constant, and a witness for [R]'s inverse. *)
let mk (m: pos { m < pow2 256 }) (mu ri: nat) : modulus = {
  m = m;
  ms = limbs m;
  nm = limbs (pow2 256 - m);
  r1 = limbs (pow2 256 % m);
  r2 = limbs (pow2 256 * pow2 256 % m);
  mu = mu;
  ri = ri;
}

(** The bottom limb, which is what the Montgomery constant is chosen
    against. *)
let limbs_head (x: nat)
  : Lemma (Seq.length (limbs x) == nl /\ Seq.index (limbs x) 0 == x % base)
  = Seq.init_index_ nl (fun i -> x / pow2 (rad * i) % base) 0;
    assert_norm (pow2 (rad * 0) == 1)

let mk_mont (m: pos { m < pow2 256 }) (mu ri: nat)
  : Lemma (requires 1 < m /\ mu < base /\ ((m % base) * mu + 1) % base == 0)
          (ensures mont_ok (mk m mu ri).ms mu)
  = limbs_ok m;
    limbs_head m

let mk_ok (m: pos { m < pow2 256 }) (mu ri: nat)
  : Lemma (requires 1 < m /\ mu < base /\
                    ((m % base) * mu + 1) % base == 0 /\
                    pow2 256 * ri % m == 1)
          (ensures modulus_ok (mk m mu ri))
  = mk_mont m mu ri;
    limbs_ok m;
    limbs_ok (pow2 256 - m);
    Math.lemma_mod_lt (pow2 256) m;
    limbs_ok (pow2 256 % m);
    Math.lemma_mod_lt (pow2 256 * pow2 256) m;
    limbs_ok (pow2 256 * pow2 256 % m)

(** {2 The conditional subtraction}

    The input is sixteen proper limbs and a top limb that is zero or one,
    together holding a value below [2 m].  Adding [2^256 - m] and reading
    the carry out decides and performs the subtraction at once: the carry is
    one exactly when the low part already exceeds the modulus. *)

(** [eval_bnd] bounds by [pow2 (rad * length)]; saying [pow2 256] instead
    costs Z3 minutes per use if the bridge is left implicit, so it is
    crossed once, here. *)
let ebnd (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base) (ensures eval s < pow2 256)
  = eval_bnd s; assert_norm (rad * nl == 256)

(** Multiplication by a carry is a choice, not a product.  Every bound
    below is linear once the two radix products are eliminated this way --
    leaving them in turns a one-second proof into a ten-minute one. *)
let mul_flag (r: nat) (k: nat)
  : Lemma (requires k <= 1) (ensures r * k == (if k = 1 then r else 0)) = ()

(** The decision itself, stated over a symbolic radix.  Everything here is
    linear once [co] and [top] are split on, and keeping [2^256] out of it
    is the difference between a second and three minutes. *)
let csub_arith (r m ea el co top: nat)
  : Lemma (requires 1 < m /\ m < r /\ ea < r /\ el < r /\ co <= 1 /\ top <= 1 /\
                    ea + r - m == el + (if co = 1 then r else 0) /\
                    ea + (if top = 1 then r else 0) < 2 * m)
          (ensures (if top + co >= 1 then el else ea) ==
                   (let x = ea + (if top = 1 then r else 0) in
                    if x < m then x else x - m))
  = ()

let mcorr_arith (r m el eu co: nat)
  : Lemma (requires 1 < m /\ m < r /\ el >= r - m /\ el < r /\ eu < r /\
                    co <= 1 /\ el + m == eu + (if co = 1 then r else 0))
          (ensures co == 1 /\ eu == el + m - r)
  = ()

let csub (d: modulus) (lo: Seq.seq nat) (top: nat) : Seq.seq nat =
  if top + carry_out (addw lo d.nm) >= 1 then carry_low (addw lo d.nm) else lo

let csub_ok (d: modulus) (lo: Seq.seq nat) (top: nat)
  : Lemma (requires modulus_ok d /\ Seq.length lo == nl /\ bnd lo base /\ top <= 1 /\
                    eval lo + pow2 256 * top < 2 * d.m)
          (ensures res d (csub d lo top) /\
                   eval (csub d lo top) ==
                     (let x = eval lo + pow2 256 * top in
                      if x < d.m then x else x - d.m))
  = let a = addw lo d.nm in
    addw_len lo d.nm;
    addw_ble lo d.nm (base - 1) (base - 1);
    assert_norm (2 * (base - 1) + 1 < base * 2);
    carry_split_bnd a (2 * (base - 1)) 1;
    carry_split_ok a;
    carry_low_len a;
    eval_addw lo d.nm;
    ebnd lo;
    ebnd (carry_low a);
    mul_flag (pow2 256) top;
    mul_flag (pow2 256) (carry_out a);
    csub_arith (pow2 256) d.m (eval lo) (eval (carry_low a)) (carry_out a) top

(** {2 Padding a product out to the reduction's width} *)

let padc (s: Seq.seq nat { Seq.length s <= ncol })
  : (r: Seq.seq nat { Seq.length r == ncol })
  = Seq.append s (Seq.create (ncol - Seq.length s) 0)

let padc_eval (s: Seq.seq nat { Seq.length s <= ncol })
  : Lemma (Seq.length (padc s) == ncol /\ eval (padc s) == eval s /\
           (forall (c: nat). ble s c ==> ble (padc s) c))
  = Seq.lemma_eq_intro (Seq.slice (padc s) 0 (Seq.length s)) s;
    eval_pad (padc s) (Seq.length s)

(** {2 Normalising the reduction's output}

    [mreduce] hands back [nl + 1] lazy columns.  One carry pass over the
    bottom [nl] of them makes those proper and pushes everything else into
    the top one, which is then zero or one because the value is below
    [2 m < 2^257]. *)

let normalize (s: Seq.seq nat { Seq.length s == nl + 1 })
  : (r: Seq.seq nat { Seq.length r == nl + 1 })
  = carry_run_len s nl;
    carry_run s nl

let normalize_ok (s: Seq.seq nat { Seq.length s == nl + 1 }) (c: nat)
  : Lemma (requires ble s c /\ c <= pow2 40 /\ eval s < pow2 257)
          (ensures eval (normalize s) == eval s /\
                   bnd (Seq.slice (normalize s) 0 nl) base /\
                   vat (normalize s) nl <= 1)
  = let r = normalize s in
    carry_run_len s nl;
    carry_run_ok s nl;
    assert_norm (pow2 40 + pow2 25 < base * (pow2 25 + 1));
    carry_run_chained s c (pow2 25) nl;
    eval_split r nl;
    assert_norm (rad * nl == 256);
    assert_norm (pow2 257 == pow2 256 * 2);
    if vat r nl >= 2 then Math.lemma_mult_le_left (pow2 256) 2 (vat r nl)

(** {2 Multiplication} *)

(** The product, padded out to the reduction's width. *)
let prod (a b: Seq.seq nat) : (t: Seq.seq nat { Seq.length t == ncol }) =
  part_len a b nl;
  assert_norm (nl + 1 <= ncol);
  padc (part a b nl)

(** The reduction, normalised: sixteen proper limbs and a top carry. *)
let redc (d: modulus) (t: Seq.seq nat { Seq.length t == ncol })
  : (r: Seq.seq nat { Seq.length r == nl + 1 })
  = mreduce_len d.ms d.mu t;
    normalize (mreduce d.ms d.mu t)

let mmul (d: modulus) (a b: Seq.seq nat) : Seq.seq nat =
  let r = redc d (prod a b) in
  csub d (Seq.slice r 0 nl) (vat r nl)

(** The two numeric facts the bound chain needs, hoisted away from any
    context so that the literals never meet a hypothesis. *)
let cmax : nat = nl * ((base - 1) * (base - 1))

let cmax_fits (_: unit) : Lemma (cmax + nl * pow2 33 <= pow2 40) =
  assert_norm (nl * ((base - 1) * (base - 1)) + nl * pow2 33 <= pow2 40)

let cmax_le (_: unit) : Lemma (cmax <= pow2 40) = assert_norm (cmax <= pow2 40)

let prod_ok (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl /\
                    bnd a base /\ bnd b base)
          (ensures eval (prod a b) == eval a * eval b /\ ble (prod a b) cmax)
  = part_len a b nl;
    assert_norm (nl + 1 <= ncol);
    padc_eval (part a b nl);
    part_ble a b (base - 1) (base - 1) nl;
    mul_ok a b

let redc_ok (d: modulus) (t: Seq.seq nat { Seq.length t == ncol })
  : Lemma (requires modulus_ok d /\ ble t cmax /\ eval t < d.m * pow2 256)
          (ensures (let r = redc d t in
                    bnd (Seq.slice r 0 nl) base /\ vat r nl <= 1 /\
                    eval (Seq.slice r 0 nl) + pow2 256 * vat r nl < 2 * d.m /\
                    pow2 256 * (eval (Seq.slice r 0 nl) + pow2 256 * vat r nl) % d.m
                      == eval t % d.m))
  = cmax_fits ();
    mreduce_ble d.ms d.mu t cmax;
    mreduce_len d.ms d.mu t;
    mreduce_ok d.ms d.mu t;
    mreduce_lt d.ms d.mu t d.m;
    let y = mreduce d.ms d.mu t in
    assert_norm (pow2 257 == 2 * pow2 256);
    normalize_ok y (cmax + nl * pow2 33);
    let r = normalize y in
    eval_split r nl;
    assert_norm (rad * nl == 256)

let mmul_ok (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures res d (mmul d a b) /\
                   pow2 256 * eval (mmul d a b) % d.m == eval a * eval b % d.m)
  = let t = prod a b in
    prod_ok a b;
    Math.lemma_mult_le_right (eval b) (eval a) (d.m - 1);
    Math.lemma_mult_le_left d.m (eval b) (pow2 256);
    redc_ok d t;
    let r = redc d t in
    let lo = Seq.slice r 0 nl in
    let x = eval lo + pow2 256 * vat r nl in
    csub_ok d lo (vat r nl);
    let z = eval (mmul d a b) in
    if x < d.m then ()
    else (Math.lemma_mod_sub x d.m 1;
          Math.lemma_mod_mul_distr_r (pow2 256) x d.m;
          Math.lemma_mod_mul_distr_r (pow2 256) (x - d.m) d.m)

(** The reason for all of it: [mmul] is multiplication of residues once the
    factor [R] is accounted for.  Cancelling the [R] is where [ri] earns its
    place in the bundle -- F* has no modular-inverse theory, so the witness
    is supplied as a constant and checked by [assert_norm]. *)
let mmul_form (d: modulus) (x y: nat) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ mform d x a /\ mform d y b)
          (ensures mform d (x * y % d.m) (mmul d a b))
  = mmul_ok d a b;
    let r = pow2 256 in
    let z = eval (mmul d a b) in
    (* [R z = a b] and [a = x R], [b = y R] modulo [m]. *)
    Math.lemma_mod_mul_distr_l (x * r) (eval b) d.m;
    Math.lemma_mod_mul_distr_r (x * r) (y * r) d.m;
    assert (r * z % d.m == x * r * (y * r) % d.m);
    (* multiply both sides by [ri] and use [R ri = 1]. *)
    Math.lemma_mod_mul_distr_l (r * z) d.ri d.m;
    Math.lemma_mod_mul_distr_l (x * r * (y * r)) d.ri d.m;
    assert (r * z * d.ri % d.m == x * r * (y * r) * d.ri % d.m);
    Math.paren_mul_right r z d.ri;
    Math.swap_mul z d.ri;
    Math.paren_mul_right r d.ri z;
    Math.lemma_mod_mul_distr_l (r * d.ri) z d.m;
    Math.small_mod z d.m;
    assert (r * z * d.ri % d.m == z);
    Math.paren_mul_right (x * r) (y * r) d.ri;
    Math.paren_mul_right y r d.ri;
    Math.lemma_mod_mul_distr_r (x * r * y) (r * d.ri) d.m;
    Math.small_mod (x * r * y % d.m) d.m;
    assert (z == x * r * y % d.m);
    Math.paren_mul_right x r y;
    Math.swap_mul r y;
    Math.paren_mul_right x y r;
    Math.lemma_mod_mul_distr_l (x * y) r d.m

(** {2 Addition and subtraction}

    Both are one pointwise pass and one conditional subtraction; neither
    disturbs the Montgomery factor, because it distributes over a sum. *)

let madd (d: modulus) (a b: Seq.seq nat) : Seq.seq nat =
  csub d (carry_low (addw a b)) (carry_out (addw a b))

let madd_ok (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures res d (madd d a b) /\
                   eval (madd d a b) == (eval a + eval b) % d.m)
  = let t = addw a b in
    addw_ble a b (base - 1) (base - 1);
    addw_len a b;
    assert_norm (2 * (base - 1) + 1 < base * 2);
    carry_split_bnd t (2 * (base - 1)) 1;
    carry_split_ok t;
    eval_addw a b;
    carry_low_len t;
    csub_ok d (carry_low t) (carry_out t);
    if eval a + eval b < d.m then Math.small_mod (eval a + eval b) d.m
    else Math.lemma_mod_sub (eval a + eval b) d.m 1

(** The complement, so that a subtraction is an addition.  [compl s] holds
    [2^16 - 1 - s_i] in each limb, so [compl s + s] is all ones. *)
let compl (s: Seq.seq nat) : Seq.seq nat =
  Seq.init #nat nl (fun i -> (base - 1) - (if vat s i < base then vat s i else base - 1))

let compl_ok (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures Seq.length (compl s) == nl /\ bnd (compl s) base /\
                   eval (compl s) == pow2 256 - 1 - eval s)
  = Seq.lemma_eq_intro (addw (compl s) s) (ones nl);
    eval_addw (compl s) s;
    eval_ones nl;
    assert_norm (rad * nl == 256)

(** One at limb zero. *)
let unit1 : Seq.seq nat = Seq.upd (Seq.create nl 0) 0 1

let unit1_ok (_: unit)
  : Lemma (Seq.length unit1 == nl /\ bnd unit1 base /\ eval unit1 == 1)
  = eval_upd (Seq.create nl 0) 0 1;
    eval_zeros (Seq.create nl 0)

(** [2^256 - b], with every limb below [2^16 + 1]. *)
let negw (b: Seq.seq nat) : Seq.seq nat = addw (compl b) unit1

let negw_ok (b: Seq.seq nat)
  : Lemma (requires Seq.length b == nl /\ bnd b base)
          (ensures Seq.length (negw b) == nl /\ ble (negw b) base /\
                   eval (negw b) == pow2 256 - eval b)
  = compl_ok b; unit1_ok (); eval_addw (compl b) unit1;
    addw_ble (compl b) unit1 (base - 1) 1

(** [a - b] is [a + (2^256 - b)]: the carry out is one exactly when
    [a >= b], and when it is not, one further addition of the modulus
    corrects the result. *)
let msub (d: modulus) (a b: Seq.seq nat) : Seq.seq nat =
  let t = addw a (negw b) in
  if carry_out t = 1 then carry_low t
  else carry_low (addw (carry_low t) d.ms)

(** The shape of the sum before the correction: a proper low half and a
    carry that is one exactly when [a >= b]. *)
let msub_pre (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures (let t = addw a (negw b) in
                    Seq.length t == nl /\ bnd (carry_low t) base /\
                    carry_out t <= 1 /\
                    eval (carry_low t)
                      + (if carry_out t = 1 then pow2 256 else 0)
                      == eval a + pow2 256 - eval b))
  = let t = addw a (negw b) in
    negw_ok b;
    addw_len a (negw b);
    addw_ble a (negw b) (base - 1) base;
    assert_norm (base - 1 + base + 2 < base * 3);
    carry_split_bnd t (base - 1 + base) 2;
    carry_split_ok t;
    eval_addw a (negw b);
    carry_low_len t;
    ebnd (carry_low t);
    mul_flag (pow2 256) (carry_out t)

(** When the subtraction went negative the low half sits just under
    [2^256]; adding the modulus overflows by exactly one, and dropping that
    overflow is the correction. *)
let mcorr (d: modulus) (lo: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ Seq.length lo == nl /\ bnd lo base /\
                    eval lo >= pow2 256 - d.m)
          (ensures res d (carry_low (addw lo d.ms)) /\
                   eval (carry_low (addw lo d.ms)) == eval lo + d.m - pow2 256)
  = let u = addw lo d.ms in
    addw_len lo d.ms;
    addw_ble lo d.ms (base - 1) (base - 1);
    assert_norm (2 * (base - 1) + 1 < base * 2);
    carry_split_bnd u (2 * (base - 1)) 1;
    carry_split_ok u;
    eval_addw lo d.ms;
    carry_low_len u;
    ebnd lo;
    ebnd (carry_low u);
    mul_flag (pow2 256) (carry_out u);
    mcorr_arith (pow2 256) d.m (eval lo) (eval (carry_low u)) (carry_out u)

let msub_ok (d: modulus) (a b: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b)
          (ensures res d (msub d a b) /\
                   eval (msub d a b) == (eval a + d.m - eval b) % d.m)
  = msub_pre d a b;
    let t = addw a (negw b) in
    carry_low_len t;
    let lo = carry_low t in
    ebnd lo;
    if carry_out t = 1 then begin
      Math.lemma_mod_sub (eval a + d.m - eval b) d.m 1;
      Math.small_mod (eval a - eval b) d.m
    end else begin
      mcorr d lo;
      Math.small_mod (eval a + d.m - eval b) d.m
    end

(** Negation, which is a subtraction from zero except that zero must stay
    zero rather than become the modulus. *)
let mzero : Seq.seq nat = Seq.create nl 0

let mzero_ok (_: unit)
  : Lemma (Seq.length mzero == nl /\ bnd mzero base /\ eval mzero == 0)
  = eval_zeros mzero

let mneg (d: modulus) (a: Seq.seq nat) : Seq.seq nat = msub d mzero a

let mneg_ok (d: modulus) (a: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a)
          (ensures res d (mneg d a) /\ eval (mneg d a) == (d.m - eval a) % d.m)
  = mzero_ok (); msub_ok d mzero a

(** {2 Entering and leaving Montgomery form} *)

let to_mont (d: modulus) (a: Seq.seq nat) : Seq.seq nat = mmul d a d.r2
let from_mont (d: modulus) (a: Seq.seq nat) : Seq.seq nat = mmul d a unit1

(** {2 Big-endian bytes}

    P-256 serialises most significant byte first, so limb [k] -- the [k]-th
    least significant -- is the byte pair at the *end* of the buffer.  The
    two lemmas are stated relationally on whatever the loop has built, in
    the same style as [Spec.Bignum256]'s little-endian pair. *)

let bat (b: Seq.seq S8.t) (i: nat) : GTot nat =
  if i < Seq.length b then S8.v (Seq.index b i) else 0

let be_pair (b: Seq.seq S8.t) (n: pos) (k: nat { k < n }) : GTot nat =
  256 * bat b (2 * (n - 1 - k)) + bat b (2 * (n - 1 - k) + 1)

#push-options "--fuel 4"
let rec eval_bytes_be (b: Seq.seq S8.t) (s: Seq.seq nat)
  : Lemma (requires Seq.length b == 2 * Seq.length s /\
                    (forall (k: nat). k < Seq.length s ==>
                       Seq.index s k == be_pair b (Seq.length s) k))
          (ensures eval s == be_nat b)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let b' = Seq.slice b 0 (2 * n - 2) in
      let s' = Seq.slice s 1 n in
      be_nat_snoc b (2 * n - 2);
      be_nat_snoc b (2 * n - 1);
      Seq.lemma_eq_intro (Seq.slice b 0 (2 * n)) b;
      Seq.lemma_eq_intro (Seq.slice b 0 (2 * n - 2)) b';
      assert (be_nat b == be_nat b' * 256 * 256 +
                          bat b (2 * n - 2) * 256 + bat b (2 * n - 1));
      let aux (k: nat { k < n - 1 }) : Lemma (Seq.index s' k == be_pair b' (n - 1) k) =
        assert (2 * (n - 1 - (k + 1)) == 2 * ((n - 1) - 1 - k));
        assert (bat b' (2 * ((n - 1) - 1 - k)) == bat b (2 * (n - 1 - (k + 1))));
        assert (bat b' (2 * ((n - 1) - 1 - k) + 1) == bat b (2 * (n - 1 - (k + 1)) + 1)) in
      Classical.forall_intro aux;
      eval_bytes_be b' s'
    end
#pop-options

(** Which limb a byte belongs to, and where in it: pure index arithmetic,
    kept away from the [pow2] facts it is used beside. *)
let be_index_arith (i: nat { i < 32 })
  : Lemma (let k = 15 - i / 2 in
           k < nl /\ 2 * (nl - 1 - k) == 2 * (i / 2) /\
           (if i % 2 = 1 then 8 * (32 - 1 - i) == rad * k
                         else 8 * (32 - 1 - i) == rad * k + 8))
  = assert_norm (rad == 16);
    assert_norm (nl == 16);
    Math.euclidean_division_definition i 2

let store_be_ok (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\ bnd s base /\
                    (forall (k: nat). k < nl ==>
                       bat b (2 * (nl - 1 - k)) == Seq.index s k / 256 /\
                       bat b (2 * (nl - 1 - k) + 1) == Seq.index s k % 256))
          (ensures b == nat_to_be 32 (eval s))
  = let v = eval s in
    ebnd s;
    let aux (i: nat { i < 32 }) : Lemma (Seq.index b i == Seq.index (nat_to_be 32 v) i) =
      let k = 15 - i / 2 in
      eval_digit s k;
      nat_to_be_index 32 v i;
      Math.pow2_plus (rad * k) 8;
      be_index_arith i;
      if i % 2 = 1 then
        Math.pow2_modulo_modulo_lemma_1 (v / pow2 (rad * k)) 8 rad
      else begin
        Math.pow2_modulo_division_lemma_1 (v / pow2 (rad * k)) 8 rad;
        Math.division_multiplication_lemma v (pow2 (rad * k)) (pow2 8)
      end;
      S8.v_extensional (Seq.index b i) (Seq.index (nat_to_be 32 v) i) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro b (nat_to_be 32 v)

(** {2 The two instances}

    [mu] is [-m^-1 mod 2^16] and [ri] is [R^-1 mod m]; both are checked by
    normalisation, which is the only place in the module where the moduli
    appear as numbers at all.  The field prime's [mu] is [1], a small gift
    from its Solinas shape -- the only one this representation collects. *)

let fmod : modulus =
  assert_norm (P.prime < pow2 256);
  mk P.prime 1
     0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000

let fmod_ok (_: unit) : Lemma (modulus_ok fmod) =
  assert_norm (P.prime < pow2 256);
  assert_norm (1 < P.prime);
  assert_norm (1 < pow2 rad);
  assert_norm (((P.prime % pow2 rad) * 1 + 1) % pow2 rad == 0);
  assert_norm (pow2 256 *
    0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000
    % P.prime == 1);
  mk_ok P.prime 1
    0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000

let qmod : modulus =
  assert_norm (P.order < pow2 256);
  mk P.order 48207
     0x60d066334905c1e907f8b6041e607725badef3e243566fafce1bc8f79c197c79

let qmod_ok (_: unit) : Lemma (modulus_ok qmod) =
  assert_norm (P.order < pow2 256);
  assert_norm (1 < P.order);
  assert_norm (48207 < pow2 rad);
  assert_norm (((P.order % pow2 rad) * 48207 + 1) % pow2 rad == 0);
  assert_norm (pow2 256 *
    0x60d066334905c1e907f8b6041e607725badef3e243566fafce1bc8f79c197c79
    % P.order == 1);
  mk_ok P.order 48207
    0x60d066334905c1e907f8b6041e607725badef3e243566fafce1bc8f79c197c79

#pop-options
