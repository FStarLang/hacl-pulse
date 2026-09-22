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

(** Arithmetic on a 256-bit modulus in four limbs, in Montgomery form.

    [Spec.Montgomery4] does the reduction for an arbitrary odd modulus;
    this module is the operations built on it -- addition, subtraction,
    negation, multiplication, and the byte conversions -- stated once over a
    general modulus.  There are four instances: P-256's field prime and
    group order in {!Spec.P256.Field}, and secp256k1's in
    {!Spec.K256.Field}.

    {b The representation.}  A residue [x] is stored as the four proper
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
    the [addw] and [carry_run] that [Spec.Bignum4] already proves
    everything about. *)
module Spec.Field4

open Spec.Bignum4
open Spec.Montgomery4
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module Loops = Hacl.Spec.Loops

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
  mu: nat;              (** [-m^-1 mod 2^64] *)
  ri: nat;              (** any [R^-1 mod m]; only ever used to cancel an [R] *)
}

let modulus_ok (d: modulus) : prop =
  mont_ok d.ms d.mu /\ eval d.ms == d.m /\ 1 < d.m /\ d.m < pow2 256 /\
  Seq.length d.nm == nl /\ bnd d.nm base /\ eval d.nm == pow2 256 - d.m /\
  Seq.length d.r1 == nl /\ bnd d.r1 base /\ eval d.r1 == pow2 256 % d.m /\
  Seq.length d.r2 == nl /\ bnd d.r2 base /\ eval d.r2 == pow2 256 * pow2 256 % d.m /\
  pow2 256 * d.ri % d.m == 1

(** A residue: eight proper limbs holding a value below the modulus. *)
let res (d: modulus) (s: Seq.seq nat) : prop =
  Seq.length s == nl /\ bnd s base /\ eval s < d.m

(** [s] represents [x] in Montgomery form. *)
let mform (d: modulus) (x: nat) (s: Seq.seq nat) : prop =
  res d s /\ eval s == x * pow2 256 % d.m

(** {2 Building a modulus bundle from its number}

    Rather than write five sequences of eight literals per modulus and
    prove each one's [eval], the limbs are read off the number itself.  The
    implementation will of course carry the literals; the specification
    only has to say what they mean. *)

let limbs_n (x: nat) (n: nat) : Seq.seq nat =
  Seq.init #nat n (fun i -> x / pow2 (rad * i) % base)

#push-options "--z3rlimit 400"
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
      Math.distributivity_add_right rad 1 (n - 1);
      assert (rad * n == rad + rad * (n - 1));
      Math.pow2_plus rad (rad * (n - 1));
      assert (pow2 (rad * n) == base * pow2 (rad * (n - 1)));
      Math.modulo_division_lemma x base (pow2 (rad * (n - 1)));
      Math.euclidean_division_definition (x % pow2 (rad * n)) base;
      Math.pow2_modulo_modulo_lemma_1 x rad (rad * n)
    end
#pop-options

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

    The input is eight proper limbs and a top limb that is zero or one,
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
  : Lemma (requires ble s c /\ c <= pow2 72 /\ eval s < pow2 257)
          (ensures eval (normalize s) == eval s /\
                   bnd (Seq.slice (normalize s) 0 nl) base /\
                   vat (normalize s) nl <= 1)
  = let r = normalize s in
    carry_run_len s nl;
    carry_run_ok s nl;
    assert_norm (pow2 72 + pow2 9 < base * (pow2 9 + 1));
    carry_run_chained s c (pow2 9) nl;
    eval_split r nl;
    assert_norm (rad * nl == 256);
    assert_norm (pow2 257 == pow2 256 * 2);
    if vat r nl >= 2 then Math.lemma_mult_le_left (pow2 256) 2 (vat r nl)

(** {3 Splitting the normalisation}

    The lemmas below relate the full pass to a pass run on a prefix, which
    is what a caller that keeps the limbs and the top column in separate
    buffers needs: steps [0] to [nl - 2] never look above limb [nl - 1],
    and step [nl - 1] is exactly the split that [carry_low] and
    [carry_out] perform. *)

let carry_runr (s: Seq.seq nat) (k: nat)
  : (r: Seq.seq nat { Seq.length r == Seq.length s /\ r == carry_run s k })
  = carry_run_len s k; carry_run s k

let rec carry_run_prefix (s: Seq.seq nat) (n: nat) (k: nat)
  : Lemma (requires n <= Seq.length s /\ k < n)
          (ensures Seq.slice (carry_runr s k) 0 n == carry_runr (Seq.slice s 0 n) k)
          (decreases k)
  = carry_run_len s k;
    carry_run_len (Seq.slice s 0 n) k;
    if k = 0 then Seq.lemma_eq_intro (Seq.slice (carry_run s 0) 0 n)
                                     (carry_run (Seq.slice s 0 n) 0)
    else begin
      carry_run_prefix s n (k - 1);
      carry_run_len s (k - 1);
      carry_run_len (Seq.slice s 0 n) (k - 1);
      Loops.unfold_repeati k carry_step s;
      Loops.unfold_repeati k carry_step (Seq.slice s 0 n);
      Seq.lemma_eq_intro
        (Seq.slice (carry_step (k - 1) (carry_run s (k - 1))) 0 n)
        (carry_step (k - 1) (Seq.slice (carry_run s (k - 1)) 0 n))
    end

let rec carry_run_above (s: Seq.seq nat) (k: nat) (i: nat)
  : Lemma (requires k < i /\ i < Seq.length s)
          (ensures vat (carry_run s k) i == vat s i)
          (decreases k)
  = carry_run_len s k;
    if k = 0 then ()
    else begin
      carry_run_above s (k - 1) i;
      carry_run_len s (k - 1);
      Loops.unfold_repeati k carry_step s
    end

let normalize_split (s: Seq.seq nat { Seq.length s == nl + 1 })
  : Lemma (Seq.slice (normalize s) 0 nl == carry_low (Seq.slice s 0 nl) /\
           vat (normalize s) nl ==
             vat s nl + carry_out (Seq.slice s 0 nl))
  = let p = Seq.slice s 0 nl in
    carry_run_len s nl;
    carry_run_len s (nl - 1);
    carry_run_len p (nl - 1);
    carry_run_prefix s nl (nl - 1);
    carry_run_above s (nl - 1) nl;
    Loops.unfold_repeati nl carry_step s;
    let r = carry_run s (nl - 1) in
    Seq.lemma_eq_intro (Seq.slice (carry_step (nl - 1) r) 0 nl)
                       (carry_low p)

(** {2 Multiplication} *)

(** The product, padded out to the reduction's width. *)
let prod (a b: Seq.seq nat) : (t: Seq.seq nat { Seq.length t == ncol }) =
  part_len a b nl;
  assert_norm (nl + 1 <= ncol);
  padc (part a b nl)

(** The reduction, normalised: eight proper limbs and a top carry. *)
let redc (d: modulus) (t: Seq.seq nat { Seq.length t == ncol })
  : (r: Seq.seq nat { Seq.length r == nl + 1 })
  = mreduce_len d.ms d.mu t;
    normalize (mreduce d.ms d.mu t)

let mmul (d: modulus) (a b: Seq.seq nat) : Seq.seq nat =
  let r = redc d (prod a b) in
  csub d (Seq.slice r 0 nl) (vat r nl)

(** The two numeric facts the bound chain needs, hoisted away from any
    context so that the literals never meet a hypothesis. *)
let cmax : nat = nl * (2 * (base - 1))

let cmax_fits (_: unit) : Lemma (cmax + nl * pow2 66 <= pow2 72) =
  assert_norm (nl * (2 * (base - 1)) + nl * pow2 66 <= pow2 72)

let cmax_le (_: unit) : Lemma (cmax <= pow2 72) = assert_norm (cmax <= pow2 72)

let prod_ok (a b: Seq.seq nat)
  : Lemma (requires Seq.length a == nl /\ Seq.length b == nl /\
                    bnd a base /\ bnd b base)
          (ensures eval (prod a b) == eval a * eval b /\ ble (prod a b) cmax)
  = part_len a b nl;
    assert_norm (nl + 1 <= ncol);
    padc_eval (part a b nl);
    part_ble a b nl;
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
    normalize_ok y (cmax + nl * pow2 66);
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
    [2^32 - 1 - s_i] in each limb, so [compl s + s] is all ones. *)
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

(** [2^256 - b], with every limb below [2^32 + 1]. *)
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

    Both curves serialise most significant byte first, so limb [k] -- the
    [k]-th least significant -- is the eight-byte group at the *end* of the
    buffer.  The lemmas are stated relationally on whatever the loop has
    built, in the same style as [Spec.Bignum256]'s little-endian pair, and
    for the same reason they are split until no one of them needs the
    solver to guess a witness.

    The eight is written out rather than derived from [rad]: [8 * k] is
    linear arithmetic and [(rad / 8) * k] is not. *)

let bat (b: Seq.seq S8.t) (i: nat) : GTot nat =
  if i < Seq.length b then S8.v (Seq.index b i) else 0

(** The eight bytes of limb [k], most significant first. *)
let be_oct (b: Seq.seq S8.t) (n: pos) (k: nat { k < n }) : GTot nat =
  72057594037927936 * bat b (8 * (n - 1 - k)) +
  281474976710656 * bat b (8 * (n - 1 - k) + 1) +
  1099511627776 * bat b (8 * (n - 1 - k) + 2) +
  4294967296 * bat b (8 * (n - 1 - k) + 3) +
  16777216 * bat b (8 * (n - 1 - k) + 4) +
  65536 * bat b (8 * (n - 1 - k) + 5) +
  256 * bat b (8 * (n - 1 - k) + 6) +
  bat b (8 * (n - 1 - k) + 7)

(** The eight bytes at the right offset really are the limb.  Unfolding
    [be_nat] eight times over a window whose entries are all bytes stays
    linear; unfolding it over a window with an opaque prefix does not, which
    is why the recursion below cuts with {!be_nat_split} instead. *)
#push-options "--fuel 9 --ifuel 1 --z3rlimit 200"
let be_oct_ok (b: Seq.seq S8.t) (n: pos) (k: nat { k < n })
  : Lemma (requires Seq.length b == 8 * n)
          (ensures (let o = 8 * (n - 1 - k) in
                    be_nat (Seq.slice b o (o + 8)) == be_oct b n k))
  = let o = 8 * (n - 1 - k) in
    let w = Seq.slice b o (o + 8) in
    be_nat_snoc w 0;
    be_nat_snoc w 1;
    be_nat_snoc w 2;
    be_nat_snoc w 3;
    be_nat_snoc w 4;
    be_nat_snoc w 5;
    be_nat_snoc w 6;
    be_nat_snoc w 7;
    Seq.lemma_eq_intro (Seq.slice w 0 8) w
#pop-options

(** The limb-wise reading of a byte string is its big-endian value.  The
    recursion drops the *last* eight bytes, which are the least significant
    limb, so the induction is on [Seq.slice s 1 n] exactly as in the
    little-endian twin. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
let rec eval_bytes_be (b: Seq.seq S8.t) (s: Seq.seq nat)
  : Lemma (requires Seq.length b == 8 * Seq.length s /\
                    (forall (k: nat). {:pattern (Seq.index s k)}
                       k < Seq.length s ==> Seq.index s k == be_oct b (Seq.length s) k))
          (ensures eval s == be_nat b)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let b' = Seq.slice b 0 (8 * n - 8) in
      let s' = Seq.slice s 1 n in
      be_nat_split b 8;
      be_oct_ok b n 0;
      assert_norm (pow2 (8 * 8) == base);
      assert (be_nat b == be_nat b' * base + Seq.index s 0);
      eval_split s 1;
      assert (eval (Seq.slice s 0 1) == Seq.index s 0);
      assert_norm (pow2 (rad * 1) == base);
      let aux (k: nat { k < n - 1 }) : Lemma (Seq.index s' k == be_oct b' (n - 1) k) =
        assert (8 * (n - 1 - (k + 1)) == 8 * ((n - 1) - 1 - k));
        assert (bat b' (8 * ((n - 1) - 1 - k)) == bat b (8 * (n - 1 - (k + 1))));
        assert (bat b' (8 * ((n - 1) - 1 - k) + 1) == bat b (8 * (n - 1 - (k + 1)) + 1));
        assert (bat b' (8 * ((n - 1) - 1 - k) + 2) == bat b (8 * (n - 1 - (k + 1)) + 2));
        assert (bat b' (8 * ((n - 1) - 1 - k) + 3) == bat b (8 * (n - 1 - (k + 1)) + 3));
        assert (bat b' (8 * ((n - 1) - 1 - k) + 4) == bat b (8 * (n - 1 - (k + 1)) + 4));
        assert (bat b' (8 * ((n - 1) - 1 - k) + 5) == bat b (8 * (n - 1 - (k + 1)) + 5));
        assert (bat b' (8 * ((n - 1) - 1 - k) + 6) == bat b (8 * (n - 1 - (k + 1)) + 6));
        assert (bat b' (8 * ((n - 1) - 1 - k) + 7) == bat b (8 * (n - 1 - (k + 1)) + 7)) in
      Classical.forall_intro aux;
      eval_bytes_be b' s'
    end
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 400"

(** [rad] is a definition rather than a literal, so [rad * k] is a product
    of two opaque terms; this puts it back in linear form. *)
let radf_lin (k: nat) : Lemma (rad * k == 64 * k) = assert_norm (rad == 64)

(** Byte [m] of limb [k], counted from the top of the limb, is byte
    [64 * k + 8 * (7 - m)] of the number. *)
let store_be_digit (s: Seq.seq nat) (k: nat { k < Seq.length s }) (m: nat { m < 8 })
  : Lemma (requires bnd s base)
          (ensures (Seq.index s k / pow2 (8 * (7 - m))) % 256 ==
                   (eval s / pow2 (64 * k + 8 * (7 - m))) % 256)
  = let v = eval s in
    radf_lin k;
    assert_norm (base == 18446744073709551616);
    assert_norm (pow2 64 == 18446744073709551616);
    eval_digit s k;
    let a = v / pow2 (64 * k) in
    Math.pow2_plus (64 * k) (8 * (7 - m));
    Math.division_multiplication_lemma v (pow2 (64 * k)) (pow2 (8 * (7 - m)));
    Math.pow2_modulo_division_lemma_1 a (8 * (7 - m)) 64;
    Math.pow2_modulo_modulo_lemma_1 (a / pow2 (8 * (7 - m))) 8 (64 - 8 * (7 - m))

(** Where byte [i] of a thirty-two byte big-endian string lives: limb
    [3 - i / 8], byte [i % 8] of it counted from the top.  Pure index
    arithmetic, kept apart from the [pow2] facts it is used beside. *)
let be_index_arith (i: nat { i < 32 })
  : Lemma (let k = 3 - i / 8 in
           k < nl /\ 8 * (nl - 1 - k) == 8 * (i / 8) /\ i % 8 < 8 /\
           8 * (32 - 1 - i) == 64 * k + 8 * (7 - i % 8))
  = assert_norm (nl == 4);
    Math.lemma_mod_lt i 8;
    Math.euclidean_division_definition i 8

(** The eight byte weights inside a limb, as literals. *)
let pow2_byte_be (m: nat { m < 8 })
  : Lemma (pow2 (8 * (7 - m)) == (if m = 7 then 1
                                  else if m = 6 then 256
                                  else if m = 5 then 65536
                                  else if m = 4 then 16777216
                                  else if m = 3 then 4294967296
                                  else if m = 2 then 1099511627776
                                  else if m = 1 then 281474976710656
                                  else 72057594037927936))
  =     assert_norm (pow2 0 == 1);
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 16 == 65536);
    assert_norm (pow2 24 == 16777216);
    assert_norm (pow2 32 == 4294967296);
    assert_norm (pow2 40 == 1099511627776);
    assert_norm (pow2 48 == 281474976710656);
    assert_norm (pow2 56 == 72057594037927936)

(** A store loop divides by literals; {!store_be_ok} divides by a power of
    two. *)
let digit_be (x: nat) (m: nat { m < 8 }) (y: nat)
  : Lemma (requires y == (if m = 7 then x % 256
                          else if m = 6 then x / 256 % 256
                          else if m = 5 then x / 65536 % 256
                          else if m = 4 then x / 16777216 % 256
                          else if m = 3 then x / 4294967296 % 256
                          else if m = 2 then x / 1099511627776 % 256
                          else if m = 1 then x / 281474976710656 % 256
                          else x / 72057594037927936 % 256))
          (ensures y == (x / pow2 (8 * (7 - m))) % 256)
  = pow2_byte_be m

(** Byte [8 (nl - 1 - k) + m] belongs to limb [k], digit [7 - m]. *)
let split8_be (k: nat { k < nl }) (m: nat { m < 8 })
  : Lemma ((8 * (nl - 1 - k) + m) / 8 == nl - 1 - k /\
           (8 * (nl - 1 - k) + m) % 8 == m /\
           3 - (8 * (nl - 1 - k) + m) / 8 == k)
  = assert_norm (nl == 4);
    Math.lemma_div_plus m (nl - 1 - k) 8;
    Math.lemma_mod_plus m (nl - 1 - k) 8;
    Math.small_div m 8;
    Math.small_mod m 8

(** Writing each limb out as eight bytes, most significant first and most
    significant limb first, produces the big-endian encoding.

    The hypothesis is quantified over the byte position and stated with
    [pow2] rather than spelled out as eight divisions by literals.  Eight
    simultaneous division facts about the same limb are ruinous for the
    solver -- a version of this lemma that carried them explicitly took
    minutes rather than seconds -- whereas a quantifier costs one
    instantiation per byte.  {!digit_be} is the bridge a store loop uses to
    produce the quantified form one byte at a time. *)
let store_be_ok (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\ bnd s base /\
                    (forall (k: nat) (m: nat). k < nl /\ m < 8 ==>
                       bat b (8 * (nl - 1 - k) + m) ==
                         (Seq.index s k / pow2 (8 * (7 - m))) % 256))
          (ensures b == nat_to_be 32 (eval s))
  = let v = eval s in
    ebnd s;
    assert_norm (nl == 4);
    let aux (i: nat { i < 32 }) : Lemma (Seq.index b i == Seq.index (nat_to_be 32 v) i) =
      let k = 3 - i / 8 in
      let m = i % 8 in
      Math.lemma_mod_lt i 8;
      Math.euclidean_division_definition i 8;
      be_index_arith i;
      split8_be k m;
      store_be_digit s k m;
      nat_to_be_index 32 v i;
      S8.v_extensional (Seq.index b i) (Seq.index (nat_to_be 32 v) i) in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro b (nat_to_be 32 v)

#pop-options

#pop-options
