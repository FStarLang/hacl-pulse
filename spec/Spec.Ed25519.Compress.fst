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

(** Decompression inverts compression.

    The verifier never sees the signer's points, only their thirty-two
    byte encodings, so for an honest signature to verify the points it
    decodes must be the points that were encoded.  This module proves that
    {!Spec.Ed25519.point_decompress} applied to
    {!Spec.Ed25519.point_compress}[ p] succeeds and returns a point
    projectively equal to [p], for every [p] on the curve
    ({!decompress_compress}).

    {2 The argument}

    Compression normalises to the affine [(x, y)] and writes [y] with the
    low bit of [x] on top.  Decompression reads them back and must recover
    [x] from [y] and that bit, which takes three facts:

    - the affine equation [y^2 - x^2 = 1 + d x^2 y^2] holds, which is the
      projective one divided by [Z^4] ({!affine_eq});
    - so [x^2 (d y^2 + 1) = y^2 - 1], and the denominator [d y^2 + 1] does
      not vanish, because if it did then [y^2 = 1] and [d = -1], which it
      is not ({!recover_x_affine});
    - [sqrt_of] finds a square root of every square ({!sqrt_of_square}).
      Its candidate is [a^((p+3)/8)]; for [a = x^2] the square of that is
      [h x^2] with [h = x^((p-1)/2)], and [h^2 = x^(p-1) = 1] by Fermat, so
      [h] is [1] or [-1].  In the first case the candidate is a root; in
      the second, multiplying by [sqrt(-1)] makes it one.

    The two square roots of [x^2] are [x] and [-x], and since [p] is odd
    exactly one of them has the parity that was encoded, unless [x = 0],
    when they coincide.

    The polynomial identities are proved over the integers, by
    [FStar.Tactics.CanonCommSemiring.int_cr] on an integer shadow of each
    field expression, so the solver never has to look at [2^255 - 19]. *)
module Spec.Ed25519.Compress

open Spec.Curve25519
open Spec.Ed25519

module MA = Spec.ModArith
module M = FStar.Math.Lemmas
module E = FStar.Math.Euclid
module CS = FStar.Tactics.CanonCommSemiring
module T = FStar.Tactics.V2
module B = Hacl.Spec.Bytes
module F = Spec.Group.Field

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Field facts}

    The handful [Spec.Ed25519.Group] proves privately, restated through
    [Spec.Group.Field] at [prime]. *)

let prime_lem () : Lemma (E.is_prime prime) = Spec.Group.Primes.prime_25519 ()

let pm : (m: pos { 1 < m }) = prime_gt_one (); prime

#push-options "--fuel 1"
let rec fexp_exp (x: elem) (n: nat)
  : Lemma (ensures fexp x n == MA.exp #pm x n) (decreases n)
  = if n = 0 then () else fexp_exp x (n - 1)

let fexp_zero_base (n: pos) : Lemma (fexp 0 n == 0) = ()
#pop-options

let finv_inv (x: elem) : Lemma (finv x == MA.inv #pm x) = prime_gt_one (); fexp_exp x (pm - 2)

let mul_finv (z: elem) : Lemma (requires z <> 0) (ensures fmul z (finv z) == one) =
  prime_lem (); finv_inv z; F.mul_inv #prime z

let div_mul (x z: elem) : Lemma (requires z <> 0) (ensures fmul (fmul x (finv z)) z == x) =
  prime_lem (); finv_inv z; F.div_mul #prime x z

let mul_nz (x y: elem) : Lemma (requires x <> 0 /\ y <> 0) (ensures fmul x y <> 0) =
  prime_lem (); F.mul_nonzero #prime x y

let cancel (a b c: elem) : Lemma (requires c <> 0 /\ fmul a c == fmul b c) (ensures a == b) =
  prime_lem (); F.cancel #prime a b c

let mul4 (a b c d: elem) : Lemma (fmul (fmul a b) (fmul c d) == fmul (fmul a c) (fmul b d)) =
  F.mul4 #prime a b c d

let fermat (x: elem) : Lemma (requires x <> 0) (ensures fexp x (prime - 1) == one) =
  prime_lem (); prime_gt_one (); fexp_exp x (prime - 1); F.exp_fermat #prime x

(** {2 Polynomial identities, through the integers}

    A field expression is an integer expression reduced once at the end
    ({!fe_ie}), so two field expressions agree when their integer shadows
    do, and that is a question for [CanonCommSemiring.int_cr].  The ring
    tactic cannot work in the field directly: its coefficient arithmetic
    would have to evaluate [fmul] on constants, which mentions
    [pow2 255]. *)

type ex =
  | V : elem -> ex
  | One : ex
  | Add : ex -> ex -> ex
  | Sub : ex -> ex -> ex
  | Mul : ex -> ex -> ex

#push-options "--ifuel 1"
let rec fe (e: ex) : elem =
  match e with
  | V a -> a
  | One -> one
  | Add a b -> fadd (fe a) (fe b)
  | Sub a b -> fsub (fe a) (fe b)
  | Mul a b -> fmul (fe a) (fe b)

(** Subtraction as [+ (-1) *], so the tactic distributes it. *)
let rec ie (e: ex) : int =
  match e with
  | V a -> a
  | One -> 1
  | Add a b -> ie a + ie b
  | Sub a b -> ie a + (-1) * ie b
  | Mul a b -> ie a * ie b
#pop-options

#push-options "--fuel 1 --ifuel 1"
let rec fe_ie (e: ex) : Lemma (ensures fe e == ie e % prime) (decreases e) =
  match e with
  | V a -> M.small_mod a prime
  | One -> prime_gt_one (); M.small_mod 1 prime
  | Add a b ->
    fe_ie a; fe_ie b;
    M.lemma_mod_plus_distr_l (ie a) (ie b) prime;
    M.lemma_mod_plus_distr_r (ie a % prime) (ie b) prime
  | Sub a b ->
    fe_ie a; fe_ie b;
    let x = ie a % prime in
    let y = ie b % prime in
    M.lemma_mod_plus (x - y) 1 prime;
    M.lemma_mod_plus_distr_l (ie a) (- y) prime;
    M.lemma_mod_sub_distr (ie a) (ie b) prime
  | Mul a b ->
    fe_ie a; fe_ie b;
    M.lemma_mod_mul_distr_l (ie a) (ie b) prime;
    M.lemma_mod_mul_distr_r (ie a % prime) (ie b) prime
#pop-options

let eq_by_int (e1 e2: ex) : Lemma (requires ie e1 == ie e2) (ensures fe e1 == fe e2) =
  fe_ie e1; fe_ie e2

let int_tac (names: list string) : T.Tac unit =
  T.norm [delta_only (`%ie :: names); iota; zeta; primops];
  CS.canon_semiring CS.int_cr

let fe_tac (names: list string) : T.Tac unit =
  T.norm [delta_only (`%fe :: names); iota; zeta];
  T.trefl ()

(** The projective equation at [(xz, yz, z)] is [z^4] times the affine
    one, side by side. *)
let lhs_p (x y z: elem) : ex =
  let vx = V x in let vy = V y in let vz = V z in
  Mul (Sub (Mul (Mul vy vz) (Mul vy vz)) (Mul (Mul vx vz) (Mul vx vz))) (Mul vz vz)

let lhs_a (x y z: elem) : ex =
  let vx = V x in let vy = V y in let vz = V z in
  Mul (Mul (Mul vz vz) (Mul vz vz)) (Sub (Mul vy vy) (Mul vx vx))

let rhs_p (x y z dd: elem) : ex =
  let vx = V x in let vy = V y in let vz = V z in
  Add (Mul (Mul vz vz) (Mul vz vz))
      (Mul (V dd) (Mul (Mul (Mul vx vz) (Mul vx vz)) (Mul (Mul vy vz) (Mul vy vz))))

let rhs_a (x y z dd: elem) : ex =
  let vx = V x in let vy = V y in let vz = V z in
  Mul (Mul (Mul vz vz) (Mul vz vz)) (Add One (Mul (V dd) (Mul (Mul vx vx) (Mul vy vy))))

let lhs_scale (x y z: elem)
  : Lemma (fmul (fsub (fmul (fmul y z) (fmul y z)) (fmul (fmul x z) (fmul x z))) (fmul z z) ==
           fmul (fmul (fmul z z) (fmul z z)) (fsub (fmul y y) (fmul x x)))
  = assert (ie (lhs_p x y z) == ie (lhs_a x y z)) by (int_tac [`%lhs_p; `%lhs_a]);
    eq_by_int (lhs_p x y z) (lhs_a x y z);
    assert (fe (lhs_p x y z) ==
            fmul (fsub (fmul (fmul y z) (fmul y z)) (fmul (fmul x z) (fmul x z))) (fmul z z))
      by (fe_tac [`%lhs_p]);
    assert (fe (lhs_a x y z) == fmul (fmul (fmul z z) (fmul z z)) (fsub (fmul y y) (fmul x x)))
      by (fe_tac [`%lhs_a])

let rhs_scale (x y z dd: elem)
  : Lemma (fadd (fmul (fmul z z) (fmul z z))
                (fmul dd (fmul (fmul (fmul x z) (fmul x z)) (fmul (fmul y z) (fmul y z)))) ==
           fmul (fmul (fmul z z) (fmul z z)) (fadd one (fmul dd (fmul (fmul x x) (fmul y y)))))
  = assert (ie (rhs_p x y z dd) == ie (rhs_a x y z dd)) by (int_tac [`%rhs_p; `%rhs_a]);
    eq_by_int (rhs_p x y z dd) (rhs_a x y z dd);
    assert (fe (rhs_p x y z dd) ==
            fadd (fmul (fmul z z) (fmul z z))
                 (fmul dd (fmul (fmul (fmul x z) (fmul x z)) (fmul (fmul y z) (fmul y z)))))
      by (fe_tac [`%rhs_p]);
    assert (fe (rhs_a x y z dd) ==
            fmul (fmul (fmul z z) (fmul z z)) (fadd one (fmul dd (fmul (fmul x x) (fmul y y)))))
      by (fe_tac [`%rhs_a])

(** [x^2 (d y^2 + 1)] is [y^2 - 1] plus the difference of the two sides of
    the affine equation. *)
let den_l (x y dd: elem) : ex =
  Mul (Mul (V x) (V x)) (Add (Mul (V dd) (Mul (V y) (V y))) One)

let den_r (x y dd: elem) : ex =
  let xx = Mul (V x) (V x) in
  let yy = Mul (V y) (V y) in
  Add (Sub yy One) (Sub (Add One (Mul (V dd) (Mul xx yy))) (Sub yy xx))

let den_eq (x y dd: elem)
  : Lemma (fmul (fmul x x) (fadd (fmul dd (fmul y y)) one) ==
           fadd (fsub (fmul y y) one)
                (fsub (fadd one (fmul dd (fmul (fmul x x) (fmul y y))))
                      (fsub (fmul y y) (fmul x x))))
  = assert (ie (den_l x y dd) == ie (den_r x y dd)) by (int_tac [`%den_l; `%den_r]);
    eq_by_int (den_l x y dd) (den_r x y dd);
    assert (fe (den_l x y dd) == fmul (fmul x x) (fadd (fmul dd (fmul y y)) one))
      by (fe_tac [`%den_l]);
    assert (fe (den_r x y dd) ==
            fadd (fsub (fmul y y) one)
                 (fsub (fadd one (fmul dd (fmul (fmul x x) (fmul y y))))
                       (fsub (fmul y y) (fmul x x))))
      by (fe_tac [`%den_r])

(** {2 The affine equation} *)

let aff (x y: elem) : prop =
  fsub (fmul y y) (fmul x x) == fadd one (fmul d (fmul (fmul x x) (fmul y y)))

#push-options "--ifuel 1"
let affine_eq (p: ext_point)
  : Lemma (requires Spec.Ed25519.Group.on_curve p)
          (ensures (let (xx, yy, zz, _) = p in
                    aff (fmul xx (finv zz)) (fmul yy (finv zz))))
  = let (xx, yy, zz, _) = p in
    let x = fmul xx (finv zz) in
    let y = fmul yy (finv zz) in
    div_mul xx zz; div_mul yy zz;
    lhs_scale x y zz;
    rhs_scale x y zz d;
    let z4 = fmul (fmul zz zz) (fmul zz zz) in
    let l = fsub (fmul y y) (fmul x x) in
    let r = fadd one (fmul d (fmul (fmul x x) (fmul y y))) in
    assert (fmul z4 l == fmul z4 r);
    mul_nz zz zz; mul_nz (fmul zz zz) (fmul zz zz);
    fmul_comm z4 l; fmul_comm z4 r;
    cancel l r z4
#pop-options

(** {2 Square roots}

    Both lemmas are about integers modulo an arbitrary prime: [h^2 = 1]
    forces [h = +-1], and [r^2 = x^2] forces [r = +-x], because the
    difference factors and a prime dividing a product divides a factor. *)

let sq_one_gen (m: pos { E.is_prime m }) (h: nat { h < m })
  : Lemma (requires (h * h) % m == 1) (ensures h == 1 \/ h == m - 1)
  = M.lemma_div_mod (h * h) m;
    let k = h * h / m in
    assert ((h - 1) * (h + 1) == h * h - 1);
    assert ((h - 1) * (h + 1) == k * m);
    M.cancel_mul_mod k m;
    E.euclid_prime m (h - 1) (h + 1);
    if h = 0 then M.small_mod 0 m
    else begin
      if h + 1 < m then M.small_mod (h + 1) m;
      M.small_mod (h - 1) m
    end

let sq_eq_gen (m: pos { E.is_prime m }) (r x: nat)
  : Lemma (requires r < m /\ x < m /\ (r * r) % m == (x * x) % m)
          (ensures r == x \/ r == (m - x) % m)
  = M.lemma_div_mod (r * r) m;
    M.lemma_div_mod (x * x) m;
    let k = r * r / m - x * x / m in
    assert ((r - x) * (r + x) == r * r - x * x);
    assert ((r - x) * (r + x) == k * m);
    M.cancel_mul_mod k m;
    E.euclid_prime m (r - x) (r + x);
    if (r - x) % m = 0 then begin
      if r >= x then M.small_mod (r - x) m
      else begin
        M.lemma_mod_plus (r - x) 1 m;
        M.small_mod (r - x + m) m
      end
    end else begin
      if r + x < m then M.small_mod (r + x) m
      else begin
        M.lemma_mod_plus (r + x - m) 1 m;
        M.small_mod (r + x - m) m;
        M.small_mod (m - x) m
      end
    end

let sq_one (h: elem) : Lemma (requires fmul h h == one) (ensures h == one \/ h == prime - 1) =
  prime_lem (); sq_one_gen prime h

let sq_eq (r x: elem) : Lemma (requires fmul r r == fmul x x) (ensures r == x \/ r == fsub 0 x) =
  prime_lem (); sq_eq_gen prime r x

(** [sqrt_of] succeeds on every square, with a root. *)
let sqrt_of_square (x: elem)
  : Lemma (match sqrt_of (fmul x x) with
           | Some r -> fmul r r == fmul x x
           | None -> False)
  = let a = fmul x x in
    let b = modp_sqrt a in
    assert_norm ((prime + 3) / 8 > 0);
    if x = 0 then fexp_zero_base ((prime + 3) / 8)
    else begin
      let e = (prime + 3) / 8 in
      let k = (prime - 1) / 2 in
      assert_norm (2 * ((prime + 3) / 8) + 2 * ((prime + 3) / 8) == (prime - 1) / 2 + 2);
      assert_norm ((prime - 1) / 2 + (prime - 1) / 2 == prime - 1);
      fexp_two x;
      fexp_mul x 2 e;
      fexp_add x (2 * e) (2 * e);
      fexp_add x k 2;
      fexp_add x k k;
      fermat x;
      let h = fexp x k in
      assert (fmul b b == fmul h a);
      sq_one h;
      if h = one then (fmul_comm one a; fmul_one a)
      else if fmul b b = a then ()
      else begin
        let i = sqrt_m1 in
        assert_norm (fmul sqrt_m1 sqrt_m1 == prime - 1);
        assert_norm (fmul (prime - 1) (prime - 1) == 1);
        mul4 b i b i;
        fmul_comm (prime - 1) a;
        fmul_assoc a (prime - 1) (prime - 1);
        fmul_one a
      end
    end

(** {2 Recovering [x]} *)

let neg_parity (x: elem)
  : Lemma (requires x <> 0)
          (ensures fsub 0 x == prime - x /\ (prime - x) % 2 <> x % 2 /\
                   fsub 0 (prime - x) == x)
  = assert_norm (prime % 2 == 1);
    M.small_mod (prime - x) prime;
    M.small_mod x prime

let fsub_self (a: elem) : Lemma (fsub a a == 0) = M.cancel_mul_mod 1 prime

let fsub_zero (a b: elem) : Lemma (requires fsub a b == 0) (ensures a == b) =
  if a >= b then (M.lemma_mod_plus (a - b) 1 prime; M.small_mod (a - b) prime)
  else M.small_mod (a + prime - b) prime

#push-options "--ifuel 1 --z3rlimit 80"
let recover_x_affine (x y: elem)
  : Lemma (requires aff x y) (ensures recover_x y (x % 2) == Some x)
  = let y2 = fmul y y in
    let u = fsub y2 one in
    let v = fadd (fmul d y2) one in
    den_eq x y d;
    fsub_self (fsub y2 (fmul x x));
    M.small_mod u prime;
    assert (fmul (fmul x x) v == u);
    if v = 0 then begin
      fsub_zero y2 one;
      fmul_one d;
      assert_norm (fadd d one <> 0)
    end;
    mul_finv v;
    fmul_assoc (fmul x x) v (finv v);
    fmul_one (fmul x x);
    assert (fmul u (finv v) == fmul x x);
    sqrt_of_square x;
    let Some r = sqrt_of (fmul x x) in
    sq_eq r x;
    if x <> 0 then neg_parity x
#pop-options

(** {2 The round trip} *)

#push-options "--ifuel 1 --z3rlimit 80"
let decompress_compress (p: ext_point)
  : Lemma (requires Spec.Ed25519.Group.on_curve p)
          (ensures (match point_decompress (point_compress p) with
                    | Some p' -> Spec.Ed25519.Group.on_curve p' /\ point_equal p' p
                    | None -> False))
  = let (xx, yy, zz, _) = p in
    let x = fmul xx (finv zz) in
    let y = fmul yy (finv zz) in
    affine_eq p;
    recover_x_affine x y;
    let n = y + (x % 2) * pow2 255 in
    assert_norm (prime < pow2 255);
    assert_norm (pow2 255 + pow2 255 == pow2 (8 * 32));
    B.le_nat_to_le 32 n;
    M.lemma_div_plus y (x % 2) (pow2 255);
    M.small_div y (pow2 255);
    M.lemma_mod_plus y (x % 2) (pow2 255);
    M.small_mod y (pow2 255);
    assert (point_compress p == B.nat_to_le 32 n);
    div_mul xx zz; div_mul yy zz;
    fmul_one xx; fmul_one yy;
    let p' = (x, y, one, fmul x y) in
    assert (point_decompress (point_compress p) == Some p');
    Spec.Ed25519.Group.decompress_on_curve (point_compress p) p'
#pop-options

#pop-options
