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

(** Arithmetic in [Z_8380417] on secret thirty-two-bit words.

    The same discipline as {!Hacl.Impl.MLKEM.Zq}: a coefficient is a
    {!Hacl.Secret.UInt32.t} below [q], every operation returns one, and
    everything is branch-free.  The differences are all consequences of
    [q] being 23 bits wide instead of 12:

    - a product of two coefficients is 46 bits, so it is formed in
      sixty-four bits;
    - multiplication by a tabulated constant is Shoup's trick with a
      thirty-two-bit companion [floor(z 2^32 / q)] ({!zq_mul_shoup});
    - a general product is reduced with Montgomery's method
      ({!mont_reduce}) and then multiplied back by [2^32 mod q] with a
      Shoup step, which keeps the result canonical and the interface
      free of Montgomery form. *)
module Hacl.Impl.MLDSA.Zq

open Spec.MLDSA.Zq

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module Math = FStar.Math.Lemmas
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** A coefficient in canonical form. *)
let zqt = x: S32.t { S32.v x < q }

inline_for_extraction
let qw : w: S32.t { S32.v w == q } = S32.classify 8380417ul

(** {2 Conditional subtraction} *)
inline_for_extraction
let csub (x: S32.t { S32.v x < 2 * q }) : r: zqt { S32.v r == S32.v x % q }
  = let m = S32.gte_mask x qw in
    let r = S32.select m (S32.sub_mod x qw) x in
    if S32.v x >= q then Math.small_mod (S32.v x - q) q else Math.small_mod (S32.v x) q;
    r

(** {2 Addition and subtraction} *)

inline_for_extraction
let zq_add (a b: zqt) : r: zqt { S32.v r == add (S32.v a) (S32.v b) }
  = assert_norm (2 * q < pow2 32);
    Math.small_mod (S32.v a + S32.v b) (pow2 32);
    csub (S32.add_mod a b)

inline_for_extraction
let zq_sub (a b: zqt) : r: zqt { S32.v r == sub (S32.v a) (S32.v b) }
  = assert_norm (2 * q < pow2 32);
    Math.small_mod (S32.v a + q) (pow2 32);
    Math.small_mod (S32.v a + q - S32.v b) (pow2 32);
    csub (S32.sub_mod (S32.add_mod a qw) b)

inline_for_extraction
let zq_neg (a: zqt) : r: zqt { S32.v r == neg (S32.v a) }
  = zq_sub (S32.classify 0ul) a

(** {2 Multiplication by a known constant}

    Shoup's trick, as in ML-KEM, with [p = 2^32]: for a constant [z] and
    its companion [zs = floor(z 2^32 / q)], [t = (y zs) >> 32]
    approximates [y z / q] from below by less than two, so
    [y z - t q < 2 q].  All of it is exact in sixty-four bits. *)

let lt_cancel (a b: int) (p: pos)
  : Lemma (requires a * p < b * p) (ensures a < b)
  = if a >= b then Math.lemma_mult_le_right p b a

let shoup_bound (y z zs: nat)
  : Lemma (requires y < pow2 32 /\ z < q /\ zs == (z * pow2 32) / q)
          (ensures (let t = (y * zs) / pow2 32 in
                    t * q <= y * z /\ y * z - t * q < 2 * q))
  = let p = pow2 32 in
    let t = (y * zs) / p in
    let r1 = (y * zs) % p in
    Math.lemma_div_mod (z * p) q;
    Math.lemma_div_mod (y * zs) p;
    let d = (z * p) % q in
    assert (z * p == zs * q + d /\ d < q);
    assert (y * zs == t * p + r1 /\ r1 < p);
    Math.paren_mul_right y z p;
    Math.distributivity_add_right y (zs * q) d;
    Math.paren_mul_right y zs q;
    Math.paren_mul_right t p q;
    Math.swap_mul p q;
    Math.paren_mul_right t q p;
    Math.distributivity_sub_left (y * z) (t * q) p;
    assert ((y * z - t * q) * p == y * d + q * r1);
    Math.lemma_mult_le_right d y p;
    Math.lemma_mult_lt_left q r1 p;
    Math.lemma_mult_le_left y d q;
    Math.lemma_mult_lt_right q y p;
    assert ((y * z - t * q) * p >= 0);
    assert ((y * z - t * q) * p < (2 * q) * p);
    if y * z - t * q < 0 then Math.lemma_mult_lt_right p (y * z - t * q) 0;
    lt_cancel (y * z - t * q) (2 * q) p

(** The companion of a constant. *)
let shoup_of (z: zq) : nat = (z * pow2 32) / q

inline_for_extraction
let zq_mul_shoup (z: zqt) (zs: S32.t { S32.v zs == shoup_of (S32.v z) }) (y: zqt)
  : r: zqt { S32.v r == mul (S32.v z) (S32.v y) }
  = let p = pow2 32 in
    q_bound ();
    assert_norm (pow2 23 * pow2 32 == pow2 55);
    assert_norm (pow2 23 * pow2 23 < pow2 64);
    assert_norm (pow2 55 < pow2 64);
    assert_norm (2 * q < pow2 32);
    Math.lemma_mult_le_right (S32.v zs) (S32.v y) (pow2 23);
    Math.lemma_mult_lt_left (pow2 23) (S32.v zs) p;
    Math.small_mod (S32.v y * S32.v zs) (pow2 64);
    Math.lemma_mult_le_right (S32.v z) (S32.v y) (pow2 23);
    Math.lemma_mult_lt_left (pow2 23) (S32.v z) (pow2 23);
    Math.small_mod (S32.v y * S32.v z) (pow2 64);
    shoup_bound (S32.v y) (S32.v z) (S32.v zs);
    let y64 = Cast.u32_to_u64 y in
    let t = S64.shift_right (S64.mul_mod y64 (Cast.u32_to_u64 zs)) 32ul in
    assert (S64.v t == (S32.v y * S32.v zs) / p);
    Math.small_mod (S64.v t * q) (pow2 64);
    let r64 = S64.sub_mod (S64.mul_mod y64 (Cast.u32_to_u64 z))
                          (S64.mul_mod t (Cast.u32_to_u64 qw)) in
    Math.small_mod (S32.v y * S32.v z - S64.v t * q) (pow2 64);
    assert (S64.v r64 == S32.v y * S32.v z - S64.v t * q);
    let r = Cast.u64_to_u32 r64 in
    Math.small_mod (S64.v r64) (pow2 32);
    Math.lemma_mod_sub (S32.v y * S32.v z) q (S64.v t);
    Math.swap_mul (S32.v y) (S32.v z);
    csub r

(** {2 Montgomery reduction}

    [R = 2^32].  For [x < q R], with [qneg = -q^-1 mod R],
    [t = (x mod R) qneg mod R] makes [x + t q] a multiple of [R], and the
    quotient is below [2 q] and congruent to [x R^-1].  Both facts come
    from the identity [qneg q + 1 = rinv R], where [rinv] happens to be
    [R^-1 mod q] itself. *)

let qneg : nat = 4236238847
let rinv : zq = 8265825

let mont_consts () : Lemma (qneg * q + 1 == rinv * pow2 32 /\ qneg < pow2 32)
  = assert_norm (qneg * q + 1 == rinv * pow2 32 /\ qneg < pow2 32)

let mont_divides (x: nat)
  : Lemma (let t = ((x % pow2 32) * qneg) % pow2 32 in
           (x + t * q) % pow2 32 == 0)
  = let r = pow2 32 in
    let lo = x % r in
    let t = (lo * qneg) % r in
    mont_consts ();
    (* t q = lo qneg q = lo (rinv r - 1) = - lo  (mod r) *)
    Math.lemma_mod_mul_distr_l (lo * qneg) q r;
    Math.paren_mul_right lo qneg q;
    Math.distributivity_sub_right lo (rinv * r) 1;
    Math.paren_mul_right lo rinv r;
    Math.lemma_mod_plus (- lo) (lo * rinv) r;
    assert ((t * q) % r == (- lo) % r);
    (* x + t q = x - lo = (x / r) r  (mod r) *)
    Math.lemma_mod_add_distr x (t * q) r;
    Math.lemma_mod_add_distr x (- lo) r;
    Math.lemma_div_mod x r;
    Math.cancel_mul_mod (x / r) r

let mont_congr (x: nat) (u r: nat)
  : Lemma (requires u == r * pow2 32 /\ u % q == x % q)
          (ensures r % q == (x * rinv) % q)
  = mont_consts ();
    Math.paren_mul_right r rinv (pow2 32);
    Math.swap_mul rinv (pow2 32);
    Math.paren_mul_right r (pow2 32) rinv;
    Math.paren_mul_right r qneg q;
    Math.distributivity_add_right r (qneg * q) 1;
    assert (r * (qneg * q) + r == u * rinv);
    Math.lemma_mod_plus r (r * qneg) q;
    assert (r % q == (u * rinv) % q);
    Math.lemma_mod_mul_distr_l u rinv q;
    Math.lemma_mod_mul_distr_l x rinv q

let mont_bound (x: nat)
  : Lemma (requires x < q * pow2 32)
          (ensures (let t = ((x % pow2 32) * qneg) % pow2 32 in
                    let u = x + t * q in
                    u < pow2 64 /\ u % pow2 32 == 0 /\
                    u / pow2 32 < 2 * q /\
                    (u / pow2 32) % q == (x * rinv) % q))
  = let r = pow2 32 in
    let t = ((x % r) * qneg) % r in
    let u = x + t * q in
    mont_divides x;
    Math.lemma_mult_lt_right q t r;
    Math.swap_mul t q;
    assert (u < 2 * q * r);
    assert_norm (2 * q * pow2 32 < pow2 64);
    Math.lemma_div_exact u r;
    Math.swap_mul (u / r) r;
    Math.lemma_mod_plus x t q;
    mont_congr x u (u / r);
    if u / r >= 2 * q then Math.lemma_mult_le_right r (2 * q) (u / r)

(** [x R^-1 mod q], for a sixty-four-bit [x < q R]. *)
inline_for_extraction
let mont_reduce (x: S64.t { S64.v x < q * pow2 32 })
  : r: zqt { S32.v r == (S64.v x * rinv) % q }
  = mont_bound (S64.v x);
    mont_consts ();
    let lo = Cast.u64_to_u32 x in
    let t = S32.mul_mod lo (S32.classify 4236238847ul) in
    assert (S32.v t == ((S64.v x % pow2 32) * qneg) % pow2 32);
    Math.lemma_mult_lt_right q (S32.v t) (pow2 32);
    assert_norm (q * pow2 32 < pow2 64);
    Math.small_mod (S32.v t * q) (pow2 64);
    let tq = S64.mul_mod (Cast.u32_to_u64 t) (Cast.u32_to_u64 qw) in
    Math.small_mod (S64.v x + S64.v tq) (pow2 64);
    let u = S64.add_mod x tq in
    let r = S64.shift_right u 32ul in
    assert_norm (2 * q < pow2 32);
    Math.small_mod (S64.v r) (pow2 32);
    let r32 = Cast.u64_to_u32 r in
    csub r32

(** {2 General multiplication}

    [mont_reduce (a b)] is [a b R^-1]; one Shoup multiplication by
    [R mod q] undoes the [R^-1]. *)

inline_for_extraction
let rmod : zqt = S32.classify 4193792ul

inline_for_extraction
let rmod_shoup : s: S32.t { S32.v s == shoup_of (S32.v rmod) }
  = assert_norm (shoup_of 4193792 == 2149320193);
    S32.classify 2149320193ul

let mul_undo (x: nat)
  : Lemma (mul 4193792 ((x * rinv) % q) == x % q)
  = assert_norm ((4193792 * rinv) % q == 1);
    Math.lemma_mod_mul_distr_r 4193792 (x * rinv) q;
    Math.paren_mul_right 4193792 x rinv;
    Math.swap_mul 4193792 x;
    Math.paren_mul_right x 4193792 rinv;
    Math.lemma_mod_mul_distr_r x (4193792 * rinv) q

let prod_lt (a b: zq) : Lemma (a * b < q * pow2 32)
  = Math.lemma_mult_le_right b a (q - 1);
    Math.lemma_mult_le_left (q - 1) b (q - 1);
    assert_norm ((q - 1) * (q - 1) < q * pow2 32)

inline_for_extraction
let zq_mul (a b: zqt) : r: zqt { S32.v r == mul (S32.v a) (S32.v b) }
  = prod_lt (S32.v a) (S32.v b);
    assert_norm (q * pow2 32 < pow2 64);
    Math.small_mod (S32.v a * S32.v b) (pow2 64);
    let x = S64.mul_mod (Cast.u32_to_u64 a) (Cast.u32_to_u64 b) in
    let m = mont_reduce x in
    mul_undo (S32.v a * S32.v b);
    zq_mul_shoup rmod rmod_shoup m

#pop-options

(** {2 Views}

    The same views as ML-KEM: [as_poly] for one polynomial, [as_zqs] for a
    flat sequence of any length (a vector, a matrix), and [as_ints] for
    the same thing as naturals, which is what the coders consume. *)

let as_poly (s: Seq.seq zqt { Seq.length s == n }) : GTot poly
  = Seq.init_ghost n (fun i -> (S32.v (Seq.index s i) <: zq))

let as_poly_index (s: Seq.seq zqt { Seq.length s == n }) (i: nat { i < n })
  : Lemma (Seq.index (as_poly s) i == S32.v (Seq.index s i))
          [SMTPat (Seq.index (as_poly s) i)]
  = Seq.init_ghost_index_ n (fun j -> (S32.v (Seq.index s j) <: zq)) i

let as_poly_intro (s: Seq.seq zqt { Seq.length s == n }) (f: poly)
  : Lemma (requires forall (i: nat). i < n ==> S32.v (Seq.index s i) == Seq.index f i)
          (ensures as_poly s == f)
  = Seq.lemma_eq_intro (as_poly s) f

let as_zqs (s: Seq.seq zqt) : GTot (Seq.lseq zq (Seq.length s))
  = Seq.init_ghost (Seq.length s) (fun i -> (S32.v (Seq.index s i) <: zq))

let as_zqs_index (s: Seq.seq zqt) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (as_zqs s) i == S32.v (Seq.index s i))
          [SMTPat (Seq.index (as_zqs s) i)]
  = Seq.init_ghost_index_ (Seq.length s) (fun j -> (S32.v (Seq.index s j) <: zq)) i

let as_zqs_intro (s: Seq.seq zqt) (f: Seq.lseq zq (Seq.length s))
  : Lemma (requires forall (i: nat). i < Seq.length s ==> S32.v (Seq.index s i) == Seq.index f i)
          (ensures as_zqs s == f)
  = Seq.lemma_eq_intro (as_zqs s) f

let as_zqs_poly (s: Seq.seq zqt { Seq.length s == n })
  : Lemma (as_zqs s == as_poly s)
  = Seq.lemma_eq_intro (as_zqs s) (as_poly s)

let as_zqs_slice (s: Seq.seq zqt) (a: nat) (b: nat { a <= b /\ b <= Seq.length s })
  : Lemma (as_zqs (Seq.slice s a b) == Seq.slice (as_zqs s) a b)
  = Seq.lemma_eq_intro (as_zqs (Seq.slice s a b)) (Seq.slice (as_zqs s) a b)

(** Entry [i] of a vector is the view of the sub-array holding it. *)
let as_zqs_at (k: pos) (s: Seq.seq zqt { Seq.length s == k * n }) (i: nat { i < k })
  : Lemma (vec_at #k (as_zqs s) i == as_poly (Seq.slice s (i * n) (i * n + n)))
  = Math.lemma_mult_le_right n (i + 1) k;
    as_zqs_slice s (i * n) (i * n + n);
    as_zqs_poly (Seq.slice s (i * n) (i * n + n))

let as_zqs_flat_at (k: pos) (m: pos) (s: Seq.seq zqt { Seq.length s == k * m })
                   (i: nat { i < k })
  : Lemma (KZ.flat_at k m (as_zqs s) i == as_zqs (Seq.slice s (i * m) (i * m + m)))
  = Math.lemma_mult_le_right m (i + 1) k;
    as_zqs_slice s (i * m) (i * m + m)

let as_ints (s: Seq.seq zqt) : GTot (Seq.lseq nat (Seq.length s))
  = Seq.init_ghost (Seq.length s) (fun i -> (S32.v (Seq.index s i) <: nat))

let as_ints_index (s: Seq.seq zqt) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (as_ints s) i == S32.v (Seq.index s i))
          [SMTPat (Seq.index (as_ints s) i)]
  = Seq.init_ghost_index_ (Seq.length s) (fun j -> (S32.v (Seq.index s j) <: nat)) i

let as_ints_intro (s: Seq.seq zqt) (f: Seq.lseq nat (Seq.length s))
  : Lemma (requires forall (i: nat). i < Seq.length s ==> S32.v (Seq.index s i) == Seq.index f i)
          (ensures as_ints s == f)
  = Seq.lemma_eq_intro (as_ints s) f

let as_ints_slice (s: Seq.seq zqt) (a: nat) (b: nat { a <= b /\ b <= Seq.length s })
  : Lemma (as_ints (Seq.slice s a b) == Seq.slice (as_ints s) a b)
  = Seq.lemma_eq_intro (as_ints (Seq.slice s a b)) (Seq.slice (as_ints s) a b)

let as_ints_flat_at (k: pos) (m: pos) (s: Seq.seq zqt { Seq.length s == k * m })
                    (i: nat { i < k })
  : Lemma (KZ.flat_at k m (as_ints s) i == as_ints (Seq.slice s (i * m) (i * m + m)))
  = Math.lemma_mult_le_right m (i + 1) k;
    as_ints_slice s (i * m) (i * m + m)
