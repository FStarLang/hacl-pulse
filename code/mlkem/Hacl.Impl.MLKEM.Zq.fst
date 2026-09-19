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

(** Arithmetic in [Z_3329] on secret sixteen-bit words.

    A coefficient is a {!Hacl.Secret.UInt16.t} whose value is below [q], and
    every operation here restores that invariant, so no caller ever has to
    reason about a lazily reduced representative.  That is a real cost --
    the reference implementations keep coefficients in a wider range and
    reduce only where they must -- but it is paid once per operation rather
    than once per proof, and the alternative is a range bound threaded
    through every loop invariant in the transform.

    Everything is branch-free.  Addition and subtraction reduce with a
    conditional subtraction driven by {!Hacl.Secret.UInt16.gte_mask};
    multiplication reduces with a Barrett step in sixty-four bits.  The
    obvious optimisation is Montgomery multiplication with the zeta table
    stored pre-scaled, which is what every fast implementation does; it
    changes the representation invariant, so it belongs in a later pass and
    not in the first correct one. *)
module Hacl.Impl.MLKEM.Zq

open Spec.MLKEM.Zq

module U16 = FStar.UInt16
module U64 = FStar.UInt64
module S16 = Hacl.Secret.UInt16
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** A coefficient in canonical form. *)
let zqt = x: S16.t { S16.v x < q }

inline_for_extraction
let qw : w: S16.t { S16.v w == q } = S16.classify 3329us

(** {2 Conditional subtraction}

    The one primitive everything else is built from: [x] is known to be
    below [2q], and exactly one subtraction brings it below [q].  [select]
    rather than [logand] because [select] is specified on the mask's two
    possible values instead of on its bits. *)
inline_for_extraction
let csub (x: S16.t { S16.v x < 2 * q }) : r: zqt { S16.v r == S16.v x % q }
  = let m = S16.gte_mask x qw in
    let r = S16.select m (S16.sub_mod x qw) x in
    if S16.v x >= q then Math.small_mod (S16.v x - q) q else Math.small_mod (S16.v x) q;
    r

(** {2 Addition and subtraction}

    [a + b < 2q] and [a + q - b < 2q], both far below [2^16], so the
    wrapping operations are exact and one conditional subtraction
    suffices.  Subtraction adds [q] first rather than testing a sign,
    which is the same trick and keeps the word unsigned throughout. *)

inline_for_extraction
let zq_add (a b: zqt) : r: zqt { S16.v r == add (S16.v a) (S16.v b) }
  = assert_norm (2 * q < pow2 16);
    Math.small_mod (S16.v a + S16.v b) (pow2 16);
    csub (S16.add_mod a b)

inline_for_extraction
let zq_sub (a b: zqt) : r: zqt { S16.v r == sub (S16.v a) (S16.v b) }
  = assert_norm (2 * q < pow2 16);
    Math.small_mod (S16.v a + q) (pow2 16);
    Math.small_mod (S16.v a + q - S16.v b) (pow2 16);
    csub (S16.sub_mod (S16.add_mod a qw) b)

inline_for_extraction
let zq_neg (a: zqt) : r: zqt { S16.v r == neg (S16.v a) }
  = zq_sub (S16.classify 0us) a

(** {2 Multiplication}

    A product of two canonical coefficients is below [2^24], and
    [5039 = floor(2^24 / q)], so [t = (x * 5039) >> 24] approximates
    [x / q] from below.  The error is small enough that a single
    conditional subtraction finishes the job -- which is what
    {!barrett_bound} says, and it is worth proving rather than asserting
    because the two inequalities pull in opposite directions and the
    margin on the second is under fifteen percent. *)

let barrett_bound (x: nat { x < pow2 24 })
  : Lemma (let t = (x * 5039) / pow2 24 in t * q <= x /\ x - t * q < 2 * q)
  = let p = pow2 24 in
    assert_norm (pow2 24 == 16777216);
    let t = (x * 5039) / p in
    Math.lemma_div_mod (x * 5039) p;
    Math.lemma_mult_le_right q (t * p) (x * 5039);
    Math.lemma_mult_le_right p t x;
    assert (t * p * q <= x * 5039 * q);
    assert (x * 5039 * q == x * 16774831);
    Math.lemma_mult_le_right x 16774831 16777216;
    assert (t * q * p <= x * p);
    assert (t * p > x * 5039 - p);
    assert (t * q * p > x * 16774831 - q * p);
    Math.lemma_mult_le_right 2385 x p;
    assert ((x - t * q) * p < 2385 * x + q * p);
    assert (2385 * x + q * p <= 2385 * p + q * p)

inline_for_extraction
let zq_mul (a b: zqt) : r: zqt { S16.v r == mul (S16.v a) (S16.v b) }
  = assert_norm ((q - 1) * (q - 1) < pow2 24);
    assert_norm (pow2 24 * 5039 < pow2 64);
    assert_norm (2 * q < pow2 16);
    Math.lemma_mult_le_right (S16.v b) (S16.v a) (q - 1);
    Math.lemma_mult_le_right (q - 1) (S16.v b) (q - 1);
    barrett_bound (S16.v a * S16.v b);
    Math.small_mod (S16.v a * S16.v b) (pow2 64);
    Math.small_mod (S16.v a * S16.v b * 5039) (pow2 64);
    Math.small_mod (S16.v a * S16.v b * 5039 / pow2 24 * q) (pow2 64);
    Math.small_mod (S16.v a * S16.v b - S16.v a * S16.v b * 5039 / pow2 24 * q) (pow2 64);
    Math.small_mod (S16.v a * S16.v b - S16.v a * S16.v b * 5039 / pow2 24 * q) (pow2 16);
    Math.lemma_mod_plus (S16.v a * S16.v b - S16.v a * S16.v b * 5039 / pow2 24 * q)
                        (S16.v a * S16.v b * 5039 / pow2 24) q;
    let x = S64.mul_mod (Cast.u16_to_u64 a) (Cast.u16_to_u64 b) in
    let t = S64.shift_right (S64.mul_mod x (S64.classify 5039uL)) 24ul in
    csub (Cast.u64_to_u16 (S64.sub_mod x (S64.mul_mod t (S64.classify 3329uL))))

#pop-options

(** {2 Division by q}

    Compression divides by [q], and a division instruction on a secret is
    not something to emit: on several of the targets here its latency
    depends on its operands.  The usual replacement is a multiply and a
    shift, and the constant is chosen so that the identity holds over the
    whole range compression uses.

    [2580335 * q = 2^33 + 623], so writing [x = a q + b],
    [x * 2580335 = a 2^33 + (623 a + 2580335 b)], and the remainder term
    stays below [2^33] because [a < 2520] and [b < q]. *)
let div_q (x: nat { x < pow2 23 })
  : Lemma (x * 2580335 / pow2 33 == x / q)
  = let a = x / q in
    let b = x % q in
    assert_norm (2580335 * q == pow2 33 + 623);
    assert_norm (pow2 23 < 2520 * q);
    div_lt x 2520 q;
    Math.lemma_div_mod x q;
    Math.lemma_mult_le_right 623 a 2519;
    Math.lemma_mult_le_right 2580335 b (q - 1);
    assert_norm (2519 * 623 + (q - 1) * 2580335 < pow2 33);
    Math.distributivity_add_left (a * q) b 2580335;
    Math.paren_mul_right a q 2580335;
    Math.distributivity_add_right a (pow2 33) 623;
    assert (x * 2580335 == a * pow2 33 + (a * 623 + b * 2580335));
    Math.lemma_div_plus (a * 623 + b * 2580335) a (pow2 33);
    Math.small_div (a * 623 + b * 2580335) (pow2 33)

(** {2 The view of an array as a polynomial}

    Coefficients live in memory as secret words and in the specification as
    naturals below [q], so the two are related by mapping [S16.v] over a
    sequence.  [S16.v] is ghost, hence [init_ghost] and [GTot]. *)

let as_poly (s: Seq.seq zqt { Seq.length s == n }) : GTot poly
  = Seq.init_ghost n (fun i -> (S16.v (Seq.index s i) <: zq))

let as_poly_index (s: Seq.seq zqt { Seq.length s == n }) (i: nat { i < n })
  : Lemma (Seq.index (as_poly s) i == S16.v (Seq.index s i))
          [SMTPat (Seq.index (as_poly s) i)]
  = Seq.init_ghost_index_ n (fun j -> (S16.v (Seq.index s j) <: zq)) i

(** What lets an implementation conclude from a pointwise loop invariant:
    an array whose words agree with a polynomial coefficient by coefficient
    {i is} that polynomial. *)
let as_poly_intro (s: Seq.seq zqt { Seq.length s == n }) (f: poly)
  : Lemma (requires forall (i: nat). i < n ==> S16.v (Seq.index s i) == Seq.index f i)
          (ensures as_poly s == f)
  = Seq.lemma_eq_intro (as_poly s) f

(** The same view without the [q] bound, for the [d]-bit values that
    compression produces and encoding consumes. *)

let as_nats (s: Seq.seq zqt { Seq.length s == n }) : GTot (Seq.lseq nat n)
  = Seq.init_ghost n (fun i -> (S16.v (Seq.index s i) <: nat))

let as_nats_index (s: Seq.seq zqt { Seq.length s == n }) (i: nat { i < n })
  : Lemma (Seq.index (as_nats s) i == S16.v (Seq.index s i))
          [SMTPat (Seq.index (as_nats s) i)]
  = Seq.init_ghost_index_ n (fun j -> (S16.v (Seq.index s j) <: nat)) i

let as_nats_intro (s: Seq.seq zqt { Seq.length s == n }) (f: Seq.lseq nat n)
  : Lemma (requires forall (i: nat). i < n ==> S16.v (Seq.index s i) == Seq.index f i)
          (ensures as_nats s == f)
  = Seq.lemma_eq_intro (as_nats s) f

(** An uncompressed polynomial read as plain naturals, which is what the
    twelve-bit encoding of a key wants. *)
let as_nats_poly (s: Seq.seq zqt { Seq.length s == n })
  : Lemma (as_nats s == widen (as_poly s))
  = Seq.lemma_eq_intro (as_nats s) (widen (as_poly s))

(** {2 Vectors}

    A [k]-vector is one array of [k * 256] coefficients, laid out exactly
    the way {!Spec.MLKEM.Zq.pvec} is, so that entry [i] is a sub-array and
    needs no copy.  The view is stated for an arbitrary length so that the
    same lemmas serve a polynomial, a vector and a matrix row. *)

let as_zqs (s: Seq.seq zqt) : GTot (Seq.lseq zq (Seq.length s))
  = Seq.init_ghost (Seq.length s) (fun i -> (S16.v (Seq.index s i) <: zq))

let as_zqs_index (s: Seq.seq zqt) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (as_zqs s) i == S16.v (Seq.index s i))
          [SMTPat (Seq.index (as_zqs s) i)]
  = Seq.init_ghost_index_ (Seq.length s) (fun j -> (S16.v (Seq.index s j) <: zq)) i

let as_zqs_intro (s: Seq.seq zqt) (f: Seq.lseq zq (Seq.length s))
  : Lemma (requires forall (i: nat). i < Seq.length s ==> S16.v (Seq.index s i) == Seq.index f i)
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

(** The same for a flat sequence of [k] blocks of any size, which is what
    a serialised vector and a matrix are. *)
let as_zqs_flat_at (k: pos) (m: pos) (s: Seq.seq zqt { Seq.length s == k * m })
                   (i: nat { i < k })
  : Lemma (flat_at k m (as_zqs s) i == as_zqs (Seq.slice s (i * m) (i * m + m)))
  = Math.lemma_mult_le_right m (i + 1) k;
    as_zqs_slice s (i * m) (i * m + m)


(** The unbounded view, for a flat sequence of any length: what a vector of
    compressed coefficients is, and what encoding consumes. *)

let as_ints (s: Seq.seq zqt) : GTot (Seq.lseq nat (Seq.length s))
  = Seq.init_ghost (Seq.length s) (fun i -> (S16.v (Seq.index s i) <: nat))

let as_ints_index (s: Seq.seq zqt) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (as_ints s) i == S16.v (Seq.index s i))
          [SMTPat (Seq.index (as_ints s) i)]
  = Seq.init_ghost_index_ (Seq.length s) (fun j -> (S16.v (Seq.index s j) <: nat)) i

let as_ints_intro (s: Seq.seq zqt) (f: Seq.lseq nat (Seq.length s))
  : Lemma (requires forall (i: nat). i < Seq.length s ==> S16.v (Seq.index s i) == Seq.index f i)
          (ensures as_ints s == f)
  = Seq.lemma_eq_intro (as_ints s) f

let as_ints_nats (s: Seq.seq zqt { Seq.length s == n })
  : Lemma (as_ints s == as_nats s)
  = Seq.lemma_eq_intro (as_ints s) (as_nats s)

let as_ints_slice (s: Seq.seq zqt) (a: nat) (b: nat { a <= b /\ b <= Seq.length s })
  : Lemma (as_ints (Seq.slice s a b) == Seq.slice (as_ints s) a b)
  = Seq.lemma_eq_intro (as_ints (Seq.slice s a b)) (Seq.slice (as_ints s) a b)

let as_ints_flat_at (k: pos) (m: pos) (s: Seq.seq zqt { Seq.length s == k * m })
                    (i: nat { i < k })
  : Lemma (flat_at k m (as_ints s) i == as_ints (Seq.slice s (i * m) (i * m + m)))
  = Math.lemma_mult_le_right m (i + 1) k;
    as_ints_slice s (i * m) (i * m + m)

let as_nats_widen (s: Seq.seq zqt { Seq.length s == n })
  : Lemma (as_nats s == widen (as_poly s))
  = Seq.lemma_eq_intro (as_nats s) (widen (as_poly s))

(** The [nat] view is the [zq] view widened; the coders take the first and
    the specifications of the keys take the second. *)
let as_ints_widen (s: Seq.seq zqt)
  : Lemma (as_ints s == widen (as_zqs s))
  = Seq.lemma_eq_intro (as_ints s) (widen (as_zqs s))

(** The same for a polynomial-sized block, which is the shape every vector
    coder works on. *)
let as_nats_at (k: pos) (s: Seq.seq zqt { Seq.length s == k * n }) (i: nat { i < k })
  : Lemma (flat_at k n (as_ints s) i == as_nats (Seq.slice s (i * n) (i * n + n)))
  = Math.lemma_mult_le_right n (i + 1) k;
    as_ints_flat_at k n s i;
    as_ints_nats (Seq.slice s (i * n) (i * n + n))
