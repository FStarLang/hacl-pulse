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

(** The ring ML-KEM works in: [Z_3329] and degree-256 polynomials over it.

    FIPS 203 fixes [q = 3329] and [n = 256] for every parameter set, so
    neither is a field of the parameter record; they are constants here.
    Both are small, which is the whole reason ML-KEM is fast: a coefficient
    fits in sixteen bits with room to spare, and a product of two
    coefficients fits in thirty-two.

    Coefficients are plain naturals below [q], not secret integers.  That is
    a departure from {!Spec.Frodo.Matrix}, where the specification carries
    [Hacl.Secret.UInt16.t] because Frodo's arithmetic {i is} machine
    arithmetic modulo [2^16] and the specification would have to describe the
    wrapping anyway.  Here the arithmetic is modular arithmetic in a ring
    that is not a power of two, the implementation has to reduce explicitly,
    and stating the specification in the mathematics rather than in the
    machine words is both shorter and what the standard says.  The
    implementation relates the two with [S16.v].

    Polynomials are coefficient sequences of length 256 with no distinction
    between the normal and the NTT domain: FIPS 203 writes both as elements
    of [R_q] and relies on the naming ([f] against [f-hat]) to tell them
    apart.  A separate type for each would be nicer, but the standard's own
    algorithms move between them freely -- [MultiplyNTTs] consumes two hats
    and produces a hat, [NTT] consumes one and produces the other -- so the
    distinction would be paid for at every call and bought nothing. *)
module Spec.MLKEM.Zq

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

(** {2 The modulus} *)

(** [q], the prime ML-KEM reduces modulo.  [3329 = 13 * 256 + 1], which is
    what makes a 256-point number-theoretic transform possible: the
    multiplicative group has order [q - 1 = 2^8 * 13], so it contains an
    element of order 256. *)
let q : pos = 3329

(** [n], the degree.  The ring is [Z_q[X] / (X^256 + 1)]. *)
let n : pos = 256

let q_bound () : Lemma (q < pow2 12) = assert_norm (3329 < pow2 12)

(** [t < r * c ==> t / c < r].  Nonlinear, so not automatic.  The same four
    lines appear in {!Spec.Frodo.Matrix}; a flat sequence with a
    run-time-valued stride needs this at every index. *)
let div_lt (t: nat) (r: nat) (c: pos) : Lemma (requires t < r * c) (ensures t / c < r)
  = Math.distributivity_sub_left r 1 c;
    Math.lemma_div_le t (r * c - 1) c;
    Math.lemma_div_plus (c - 1) (r - 1) c;
    Math.small_div (c - 1) c

(** A coefficient.  Everything in this module and its callers keeps
    coefficients canonical -- in [0, q) rather than in some wider range a
    lazy reduction would allow -- because the encoding functions depend on
    it and because it is one less invariant to carry. *)
let zq = x: nat { x < q }

(** {2 Arithmetic}

    The three operations, each written so that its result is canonical by
    construction.  [%] on naturals in F\* is Euclidean, so [(a + b) % q] is
    already in range and the refinement needs no help; subtraction would go
    negative, so it is done by adding [q] first, which is exactly what the
    implementation does with a mask. *)

let add (a b: zq) : zq = (a + b) % q

let sub (a b: zq) : zq = (a + q - b) % q

let mul (a b: zq) : zq = (a * b) % q

let neg (a: zq) : zq = (q - a) % q

(** {2 The ring laws}

    Stated and proved here rather than left to the solver.  Each one is an
    instance of a lemma in {!FStar.Math.Lemmas} about [%] distributing over
    the operation, and each is cheap; what is not cheap is rediscovering
    them inside a query that also has a hundred sequence facts in it. *)

let add_comm (a b: zq) : Lemma (add a b == add b a) = ()

let add_assoc (a b c: zq) : Lemma (add (add a b) c == add a (add b c))
  = Math.lemma_mod_add_distr c (a + b) q;
    Math.lemma_mod_add_distr a (b + c) q

let add_zero (a: zq) : Lemma (add a 0 == a) = Math.small_mod a q

let add_neg (a: zq) : Lemma (add a (neg a) == 0)
  = if a = 0 then assert_norm ((0 + (q - 0) % q) % q == 0)
    else begin
      Math.small_mod (q - a) q;
      assert (a + (q - a) == q)
    end

let mul_comm (a b: zq) : Lemma (mul a b == mul b a)
  = Math.swap_mul a b

let mul_assoc (a b c: zq) : Lemma (mul (mul a b) c == mul a (mul b c))
  = Math.lemma_mod_mul_distr_l (a * b) c q;
    Math.paren_mul_right a b c;
    Math.lemma_mod_mul_distr_r a (b * c) q

let mul_one (a: zq) : Lemma (mul a 1 == a) = Math.small_mod a q

let mul_zero (a: zq) : Lemma (mul a 0 == 0) = ()

let mul_add_distr (a b c: zq) : Lemma (mul a (add b c) == add (mul a b) (mul a c))
  = Math.lemma_mod_mul_distr_r a (b + c) q;
    Math.distributivity_add_right a b c;
    Math.modulo_distributivity (a * b) (a * c) q

(** [sub] is [add] of the negation, which is how the implementation does it
    and how the proofs above become reusable. *)
let sub_is_add_neg (a b: zq) : Lemma (sub a b == add a (neg b))
  = if b = 0 then Math.small_mod a q
    else Math.small_mod (q - b) q

(** {2 Exponentiation}

    Used only for the roots of unity: [zeta_pow k] is [17^k].  Defined by
    recursion rather than by square-and-multiply because nothing evaluates
    it at run time -- the implementation reads a table -- and because the
    recursive definition is the one the exponent laws are easy against. *)

let rec pow (a: zq) (k: nat) : Tot zq (decreases k)
  = if k = 0 then 1 else mul a (pow a (k - 1))

let pow_zero (a: zq) : Lemma (pow a 0 == 1) = ()

let pow_one (a: zq) : Lemma (pow a 1 == a) = mul_one a; mul_comm a 1

let rec pow_add (a: zq) (j k: nat)
  : Lemma (ensures pow a (j + k) == mul (pow a j) (pow a k)) (decreases j)
  = if j = 0 then (mul_comm (pow a 0) (pow a k); mul_one (pow a k))
    else begin
      pow_add a (j - 1) k;
      mul_assoc a (pow a (j - 1)) (pow a k)
    end

(** {2 The 256th root of unity}

    [zeta = 17] is the element FIPS 203 names.  Its order is 256: the two
    facts below are what every NTT identity rests on, and both are decided
    by normalization rather than by the solver, because [17^128 mod 3329] is
    a computation and not a fact about arithmetic. *)

let zeta : zq = 17

let zeta_128 () : Lemma (pow zeta 128 == q - 1)
  = assert_norm (pow zeta 128 == q - 1)

let zeta_256 () : Lemma (pow zeta 256 == 1)
  = assert_norm (pow zeta 256 == 1)

(** {2 Bit reversal}

    The NTT visits the roots in bit-reversed order, so the zeta tables are
    indexed by [bitrev7].  Written as an explicit seven-term sum rather than
    as a loop: seven is small, and the closed form is a value the solver can
    evaluate at a literal index without unrolling anything. *)

let bit (i: nat) (k: nat) : n: nat { n < 2 } = (i / pow2 k) % 2

let bitrev7 (i: nat { i < 128 }) : r: nat { r < 128 }
  = let r =   bit i 0 * 64 + bit i 1 * 32 + bit i 2 * 16 + bit i 3 * 8
            + bit i 4 * 4  + bit i 5 * 2  + bit i 6 in
    assert (r <= 127);
    r

(** {2 Polynomials and vectors}

    A polynomial is its 256 coefficients, low degree first.  A vector is [k]
    of them, and a matrix [k] vectors, both flat, in the same style as
    {!Spec.Frodo.Matrix}: the dimension is an argument rather than an index,
    because it reaches the implementation as a run-time [size_t]. *)

let poly = Seq.lseq zq n

let poly_zero : poly = Seq.create n 0

let poly_add (f g: poly) : poly
  = Seq.init n (fun i -> add (Seq.index f i) (Seq.index g i))

let poly_sub (f g: poly) : poly
  = Seq.init n (fun i -> sub (Seq.index f i) (Seq.index g i))

let poly_add_index (f g: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_add f g) i == add (Seq.index f i) (Seq.index g i))
          [SMTPat (Seq.index (poly_add f g) i)]
  = ()

let poly_sub_index (f g: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_sub f g) i == sub (Seq.index f i) (Seq.index g i))
          [SMTPat (Seq.index (poly_sub f g) i)]
  = ()

(** A flat concatenation of [k] blocks of [m] elements: the shape every
    vector, key and ciphertext component in ML-KEM has.  The dimension is an
    argument rather than an index because it reaches the implementation as a
    run-time [size_t], and the block size is explicit for the same reason the
    matrix dimensions are in {!Spec.Frodo.Matrix}: the unifier cannot recover
    an implicit from a product. *)

let flat_at (#a: Type) (k: pos) (m: pos) (v: Seq.lseq a (k * m)) (i: nat { i < k })
  : Seq.lseq a m
  = Math.lemma_mult_le_right m (i + 1) k;
    Seq.slice v (i * m) (i * m + m)

let flat_of_fun (#a: Type) (k: pos) (m: pos) (f: (i: nat { i < k }) -> Seq.lseq a m)
  : Seq.lseq a (k * m)
  = Seq.init (k * m) (fun t -> div_lt t k m; Seq.index (f (t / m)) (t % m))

(** The same for a step that is only ghostly computable, which is most of
    them: anything that reads a secret byte is [GTot]. *)
let flat_of_fun_g (#a: Type) (k: pos) (m: pos) (f: (i: nat { i < k }) -> GTot (Seq.lseq a m))
  : GTot (Seq.lseq a (k * m))
  = Seq.init_ghost (k * m) (fun t -> div_lt t k m; Seq.index (f (t / m)) (t % m))

let flat_at_of_fun (#a: Type) (k: pos) (m: pos) (f: (i: nat { i < k }) -> Seq.lseq a m)
                   (i: nat { i < k })
  : Lemma (flat_at k m (flat_of_fun k m f) i == f i)
  = let v = flat_of_fun k m f in
    Math.lemma_mult_le_right m (i + 1) k;
    let s = flat_at k m v i in
    introduce forall (j: nat { j < m }). Seq.index s j == Seq.index (f i) j
    with begin
      Math.lemma_mod_plus j i m;
      Math.small_mod j m;
      Math.lemma_div_plus j i m;
      Math.small_div j m
    end;
    Seq.lemma_eq_intro s (f i)

(** The same for a ghost step. *)
let flat_at_of_fun_g (#a: Type) (k: pos) (m: pos)
                     (f: (i: nat { i < k }) -> GTot (Seq.lseq a m)) (i: nat { i < k })
  : Lemma (flat_at k m (flat_of_fun_g k m f) i == f i)
  = let v = flat_of_fun_g k m f in
    Math.lemma_mult_le_right m (i + 1) k;
    let s = flat_at k m v i in
    introduce forall (j: nat { j < m }). Seq.index s j == Seq.index (f i) j
    with begin
      Math.lemma_mod_plus j i m;
      Math.small_mod j m;
      Math.lemma_div_plus j i m;
      Math.small_div j m
    end;
    Seq.lemma_eq_intro s (f i)

(** A vector of [k] polynomials: entry [i] occupies coefficients [i * n]
    through [i * n + n - 1]. *)
let pvec (k: pos) = Seq.lseq zq (k * n)

let vec_at (#k: pos) (v: pvec k) (i: nat { i < k }) : poly = flat_at k n v i

let vec_of_fun (k: pos) (f: (i: nat { i < k }) -> poly) : pvec k = flat_of_fun k n f

let vec_of_fun_g (k: pos) (f: (i: nat { i < k }) -> GTot poly) : GTot (pvec k)
  = flat_of_fun_g k n f

let vec_at_of_fun_g (k: pos) (f: (i: nat { i < k }) -> GTot poly) (i: nat { i < k })
  : Lemma (vec_at (vec_of_fun_g k f) i == f i)
  = flat_at_of_fun_g k n f i

let vec_at_of_fun (k: pos) (f: (i: nat { i < k }) -> poly) (i: nat { i < k })
  : Lemma (vec_at (vec_of_fun k f) i == f i)
  = flat_at_of_fun k n f i

(** Forgetting the [< q] refinement.  [FStar.Seq] is invariant in its
    element type, so a [poly] is not a sequence of naturals however obvious
    that is; the serialisers take the wider type because half of what they
    serialise is compressed and therefore not [q]-bounded. *)
let widen (#m: nat) (f: Seq.lseq zq m) : Seq.lseq nat m
  = Seq.init m (fun i -> (Seq.index f i <: nat))

let widen_index (#m: nat) (f: Seq.lseq zq m) (i: nat { i < m })
  : Lemma (Seq.index (widen f) i == Seq.index f i) [SMTPat (Seq.index (widen f) i)]
  = ()

let vec_add (#k: pos) (u v: pvec k) : pvec k
  = Seq.init (k * n) (fun i -> add (Seq.index u i) (Seq.index v i))

let vec_sub (#k: pos) (u v: pvec k) : pvec k
  = Seq.init (k * n) (fun i -> sub (Seq.index u i) (Seq.index v i))
