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

(** The ring ML-DSA works in: [Z_8380417] and degree-256 polynomials over
    it.

    The same choices as {!Spec.MLKEM.Zq}: coefficients are naturals below
    [q], canonical everywhere, and the specification says modular
    arithmetic rather than machine arithmetic.  The flat-sequence helpers
    ([flat_at], [flat_of_fun] and their lemmas) do not mention [q] and are
    used from there rather than repeated.

    ML-DSA has signed quantities -- the secret vectors, the mask, [z],
    [t0] -- that FIPS 204 writes as integers in a symmetric range and then
    treats as elements of [R_q] anyway.  This specification keeps all of
    them in [Z_q] and says "small" with {!norm}, the absolute value of the
    centred representative.  The coders pack [b - c] for a bound [b], and
    [b - c] computed modulo [q] is the integer [b - c] whenever [c] is in
    range, so nothing below ever needs a signed type. *)
module Spec.MLDSA.Zq

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module KZ = Spec.MLKEM.Zq

(** {2 The modulus} *)

(** [q = 2^23 - 2^13 + 1].  [q - 1] is divisible by 512, so [Z_q] contains
    a primitive 512th root of unity and [X^256 + 1] splits into linear
    factors: the NTT runs all eight layers and multiplication in the NTT
    domain is pointwise. *)
let q : pos = 8380417

let n : pos = 256

(** The number of bits [Power2Round] drops from [t]. *)
let d : pos = 13

let q_bound () : Lemma (q < pow2 23) = assert_norm (8380417 < pow2 23)

let zq = x: nat { x < q }

(** {2 Arithmetic} *)

let add (a b: zq) : zq = (a + b) % q

let sub (a b: zq) : zq = (a + q - b) % q

let mul (a b: zq) : zq = (a * b) % q

let neg (a: zq) : zq = (q - a) % q

(** An integer reduced into [Z_q], for the constants FIPS 204 writes as
    signed. *)
let of_int (x: int) : zq = x % q

(** {2 Size}

    [|x mod+- q|]: the distance from [x] to the nearest multiple of [q].
    [q] is odd, so the centred range is [[-(q-1)/2, (q-1)/2]] and there is
    no tie. *)

let half_q : nat = (q - 1) / 2

let norm (x: zq) : nat = if x > half_q then q - x else x

let centre (x: zq) : int = if x > half_q then x - q else x

(** Every coefficient of [s] is strictly smaller than [b].  [FIPS 204]
    writes [||w||_inf < b]; the implementation's loop computes exactly
    this conjunction, coefficient by coefficient. *)
let rec all_lt (s: Seq.seq zq) (b: nat) : Tot bool (decreases Seq.length s)
  = if Seq.length s = 0 then true
    else norm (Seq.index s 0) < b && all_lt (Seq.tail s) b

let rec all_lt_spec (s: Seq.seq zq) (b: nat)
  : Lemma (ensures all_lt s b <==> (forall (i: nat). i < Seq.length s ==> norm (Seq.index s i) < b))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      all_lt_spec (Seq.tail s) b;
      assert (forall (i: nat). 0 < i /\ i < Seq.length s ==> Seq.index s i == Seq.index (Seq.tail s) (i - 1))
    end

(** {2 Exponentiation and the root of unity} *)

let rec pow (a: zq) (k: nat) : Tot zq (decreases k)
  = if k = 0 then 1 else mul a (pow a (k - 1))

(** [zeta = 1753], a primitive 512th root of unity modulo [q]. *)
let zeta : zq = 1753

let zeta_256 () : Lemma (pow zeta 256 == q - 1)
  = assert_norm (pow zeta 256 == q - 1)

let bit (i: nat) (k: nat) : r: nat { r < 2 } = (i / pow2 k) % 2

(** [BitRev8]. *)
let bitrev8 (i: nat { i < 256 }) : r: nat { r < 256 }
  = let r =   bit i 0 * 128 + bit i 1 * 64 + bit i 2 * 32 + bit i 3 * 16
            + bit i 4 * 8   + bit i 5 * 4  + bit i 6 * 2  + bit i 7 in
    assert (r <= 255);
    r

(** {2 Polynomials and vectors} *)

let poly = Seq.lseq zq n

let poly_zero : poly = Seq.create n 0

let poly_add (f g: poly) : poly
  = Seq.init n (fun i -> add (Seq.index f i) (Seq.index g i))

let poly_sub (f g: poly) : poly
  = Seq.init n (fun i -> sub (Seq.index f i) (Seq.index g i))

(** Multiplication in the NTT domain, where it is pointwise. *)
let poly_mul (f g: poly) : poly
  = Seq.init n (fun i -> mul (Seq.index f i) (Seq.index g i))

let poly_add_index (f g: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_add f g) i == add (Seq.index f i) (Seq.index g i))
          [SMTPat (Seq.index (poly_add f g) i)]
  = ()

let poly_sub_index (f g: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_sub f g) i == sub (Seq.index f i) (Seq.index g i))
          [SMTPat (Seq.index (poly_sub f g) i)]
  = ()

let poly_mul_index (f g: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_mul f g) i == mul (Seq.index f i) (Seq.index g i))
          [SMTPat (Seq.index (poly_mul f g) i)]
  = ()

(** A [k]-vector of polynomials, flat: entry [i] is coefficients [i * n]
    through [i * n + n - 1], exactly as in ML-KEM. *)
let pvec (k: pos) = Seq.lseq zq (k * n)

let vec_at (#k: pos) (v: pvec k) (i: nat { i < k }) : poly = KZ.flat_at k n v i

let vec_of_fun (k: pos) (f: (i: nat { i < k }) -> poly) : pvec k = KZ.flat_of_fun k n f

let vec_of_fun_g (k: pos) (f: (i: nat { i < k }) -> GTot poly) : GTot (pvec k)
  = KZ.flat_of_fun_g k n f

let vec_at_of_fun (k: pos) (f: (i: nat { i < k }) -> poly) (i: nat { i < k })
  : Lemma (vec_at (vec_of_fun k f) i == f i)
  = KZ.flat_at_of_fun k n f i

let vec_at_of_fun_g (k: pos) (f: (i: nat { i < k }) -> GTot poly) (i: nat { i < k })
  : Lemma (vec_at (vec_of_fun_g k f) i == f i)
  = KZ.flat_at_of_fun_g k n f i

(** Coefficient-wise operations on vectors.  Being coefficient-wise, they
    are [Seq.init]s over the flat sequence rather than per entry. *)

let vec_add (#k: pos) (u v: pvec k) : pvec k
  = Seq.init (k * n) (fun i -> add (Seq.index u i) (Seq.index v i))

let vec_sub (#k: pos) (u v: pvec k) : pvec k
  = Seq.init (k * n) (fun i -> sub (Seq.index u i) (Seq.index v i))

let vec_map (#k: pos) (f: zq -> zq) (v: pvec k) : pvec k
  = Seq.init (k * n) (fun i -> f (Seq.index v i))

(** A [k x l] matrix, flat and row-major: row [i] is an [l]-vector, entry
    [(i, j)] is polynomial [i * l + j]. *)
let pmat (k l: pos) = Seq.lseq zq (k * l * n)

let mat_row (#k #l: pos) (m: pmat k l) (i: nat { i < k }) : pvec l
  = Math.lemma_mult_le_right (l * n) (i + 1) k;
    Math.paren_mul_right k l n;
    Seq.slice m (i * (l * n)) (i * (l * n) + l * n)
