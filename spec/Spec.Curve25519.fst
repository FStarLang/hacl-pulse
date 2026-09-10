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

(** X25519, as RFC 7748 defines it.

    The field is the integers modulo [2^255 - 19] and nothing here is a
    machine integer: an element is a natural number below the prime, and the
    exponentiation is the naive right-to-left recursion, which no one would
    run but which is the easiest thing to reason about.  The two lemmas
    [fexp_add] and [fexp_mul] are what a real implementation needs, because
    an inversion is an addition chain and an addition chain is a sequence of
    applications of exactly those two equations.

    The curve arithmetic is the [x]-only Montgomery ladder.  A projective
    point is a pair [(x, z)] standing for the affine [x/z]; the ladder keeps
    two of them, [n] and [n+1] times the input, and each step does one
    differential addition and one doubling.  The conditional swap is written
    as a function of the scalar bit rather than as an [if] over points, which
    is what makes the implementation constant time.

    Clamping happens on the scalar before the ladder runs, so the caller
    never has to do it, and a private key is just thirty-two arbitrary
    bytes. *)
module Spec.Curve25519

open Hacl.Spec.Bytes

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module U8 = FStar.UInt8
module Loops = Hacl.Spec.Loops

(** {2 The field} *)

let prime : pos = pow2 255 - 19

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let prime_gt_one (_: unit) : Lemma (1 < prime) =
  assert_norm (1 < pow2 255 - 19)

type elem = x: nat { x < prime }

let one : elem = prime_gt_one (); 1

let fadd (x y: elem) : elem = (x + y) % prime
let fsub (x y: elem) : elem = (x + prime - y) % prime
let fmul (x y: elem) : elem = (x * y) % prime

(** {3 Exponentiation}

    [fexp x n] is [x^n].  Defined by the obvious recursion -- this is a
    specification, not a program -- and characterised by the two equations
    below, which are all an addition chain ever needs. *)

let rec fexp (x: elem) (n: nat) : Tot elem (decreases n) =
  if n = 0 then one else fmul x (fexp x (n - 1))

let fexp_zero (x: elem) : Lemma (fexp x 0 == one) = ()

let fmul_one (x: elem) : Lemma (fmul x one == x) =
  prime_gt_one ();
  Math.small_mod x prime

let fmul_comm (x y: elem) : Lemma (fmul x y == fmul y x) =
  Math.swap_mul x y

(** [fmul] is [(_ * _) % prime], so associativity is the two multiplication-
    modulo lemmas plus the associativity of [*]. *)
let fmul_assoc (x y z: elem) : Lemma (fmul (fmul x y) z == fmul x (fmul y z)) =
  Math.lemma_mod_mul_distr_l (x * y) z prime;
  Math.lemma_mod_mul_distr_r x (y * z) prime;
  Math.paren_mul_right x y z

let rec fexp_add (x: elem) (a b: nat)
  : Lemma (ensures fexp x (a + b) == fmul (fexp x a) (fexp x b)) (decreases a)
  = if a = 0 then (fmul_comm (fexp x 0) (fexp x b); fmul_one (fexp x b))
    else begin
      fexp_add x (a - 1) b;
      fmul_assoc x (fexp x (a - 1)) (fexp x b)
    end

let rec fexp_mul (x: elem) (a b: nat)
  : Lemma (ensures fexp x (a * b) == fexp (fexp x a) b) (decreases b)
  = if b = 0 then ()
    else begin
      fexp_mul x a (b - 1);
      fexp_add x a (a * (b - 1));
      Math.distributivity_sub_right a b 1;
      fmul_comm (fexp x a) (fexp (fexp x a) (b - 1))
    end

(** Squaring, which is what an addition chain spends nearly all its time
    doing, is [fexp _ 2]; saying so lets the chain speak of exponents only. *)
#push-options "--fuel 4"
let fexp_one (x: elem) : Lemma (fexp x 1 == x) = fmul_one x
let fexp_two (x: elem) : Lemma (fexp x 2 == fmul x x) = fmul_one x
#pop-options

(** Fermat's inverse.  [prime] is prime, so [x^(p-2) x = x^(p-1) = 1] for
    every nonzero [x]; for [x = 0] this is [0], which is what the ladder
    wants -- a point at infinity encodes as thirty-two zero bytes. *)
let finv (x: elem) : elem = prime_gt_one (); fexp x (prime - 2)

(** {2 Points}

    A projective [x]-coordinate: the pair [(x, z)] means [x/z], and [(_, 0)]
    is the point at infinity. *)

type proj = elem & elem

let a24 : elem = assert_norm (121665 < prime); 121665

(** One ladder step, RFC 7748 section 5's formulas: [nq] is [n] times the
    base point and [nqp1] is [n+1] times it, sharing the difference [x1].
    The result is [2n] and [2n+1]. *)
let add_and_double (x1: elem) (nq nqp1: proj) : proj & proj =
  let (x2, z2) = nq in
  let (x3, z3) = nqp1 in
  let a = fadd x2 z2 in
  let b = fsub x2 z2 in
  let aa = fmul a a in
  let bb = fmul b b in
  let e = fsub aa bb in
  let c = fadd x3 z3 in
  let d = fsub x3 z3 in
  let da = fmul d a in
  let cb = fmul c b in
  let x3' = fmul (fadd da cb) (fadd da cb) in
  let z3' = fmul x1 (fmul (fsub da cb) (fsub da cb)) in
  let x2' = fmul aa bb in
  let z2' = fmul e (fadd aa (fmul a24 e)) in
  ((x2', z2'), (x3', z3'))

(** {2 Scalars} *)

(** RFC 7748's clamp: clear the three low bits of the first byte, clear the
    top bit of the last and set the one below it. *)
let clamp_byte (i: nat { i < 32 }) (b: S8.t) : S8.t =
  if i = 0 then S8.logand b (S8.classify 0xf8uy)
  else if i = 31 then S8.logor (S8.logand b (S8.classify 0x7fuy)) (S8.classify 0x40uy)
  else b

let clamp (k: Seq.lseq S8.t 32) : Seq.lseq S8.t 32 =
  Seq.init 32 (fun i -> clamp_byte i (Seq.index k i))

(** Bit [i] of a byte string, counting from the least significant bit of the
    first byte. *)
let ith_bit (k: Seq.lseq S8.t 32) (i: nat { i < 256 }) : GTot (n: nat { n < 2 }) =
  (S8.v (Seq.index k (i / 8)) / pow2 (i % 8)) % 2

let cswap (b: nat { b < 2 }) (p q: proj) : proj & proj =
  if b = 1 then (q, p) else (p, q)

(** Step [i] of the ladder consumes bit [255 - i], most significant first. *)
let ladder_step (x1: elem) (k: Seq.lseq S8.t 32) (i: nat { i < 256 })
                (st: proj & proj) : GTot (proj & proj) =
  let (p, q) = st in
  let b = ith_bit k (255 - i) in
  let (p, q) = cswap b p q in
  let (p, q) = add_and_double x1 p q in
  cswap b p q

(** The ladder as a fold, which is the shape the implementation's loop
    proves against.  [ladder_at] is deliberately total on every [i] so that
    [Loops.repeati] does not need a refinement. *)
let ladder_at (x1: elem) (k: Seq.lseq S8.t 32) (i: nat) (st: proj & proj)
  : GTot (proj & proj)
  = if i < 256 then ladder_step x1 k i st else st

let ladder_init (x1: elem) : proj & proj = ((one, 0), (x1, one))

let montgomery_ladder (x1: elem) (k: Seq.lseq S8.t 32) : GTot (proj & proj) =
  Loops.repeati_g 256 (ladder_at x1 k) (ladder_init x1)

(** {2 Encoding} *)

(** The [u] coordinate of a public key.  RFC 7748 says to mask the top bit
    and reduce, and says implementations must accept non-canonical
    encodings, which is exactly what the second [%] does. *)
let decode_point (u: Seq.lseq S8.t 32) : GTot elem =
  prime_gt_one ();
  (le_nat u % pow2 255) % prime

let decode_scalar (k: Seq.lseq S8.t 32) : Seq.lseq S8.t 32 = clamp k

let encode_point (p: proj) : Seq.lseq S8.t 32 =
  let (x, z) = p in
  nat_to_le 32 (fmul x (finv z))

let scalarmult (k u: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32) =
  let (nq, _) = montgomery_ladder (decode_point u) (decode_scalar k) in
  encode_point nq

let basepoint : Seq.lseq S8.t 32 = nat_to_le 32 9

(** Nine, encoded: the implementation writes the bytes and this says that
    is [basepoint]. *)
let basepoint_eq (s: Seq.lseq S8.t 32)
  : Lemma (requires S8.v (Seq.index s 0) == 9 /\
                    (forall (i: nat). 0 < i /\ i < 32 ==> S8.v (Seq.index s i) == 0))
          (ensures s == basepoint)
  = let aux (i: nat { i < 32 }) : Lemma (Seq.index s i == Seq.index basepoint i) =
      nat_to_le_index 32 9 i;
      if i = 0 then assert_norm (9 / pow2 0 % 256 == 9)
      else begin
        Math.pow2_le_compat (8 * i) 8;
        assert_norm (pow2 8 == 256);
        Math.small_division_lemma_1 9 (pow2 (8 * i))
      end in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro s basepoint

let secret_to_public (k: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32) =
  scalarmult k basepoint

(** {2 ECDH}

    An X25519 shared secret is rejected exactly when it is zero, which
    happens iff the peer sent a point of small order.  No other validation:
    the curve has no invalid-curve attack to defend against. *)
let is_zero (s: Seq.lseq S8.t 32) : GTot bool = le_nat s = 0

(** A little-endian number is zero exactly when every one of its bytes is.
    One direction is [le_nat_zeros]; the other is that a nonzero byte at [k]
    contributes at least [256^k]. *)
let rec le_nat_pos (s: Seq.seq S8.t) (k: nat { k < Seq.length s })
  : Lemma (requires S8.v (Seq.index s k) > 0) (ensures le_nat s > 0)
          (decreases k)
  = if k = 0 then ()
    else begin
      let n = Seq.length s in
      let t = Seq.slice s 1 n in
      assert (Seq.index t (k - 1) == Seq.index s k);
      le_nat_pos t (k - 1)
    end

let le_nat_zero_iff (s: Seq.seq S8.t)
  : Lemma ((le_nat s == 0) <==>
           (forall (i: nat). i < Seq.length s ==> S8.v (Seq.index s i) == 0))
  = let fwd () : Lemma (requires le_nat s == 0)
                       (ensures forall (i: nat). i < Seq.length s ==>
                                  S8.v (Seq.index s i) == 0)
      = let aux (i: nat { i < Seq.length s }) : Lemma (S8.v (Seq.index s i) == 0) =
          if S8.v (Seq.index s i) > 0 then le_nat_pos s i in
        FStar.Classical.forall_intro aux in
    FStar.Classical.move_requires fwd ();
    FStar.Classical.move_requires le_nat_zeros s

let ecdh (k u: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32 & bool) =
  let s = scalarmult k u in
  (s, not (is_zero s))

#pop-options
