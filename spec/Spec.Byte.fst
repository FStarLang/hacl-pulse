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

(** Bytes as numbers, for the specifications that are arithmetic.

    Most of this library's specifications are written on
    [Hacl.Secret.UInt8.t] and say what the implementation computes in the same
    vocabulary the implementation uses.  AES and GHASH are different: they are
    arithmetic in GF(2^8) and GF(2^128), and their statements -- [xtime], the
    affine map that defines the S-box, the reduction step of the GHASH
    multiplication -- read as arithmetic on numbers.  Writing them on secret
    bytes would mean the same equations with [S8.logxor] where [^^] is, and
    every proof about them carrying an [S8.v] round trip.

    So they are written on numbers below 256, and [vals] is the view that
    connects a secret byte sequence to the numbers it denotes.  It is the only
    place the two worlds meet.

    The bitwise operations route through [FStar.UInt8] rather than through
    [FStar.UInt] because [FStar.UInt.logxor] is an abstract [val]: it has no
    definition to unfold, so a term built from it can only be reasoned about
    by the solver, one axiom at a time, and the normalizer cannot evaluate it
    at all.  [FStar.UInt8]'s operations are primitives that F*'s normalizer
    runs directly.  The two agree by the postconditions in [FStar.UInt8.fsti],
    which is what [xor_is_logxor] records. *)
module Spec.Byte

module Seq = FStar.Seq
module UInt = FStar.UInt
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

let elem = UInt.uint_t 8

unfold let ( ^^ ) (a b: elem) : elem =
  U8.v (U8.logxor (U8.uint_to_t a) (U8.uint_to_t b))

let xor_is_logxor (a b: elem) : Lemma (a ^^ b == UInt.logxor #8 a b) = ()

let xor_zero (a: elem) : Lemma (a ^^ 0 == a /\ 0 ^^ a == a) =
  UInt.logxor_lemma_1 #8 a;
  UInt.logxor_commutative #8 a 0

let xor_self (a: elem) : Lemma (a ^^ a == 0) = UInt.logxor_self #8 a

let xor_comm (a b: elem) : Lemma (a ^^ b == b ^^ a) = UInt.logxor_commutative #8 a b

let xor_assoc (a b c: elem) : Lemma (a ^^ (b ^^ c) == (a ^^ b) ^^ c) =
  UInt.logxor_associative #8 a b c

(** Byte [k / 8] from the bottom of [n]. *)
let byte_at (n: nat) (k: nat) : elem =
  assert_norm (pow2 8 == 256);
  (n / pow2 k) % 256

(** Rotation of the eight bits, left by [k]. *)
let rotl8 (x: elem) (k: nat { 0 < k /\ k < 8 }) : elem =
  let b = U8.uint_to_t x in
  U8.v (U8.logor (U8.shift_left b (U32.uint_to_t k))
                 (U8.shift_right b (U32.uint_to_t (8 - k))))

(** The two halves of the rotation occupy disjoint bits, so the or is an
    addition -- which is what lets [Hacl.Secret.UInt8.rotate_left], whose
    postcondition is arithmetic, be recognized as this. *)
let rotl8_value (x: elem) (k: nat { 0 < k /\ k < 8 })
  : Lemma (rotl8 x k == (x % pow2 (8 - k)) * pow2 k + x / pow2 (8 - k))
  = let b = U8.uint_to_t x in
    let hi = U8.shift_left b (U32.uint_to_t k) in
    let lo = U8.shift_right b (U32.uint_to_t (8 - k)) in
    UInt.shift_left_value_lemma #8 x k;
    UInt.shift_right_value_lemma #8 x (8 - k);
    Math.pow2_multiplication_modulo_lemma_2 x 8 k;
    Math.multiple_modulo_lemma (x % pow2 (8 - k)) (pow2 k);
    Math.lemma_div_lt x 8 (8 - k);
    UInt.logor_disjoint #8 (U8.v hi) (U8.v lo) k

(** {2 The view of a secret byte sequence}

    The implementations work on [Hacl.Secret.UInt8.t]; their postconditions
    say that [vals] of the output is what the specification computes.

    The ascription on the body is load-bearing.  Without it F* infers the
    element type of the sequence from [S8.v]'s own refinement, [n: nat { n <
    pow2 8 }], which is not syntactically [elem]; [Seq.lemma_init_ghost_len]'s
    pattern then fails to match and even the length of [vals s] becomes
    unprovable. *)

let vals (s: Seq.seq S8.t) : GTot (Seq.seq elem) =
  Seq.init_ghost (Seq.length s) (fun k -> (S8.v (Seq.index s k) <: elem))

let vals_len (s: Seq.seq S8.t)
  : Lemma (Seq.length (vals s) == Seq.length s)
          [SMTPat (Seq.length (vals s))]
  = ()

let vals_index (s: Seq.seq S8.t) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (vals s) i == S8.v (Seq.index s i))
          [SMTPat (Seq.index (vals s) i)]
  = Seq.init_ghost_index (Seq.length s) (fun k -> (S8.v (Seq.index s k) <: elem))

let vals_upd (s: Seq.seq S8.t) (i: nat { i < Seq.length s }) (x: S8.t)
  : Lemma (vals (Seq.upd s i x) == Seq.upd (vals s) i (S8.v x))
  = Seq.lemma_eq_intro (vals (Seq.upd s i x)) (Seq.upd (vals s) i (S8.v x))

(** [vals] commutes with slicing, which is what a caller who hands a
    sub-buffer to a block function needs. *)
let vals_slice (s: Seq.seq S8.t) (lo: nat) (hi: nat { lo <= hi /\ hi <= Seq.length s })
  : Lemma (vals (Seq.slice s lo hi) == Seq.slice (vals s) lo hi)
  = Seq.lemma_eq_intro (vals (Seq.slice s lo hi)) (Seq.slice (vals s) lo hi)

(** {2 Classifying back}

    [vals] has an inverse: a byte is a byte, and the secrecy of a value is a
    property of how a program uses it, not of the number.  Specifications
    that have to speak about both worlds at once -- HPKE, whose AEAD may be
    either AES-GCM (specified over [elem]) or ChaCha20-Poly1305 (specified
    over [S8.t]) -- need to move in this direction too.

    This is a ghost function, so it classifies nothing at run time; there is
    no declassification here and none anywhere else. *)
let secrets (s: Seq.seq elem) : GTot (Seq.seq S8.t) =
  Seq.init_ghost (Seq.length s) (fun k -> S8.classify (U8.uint_to_t (Seq.index s k)))

let secrets_len (s: Seq.seq elem)
  : Lemma (Seq.length (secrets s) == Seq.length s)
          [SMTPat (Seq.length (secrets s))]
  = ()

let secrets_index (s: Seq.seq elem) (i: nat { i < Seq.length s })
  : Lemma (S8.v (Seq.index (secrets s) i) == Seq.index s i)
          [SMTPat (Seq.index (secrets s) i)]
  = Seq.init_ghost_index (Seq.length s) (fun k -> S8.classify (U8.uint_to_t (Seq.index s k)))

let vals_secrets (s: Seq.seq elem)
  : Lemma (vals (secrets s) == s) [SMTPat (vals (secrets s))]
  = Seq.lemma_eq_intro (vals (secrets s)) s

(** The other composite: [vals] is injective, because [S8.v] is. *)
let secrets_vals (s: Seq.seq S8.t)
  : Lemma (secrets (vals s) == s) [SMTPat (secrets (vals s))]
  = Seq.lemma_eq_intro (secrets (vals s)) s

let vals_injective (s1 s2: Seq.seq S8.t)
  : Lemma (requires vals s1 == vals s2) (ensures s1 == s2)
  = secrets_vals s1; secrets_vals s2
