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

(** The three ML-DSA parameter sets, FIPS 204 table 1.

    As with {!Spec.MLKEM.Params}, [q], [n] and [d] are the same for every
    set and are constants of {!Spec.MLDSA.Zq}; what varies is eight numbers,
    and every derived length is a function of them.  [gamma1] is a power of
    two and [gamma2] is [(q - 1)] divided by 88 or by 32, so the record
    carries the exponent and the divisor rather than the values: those are
    what the coders' bit widths are functions of. *)
module Spec.MLDSA.Params

open Spec.MLDSA.Zq

noeq
type params = {
  (** [A] is [k x l]; [s2], [t] and the hint are [k]-vectors and [s1],
      [y] and [z] are [l]-vectors. *)
  k: r: pos { r == 4 \/ r == 6 \/ r == 8 };
  l: r: pos { r == 4 \/ r == 5 \/ r == 7 };
  (** The secret coefficients lie in [-eta, eta]. *)
  eta: e: pos { e == 2 \/ e == 4 };
  (** The number of [+-1]s in the challenge. *)
  tau: t: pos { t <= 60 };
  (** The collision strength of the commitment hash, in bits. *)
  lambda: x: pos { x == 128 \/ x == 192 \/ x == 256 };
  (** [gamma1 = 2^gamma1_bits], the range of the masking vector. *)
  gamma1_bits: g: pos { g == 17 \/ g == 19 };
  (** [gamma2 = (q - 1) / gamma2_div], the low-order rounding range. *)
  gamma2_div: g: pos { g == 88 \/ g == 32 };
  (** The maximum number of ones in the hint. *)
  omega: w: pos { w <= 80 };
}

let mldsa44 : params =
  { k = 4; l = 4; eta = 2; tau = 39; lambda = 128; gamma1_bits = 17; gamma2_div = 88; omega = 80 }
let mldsa65 : params =
  { k = 6; l = 5; eta = 4; tau = 49; lambda = 192; gamma1_bits = 19; gamma2_div = 32; omega = 55 }
let mldsa87 : params =
  { k = 8; l = 7; eta = 2; tau = 60; lambda = 256; gamma1_bits = 19; gamma2_div = 32; omega = 75 }

(** {2 Derived values} *)

let gamma1 (p: params) : pos = pow2 p.gamma1_bits

let gamma2 (p: params) : pos = (q - 1) / p.gamma2_div

let beta (p: params) : pos = p.tau * p.eta

(** [beta] is at most 240, far below both rounding ranges. *)
let beta_lt (p: params) : Lemma (beta p < gamma1 p /\ beta p < gamma2 p)
  = FStar.Math.Lemmas.pow2_le_compat p.gamma1_bits 17;
    assert_norm (pow2 17 == 131072);
    assert (p.tau * p.eta <= 60 * 4)

(** The number of high-order values [HighBits] can produce is
    [(q - 1) / (2 gamma2)]: 44 or 16.  [w1] coefficients are below it and
    are packed at [bitlen((q - 1) / (2 gamma2) - 1)] bits: 6 or 4. *)
let w1_bits (p: params) : pos = if p.gamma2_div = 88 then 6 else 4

(** [s1] and [s2] coefficients are packed as [eta - c] in [0, 2 eta] at
    [bitlen(2 eta)] bits: 3 or 4. *)
let eta_bits (p: params) : pos = if p.eta = 2 then 3 else 4

(** [z] coefficients are packed as [gamma1 - c] in [0, 2 gamma1 - 1] at
    [1 + bitlen(gamma1 - 1)] bits: 18 or 20. *)
let z_bits (p: params) : pos = p.gamma1_bits + 1

(** {2 Sizes, in bytes} *)

(** The commitment hash [c-tilde]. *)
let ct_len (p: params) : pos = p.lambda / 4

(** [rho] and [k] polynomials of [t1] at ten bits. *)
let pk_len (p: params) : pos = 32 + 320 * p.k

(** [rho], [K], [tr], then [s1], [s2] at [eta_bits] and [t0] at thirteen
    bits. *)
let sk_len (p: params) : pos = 128 + 32 * eta_bits p * (p.l + p.k) + 416 * p.k

(** [c-tilde], [z] at [z_bits], and the hint: [omega] positions and [k]
    running counts. *)
let sig_len (p: params) : pos = ct_len p + 32 * z_bits p * p.l + p.omega + p.k

(** {2 The signing loop bound}

    FIPS 204 lets an implementation give up after a bounded number of
    attempts, provided the bound is at least the one appendix C tabulates
    for the parameter set (814 for ML-DSA-44, fewer for the larger sets).
    One bound serves all three here.  [kappa] advances by [l] per attempt
    and is encoded in sixteen bits, so the bound also has to keep
    [max_attempts * l] below [2^16]; at [l = 7] that allows 9362, and 1024
    is comfortably inside both constraints.  The expected number of
    attempts is between four and five; reaching 1024 has probability far
    below [2^-256]. *)
let max_attempts : pos = 1024

let kappa_bound (p: params) (a: nat { a < max_attempts }) (r: nat { r < p.l })
  : Lemma (a * p.l + r < pow2 16)
  = assert_norm (pow2 16 == 65536)

(** The published sizes, FIPS 204 table 2. *)
let sizes_44 () : Lemma (pk_len mldsa44 == 1312 /\ sk_len mldsa44 == 2560 /\ sig_len mldsa44 == 2420)
  = assert_norm (pk_len mldsa44 == 1312 /\ sk_len mldsa44 == 2560 /\ sig_len mldsa44 == 2420)
let sizes_65 () : Lemma (pk_len mldsa65 == 1952 /\ sk_len mldsa65 == 4032 /\ sig_len mldsa65 == 3309)
  = assert_norm (pk_len mldsa65 == 1952 /\ sk_len mldsa65 == 4032 /\ sig_len mldsa65 == 3309)
let sizes_87 () : Lemma (pk_len mldsa87 == 2592 /\ sk_len mldsa87 == 4896 /\ sig_len mldsa87 == 4627)
  = assert_norm (pk_len mldsa87 == 2592 /\ sk_len mldsa87 == 4896 /\ sig_len mldsa87 == 4627)
