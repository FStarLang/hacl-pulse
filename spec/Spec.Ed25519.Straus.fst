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

(** What a variable-time double-scalar multiplication computes.

    Verification checks [[S]B = R + [k]A].  {!Hacl.Ed25519.Straus} instead
    computes [Q = [k](-A) + [S]B] with one doubling chain shared between
    the two scalars, and compares [Q] with [R].  This file says why that is
    the same test, and what the two digit strings the chain walks add up
    to.

    The group argument wants exactly one inverse: [[k](-A) + [k]A] is the
    identity, which is distributivity and [-A + A = 0].  No order of the
    group enters, so [A] may carry any small-order component it likes --
    the comparison is still exactly the one the specification makes. *)
module Spec.Ed25519.Straus

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

module G = Spec.Group.Smul
module SM = Spec.Ed25519.Smul
module B = Hacl.Spec.Bytes
module U8 = FStar.UInt8
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The accumulator} *)

let lin2 (a b: nat) (na: ext_point) : ext_point = G.lin2 SM.eg a b na g

(** [p] is [[a]na + [b]G].  Opaque, for the reason every invariant over
    [point_equal] is. *)
[@@"opaque_to_smt"]
let st (p na: ext_point) (a b: nat) : prop =
  on_curve na /\ on_curve p /\ point_equal p (lin2 a b na)

let st_on_curve (p na: ext_point) (a b: nat)
  : Lemma (requires st p na a b) (ensures on_curve p /\ on_curve na)
  = reveal_opaque (`%st) (st p na a b)

let st_cong (p na: ext_point) (a b a' b': nat)
  : Lemma (requires st p na a b /\ a == a' /\ b == b') (ensures st p na a' b')
  = ()

let st_zero (na: ext_point)
  : Lemma (requires on_curve na) (ensures st point_at_infinity na 0 0)
  = reveal_opaque (`%st) (st point_at_infinity na 0 0);
    g_on_curve ();
    G.lin2_zero SM.eg na g

let st_dbl (p na: ext_point) (a b: nat)
  : Lemma (requires st p na a b) (ensures st (point_double p) na (2 * a) (2 * b))
  = reveal_opaque (`%st) (st p na a b);
    reveal_opaque (`%st) (st (point_double p) na (2 * a) (2 * b));
    g_on_curve ();
    G.lin2_dbl SM.eg a b na g p

(** Adding [e = [d]na]. *)
let st_adda (p na e: ext_point) (a b d: nat)
  : Lemma (requires st p na a b /\ on_curve e /\ point_equal e (SM.smul d na))
          (ensures st (point_add p e) na (a + d) b)
  = reveal_opaque (`%st) (st p na a b);
    reveal_opaque (`%st) (st (point_add p e) na (a + d) b);
    g_on_curve ();
    G.lin2_addl SM.eg a b d na g p e

(** Adding [e = [d]G]. *)
let st_addb (p na e: ext_point) (a b d: nat)
  : Lemma (requires st p na a b /\ on_curve e /\ point_equal e (SM.smul d g))
          (ensures st (point_add p e) na a (b + d))
  = reveal_opaque (`%st) (st p na a b);
    reveal_opaque (`%st) (st (point_add p e) na a (b + d));
    g_on_curve ();
    G.lin2_addr SM.eg a b d na g p e

(** {2 The test it decides} *)

let le_scalar (n: nat { n < q }) : Lemma (B.le_nat (scalar_bytes n) == n)
  = assert_norm (q < pow2 (8 * 32));
    B.le_nat_to_le 32 n

(** [[k](-A) + [k]A] is the identity. *)
let kill (aa: ext_point) (k: nat)
  : Lemma (requires on_curve aa)
          (ensures point_equal (point_add (SM.smul k (point_negate aa)) (SM.smul k aa))
                               point_at_infinity)
  = let na = point_negate aa in
    point_negate_on_curve aa;
    point_at_infinity_on_curve ();
    point_add_on_curve na aa;
    SM.smul_ok k na; SM.smul_ok k aa; SM.smul_ok k (point_add na aa);
    SM.smul_ok k point_at_infinity;
    point_add_on_curve (SM.smul k na) (SM.smul k aa);
    G.smul_distr SM.eg k na aa;
    point_equal_sym (SM.smul k (point_add na aa))
                    (point_add (SM.smul k na) (SM.smul k aa));
    point_add_negate aa;
    SM.smul_congr k (point_add na aa) point_at_infinity;
    G.smul_of_zero SM.eg k;
    point_equal_trans (point_add (SM.smul k na) (SM.smul k aa))
                      (SM.smul k (point_add na aa)) (SM.smul k point_at_infinity);
    point_equal_trans (point_add (SM.smul k na) (SM.smul k aa))
                      (SM.smul k point_at_infinity) point_at_infinity

#push-options "--z3rlimit 100"
(** Comparing [Q] with [R] is comparing [[S]B] with [R + [k]A]. *)
let st_verify (qq aa rp: ext_point) (k s: (n: nat { n < q }))
  : Lemma (requires on_curve aa /\ on_curve rp /\ st qq (point_negate aa) k s)
          (ensures point_equal qq rp ==
                   point_equal (point_mul_g (scalar_bytes s))
                               (point_add rp (point_mul (scalar_bytes k) aa)))
  = reveal_opaque (`%st) (st qq (point_negate aa) k s);
    let na = point_negate aa in
    let kn = SM.smul k na in
    let ka = SM.smul k aa in
    let sb = SM.smul s g in
    let sb' = point_mul_g (scalar_bytes s) in
    let ka' = point_mul (scalar_bytes k) aa in
    g_on_curve ();
    point_negate_on_curve aa;
    point_at_infinity_on_curve ();
    SM.smul_ok k na; SM.smul_ok k aa; SM.smul_ok s g;
    point_add_on_curve kn sb;
    point_add_on_curve rp ka;
    kill aa k;
    G.cancel SM.eg kn ka sb rp;
    SM.point_equal_congr qq (point_add kn sb) rp rp;
    point_equal_refl rp;
    le_scalar s; le_scalar k;
    SM.point_mul_is_smul (scalar_bytes s) g;
    SM.point_mul_is_smul (scalar_bytes k) aa;
    point_add_congr rp rp ka' ka;
    point_add_on_curve rp ka';
    SM.point_equal_congr sb' sb (point_add rp ka') (point_add rp ka)
#pop-options

(** {2 Digit strings}

    A scalar is written as 256 digits [d_j], each zero or odd, with
    [sum d_j 2^j] its value.  [dsum] is that sum over the first [n]
    digits; [hsum] is the Horner evaluation from the top down to [i],
    which is what the doubling chain has accumulated after the rung at
    [i]. *)

let nd : nat = 256

let dg (s: Seq.seq U8.t) (j: nat) : nat =
  if j < Seq.length s then U8.v (Seq.index s j) else 0

let rec dsum (s: Seq.seq U8.t) (n: nat) : Tot nat (decreases n) =
  if n = 0 then 0 else dsum s (n - 1) + dg s (n - 1) * pow2 (n - 1)

let rec hsum (s: Seq.seq U8.t) (i: nat) : Tot nat (decreases (nd - i)) =
  if i >= nd then 0 else 2 * hsum s (i + 1) + dg s i

#push-options "--fuel 1"

let hsum_step (s: Seq.seq U8.t) (i: nat)
  : Lemma (requires i < nd) (ensures hsum s i == 2 * hsum s (i + 1) + dg s i)
  = ()

let hsum_top (s: Seq.seq U8.t) : Lemma (hsum s nd == 0) = ()

let rec hsum_split (s: Seq.seq U8.t) (i: nat)
  : Lemma (requires i <= nd)
          (ensures hsum s i * pow2 i + dsum s i == dsum s nd)
          (decreases (nd - i))
  = if i = nd then ()
    else begin
      hsum_split s (i + 1);
      Math.pow2_plus 1 i;
      assert_norm (pow2 1 == 2);
      Math.distributivity_add_left (2 * hsum s (i + 1)) (dg s i) (pow2 i);
      Math.paren_mul_right 2 (hsum s (i + 1)) (pow2 i);
      Math.paren_mul_right (hsum s (i + 1)) 2 (pow2 i)
    end

let hsum_dsum (s: Seq.seq U8.t) : Lemma (hsum s 0 == dsum s nd)
  = hsum_split s 0; assert_norm (pow2 0 == 1)

let rec dsum_upd (s: Seq.seq U8.t) (j: nat) (v: U8.t) (n: nat)
  : Lemma (requires j < Seq.length s)
          (ensures dsum (Seq.upd s j v) n ==
                   (if j < n then dsum s n + (U8.v v - dg s j) * pow2 j
                    else dsum s n))
          (decreases n)
  = if n = 0 then ()
    else begin
      dsum_upd s j v (n - 1);
      if n - 1 = j then Math.distributivity_sub_left (U8.v v) (dg s j) (pow2 j)
    end

#pop-options

(** Folding digit [i + t], which is one, into digit [i]: the sum is
    unchanged, because [2^t 2^i = 2^(i + t)]. *)
let dsum_fold (s: Seq.seq U8.t) (i t: nat) (v: U8.t)
  : Lemma (requires Seq.length s == nd /\ i + t < nd /\ t > 0 /\ dg s (i + t) == 1 /\
                    U8.v v == dg s i + pow2 t)
          (ensures dsum (Seq.upd (Seq.upd s i v) (i + t) 0uy) nd == dsum s nd /\
                   Seq.length (Seq.upd (Seq.upd s i v) (i + t) 0uy) == Seq.length s)
  = let s1 = Seq.upd s i v in
    dsum_upd s i v nd;
    dsum_upd s1 (i + t) 0uy nd;
    assert (dg s1 (i + t) == 1);
    Math.pow2_plus t i;
    assert (dsum s1 nd == dsum s nd + pow2 t * pow2 i);
    assert (dsum (Seq.upd s1 (i + t) 0uy) nd == dsum s1 nd - pow2 (i + t))

(** Bit [n] of [k] completes [k mod 2^n] to [k mod 2^(n+1)]. *)
let mod_succ (k: nat) (n: nat)
  : Lemma (k % pow2 (n + 1) == k % pow2 n + G.gbit k n * pow2 n)
  = let b = pow2 n in
    Math.pow2_plus n 1;
    assert_norm (pow2 1 == 2);
    let m = k % (b * 2) in
    Math.euclidean_division_definition m b;
    Math.modulo_division_lemma k b 2;
    Math.modulo_modulo_lemma k b 2

#push-options "--fuel 1"
let rec dsum_bits (s: Seq.seq U8.t) (k: nat) (n: nat)
  : Lemma (requires (forall (j: nat). j < n ==> dg s j == G.gbit k j))
          (ensures dsum s n == k % pow2 n)
          (decreases n)
  = if n = 0 then assert_norm (pow2 0 == 1)
    else begin
      dsum_bits s k (n - 1);
      mod_succ k (n - 1)
    end
#pop-options

#pop-options
