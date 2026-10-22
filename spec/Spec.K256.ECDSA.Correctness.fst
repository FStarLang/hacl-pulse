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

(** secp256k1 ECDSA: a signature verifies under the signer's public key, and
    the low-S form does too.

    If [ecdsa_sign_msg_as_qelem m sk nonce] returns [Some sg], then
    [dh_initiator sk] -- the public key of [sk], as the specification
    defines it -- returns some [pk], and [ecdsa_verify_msg_as_qelem] accepts
    [sg], split into [r] and [s], against [pk] and [m] ({!verify_sign}).  If
    [secp256k1_ecdsa_sign_msg_as_qelem] returns [Some sg], then [sg] is
    normalized and [secp256k1_ecdsa_verify_msg_as_qelem] accepts it
    ({!secp256k1_verify_sign}).  Both lift to the SHA2-256 front ends
    ({!verify_sign_sha256}, {!secp256k1_verify_sign_sha256}).

    The first half is the proof of {!Spec.P256.ECDSA.Correctness} over this
    curve: with [s = k^-1 (m + r d)], the verifier's [u1 + u2 d] is [k]
    modulo [n] ({!Spec.Group.ECDSA.recover_nonce}), [u1 G + u2 Q] is
    equivalent to [(u1 + u2 d mod n) G] ({!Spec.Group.ECDSA.verify_eq}),
    and so to the signer's [k G], whose affine [x]-coordinate is [r].

    Normalization replaces [s] by [n - s], which is [-s] modulo [n], when
    [s] is in the upper half.  The verifier then recovers [-k] instead of
    [k] ({!Spec.Group.ECDSA.recover_neg_nonce}), and [(n - k) G] is the
    negation of [k G] ({!Spec.Group.ECDSA.smul_neg} with
    [point_add_negate]).  Negation keeps the [x]-coordinate, so the
    comparison with [r] succeeds all the same ({!neg_point_x}).  [n] is odd,
    so [n - s] is in the lower half. *)
module Spec.K256.ECDSA.Correctness

open Hacl.Spec.Bytes
open Spec.K256
open Spec.K256.Group

module GE = Spec.Group.ECDSA
module SM = Spec.K256.Smul
module O = Spec.K256.Order
module F = Spec.Group.Field
module MA = Spec.ModArith
module M = FStar.Math.Lemmas
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The verification equation} *)

(** The verifier's point, before it looks at coordinates. *)
let verify_point (q: proj_point) (d u1 u2: nat)
  : Lemma (requires 0 < d /\ d < order /\ u1 < order /\ u2 < order /\
                    on_curve q /\ peq q (point_mul_g d) /\
                    (u1 + u2 * d) % order <> 0)
          (ensures (let c = (u1 + u2 * d) % order in
                    on_curve (point_mul_double_g u1 u2 q) /\
                    ~(is_point_at_infinity (point_mul_double_g u1 u2 q)) /\
                    to_aff_point (point_mul_double_g u1 u2 q) == to_aff_point (point_mul_g c)))
  = let c = (u1 + u2 * d) % order in
    let a1 = point_mul u1 g in
    let a2 = point_mul u2 q in
    let res = point_mul_double_g u1 u2 q in
    O.bounds ();
    g_on_curve ();
    O.g_has_order ();
    M.small_mod d order;
    O.point_mul_g_nonzero d;
    M.lemma_mod_twice (u1 + u2 * d) order;
    O.point_mul_g_nonzero c;
    O.smul_g_nonzero c;
    SM.smul_ok d g;
    peq_trans q (point_mul_g d) (SM.smul d g);
    SM.point_mul_is_smul u1 g;
    SM.point_mul_is_smul u2 q;
    SM.smul_ok u1 g;
    SM.smul_ok u2 q;
    point_add_congr a1 (SM.smul u1 g) a2 (SM.smul u2 q);
    point_add_on_curve a1 a2;
    GE.verify_eq SM.kg order g q d u1 u2;
    point_add_on_curve (SM.smul u1 g) (SM.smul u2 q);
    peq_trans res (point_add (SM.smul u1 g) (SM.smul u2 q)) (SM.smul c g);
    O.not_inf_of_peq res (SM.smul c g);
    peq_sym (point_mul_g c) (SM.smul c g);
    peq_trans res (SM.smul c g) (point_mul_g c);
    peq_to_aff_point res (point_mul_g c)

(** Verification accepts [(r, s)] under the public key of [d] whenever the
    scalar it recovers is nonzero and names a point whose [x]-coordinate is
    [r] modulo [n]. *)
let verify_accepts (m: qelem) (d r s: nat)
  : Lemma (requires 0 < d /\ d < order /\ 0 < r /\ r < order /\ 0 < s /\ s < order /\
                    (let u1 = qmul (qinv s) m in
                     let u2 = qmul (qinv s) r in
                     let c = (u1 + u2 * d) % order in
                     c <> 0 /\ fst (to_aff_point (point_mul_g c)) % order == r))
          (ensures ecdsa_verify_msg_as_qelem m (store_point (point_mul_g d))
                                             (nat_to_be 32 r) (nat_to_be 32 s))
  = let p = point_mul_g d in
    O.bounds ();
    be_nat_to_be 32 r;
    be_nat_to_be 32 s;
    M.small_mod d order;
    O.point_mul_g_nonzero d;
    O.store_load p;
    let (x, y) = to_aff_point p in
    let q : proj_point = (x, y, fone) in
    let u1 = qmul (qinv s) m in
    let u2 = qmul (qinv s) r in
    verify_point q d u1 u2

(** {2 Sign, then verify} *)

let sig_slices (r s: nat)
  : Lemma (let sg = Seq.append (nat_to_be 32 r) (nat_to_be 32 s) in
           Seq.slice sg 0 32 == nat_to_be 32 r /\ Seq.slice sg 32 64 == nat_to_be 32 s)
  = let sg = Seq.append (nat_to_be 32 r) (nat_to_be 32 s) in
    Seq.Properties.append_slices (nat_to_be 32 r) (nat_to_be 32 s);
    Seq.lemma_eq_elim (Seq.slice sg 0 32) (nat_to_be 32 r);
    Seq.lemma_eq_elim (Seq.slice sg 32 64) (nat_to_be 32 s)

(** The signer's [s] gives back its nonce. *)
let sign_scalars (m: qelem) (d k: qelem)
  : Lemma (requires 0 < k /\
                    (let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
                     qmul (qinv k) (qadd m (qmul r d)) <> 0))
          (ensures (let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
                    let s = qmul (qinv k) (qadd m (qmul r d)) in
                    (qmul (qinv s) m + qmul (qinv s) r * d) % order == k))
  = let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
    let s = qmul (qinv k) (qadd m (qmul r d)) in
    O.order_is_prime ();
    F.mul_inv #order k;
    F.inv_mul #order s;
    GE.recover_nonce #order m r d k (qinv k) (qinv s)

#push-options "--ifuel 1"

(** {b Correctness of ECDSA.}  A signature produced with private key [sk]
    verifies against the public key [dh_initiator sk]. *)
let verify_sign (m: qelem) (sk nonce: Seq.lseq S8.t 32)
  : Lemma (requires Some? (ecdsa_sign_msg_as_qelem m sk nonce))
          (ensures (let sg = Some?.v (ecdsa_sign_msg_as_qelem m sk nonce) in
                    Some? (dh_initiator sk) /\
                    ecdsa_verify_msg_as_qelem m (Some?.v (dh_initiator sk))
                                              (Seq.slice sg 0 32) (Seq.slice sg 32 64)))
  = let d : qelem = be_nat sk in
    let k : qelem = be_nat nonce in
    let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
    let s = qmul (qinv k) (qadd m (qmul r d)) in
    sig_slices r s;
    sign_scalars m d k;
    verify_accepts m d r s

#pop-options

(** {2 Low-S} *)

(** [(n - k) G] and [k G] have the same affine [x]-coordinate. *)
let neg_point_x (k: nat)
  : Lemma (requires 0 < k /\ k < order)
          (ensures fst (to_aff_point (point_mul_g (order - k))) ==
                   fst (to_aff_point (point_mul_g k)))
  = let p = point_mul_g k in
    let sk = SM.smul k g in
    let np = point_negate p in
    O.bounds ();
    g_on_curve ();
    O.g_has_order ();
    M.small_mod k order;
    M.small_mod (order - k) order;
    O.point_mul_g_nonzero k;
    O.point_mul_g_nonzero (order - k);
    SM.smul_ok k g;
    SM.smul_ok (order - k) g;
    point_negate_on_curve p;
    point_add_negate p;
    peq_refl np;
    point_add_congr np np p sk;
    point_add_on_curve np p;
    point_add_on_curve np sk;
    point_at_infinity_on_curve ();
    peq_sym (point_add np p) (point_add np sk);
    peq_trans (point_add np sk) (point_add np p) point_at_infinity;
    GE.smul_neg SM.kg order k g np;
    peq_trans (point_mul_g (order - k)) (SM.smul (order - k) g) np;
    peq_to_aff_point (point_mul_g (order - k)) np

#restart-solver

(** With [n - s] in place of [s], the verifier recovers [n - k]. *)
let low_s_scalars (m: qelem) (d k: qelem)
  : Lemma (requires 0 < k /\
                    (let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
                     qmul (qinv k) (qadd m (qmul r d)) <> 0))
          (ensures (let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
                    let s = qmul (qinv k) (qadd m (qmul r d)) in
                    let s' : qelem = order - s in
                    (qmul (qinv s') m + qmul (qinv s') r * d) % order == order - k))
  = let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
    let s = qmul (qinv k) (qadd m (qmul r d)) in
    let s' : qelem = order - s in
    O.order_is_prime ();
    M.small_mod s' order;
    assert (MA.neg #order s == s');
    F.mul_inv #order k;
    F.inv_mul #order s';
    GE.recover_neg_nonce #order m r d k (qinv k) (qinv s')

let q_half_val (_: unit) : Lemma (2 * q_half + 1 == order) =
  assert_norm (2 * q_half + 1 == order)

#push-options "--ifuel 1"

(** {b Correctness of low-S ECDSA.}  A signature produced by the low-S
    signer is normalized, and the low-S verifier accepts it against the
    public key [dh_initiator sk]. *)
let secp256k1_verify_sign (m: qelem) (sk nonce: Seq.lseq S8.t 32)
  : Lemma (requires Some? (secp256k1_ecdsa_sign_msg_as_qelem m sk nonce))
          (ensures (let sg = Some?.v (secp256k1_ecdsa_sign_msg_as_qelem m sk nonce) in
                    is_signature_normalized sg /\
                    Some? (dh_initiator sk) /\
                    secp256k1_ecdsa_verify_msg_as_qelem m (Some?.v (dh_initiator sk))
                                                        (Seq.slice sg 0 32) (Seq.slice sg 32 64)))
  = let d : qelem = be_nat sk in
    let k : qelem = be_nat nonce in
    let r : qelem = fst (to_aff_point (point_mul_g k)) % order in
    let s = qmul (qinv k) (qadd m (qmul r d)) in
    let s' : qelem = if s > q_half then order - s else s in
    O.bounds ();
    q_half_val ();
    sig_slices r s;
    sig_slices r s';
    be_nat_to_be 32 s;
    be_nat_to_be 32 s';
    if s > q_half then begin
      low_s_scalars m d k;
      neg_point_x k;
      verify_accepts m d r s'
    end else begin
      sign_scalars m d k;
      verify_accepts m d r s
    end

#pop-options

(** {2 The SHA2-256 front ends} *)

let verify_sign_sha256 (msg: Seq.seq S8.t { msg_ok msg }) (sk nonce: Seq.lseq S8.t 32)
  : Lemma (requires Some? (sign_sha256 msg sk nonce))
          (ensures (let sg = Some?.v (sign_sha256 msg sk nonce) in
                    Some? (dh_initiator sk) /\
                    verify_sha256 msg (Some?.v (dh_initiator sk))
                                  (Seq.slice sg 0 32) (Seq.slice sg 32 64)))
  = verify_sign (sha256_as_qelem msg) sk nonce

let secp256k1_verify_sign_sha256 (msg: Seq.seq S8.t { msg_ok msg })
                                 (sk nonce: Seq.lseq S8.t 32)
  : Lemma (requires Some? (secp256k1_sign_sha256 msg sk nonce))
          (ensures (let sg = Some?.v (secp256k1_sign_sha256 msg sk nonce) in
                    is_signature_normalized sg /\
                    Some? (dh_initiator sk) /\
                    secp256k1_verify_sha256 msg (Some?.v (dh_initiator sk))
                                            (Seq.slice sg 0 32) (Seq.slice sg 32 64)))
  = secp256k1_verify_sign (sha256_as_qelem msg) sk nonce

#pop-options
