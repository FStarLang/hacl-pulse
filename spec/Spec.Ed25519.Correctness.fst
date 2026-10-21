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

(** Ed25519 signatures verify.

    {!sign_expanded_verify}: for any scalar bytes [s], prefix and message,
    the signature [sign_expanded pub s prefix msg] under the public key
    [pub = point_compress (point_mul_g s)] passes [verify pub msg].
    {!sign_verify} specialises it to [sign] and [secret_to_public], and
    {!sign_verify_expanded_keys} restates it over the slices of
    [expand_keys], the form the implementation's API takes.

    {2 The argument}

    Write [a = le_nat s], [r] the nonce, [R = [r]B], [k] the challenge and
    [S = (r + k (a mod q)) mod q].  The verifier

    - splits the signature back into [compress R] and the bytes of [S];
    - decompresses the public key and [R] to points equivalent to [[a]B]
      and [R] ({!Spec.Ed25519.Compress.decompress_compress});
    - reads [S] back exactly, so [S < q] passes and the challenge it
      recomputes is the signer's [k];
    - checks [[S]B = R + [k]A] up to projective equivalence.

    That check is the group arithmetic of {!algebra}: [[S]B] is
    [[r + k (a mod q)]B] because [[q]B = O]
    ({!Spec.Ed25519.Order.smul_mod_q}), and [[k]([a]B) = [k a]B =
    [k (a mod q)]B] by {!Spec.Ed25519.Order.smul_mul} and the same
    reduction, so both sides are [[r]B + [k (a mod q)]B]. *)
module Spec.Ed25519.Correctness

module G = Spec.Group.Smul
module SM = Spec.Ed25519.Smul
module O = Spec.Ed25519.Order
module CP = Spec.Ed25519.Compress
module B = Hacl.Spec.Bytes
module M = FStar.Math.Lemmas
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Bytes} *)

let split_sig (rr sb: Seq.lseq S8.t 32)
  : Lemma (Seq.slice (Seq.append rr sb) 0 32 == rr /\
           Seq.slice (Seq.append rr sb) 32 64 == sb)
  = Seq.append_slices rr sb

let scalar_bytes_le (n: nat { n < q })
  : Lemma (B.le_nat (scalar_bytes n) == n)
  = q_lt_prime ();
    assert_norm (prime < pow2 (8 * 32));
    B.le_nat_to_le 32 n

(** {2 Multiples of the base point} *)

(** [[n]B], with the scalar given as its encoding. *)
let point_mul_g_smul (n: nat { n < q })
  : Lemma (on_curve (point_mul_g (scalar_bytes n)) /\
           point_equal (point_mul_g (scalar_bytes n)) (SM.smul n g))
  = g_on_curve ();
    SM.point_mul_is_smul (scalar_bytes n) g;
    scalar_bytes_le n

let smul_g_ok (n: nat) : Lemma (on_curve (SM.smul n g))
  = g_on_curve (); SM.smul_ok n g

(** [[k]([a]B) = [k (a mod q)]B]. *)
let smul_smul_g (k a: nat)
  : Lemma (point_equal (SM.smul k (SM.smul a g)) (SM.smul (k * (a % q)) g))
  = g_on_curve ();
    smul_g_ok a;
    smul_g_ok (k * a);
    smul_g_ok ((k * a) % q);
    smul_g_ok (k * (a % q));
    SM.smul_ok k (SM.smul a g);
    O.smul_mul SM.eg k a g;
    O.smul_mod_q (k * a);
    M.lemma_mod_mul_distr_r k a q;
    O.smul_mod_q (k * (a % q));
    point_equal_sym (SM.smul (k * (a % q)) g) (SM.smul ((k * a) % q) g);
    point_equal_trans (SM.smul k (SM.smul a g)) (SM.smul (k * a) g)
                      (SM.smul ((k * a) % q) g);
    point_equal_trans (SM.smul k (SM.smul a g)) (SM.smul ((k * a) % q) g)
                      (SM.smul (k * (a % q)) g)

(** The verification equation, for any [R] and [A] equivalent to [[r]B]
    and [[a]B]. *)
let algebra (r: nat { r < q }) (k: nat { k < q }) (a: nat) (rp aa: ext_point)
  : Lemma (requires on_curve rp /\ on_curve aa /\
                    point_equal rp (SM.smul r g) /\ point_equal aa (SM.smul a g))
          (ensures point_equal (point_mul_g (scalar_bytes ((r + k * (a % q)) % q)))
                               (point_add rp (point_mul (scalar_bytes k) aa)))
  = let n = r + k * (a % q) in
    let sb = point_mul_g (scalar_bytes (n % q)) in
    let ka = point_mul (scalar_bytes k) aa in
    let x = SM.smul n g in
    g_on_curve ();
    smul_g_ok a;
    smul_g_ok r;
    smul_g_ok n;
    smul_g_ok (n % q);
    smul_g_ok (k * (a % q));
    (* [[S]B ~ [n]B] *)
    point_mul_g_smul (n % q);
    O.smul_mod_q n;
    point_equal_sym x (SM.smul (n % q) g);
    point_equal_trans sb (SM.smul (n % q) g) x;
    (* [[k]A ~ [k (a mod q)]B] *)
    SM.point_mul_is_smul (scalar_bytes k) aa;
    scalar_bytes_le k;
    SM.smul_ok k aa;
    SM.smul_ok k (SM.smul a g);
    SM.smul_congr k aa (SM.smul a g);
    smul_smul_g k a;
    point_equal_trans ka (SM.smul k aa) (SM.smul k (SM.smul a g));
    point_equal_trans ka (SM.smul k (SM.smul a g)) (SM.smul (k * (a % q)) g);
    (* [R + [k]A ~ [n]B] *)
    SM.smul_add_congr r (k * (a % q)) g rp ka;
    point_equal_sym (point_add rp ka) x;
    point_equal_trans sb x (point_add rp ka)

(** {2 Sign, then verify} *)

let sign_expanded_verify (s prefix: Seq.lseq S8.t 32)
                         (msg: Seq.seq S8.t { msg_ok msg })
  : Lemma (let pub = point_compress (point_mul_g s) in
           verify pub msg (sign_expanded pub s prefix msg) == true)
  = let aa = point_mul_g s in
    let pub = point_compress aa in
    let a = B.le_nat s in
    let r = sig_r prefix msg in
    let rpt = point_mul_g (scalar_bytes r) in
    let rr = point_compress rpt in
    let k = sig_k rr pub msg in
    q_lt_prime ();
    let ss = (r + k * (a % q)) % q in
    g_on_curve ();
    SM.point_mul_is_smul s g;
    point_mul_g_smul r;
    split_sig rr (scalar_bytes ss);
    scalar_bytes_le ss;
    CP.decompress_compress aa;
    CP.decompress_compress rpt;
    smul_g_ok a;
    smul_g_ok r;
    let Some aa' = point_decompress pub in
    let Some rp = point_decompress rr in
    point_equal_trans aa' aa (SM.smul a g);
    point_equal_trans rp rpt (SM.smul r g);
    algebra r k a rp aa'

let sign_verify (secret: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { msg_ok msg })
  : Lemma (verify (secret_to_public secret) msg (sign secret msg) == true)
  = sign_expanded_verify (expand_low secret) (expand_prefix secret) msg

(** The same, with the key material read out of [expand_keys]. *)
let sign_verify_expanded_keys (secret: Seq.lseq S8.t 32)
                              (msg: Seq.seq S8.t { msg_ok msg })
  : Lemma (let ks = expand_keys secret in
           let pub : Seq.lseq S8.t 32 = Seq.slice ks 0 32 in
           let s : Seq.lseq S8.t 32 = Seq.slice ks 32 64 in
           let prefix : Seq.lseq S8.t 32 = Seq.slice ks 64 96 in
           verify pub msg (sign_expanded pub s prefix msg) == true)
  = let ks = expand_keys secret in
    let tl = Seq.append (expand_low secret) (expand_prefix secret) in
    Seq.append_slices (secret_to_public secret) tl;
    Seq.append_slices (expand_low secret) (expand_prefix secret);
    Seq.lemma_eq_intro (Seq.slice ks 32 64) (expand_low secret);
    Seq.lemma_eq_intro (Seq.slice ks 64 96) (expand_prefix secret);
    sign_verify secret msg

#pop-options
