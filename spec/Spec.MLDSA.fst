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

(** ML-DSA, FIPS 204.

    Three layers, as in the standard.

    - The internal algorithms ([ML-DSA.KeyGen_internal],
      [ML-DSA.Sign_internal], [ML-DSA.Verify_internal]) take every random
      input as an argument and sign the formatted message [M'] directly.
    - Below them sit {!sign_mu} and {!verify_mu}, which start from the
      message representative [mu].  The standard computes [mu] inside the
      internal algorithms; separating it is what lets a caller hash a long
      message elsewhere ("external mu", FIPS 204 section 6.2, footnote).
    - Above them, {!sign} and {!verify} format [M' = 0 || |ctx| || ctx || M]
      for the pure, non-prehashed variant.

    Signing is a rejection loop.  It is specified with the bound
    {!Spec.MLDSA.Params.max_attempts} and returns [None] if every attempt
    is rejected; the discussion at that constant explains why this is
    faithful.  The randomiser [rnd] is an argument: thirty-two zero bytes
    give the deterministic variant. *)
module Spec.MLDSA

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.NTT
open Spec.MLDSA.Rounding
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module SHA3 = Spec.SHA3
module ID = FStar.IndefiniteDescription

#push-options "--fuel 0 --ifuel 0"

(** [H], SHAKE256 at a given output length. *)
let hash (s: Seq.seq S8.t) (len: nat) : GTot (Seq.lseq S8.t len) = SHA3.shake256 s len

let byte (x: nat { x < 256 }) : S8.t = S8.classify (U8.uint_to_t x)

(** {2 Key generation}

    Algorithm 6.  The seed is extended with [k] and [l] before hashing, so
    that one seed gives unrelated keys at different parameter sets. *)

let keygen_seed (p: params) (xi: Seq.lseq S8.t 32) : Seq.seq S8.t
  = Seq.append xi (Seq.init 2 (fun t -> byte (if t = 0 then p.k else p.l)))

(** [t = A s1 + s2], computed in the NTT domain and brought back. *)
let keygen_t (p: params) (a: pmat p.k p.l) (s1: pvec p.l) (s2: pvec p.k) : pvec p.k
  = vec_add (vec_intt (mat_vec_mul a (vec_ntt s1))) s2

let keygen_internal (p: params) (xi: Seq.lseq S8.t 32)
  : GTot (Seq.lseq S8.t (pk_len p) & Seq.lseq S8.t (sk_len p))
  = let h = hash (keygen_seed p xi) 128 in
    let rho : Seq.lseq S8.t 32 = Seq.slice h 0 32 in
    let rho' : Seq.lseq S8.t 64 = Seq.slice h 32 96 in
    let key : Seq.lseq S8.t 32 = Seq.slice h 96 128 in
    let a = expand_a p rho in
    let s1 = expand_s1 p rho' in
    let s2 = expand_s2 p rho' in
    let t = keygen_t p a s1 s2 in
    let pk = pk_encode p rho (vec_power2round_hi t) in
    let tr = hash pk 64 in
    pk, sk_encode p rho key tr s1 s2 (vec_power2round_lo t)

(** {2 Signing}

    Algorithm 7, from [mu].  The private key is decoded once, and its
    vectors are moved into the NTT domain once, before the loop. *)

noeq
type sign_ctx (p: params) = {
  sc_a: pmat p.k p.l;
  sc_s1: pvec p.l;
  sc_s2: pvec p.k;
  sc_t0: pvec p.k;
}

let sign_ctx_of (p: params) (sk: sk_parts p) : GTot (sign_ctx p)
  = { sc_a = expand_a p sk.sk_rho;
      sc_s1 = vec_ntt sk.sk_s1;
      sc_s2 = vec_ntt sk.sk_s2;
      sc_t0 = vec_ntt sk.sk_t0 }

(** The commitment [w = A y] and its high part, the challenge hash
    [c~ = H(mu || w1Encode(w1))]. *)
let commit (p: params) (a: pmat p.k p.l) (y: pvec p.l) : pvec p.k
  = vec_intt (mat_vec_mul a (vec_ntt y))

let challenge_hash (p: params) (mu: Seq.lseq S8.t 64) (w1: Seq.lseq nat (p.k * n))
  : GTot (Seq.lseq S8.t (ct_len p))
  = hash (Seq.append mu (w1_encode p w1)) (ct_len p)

(** One attempt, with mask counter [kappa = a l].  The four rejection
    conditions are, in order: [z] too large, the low part of [w - c s2] too
    large, [c t0] too large, and too many hint bits. *)
let sign_attempt (p: params) (sc: sign_ctx p) (mu: Seq.lseq S8.t 64)
                 (rho'': Seq.lseq S8.t 64) (a: nat { a < max_attempts })
  : GTot (option (Seq.lseq S8.t (sig_len p)))
  = beta_lt p;
    let y = expand_mask p rho'' a in
    let w = commit p sc.sc_a y in
    let ct = challenge_hash p mu (vec_high_bits p w) in
    let c = ntt (sample_in_ball p ct) in
    let cs1 = vec_intt (vec_scale c sc.sc_s1) in
    let cs2 = vec_intt (vec_scale c sc.sc_s2) in
    let z = vec_add y cs1 in
    let r = vec_sub w cs2 in
    if not (all_lt z (gamma1 p - beta p)) then None
    else if not (all_lt (vec_low_bits p r) (gamma2 p - beta p)) then None
    else begin
      let ct0 = vec_intt (vec_scale c sc.sc_t0) in
      let h = vec_make_hint p (vec_map neg ct0) (vec_add r ct0) in
      if not (all_lt ct0 (gamma2 p)) then None
      else if count_true h > p.omega then None
      else Some (sig_encode p ct z h)
    end

let rec sign_loop (p: params) (sc: sign_ctx p) (mu: Seq.lseq S8.t 64)
                  (rho'': Seq.lseq S8.t 64) (a: nat)
  : GTot (option (Seq.lseq S8.t (sig_len p))) (decreases max_attempts - a)
  = if a >= max_attempts then None
    else match sign_attempt p sc mu rho'' a with
      | Some s -> Some s
      | None -> sign_loop p sc mu rho'' (a + 1)

let sign_mu (p: params) (sk: Seq.lseq S8.t (sk_len p)) (mu: Seq.lseq S8.t 64)
            (rnd: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t (sig_len p)))
  = let sp = sk_decode p sk in
    let rho'' = hash (Seq.append sp.sk_key (Seq.append rnd mu)) 64 in
    sign_loop p (sign_ctx_of p sp) mu rho'' 0

(** [mu = H(tr || M')]. *)
let message_rep (tr: Seq.seq S8.t) (m': Seq.seq S8.t) : GTot (Seq.lseq S8.t 64)
  = hash (Seq.append tr m') 64

let sign_internal (p: params) (sk: Seq.lseq S8.t (sk_len p)) (m': Seq.seq S8.t)
                  (rnd: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t (sig_len p)))
  = sign_mu p sk (message_rep (Seq.slice sk 64 128) m') rnd

(** {2 Verification}

    Algorithm 8, from [mu].  [w' = A z - c t1 2^d]; the signature is
    accepted when [z] is short and the challenge recomputes. *)

let t1_shift (#k: pos) (t1: Seq.lseq nat (k * n)) : pvec k
  = Seq.init (k * n) (fun i -> of_int (Seq.index t1 i * pow2 d))

let verify_w (p: params) (a: pmat p.k p.l) (t1: Seq.lseq nat (p.k * n))
             (c: poly) (z: pvec p.l)
  : pvec p.k
  = vec_intt (vec_sub (mat_vec_mul a (vec_ntt z)) (vec_scale (ntt c) (vec_ntt (t1_shift t1))))

let verify_mu (p: params) (pk: Seq.lseq S8.t (pk_len p)) (mu: Seq.lseq S8.t 64)
              (sg: Seq.lseq S8.t (sig_len p))
  : GTot bool
  = let rho, t1 = pk_decode p pk in
    let ct, z, ho = sig_decode p sg in
    match ho with
    | None -> false
    | Some h ->
      beta_lt p;
      all_lt z (gamma1 p - beta p) &&
      (let w' = verify_w p (expand_a p rho) t1 (sample_in_ball p ct) z in
       ID.strong_excluded_middle (ct == challenge_hash p mu (vec_use_hint p h w')))

let verify_internal (p: params) (pk: Seq.lseq S8.t (pk_len p)) (m': Seq.seq S8.t)
                    (sg: Seq.lseq S8.t (sig_len p))
  : GTot bool
  = verify_mu p pk (message_rep (hash pk 64) m') sg

(** {2 The pure variant}

    Algorithms 2 and 3.  [M' = 0 || |ctx| || ctx || M]; the context is at
    most 255 bytes, and a longer one is an error for signing and a
    rejection for verification. *)

let format_msg (msg: Seq.seq S8.t) (ctx: Seq.seq S8.t { Seq.length ctx < 256 }) : Seq.seq S8.t
  = Seq.append (Seq.init 2 (fun t -> byte (if t = 0 then 0 else Seq.length ctx)))
               (Seq.append ctx msg)

let sign (p: params) (sk: Seq.lseq S8.t (sk_len p)) (msg: Seq.seq S8.t) (ctx: Seq.seq S8.t)
         (rnd: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t (sig_len p)))
  = if Seq.length ctx >= 256 then None
    else sign_internal p sk (format_msg msg ctx) rnd

let verify (p: params) (pk: Seq.lseq S8.t (pk_len p)) (msg: Seq.seq S8.t) (ctx: Seq.seq S8.t)
           (sg: Seq.lseq S8.t (sig_len p))
  : GTot bool
  = Seq.length ctx < 256 && verify_internal p pk (format_msg msg ctx) sg

(** The deterministic variant fixes [rnd] to zero. *)
let rnd_zero : Seq.lseq S8.t 32 = Seq.create 32 (byte 0)

#pop-options
