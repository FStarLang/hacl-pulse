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

(** Sampling, FIPS 204 algorithms 29 to 34.

    Three of the four samplers are rejection samplers, and they are
    specified the way ML-KEM's [SampleNTT] is (see {!Spec.MLKEM.Sample}):
    as a bounded fold over the extendable-output stream that falls back to
    a fixed value if the bound is exhausted, together with a stability
    lemma that lets the implementation stop as soon as it is done.  The
    bounds are at least those of FIPS 204 appendix C, so a conforming
    implementation that never reaches them computes exactly these
    functions:

    - [RejNTTPoly]: {!max_triples} = 896 three-byte candidates (sixteen
      SHAKE128 blocks; appendix C asks for 894).
    - [RejBoundedPoly]: {!max_bounded} = 1088 bytes (eight SHAKE256
      blocks; appendix C asks for 481).
    - [SampleInBall]: {!max_ball} = 1080 bytes after the eight sign bytes
      (the rest of eight SHAKE256 blocks; appendix C asks for 221).

    The fourth, [ExpandMask], is a fixed-length unpacking and needs no
    bound. *)
module Spec.MLDSA.Sample

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module SHA3 = Spec.SHA3
module KZ = Spec.MLKEM.Zq

#push-options "--fuel 1 --ifuel 1"

(** {2 The extendable-output streams}

    As in ML-KEM: byte [i] of a squeeze does not depend on the squeeze
    length, so each stream can be read as an infinite sequence. *)

let shake128_byte (seed: Seq.seq S8.t) (i: nat) : GTot S8.t
  = Seq.index (SHA3.shake128 seed (i + 1)) i

let shake256_byte (seed: Seq.seq S8.t) (i: nat) : GTot S8.t
  = Seq.index (SHA3.shake256 seed (i + 1)) i

let shake128_byte_index (seed: Seq.seq S8.t) (l: nat) (i: nat { i < l })
  : Lemma (Seq.index (SHA3.shake128 seed l) i == shake128_byte seed i)
  = SHA3.squeeze_index 168 (SHA3.absorb 168 SHA3.shake_suffix seed) l i;
    SHA3.squeeze_index 168 (SHA3.absorb 168 SHA3.shake_suffix seed) (i + 1) i

let shake256_byte_index (seed: Seq.seq S8.t) (l: nat) (i: nat { i < l })
  : Lemma (Seq.index (SHA3.shake256 seed l) i == shake256_byte seed i)
  = SHA3.squeeze_index 136 (SHA3.absorb 136 SHA3.shake_suffix seed) l i;
    SHA3.squeeze_index 136 (SHA3.absorb 136 SHA3.shake_suffix seed) (i + 1) i

(** A partially filled polynomial. *)
let partial = s: Seq.seq zq { Seq.length s <= n }

let push (acc: partial) (x: int) : GTot partial
  = if Seq.length acc < n && 0 <= x && x < q then Seq.snoc acc x else acc

(** {2 Uniform sampling in the NTT domain}

    Algorithm 30.  Three bytes give one 23-bit candidate (the top bit of
    the third byte is dropped), kept if it is below [q]. *)

let ntt_cand (seed: Seq.seq S8.t) (t: nat) : GTot nat
  = S8.v (shake128_byte seed (3 * t)) +
    256 * S8.v (shake128_byte seed (3 * t + 1)) +
    65536 * (S8.v (shake128_byte seed (3 * t + 2)) % 128)

let ntt_step (seed: Seq.seq S8.t) (t: nat) (acc: partial) : GTot partial
  = push acc (ntt_cand seed t)

let ntt_sampled (seed: Seq.seq S8.t) (m: nat) : GTot partial
  = Loops.repeati_g m (ntt_step seed) Seq.empty

let rec ntt_sampled_stable (seed: Seq.seq S8.t) (m1: nat) (m2: nat { m1 <= m2 })
  : Lemma (requires Seq.length (ntt_sampled seed m1) == n)
          (ensures ntt_sampled seed m2 == ntt_sampled seed m1)
          (decreases m2 - m1)
  = if m2 = m1 then ()
    else begin
      ntt_sampled_stable seed m1 (m2 - 1);
      Loops.unfold_repeati_g m2 (ntt_step seed) Seq.empty
    end

let max_triples : pos = 896

let rej_ntt_poly (seed: Seq.seq S8.t) : GTot poly
  = let s = ntt_sampled seed max_triples in
    if Seq.length s = n then s else poly_zero

(** {2 Bounded sampling}

    Algorithm 31 with algorithm 15 ([CoeffFromHalfByte]).  Each byte gives
    two four-bit candidates, low nibble first.  For [eta = 2] the values
    below 15 map to [2 - (z mod 5)]; for [eta = 4] those below 9 map to
    [4 - z]. *)

let coeff_ok (eta: pos) (z: nat) : bool
  = if eta = 2 then z < 15 else z < 9

let coeff_of (eta: pos) (z: nat) : zq
  = if eta = 2 then of_int (2 - z % 5) else of_int (4 - z)

let push_half (eta: pos) (acc: partial) (z: nat) : GTot partial
  = if Seq.length acc < n && coeff_ok eta z then Seq.snoc acc (coeff_of eta z) else acc

let bounded_step (eta: pos) (seed: Seq.seq S8.t) (t: nat) (acc: partial) : GTot partial
  = let b = S8.v (shake256_byte seed t) in
    push_half eta (push_half eta acc (b % 16)) (b / 16)

let bounded_sampled (eta: pos) (seed: Seq.seq S8.t) (m: nat) : GTot partial
  = Loops.repeati_g m (bounded_step eta seed) Seq.empty

let rec bounded_sampled_stable (eta: pos) (seed: Seq.seq S8.t) (m1: nat) (m2: nat { m1 <= m2 })
  : Lemma (requires Seq.length (bounded_sampled eta seed m1) == n)
          (ensures bounded_sampled eta seed m2 == bounded_sampled eta seed m1)
          (decreases m2 - m1)
  = if m2 = m1 then ()
    else begin
      bounded_sampled_stable eta seed m1 (m2 - 1);
      Loops.unfold_repeati_g m2 (bounded_step eta seed) Seq.empty
    end

let max_bounded : pos = 1088

let rej_bounded_poly (eta: pos) (seed: Seq.seq S8.t) : GTot poly
  = let s = bounded_sampled eta seed max_bounded in
    if Seq.length s = n then s else poly_zero

(** {2 The challenge}

    Algorithm 29.  The first eight bytes of the stream are sign bits,
    least significant first.  Then for each [i] from [256 - tau] to [255]
    bytes are read until one, [j], is at most [i]; [c[i]] takes [c[j]] and
    [c[j]] becomes [+-1] according to sign bit [i + tau - 256].  The fold
    runs over stream bytes rather than over [i], so the state carries the
    next [i] to place. *)

noeq
type ball_state = {
  ball_c: poly;
  ball_i: nat;
}

let sign_bit (seed: Seq.seq S8.t) (k: nat { k < 64 }) : GTot bool
  = (S8.v (shake256_byte seed (k / 8)) / pow2 (k % 8)) % 2 = 1

let ball_step (tau: pos { tau <= 60 }) (seed: Seq.seq S8.t) (t: nat) (st: ball_state)
  : GTot ball_state
  = if st.ball_i >= n || st.ball_i < n - tau then st
    else begin
      let i = st.ball_i in
      let j = S8.v (shake256_byte seed (8 + t)) in
      if j <= i then begin
        let c = st.ball_c in
        let c = Seq.upd c i (Seq.index c j) in
        let c = Seq.upd c j (if sign_bit seed (i + tau - n) then q - 1 else 1) in
        { ball_c = c; ball_i = i + 1 }
      end
      else st
    end

let ball_init (tau: pos { tau <= 60 }) : ball_state
  = { ball_c = poly_zero; ball_i = n - tau }

let ball_sampled (tau: pos { tau <= 60 }) (seed: Seq.seq S8.t) (m: nat) : GTot ball_state
  = Loops.repeati_g m (ball_step tau seed) (ball_init tau)

let rec ball_sampled_stable (tau: pos { tau <= 60 }) (seed: Seq.seq S8.t)
                            (m1: nat) (m2: nat { m1 <= m2 })
  : Lemma (requires (ball_sampled tau seed m1).ball_i == n)
          (ensures ball_sampled tau seed m2 == ball_sampled tau seed m1)
          (decreases m2 - m1)
  = if m2 = m1 then ()
    else begin
      ball_sampled_stable tau seed m1 (m2 - 1);
      Loops.unfold_repeati_g m2 (ball_step tau seed) (ball_init tau)
    end

let max_ball : pos = 1080

let sample_in_ball (p: params) (seed: Seq.seq S8.t) : GTot poly
  = let st = ball_sampled p.tau seed max_ball in
    if st.ball_i = n then st.ball_c else poly_zero

(** {2 Seeds}

    Every seed is a fixed prefix followed by one or two index bytes. *)

let u16_le (x: nat { x < pow2 16 }) : Seq.lseq S8.t 2
  = assert_norm (pow2 16 == 65536);
    Seq.init 2 (fun t -> S8.classify (U8.uint_to_t (if t = 0 then x % 256 else x / 256)))

let seed_2 (pre: Seq.seq S8.t) (a: nat { a < 256 }) (b: nat { b < 256 }) : Seq.seq S8.t
  = Seq.append pre (Seq.init 2 (fun t -> S8.classify (U8.uint_to_t (if t = 0 then a else b))))

let seed_16 (pre: Seq.seq S8.t) (x: nat { x < pow2 16 }) : Seq.seq S8.t
  = Seq.append pre (u16_le x)

(** {2 Expansion}

    Algorithm 32.  Entry [(r, s)] of [A-hat] is seeded with [rho], then
    the column [s], then the row [r]. *)
let expand_a (p: params) (rho: Seq.lseq S8.t 32) : GTot (pmat p.k p.l)
  = KZ.flat_of_fun_g (p.k * p.l) n (fun t ->
      KZ.div_lt t p.k p.l;
      rej_ntt_poly (seed_2 rho (t % p.l) (t / p.l)))

(** Algorithm 33. *)
let expand_s1 (p: params) (rho': Seq.lseq S8.t 64) : GTot (pvec p.l)
  = assert_norm (pow2 16 == 65536);
    vec_of_fun_g p.l (fun r -> rej_bounded_poly p.eta (seed_16 rho' r))

let expand_s2 (p: params) (rho': Seq.lseq S8.t 64) : GTot (pvec p.k)
  = assert_norm (pow2 16 == 65536);
    vec_of_fun_g p.k (fun r -> rej_bounded_poly p.eta (seed_16 rho' (r + p.l)))

(** Algorithm 34.  [kappa] is a multiple of [l] bounded by
    {!kappa_bound}. *)
let mask_bound (p: params) : Lemma (gamma1 p < q /\ z_bits p <= 20)
  = Math.pow2_lt_compat 20 p.gamma1_bits;
    assert_norm (pow2 20 < q)

let expand_mask_poly (p: params) (rho'': Seq.lseq S8.t 64) (x: nat { x < pow2 16 }) : GTot poly
  = mask_bound p;
    bit_unpack (gamma1 p) (z_bits p) (SHA3.shake256 (seed_16 rho'' x) (32 * z_bits p))

let expand_mask (p: params) (rho'': Seq.lseq S8.t 64) (a: nat { a < max_attempts })
  : GTot (pvec p.l)
  = vec_of_fun_g p.l (fun r ->
      kappa_bound p a r;
      expand_mask_poly p rho'' (a * p.l + r))

#pop-options
