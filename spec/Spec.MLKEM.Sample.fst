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

(** Sampling, FIPS 203 algorithms 7 and 8.

    Two very different samplers.  [SamplePolyCBD] is a fixed-length
    bit-counting function of exactly [64 eta] pseudorandom bytes and needs
    no comment.  [SampleNTT] is rejection sampling from a SHAKE128 stream,
    and rejection sampling does not terminate in any provable sense: the
    standard's loop runs until 256 candidates have been accepted, and
    nothing bounds how long that takes.

    The choice made here is to fix a generous bound -- {!max_triples},
    sixteen SHAKE128 blocks -- and to specify the sampler as a total
    function that falls back to the zero polynomial if the bound is
    exhausted.  Three things make that the right trade:

    - The implementation computes {i exactly} this function, so there is no
      gap between what is proved and what runs.  A specification with an
      unbounded loop would have to be relational ("there exists a prefix
      length such that..."), and that relation would then infect the
      specification of key generation, encapsulation and every wrapper.
    - Sixteen blocks give 1792 candidates, each accepted with probability
      [3329/4096]; 256 are needed.  The shortfall is more than a hundred
      standard deviations away.  No seed that reaches the fallback will
      ever be exhibited.
    - {!sampled_stable} says the accumulator stops moving once it is full,
      so the implementation is free to stop squeezing as soon as it has 256
      coefficients -- which in practice is after three or four blocks --
      while still being equal to the bounded specification.

    That last lemma is the one that makes the bound free: it is paid for
    once here rather than in the loop invariant. *)
module Spec.MLKEM.Sample

open Spec.MLKEM.Zq
open Spec.MLKEM.Encode

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module SHA3 = Spec.SHA3

#push-options "--fuel 1 --ifuel 1"

(** {2 The extendable-output stream}

    [squeeze] reads byte [i] out of block [i / rate] of the Keccak state,
    so a longer squeeze agrees with a shorter one everywhere the shorter
    one is defined.  That is what lets the stream be treated as infinite
    and the implementation produce it a block at a time. *)

let shake128_prefix (msg: Seq.seq S8.t) (l1 l2: nat) (i: nat { i < l1 /\ i < l2 })
  : Lemma (Seq.index (SHA3.shake128 msg l1) i == Seq.index (SHA3.shake128 msg l2) i)
  = SHA3.squeeze_index 168 (SHA3.absorb 168 SHA3.shake_suffix msg) l1 i;
    SHA3.squeeze_index 168 (SHA3.absorb 168 SHA3.shake_suffix msg) l2 i

let xof_byte (seed: Seq.seq S8.t) (i: nat) : GTot S8.t
  = Seq.index (SHA3.shake128 seed (i + 1)) i

let xof_byte_index (seed: Seq.seq S8.t) (l: nat) (i: nat { i < l })
  : Lemma (Seq.index (SHA3.shake128 seed l) i == xof_byte seed i)
          [SMTPat (Seq.index (SHA3.shake128 seed l) i)]
  = shake128_prefix seed l (i + 1) i

(** {2 Uniform sampling}

    Algorithm 7.  Three bytes give two twelve-bit candidates; each is kept
    if it is below [q].  The candidate that would overflow the output is
    dropped rather than wrapping, which is what the standard's [j < 256]
    guard does. *)

let partial = s: Seq.seq zq { Seq.length s <= n }

let sample_step (seed: Seq.seq S8.t) (t: nat) (acc: partial) : GTot partial
  = if Seq.length acc = n then acc
    else begin
      let b0 = S8.v (xof_byte seed (3 * t)) in
      let b1 = S8.v (xof_byte seed (3 * t + 1)) in
      let b2 = S8.v (xof_byte seed (3 * t + 2)) in
      let d1 = b0 + 256 * (b1 % 16) in
      let d2 = b1 / 16 + 16 * b2 in
      let acc: partial = if d1 < q then Seq.snoc acc d1 else acc in
      if Seq.length acc < n && d2 < q then Seq.snoc acc d2 else acc
    end

let sampled (seed: Seq.seq S8.t) (m: nat) : GTot partial
  = Loops.repeati_g m (sample_step seed) Seq.empty

(** Once full, the accumulator is fixed: every later step is the identity.
    This is what lets the implementation stop early. *)
let rec sampled_stable (seed: Seq.seq S8.t) (m1: nat) (m2: nat { m1 <= m2 })
  : Lemma (requires Seq.length (sampled seed m1) == n)
          (ensures sampled seed m2 == sampled seed m1)
          (decreases m2 - m1)
  = if m2 = m1 then ()
    else begin
      sampled_stable seed m1 (m2 - 1);
      Loops.unfold_repeati_g m2 (sample_step seed) Seq.empty
    end

(** Sixteen SHAKE128 blocks.  See the discussion at the head of the file
    for why this is both bounded and faithful. *)
let max_triples : pos = 896

let xof_max : pos = 3 * max_triples

let sample_ntt (seed: Seq.seq S8.t) : GTot poly
  = let s = sampled seed max_triples in
    if Seq.length s = n then s else poly_zero

(** The seed of [A-hat[i][j]] is [rho] followed by the column index and
    then the row index -- in that order, which is the transposition the
    standard bakes into the seed rather than into the multiplication. *)
let matrix_seed (rho: Seq.lseq S8.t 32) (i: nat { i < 256 }) (j: nat { j < 256 })
  : Seq.lseq S8.t 34
  = Seq.append rho (Seq.init 2 (fun t ->
      S8.classify (U8.uint_to_t (if t = 0 then j else i))))

(** {2 Centred binomial sampling}

    Algorithm 8.  [f[i]] is the difference of two sums of [eta] bits, so it
    lies in [-eta, eta]; [eta] is 2 or 3, and the result is taken in [Z_q],
    where the negative half wraps to the top. *)

let rec bit_sum (b: Seq.seq S8.t) (off: nat) (m: nat)
  : GTot (x: nat { x <= m }) (decreases m)
  = if m = 0 then 0 else stream_bit b off + bit_sum b (off + 1) (m - 1)

let sample_cbd (eta: pos { eta <= 3 }) (b: Seq.lseq S8.t (64 * eta)) : GTot poly
  = Seq.init_ghost n (fun i ->
      let x: zq = bit_sum b (2 * i * eta) eta in
      let y: zq = bit_sum b (2 * i * eta + eta) eta in
      sub x y)

(** {2 The pseudorandom function}

    [PRF_eta(s, b) = SHAKE256(s || b, 64 eta)].  The byte is a public
    counter, so it is classified on the way in rather than being secret
    already. *)

let prf (eta: pos { eta <= 3 }) (s: Seq.lseq S8.t 32) (b: U8.t) : GTot (Seq.lseq S8.t (64 * eta))
  = SHA3.shake256 (Seq.snoc s (S8.classify b)) (64 * eta)

(** [SamplePolyCBD] driven by the PRF, which is how every caller uses it. *)
let sample_poly_cbd (eta: pos { eta <= 3 }) (s: Seq.lseq S8.t 32) (b: U8.t) : GTot poly
  = sample_cbd eta (prf eta s b)

#pop-options
