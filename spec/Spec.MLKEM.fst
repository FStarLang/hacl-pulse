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

(** ML-KEM, FIPS 203.

    Two layers.  K-PKE is a passively secure public-key encryption scheme
    for 32-byte messages; ML-KEM is the Fujisaki-Okamoto transform of it
    into a key-encapsulation mechanism.  The standard keeps the layers
    apart and warns that K-PKE must not be used on its own; this module
    keeps them apart too, and nothing below [kpke_decrypt] is exported to
    C.

    Randomness is an argument everywhere, as it is in the standard's
    "internal" algorithms.  The derandomised form is the only one that can
    be tested against the known-answer vectors, and it is the only one a
    caller with its own entropy source can use. *)
module Spec.MLKEM

open Spec.MLKEM.Zq
open Spec.MLKEM.Params
open Spec.MLKEM.NTT
open Spec.MLKEM.Encode
open Spec.MLKEM.Sample

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module SHA3 = Spec.SHA3

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

(** {2 The hash functions}

    FIPS 203 names four.  They are all SHA-3 or SHAKE, which is the reason
    ML-KEM needs no other primitive: one Keccak permutation covers hashing,
    the pseudorandom function, the extendable output and the
    implicit-rejection key. *)

let hash_g (s: Seq.seq S8.t) : GTot (Seq.lseq S8.t 64) = SHA3.sha3_512 s
let hash_h (s: Seq.seq S8.t) : GTot (Seq.lseq S8.t 32) = SHA3.sha3_256 s
let hash_j (s: Seq.seq S8.t) : GTot (Seq.lseq S8.t 32) = SHA3.shake256 s 32

(** {2 The public matrix}

    [A-hat[i][j] = SampleNTT(rho || j || i)].  The transposition
    encapsulation needs is in the seed, not in the multiplication, so the
    two directions differ only in which index goes first and neither ever
    materialises a transpose. *)

let gen_matrix (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (transposed: bool) : GTot (pmat k)
  = flat_of_fun_g (k * k) n (fun c ->
      div_lt c k k;
      let i = c / k in
      let j = c % k in
      if transposed then sample_ntt (matrix_seed rho j i)
      else sample_ntt (matrix_seed rho i j))

(** {2 Noise}

    [k] consecutive PRF calls with a running counter.  The counter is a
    public byte and never exceeds [2k + 1 <= 9]. *)

let noise_vec (k: pos { k <= 4 }) (eta: pos { eta <= 3 }) (s: Seq.lseq S8.t 32) (start: nat { start + k <= 256 })
  : GTot (pvec k)
  = vec_of_fun_g k (fun i -> sample_poly_cbd eta s (U8.uint_to_t (start + i)))

(** {2 K-PKE} *)

(** Algorithm 13.  [d] is the 32-byte seed; the standard appends the
    module rank to it so that the same seed under two parameter sets gives
    unrelated keys. *)
let kpke_keygen (p: params) (d: Seq.lseq S8.t 32)
  : GTot (Seq.lseq S8.t (ek_len p) & Seq.lseq S8.t (dk_pke_len p))
  = let g = hash_g (Seq.snoc d (S8.classify (U8.uint_to_t p.k))) in
    let rho = Seq.slice g 0 32 in
    let sigma = Seq.slice g 32 64 in
    let a = gen_matrix p.k rho false in
    let s = vec_ntt (noise_vec p.k p.eta1 sigma 0) in
    let e = vec_ntt (noise_vec p.k p.eta1 sigma p.k) in
    let t = vec_add (mat_vec_mul a s) e in
    Seq.append (vec_encode_12 t) rho, vec_encode_12 s

(** Algorithm 14.  [r] is the 32-byte encryption randomness; in ML-KEM it
    is derived from the message, which is what makes the transform work. *)
let kpke_encrypt (p: params) (ek: Seq.lseq S8.t (ek_len p))
                 (m: Seq.lseq S8.t 32) (r: Seq.lseq S8.t 32)
  : GTot (Seq.lseq S8.t (ct_len p))
  = let t = vec_decode 12 p.k (Seq.slice ek 0 (p.k * (32 * 12))) in
    let rho = Seq.slice ek (p.k * (32 * 12)) (ek_len p) in
    let at = gen_matrix p.k rho true in
    let y = vec_ntt (noise_vec p.k p.eta1 r 0) in
    let e1 = noise_vec p.k p.eta2 r p.k in
    let e2 = sample_poly_cbd p.eta2 r (U8.uint_to_t (2 * p.k)) in
    let mu = poly_decompress 1 (widen (byte_decode 1 m)) in
    let u = vec_add (vec_intt (mat_vec_mul at y)) e1 in
    let v = poly_add (poly_add (intt (dot t y)) e2) mu in
    Seq.append (vec_encode p.du p.k (vec_compress p.du u))
               (byte_encode p.dv (poly_compress p.dv v))

(** Algorithm 15.  The subtraction is where the noise has to fit: [w] is
    [mu] plus everything the two rounds of compression and the three noise
    terms contributed, and [Compress_1] recovers [mu] exactly when that sum
    stays inside a quarter turn.  The parameter sets are chosen so that it
    does, except with probability below [2^-138]. *)
let kpke_decrypt (p: params) (dk: Seq.lseq S8.t (dk_pke_len p)) (c: Seq.lseq S8.t (ct_len p))
  : GTot (Seq.lseq S8.t 32)
  = let c1 = Seq.slice c 0 (p.k * (32 * p.du)) in
    let c2 = Seq.slice c (p.k * (32 * p.du)) (ct_len p) in
    let u = vec_decompress p.du p.k (widen (vec_decode p.du p.k c1)) in
    let v = poly_decompress p.dv (widen (byte_decode p.dv c2)) in
    let s = vec_decode 12 p.k dk in
    let w = poly_sub v (intt (dot s (vec_ntt u))) in
    byte_encode 1 (poly_compress 1 w)

(** {2 ML-KEM} *)

(** Algorithm 16.  The decapsulation key carries the encapsulation key and
    its hash as well as the K-PKE decryption key, so that decapsulation can
    re-encrypt without being handed the public key separately, and [z] for
    implicit rejection. *)
let keygen (p: params) (d: Seq.lseq S8.t 32) (z: Seq.lseq S8.t 32)
  : GTot (Seq.lseq S8.t (ek_len p) & Seq.lseq S8.t (dk_len p))
  = let ek, dk_pke = kpke_keygen p d in
    ek, Seq.append dk_pke (Seq.append ek (Seq.append (hash_h ek) z))

(** Algorithm 17.  [m] is the 32-byte message; the shared secret and the
    encryption randomness are the two halves of [G(m || H(ek))], so the
    ciphertext is a deterministic function of the message and the key. *)
let encaps (p: params) (ek: Seq.lseq S8.t (ek_len p)) (m: Seq.lseq S8.t 32)
  : GTot (Seq.lseq S8.t 32 & Seq.lseq S8.t (ct_len p))
  = let g = hash_g (Seq.append m (hash_h ek)) in
    Seq.slice g 0 32, kpke_encrypt p ek m (Seq.slice g 32 64)

(** Algorithm 18.  Decapsulation always returns a key: on a malformed
    ciphertext it returns [J(z || c)], which is indistinguishable from a
    real one to anyone without [z].  That is implicit rejection, the same
    idiom Frodo uses, and the implementation must select between the two
    without branching. *)
let decaps (p: params) (dk: Seq.lseq S8.t (dk_len p)) (c: Seq.lseq S8.t (ct_len p))
  : GTot (Seq.lseq S8.t 32)
  = let dk_pke = Seq.slice dk 0 (dk_pke_len p) in
    let ek = Seq.slice dk (dk_pke_len p) (dk_pke_len p + ek_len p) in
    let h = Seq.slice dk (dk_pke_len p + ek_len p) (dk_pke_len p + ek_len p + 32) in
    let z = Seq.slice dk (dk_pke_len p + ek_len p + 32) (dk_len p) in
    let m = kpke_decrypt p dk_pke c in
    let g = hash_g (Seq.append m h) in
    let c' = kpke_encrypt p ek m (Seq.slice g 32 64) in
    if Seq.equal c c' then Seq.slice g 0 32 else hash_j (Seq.append z c)

(** {2 Input checking}

    FIPS 203 section 7 puts two checks outside the algorithms, on the
    grounds that they are the caller's business: the checks are about where
    a key came from, not about what encapsulation does with it.  Both are
    cheap and both are about malformed input rather than about an attack on
    the mathematics, so neither has to run in constant time -- a key that
    fails either one is a key the caller was never going to use.

    The {e modulus check} of section 7.2: an encapsulation key is 384k
    bytes of twelve-bit coefficients and thirty-two bytes of seed, and
    twelve bits hold values up to 4095 while a coefficient is less than
    q = 3329.  [ByteDecode_12] reduces, so a key whose coefficients are out
    of range decodes to something that re-encodes differently.  Round-tripping
    is therefore exactly the check, and saying it that way -- rather than
    "every coefficient is less than q" -- is both shorter and closer to
    what the standard writes. *)
let ek_valid (p: params) (ek: Seq.lseq S8.t (ek_len p)) : GTot prop
  = let b = Seq.slice ek 0 (p.k * (32 * 12)) in
    Seq.equal (vec_encode_12 (vec_decode 12 p.k b)) b

(** The {e hash check} of section 7.3: a decapsulation key carries the
    encapsulation key it belongs to and that key's hash, and decapsulation
    trusts both.  A key whose stored hash does not match the stored
    encapsulation key is not a key this implementation produced. *)
let dk_valid (p: params) (dk: Seq.lseq S8.t (dk_len p)) : GTot prop
  = let ek = Seq.slice dk (dk_pke_len p) (dk_pke_len p + ek_len p) in
    let h = Seq.slice dk (dk_pke_len p + ek_len p) (dk_pke_len p + ek_len p + 32) in
    Seq.equal (hash_h ek) h

#pop-options
