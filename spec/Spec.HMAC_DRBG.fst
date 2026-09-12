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

(** HMAC_DRBG, NIST SP 800-90A section 10.1.2.

    The state is a key [K], a value [V] -- both one digest long -- and a
    reseed counter.  Every transition is the same [update] function:

      [K := HMAC(K, V || 0x00 || data)]
      [V := HMAC(K, V)]
      and, if [data] is non-empty, the same again with [0x01].

    Generating [n] bytes iterates [V := HMAC(K, V)] and concatenates, then
    runs [update] once more so that the state does not reveal the output.

    Unlike HACL*, SHA-1 is not offered: this library does not implement it.
    That leaves SHA2-256, SHA2-384 and SHA2-512, which is the set SP 800-90A
    still approves. *)
module Spec.HMAC_DRBG

open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC

module Seq = FStar.Seq
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

(** {2 The limits}

    SP 800-90A states these as properties of an implementation rather than
    of the mechanism, and HACL* picked the values below; they are repeated
    here so that a caller can rely on the same numbers. *)

let reseed_interval : pos = 1024
let max_output_length : pos = 65536
let max_length : pos = 65536
let max_personalization_string_length : pos = 65536
let max_additional_input_length : pos = 65536

(** The security strength in bytes: SP 800-90A table 2 asks for at least
    [security_strength] bits of entropy, which is 256 bits for every hash
    this library offers. *)
let min_length : pos = 32

(** {2 The state}

    Indexed by the digest length rather than by the algorithm, so that
    nothing here has to mention a [params] record it does not use. *)
noeq type state (hl: nat) = {
  k: Seq.lseq S8.t hl;
  v: Seq.lseq S8.t hl;
  ctr: nat;
}

(** {2 The update function, 10.1.2.2}

    Every [hmac] here is keyed by one digest and hashes at most one digest,
    one byte and the caller's data; this is the bound that makes all of them
    well defined. *)
unfold let data_ok (#t: Type0) {| word t |} (p: params t) (data: Seq.seq S8.t) : prop =
  block_len #t + hash_bytes p + 1 + Seq.length data < max_input #t

let byte (c: U8.t) : Seq.lseq S8.t 1 = Seq.create 1 (S8.classify c)

(** [V || c || data], the message each re-keying hashes. *)
let tagged (#hl: nat) (v: Seq.lseq S8.t hl) (c: U8.t) (data: Seq.seq S8.t)
  : (r: Seq.seq S8.t { Seq.length r == hl + 1 + Seq.length data })
  = Seq.append v (Seq.append (byte c) data)

let update (#t: Type0) {| word t |} (p: params t)
           (data: Seq.seq S8.t { data_ok p data })
           (st: state (hash_bytes p))
  : GTot (state (hash_bytes p))
  = outer_fits #t p;
    let k1 = hmac p st.k (tagged st.v 0x00uy data) in
    let v1 = hmac p k1 st.v in
    if Seq.length data = 0 then { st with k = k1; v = v1 }
    else
      let k2 = hmac p k1 (tagged v1 0x01uy data) in
      let v2 = hmac p k2 v1 in
      { st with k = k2; v = v2 }

(** {2 Instantiation, 10.1.2.3} *)

(** [K] starts all zero and [V] all one; SP 800-90A says so explicitly, and
    the first [update] is what makes them unpredictable. *)
let initial (#t: Type0) {| word t |} (p: params t) : state (hash_bytes p) = {
  k = Seq.create (hash_bytes p) (S8.classify 0x00uy);
  v = Seq.create (hash_bytes p) (S8.classify 0x01uy);
  ctr = 1;
}

let seed_material (entropy nonce personalization: Seq.seq S8.t)
  : (r: Seq.seq S8.t { Seq.length r == Seq.length entropy + Seq.length nonce +
                                      Seq.length personalization })
  = Seq.append entropy (Seq.append nonce personalization)

let instantiate (#t: Type0) {| word t |} (p: params t)
                (entropy nonce: Seq.seq S8.t)
                (personalization: Seq.seq S8.t
                   { data_ok p (seed_material entropy nonce personalization) })
  : GTot (state (hash_bytes p))
  = update p (seed_material entropy nonce personalization) (initial p)

(** {2 Reseeding, 10.1.2.4}

    The counter goes back to one; [update] leaves it alone, so it is set
    here. *)
let reseed (#t: Type0) {| word t |} (p: params t)
           (st: state (hash_bytes p))
           (entropy: Seq.seq S8.t)
           (additional: Seq.seq S8.t { data_ok p (Seq.append entropy additional) })
  : GTot (state (hash_bytes p))
  = let st' = update p (Seq.append entropy additional) st in
    { st' with ctr = 1 }

(** {2 Generation, 10.1.2.5}

    [V := HMAC(K, V)] over and over.  The returned [V] is the last block
    produced even when only part of it was used, which is what SP 800-90A's
    "leftmost" wording means and what every other implementation does. *)
let rec gen_bytes (#t: Type0) {| word t |} (p: params t)
                  (k: Seq.lseq S8.t (hash_bytes p))
                  (v: Seq.lseq S8.t (hash_bytes p))
                  (n: nat)
  : GTot (Seq.lseq S8.t n & Seq.lseq S8.t (hash_bytes p)) (decreases n)
  = outer_fits #t p;
    if n = 0 then (Seq.empty, v)
    else
      let v1 = hmac p k v in
      let hl = hash_bytes p in
      if n <= hl then (Seq.slice v1 0 n, v1)
      else
        let (rest, vl) = gen_bytes p k v1 (n - hl) in
        (Seq.append v1 rest, vl)

(** [None] means the caller must reseed first; that is the only way this
    can refuse. *)
let generate (#t: Type0) {| word t |} (p: params t)
             (st: state (hash_bytes p)) (n: nat)
             (additional: Seq.seq S8.t { data_ok p additional })
  : GTot (option (Seq.lseq S8.t n & state (hash_bytes p)))
  = if st.ctr > reseed_interval then None
    else
      let st1 = if Seq.length additional = 0 then st else update p additional st in
      let (out, vl) = gen_bytes p st1.k st1.v n in
      let st2 = update p additional { st1 with v = vl } in
      Some (out, { st2 with ctr = st1.ctr + 1 })
