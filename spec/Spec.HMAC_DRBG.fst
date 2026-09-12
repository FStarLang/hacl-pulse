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
  block_len #t + hash_bytes p + 1 + Seq.length data < pow2 61 /\
  block_len #t + hash_bytes p + 1 + Seq.length data < max_input #t

let byte (c: U8.t) : Seq.lseq S8.t 1 = Seq.create 1 (S8.classify c)

(** [V || c || data], the message each re-keying hashes. *)
let tagged (v: Seq.seq S8.t) (c: U8.t) (data: Seq.seq S8.t)
  : (r: Seq.seq S8.t { Seq.length r == Seq.length v + 1 + Seq.length data })
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

(** [None] means either that the caller must reseed first or that it asked
    for more than [max_output_length] bytes at once. *)
let generate (#t: Type0) {| word t |} (p: params t)
             (st: state (hash_bytes p)) (n: nat)
             (additional: Seq.seq S8.t { data_ok p additional })
  : GTot (option (Seq.lseq S8.t n & state (hash_bytes p)))
  = if st.ctr > reseed_interval || n > max_output_length then None
    else
      let st1 = if Seq.length additional = 0 then st else update p additional st in
      let (out, vl) = gen_bytes p st1.k st1.v n in
      let st2 = update p additional { st1 with v = vl } in
      Some (out, { st2 with ctr = st1.ctr + 1 })

(** {2 Total wrappers, for the implementation}

    A Pulse [ensures] is elaborated with no [requires] in scope, so the
    refinements on [hmac] and on [state] have to be discharged inside a
    definition rather than at its use. *)

(** [hmac] where it is defined, and the empty sequence elsewhere. *)
let hm (#t: Type0) {| word t |} (p: params t) (key: Seq.seq S8.t) (msg: Seq.seq S8.t)
  : GTot (Seq.seq S8.t)
  = if Seq.length key < max_input #t && block_len #t + Seq.length msg < max_input #t
    then hmac p key msg
    else Seq.empty

let hm_def (#t: Type0) {| word t |} (p: params t) (key: Seq.seq S8.t) (msg: Seq.seq S8.t)
  : Lemma (requires Seq.length key < max_input #t /\
                    block_len #t + Seq.length msg < max_input #t)
          (ensures hm p key msg == hmac p key msg /\
                   Seq.length (hm p key msg) == hash_bytes p)
  = ()

(** [update] on a bare pair of sequences. *)
let upd (#t: Type0) {| word t |} (p: params t)
        (vk: Seq.seq S8.t) (vv: Seq.seq S8.t) (data: Seq.seq S8.t)
  : GTot (Seq.seq S8.t & Seq.seq S8.t)
  = if Seq.length vk = hash_bytes p && Seq.length vv = hash_bytes p && data_ok p data
    then let st = update p data ({ k = vk; v = vv; ctr = 0 }) in (st.k, st.v)
    else (Seq.empty, Seq.empty)

let upd_def (#t: Type0) {| word t |} (p: params t)
            (data: Seq.seq S8.t { data_ok p data }) (st: state (hash_bytes p))
  : Lemma (upd p st.k st.v data == ((update p data st).k, (update p data st).v))
  = ()

(** [gen_bytes] on a bare pair of sequences. *)
let gen (#t: Type0) {| word t |} (p: params t)
        (vk: Seq.seq S8.t) (vv: Seq.seq S8.t) (n: nat)
  : GTot (Seq.seq S8.t & Seq.seq S8.t)
  = if Seq.length vk = hash_bytes p && Seq.length vv = hash_bytes p
    then let (o, vl) = gen_bytes p vk vv n in (o, vl)
    else (Seq.empty, Seq.empty)

(** The implementation writes [V] then the tag byte into a scratch buffer. *)
let tagged_prefix (v: Seq.seq S8.t) (c: U8.t) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length b == Seq.length v + 1 /\
                    (forall (k: nat). k < Seq.length v ==> Seq.index b k == Seq.index v k) /\
                    Seq.index b (Seq.length v) == S8.classify c)
          (ensures b == Seq.append v (byte c))
  = assert (Seq.equal b (Seq.append v (byte c)))

(** ... and then hashes that buffer followed by the caller's data. *)
let tagged_split (v: Seq.seq S8.t) (c: U8.t) (data: Seq.seq S8.t)
  : Lemma (Seq.append (Seq.append v (byte c)) data == tagged v c data)
  = Seq.append_assoc v (byte c) data

(** {2 Unfolding [gen_bytes] one block at a time}

    The implementation is a loop, so the recursion has to be turned into a
    step relation on the suffix that is still to be produced. *)

let gen_len (#t: Type0) {| word t |} (p: params t)
            (vk: Seq.seq S8.t) (vv: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length vk == hash_bytes p /\ Seq.length vv == hash_bytes p)
          (ensures Seq.length (fst (gen p vk vv n)) == n /\
                   Seq.length (snd (gen p vk vv n)) == hash_bytes p)
  = ()

(** Nothing left to do. *)
let gen_zero (#t: Type0) {| word t |} (p: params t)
             (vk: Seq.seq S8.t) (vv: Seq.seq S8.t)
  : Lemma (requires Seq.length vk == hash_bytes p /\ Seq.length vv == hash_bytes p)
          (ensures gen p vk vv 0 == (Seq.empty #S8.t, vv))
  = ()

(** The last, possibly partial, block. *)
let gen_last (#t: Type0) {| word t |} (p: params t)
             (vk: Seq.seq S8.t) (vv: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length vk == hash_bytes p /\ Seq.length vv == hash_bytes p /\
                    0 < n /\ n <= hash_bytes p)
          (ensures (let v1 = hm p vk vv in
                    Seq.length v1 == hash_bytes p /\
                    gen p vk vv n == (Seq.slice v1 0 n, v1)))
  = outer_fits #t p

(** A whole block, with more to come. *)
let gen_step (#t: Type0) {| word t |} (p: params t)
             (vk: Seq.seq S8.t) (vv: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length vk == hash_bytes p /\ Seq.length vv == hash_bytes p /\
                    hash_bytes p < n)
          (ensures (let hl = hash_bytes p in
                    let v1 = hm p vk vv in
                    Seq.length v1 == hl /\
                    fst (gen p vk vv n) == Seq.append v1 (fst (gen p vk v1 (n - hl))) /\
                    snd (gen p vk vv n) == snd (gen p vk v1 (n - hl))))
  = outer_fits #t p

(** The implementation takes the data in three pieces -- entropy, nonce and
    personalization string for [instantiate], entropy and additional input
    for [reseed], additional input alone for [generate] -- so that nothing
    ever has to concatenate them into a buffer sized at run time. *)
let dcat (a: Seq.seq S8.t) (b: Seq.seq S8.t) (c: Seq.seq S8.t)
  : (r: Seq.seq S8.t { Seq.length r == Seq.length a + Seq.length b + Seq.length c })
  = Seq.append a (Seq.append b c)

(** {2 The three transitions, on bare sequences} *)

let inst_def (#t: Type0) {| word t |} (p: params t)
             (entropy: Seq.seq S8.t) (nonce: Seq.seq S8.t) (personalization: Seq.seq S8.t)
  : Lemma (requires data_ok p (seed_material entropy nonce personalization))
          (ensures (let st = instantiate p entropy nonce personalization in
                    let (a, b) = upd p (initial p).k (initial p).v
                                     (seed_material entropy nonce personalization) in
                    st.k == a /\ st.v == b /\ st.ctr == 1))
  = ()

let reseed_def (#t: Type0) {| word t |} (p: params t)
               (st: state (hash_bytes p))
               (entropy: Seq.seq S8.t) (additional: Seq.seq S8.t)
  : Lemma (requires data_ok p (Seq.append entropy additional))
          (ensures (let st' = reseed p st entropy additional in
                    let (a, b) = upd p st.k st.v (Seq.append entropy additional) in
                    st'.k == a /\ st'.v == b /\ st'.ctr == 1))
  = ()

(** [generate] on a bare state: the output, the new key, the new value and
    the new counter. *)
let gene (#t: Type0) {| word t |} (p: params t)
         (vk: Seq.seq S8.t) (vv: Seq.seq S8.t) (c: nat)
         (n: nat) (additional: Seq.seq S8.t)
  : GTot (option (Seq.seq S8.t & Seq.seq S8.t & Seq.seq S8.t & nat))
  = if Seq.length vk = hash_bytes p && Seq.length vv = hash_bytes p && data_ok p additional
    then match generate p ({ k = vk; v = vv; ctr = c }) n additional with
         | None -> None
         | Some (o, st) -> Some (o, st.k, st.v, st.ctr)
    else None

(** What the implementation does, step by step: an optional first update,
    the output loop, a second update, and the counter. *)
let gene_def (#t: Type0) {| word t |} (p: params t)
             (vk: Seq.seq S8.t) (vv: Seq.seq S8.t) (c: nat)
             (n: nat) (additional: Seq.seq S8.t)
  : Lemma (requires Seq.length vk == hash_bytes p /\ Seq.length vv == hash_bytes p /\
                    data_ok p additional /\ c <= reseed_interval /\ n <= max_output_length)
          (ensures (let (k1, v1) = if Seq.length additional = 0 then (vk, vv)
                                   else upd p vk vv additional in
                    let (o, vl) = gen p k1 v1 n in
                    let (k2, v2) = upd p k1 vl additional in
                    gene p vk vv c n additional == Some (o, k2, v2, c + 1)))
  = ()
