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

(** RSA-PSS, PKCS #1 v2.2 (RFC 8017), sections 9.1 and 8.1.

    Two independent halves.  {b MGF1} is the mask generation function: the
    first [maskLen] bytes of

      Hash(seed | 0) | Hash(seed | 1) | Hash(seed | 2) | ...

    where the counter is four big-endian bytes.  It is exactly HKDF's expand
    with the chaining removed, and it is specified the same way -- as the
    concatenation of all the blocks, sliced -- so that an implementation which
    writes one block at a time can state its invariant pointwise.

    {b EMSA-PSS} is the encoding.  Signing hashes the message, hashes that
    digest together with eight zero bytes and a random salt, and hides the
    salt under a mask derived from the second digest; verifying recovers the
    salt and recomputes the second digest.  The two are specified separately
    rather than as encode-and-compare, because verification has to accept
    things an encoder would never produce -- that is the whole content of the
    format checks. *)
module Spec.RSAPSS

open Hacl.Secret.Word
open Spec.SHA2
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 1 --ifuel 0"

(** {2 MGF1}

    The seed is always a digest, so the length side conditions are never
    interesting; they are stated anyway because [hash] demands them. *)

(** A seed the counter can be appended to without overflowing the hash. *)
unfold let seed_ok (#t: Type0) {| word t |} (seed: Seq.seq S8.t) =
  Seq.length seed + 4 < max_input #t

(** The same, as a type: an [ensures] is checked without the [requires] in
    scope, so anything mentioning [mgf] has to carry the bound on its binder. *)
let seed_t (t: Type0) {| word t |} = s: Seq.seq S8.t { seed_ok #t s }

(** The counter, four big-endian bytes. *)
let counter (i: nat) : Seq.lseq S8.t 4 = nat_to_be 4 i

(** Block [i] of the mask. *)
let mgf_block (#t: Type0) {| word t |} (p: params t)
              (seed: Seq.seq S8.t { seed_ok #t seed }) (i: nat)
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = Seq.lemma_len_append seed (counter i);
    hash p (Seq.append seed (counter i))

(** Blocks [0 .. n).  The counter is bounded by [pow2 32] only because that
    is where [nat_to_be 4] stops being injective; no caller comes near it. *)
let rec mgf_all (#t: Type0) {| word t |} (p: params t)
                (seed: Seq.seq S8.t { seed_ok #t seed }) (n: nat)
  : GTot (r: Seq.seq S8.t { Seq.length r == n * (hash_bytes p) }) (decreases n)
  = if n = 0
    then Seq.empty
    else begin
      Math.distributivity_add_left (n - 1) 1 (hash_bytes p);
      Seq.append (mgf_all p seed (n - 1)) (mgf_block p seed (n - 1))
    end

(** The two facts about rounding a division up.  They are stated over plain
    naturals, with no [params] in sight, because the implementation's loop
    computes its block count as a machine value and every occurrence of
    [nblocks] in a Pulse query costs more than the whole loop. *)
let div_ceil_ok (m: nat) (hb: pos) : Lemma (m <= ((m + hb - 1) / hb) * hb)
  = Math.euclidean_division_definition (m + hb - 1) hb;
    Math.lemma_mod_lt (m + hb - 1) hb

let div_ceil_le (m: nat) (hb: pos) : Lemma ((m + hb - 1) / hb <= m)
  = Math.lemma_mult_le_left m 1 hb;
    Math.lemma_div_le (m + hb - 1) (m * hb + hb - 1) hb;
    Math.division_addition_lemma (hb - 1) hb m;
    Math.small_div (hb - 1) hb

(** How many blocks [maskLen] bytes take, and the fact that they suffice. *)
let nblocks (#t: Type0) {| word t |} (p: params t) (maskLen: nat)
  : n: nat { maskLen <= n * (hash_bytes p) } =
  let hb = hash_bytes p in
  div_ceil_ok maskLen hb;
  (maskLen + hb - 1) / hb

(** There is never more than one block per byte of output, which is what
    bounds the counter. *)
let nblocks_le (#t: Type0) {| word t |} (p: params t) (maskLen: nat)
  : Lemma (nblocks p maskLen <= maskLen)
  = div_ceil_le maskLen (hash_bytes p)

(** MGF1 proper. *)
let mgf (#t: Type0) {| word t |} (p: params t)
        (seed: Seq.seq S8.t { seed_ok #t seed }) (maskLen: nat)
  : GTot (Seq.lseq S8.t maskLen)
  = Seq.slice (mgf_all p seed (nblocks p maskLen)) 0 maskLen

(** {2 Lemmas for the implementation}

    The implementation writes one block at a time into the output and never
    materializes [mgf_all]; as in HKDF, these two facts are what let its loop
    invariant be stated pointwise. *)

(** [a * c < b * c] cancels. *)
let mult_lt_cancel (a b c: nat)
  : Lemma (requires 0 < c /\ a * c < b * c) (ensures a < b)
  = if a >= b then Math.lemma_mult_le_right c b a

let mgf_all_index_prev (#t: Type0) {| word t |} (p: params t)
                       (seed: Seq.seq S8.t { seed_ok #t seed }) (n: nat { 0 < n })
  : Lemma (forall (k: nat). k < (n - 1) * (hash_bytes p) ==>
             Seq.index (mgf_all p seed n) k == Seq.index (mgf_all p seed (n - 1)) k)
  = let prev = mgf_all p seed (n - 1) in
    let last = mgf_block p seed (n - 1) in
    let aux (k: nat { k < (n - 1) * (hash_bytes p) })
      : Lemma (Seq.index (mgf_all p seed n) k == Seq.index prev k)
      = Seq.lemma_index_app1 prev last k
    in
    FStar.Classical.forall_intro aux

let mgf_all_index_last (#t: Type0) {| word t |} (p: params t)
                       (seed: Seq.seq S8.t { seed_ok #t seed }) (n: nat { 0 < n })
  : Lemma (forall (k: nat). k < (hash_bytes p) ==>
             Seq.index (mgf_all p seed n) ((n - 1) * (hash_bytes p) + k) ==
             Seq.index (mgf_block p seed (n - 1)) k)
  = let prev = mgf_all p seed (n - 1) in
    let last = mgf_block p seed (n - 1) in
    let aux (k: nat { k < (hash_bytes p) })
      : Lemma (Seq.index (mgf_all p seed n) ((n - 1) * (hash_bytes p) + k) ==
               Seq.index last k)
      = Seq.lemma_index_app2 prev last ((n - 1) * (hash_bytes p) + k)
    in
    FStar.Classical.forall_intro aux

(** [mgf_all] is monotone: the first [m] blocks of [n] are the [m] blocks of
    [m], so a loop that has written [m] blocks is already correct about them
    whatever [n] turns out to be. *)
let rec mgf_all_index_le (#t: Type0) {| word t |} (p: params t)
                         (seed: Seq.seq S8.t { seed_ok #t seed }) (m: nat) (n: nat { m <= n })
  : Lemma (ensures forall (k: nat). k < m * (hash_bytes p) ==>
             Seq.index (mgf_all p seed n) k == Seq.index (mgf_all p seed m) k)
          (decreases n - m)
  = if m = n
    then ()
    else begin
      Math.lemma_mult_le_right (hash_bytes p) m (n - 1);
      mgf_all_index_prev p seed n;
      mgf_all_index_le p seed m (n - 1)
    end

(** The mask, pointwise against the blocks: what the implementation proves. *)
let mgf_index (#t: Type0) {| word t |} (p: params t)
              (seed: Seq.seq S8.t { seed_ok #t seed }) (maskLen: nat) (n: nat)
  : Lemma (requires maskLen <= n * (hash_bytes p))
          (ensures forall (k: nat). k < maskLen ==>
             Seq.index (mgf p seed maskLen) k == Seq.index (mgf_all p seed n) k)
  = let nb = nblocks p maskLen in
    let all = mgf_all p seed nb in
    let aux (k: nat { k < maskLen })
      : Lemma (Seq.index (mgf p seed maskLen) k == Seq.index (mgf_all p seed n) k)
      = Seq.lemma_index_slice all 0 maskLen k;
        if nb <= n
        then mgf_all_index_le p seed nb n
        else mgf_all_index_le p seed n nb
    in
    FStar.Classical.forall_intro aux

(** One round of the implementation's loop, entirely as sequence reasoning.

    The loop has written [vc] blocks, hashes block [vc] into [dg], and copies
    as much of it as fits; this says the result still agrees with
    [mgf_all p seed n] everywhere it has been written.  It lives here, and not
    as a pile of assertions in the Pulse function, because a goal with this
    many quantifiers is hopeless in a context that also carries six arrays. *)
let mgf_round_index (#t: Type0) {| word t |} (p: params t) (seed: seed_t t)
                    (maskLen: nat) (n: nat { maskLen <= n * (hash_bytes p) })
                    (vc: nat { vc + 1 <= n })
                    (old: Seq.lseq S8.t maskLen) (fresh: Seq.lseq S8.t maskLen)
                    (dg: Seq.lseq S8.t (hash_bytes p))
  : Lemma (requires
      dg == mgf_block p seed vc /\
      (forall (k: nat). k < maskLen /\ k < vc * (hash_bytes p) ==>
         Seq.index old k == Seq.index (mgf_all p seed n) k) /\
      (forall (k: nat). k < maskLen /\ k < vc * (hash_bytes p) ==>
         Seq.index fresh k == Seq.index old k) /\
      (forall (j: nat). j < (hash_bytes p) /\ vc * (hash_bytes p) + j < maskLen ==>
         Seq.index fresh (vc * (hash_bytes p) + j) == Seq.index dg j))
    (ensures forall (k: nat). k < maskLen /\ k < (vc + 1) * (hash_bytes p) ==>
       Seq.index fresh k == Seq.index (mgf_all p seed n) k)
  = let hb = hash_bytes p in
    Math.distributivity_add_left vc 1 hb;
    mgf_all_index_last p seed (vc + 1);
    mgf_all_index_le p seed (vc + 1) n;
    let aux (k: nat { k < maskLen /\ k < (vc + 1) * hb })
      : Lemma (Seq.index fresh k == Seq.index (mgf_all p seed n) k)
      = if k < vc * hb
        then ()
        else begin
          Math.lemma_mult_le_right hb (vc + 1) n;
          let j : nat = k - vc * hb in
          assert (j < hb);
          assert (Seq.index fresh (vc * hb + j) == Seq.index dg j);
          assert (Seq.index (mgf_all p seed (vc + 1)) ((vc + 1 - 1) * hb + j) ==
                  Seq.index (mgf_block p seed (vc + 1 - 1)) j);
          assert (vc * hb + j == k)
        end
    in
    FStar.Classical.forall_intro aux

#pop-options
