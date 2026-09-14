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

(** Refinement subtyping does not fire through [erased], so a call site that
    has to produce a refined sequence goes through one of these. *)
let as_mp_salt (#t: Type0) {| word t |} (p: params t) (s: Seq.seq S8.t)
  : Pure (s: Seq.seq S8.t { 8 + (hash_bytes p) + Seq.length s < max_input #t })
         (requires 8 + (hash_bytes p) + Seq.length s < max_input #t)
         (ensures fun r -> r == s)
  = s

let as_seed (#t: Type0) {| word t |} (s: Seq.seq S8.t)
  : Pure (seed_t t) (requires seed_ok #t s) (ensures fun r -> r == s)
  = s

let as_lseq (n: nat) (s: Seq.seq S8.t)
  : Pure (Seq.lseq S8.t n) (requires Seq.length s == n) (ensures fun r -> r == s)
  = s

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


(** {2 EMSA-PSS, RFC 8017 section 9.1}

    The encoded message is [emLen = ceil(emBits/8)] bytes laid out as

      maskedDB (emLen - hLen - 1) | H (hLen) | 0xbc

    where [DB = 0^k | 0x01 | salt] and [maskedDB] is [DB] masked with
    [MGF1(H, |DB|)] and then truncated to [emBits] bits.  [H] itself is the
    hash of eight zero bytes, the message digest, and the salt.

    [emBits] is [modBits - 1], so the top byte of the encoding always has at
    least one spare bit; that is what makes the encoded number smaller than
    the modulus.

    Encoding and verification are two separate definitions, not
    encode-then-compare.  A verifier has to reject encodings that no encoder
    would ever produce -- a wrong trailer byte, spare bits that are not
    clear, a padding string that is not zero -- and those rejections are the
    entire content of the format. *)

(** [ceil(emBits/8)], and the fact that it leaves fewer than eight spare
    bits, which is what makes the masking shift legal. *)
let em_len (emBits: pos) : pos =
  div_ceil_ok emBits 8;
  Math.lemma_div_le 8 (emBits + 7) 8;
  (emBits + 7) / 8

let em_len_ok (emBits: pos) : Lemma (8 * em_len emBits - emBits < 8)
  = Math.euclidean_division_definition (emBits + 7) 8;
    Math.lemma_mod_lt (emBits + 7) 8

(** The mask that keeps the bits of the top byte that belong to the number. *)
let top_mask (emBits: pos) : S8.t =
  em_len_ok emBits;
  S8.classify (U8.uint_to_t (255 / pow2 (8 * em_len emBits - emBits)))

let clear_top (emBits: pos) (s: Seq.seq S8.t { 0 < Seq.length s })
  : Seq.lseq S8.t (Seq.length s)
  = Seq.upd s 0 (S8.logand (Seq.index s 0) (top_mask emBits))

(** Pointwise exclusive or. *)
let xor_seq (a: Seq.seq S8.t) (b: Seq.seq S8.t { Seq.length b == Seq.length a })
  : Seq.lseq S8.t (Seq.length a)
  = Seq.init (Seq.length a) (fun i -> S8.logxor (Seq.index a i) (Seq.index b i))

(** Everything the encoding needs to be well defined: room for the salt, and
    hash inputs within range.  Both hold for every modulus and salt anyone
    uses; they are stated because [hash] and [mgf] demand them. *)
unfold let pss_ok (#t: Type0) {| word t |} (p: params t) (sLen: nat) (emBits: pos) =
  (hash_bytes p) + sLen + 2 <= em_len emBits /\
  8 + (hash_bytes p) + sLen < max_input #t /\
  (hash_bytes p) + 4 < max_input #t

(** A digest is a legal MGF1 seed. *)
let seed_ok_hash (#t: Type0) {| word t |} (p: params t) (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == (hash_bytes p) /\ (hash_bytes p) + 4 < max_input #t)
          (ensures seed_ok #t s)
  = ()

(** [M' = 0^8 | mHash | salt]. *)
let m_prime (#t: Type0) {| word t |} (p: params t)
            (mHash: Seq.lseq S8.t (hash_bytes p)) (salt: Seq.seq S8.t)
  : Seq.lseq S8.t (8 + (hash_bytes p) + Seq.length salt)
  = Seq.append (Seq.append (Seq.create 8 S8.zero) mHash) salt

let pss_h (#t: Type0) {| word t |} (p: params t) (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
          (mHash: Seq.lseq S8.t (hash_bytes p)) (salt: Seq.lseq S8.t sLen)
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = hash p (m_prime p mHash salt)

(** [DB = 0^k | 0x01 | salt], of length [emLen - hLen - 1]. *)
let pss_db (#t: Type0) {| word t |} (p: params t) (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
           (salt: Seq.lseq S8.t sLen)
  : Seq.lseq S8.t (em_len emBits - (hash_bytes p) - 1)
  = let dbLen = em_len emBits - (hash_bytes p) - 1 in
    Seq.append (Seq.append (Seq.create (dbLen - sLen - 1) S8.zero)
                           (Seq.create 1 (S8.classify 1uy)))
               salt

(** EMSA-PSS-ENCODE. *)
let pss_encode (#t: Type0) {| word t |} (p: params t)
               (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
               (salt: Seq.lseq S8.t sLen)
               (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : GTot (Seq.lseq S8.t (em_len emBits))
  = let hLen = hash_bytes p in
    let dbLen = em_len emBits - hLen - 1 in
    let h = pss_h p sLen emBits (hash p msg) salt in
    seed_ok_hash p h;
    let masked = clear_top emBits (xor_seq (pss_db p sLen emBits salt) (mgf p h dbLen)) in
    let trailer = Seq.create 1 (S8.classify 0xbcuy) in
    Seq.lemma_len_append masked h;
    Seq.lemma_len_append (Seq.append masked h) trailer;
    Seq.append (Seq.append masked h) trailer

(** EMSA-PSS-VERIFY, as a predicate: the implementation returns a [bool] and
    proves it equivalent to this. *)
let pss_valid (#t: Type0) {| word t |} (p: params t)
              (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
              (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
              (em: Seq.lseq S8.t (em_len emBits))
  : GTot prop
  = let hLen = hash_bytes p in
    let emLen = em_len emBits in
    let dbLen = emLen - hLen - 1 in
    let masked = Seq.slice em 0 dbLen in
    let h = Seq.slice em dbLen (dbLen + hLen) in
    seed_ok_hash p h;
    let db = clear_top emBits (xor_seq masked (mgf p h dbLen)) in
    let salt = Seq.slice db (dbLen - sLen) dbLen in
    S8.v (Seq.index em (emLen - 1)) == 0xbc /\
    S8.v (S8.logand (Seq.index masked 0) (S8.lognot (top_mask emBits))) == 0 /\
    (forall (k: nat). k < dbLen - sLen - 1 ==> S8.v (Seq.index db k) == 0) /\
    S8.v (Seq.index db (dbLen - sLen - 1)) == 1 /\
    h == pss_h p sLen emBits (hash p msg) salt


(** {2 Lemmas for the implementation}

    The implementation builds the encoding in place, byte by byte, and never
    materializes [pss_db] or the mask.  These say what each byte has to be
    and that getting them all right is the same as being the encoding. *)

(** [DB] byte by byte. *)
let pss_db_index (#t: Type0) {| word t |} (p: params t)
                 (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                 (salt: Seq.lseq S8.t sLen) (k: nat { k < em_len emBits - (hash_bytes p) - 1 })
  : Lemma (let dbLen = em_len emBits - (hash_bytes p) - 1 in
           Seq.index (pss_db p sLen emBits salt) k ==
             (if k < dbLen - sLen - 1 then S8.zero
              else if k = dbLen - sLen - 1 then S8.classify 1uy
              else Seq.index salt (k - (dbLen - sLen))))
  = let dbLen = em_len emBits - (hash_bytes p) - 1 in
    let pad = Seq.create (dbLen - sLen - 1) S8.zero in
    let one = Seq.create 1 (S8.classify 1uy) in
    let head = Seq.append pad one in
    Seq.lemma_len_append pad one;
    if k < dbLen - sLen
    then begin
      Seq.lemma_index_app1 head salt k;
      if k < dbLen - sLen - 1 then Seq.lemma_index_app1 pad one k
                              else Seq.lemma_index_app2 pad one k
    end
    else Seq.lemma_index_app2 head salt k

(** The masked block, byte by byte. *)
let masked_index (emBits: pos) (db: Seq.seq S8.t { 0 < Seq.length db })
                 (mask: Seq.seq S8.t { Seq.length mask == Seq.length db })
                 (k: nat { k < Seq.length db })
  : Lemma (Seq.index (clear_top emBits (xor_seq db mask)) k ==
             (if k = 0
              then S8.logand (S8.logxor (Seq.index db 0) (Seq.index mask 0)) (top_mask emBits)
              else S8.logxor (Seq.index db k) (Seq.index mask k)))
  = ()

(** ... and the same fact read backwards: an array that was xored and then
    truncated in place *is* the masked sequence. *)
let clear_top_xor_index (emBits: pos) (n: pos) (a: Seq.lseq S8.t n)
                        (b: Seq.lseq S8.t n) (r: Seq.lseq S8.t n)
  : Lemma (requires
      Seq.index r 0 ==
        S8.logand (S8.logxor (Seq.index a 0) (Seq.index b 0)) (top_mask emBits) /\
      (forall (k: nat). 0 < k /\ k < n ==>
         Seq.index r k == S8.logxor (Seq.index a k) (Seq.index b k)))
    (ensures r == clear_top emBits (xor_seq a b))
  = let e = clear_top emBits (xor_seq a b) in
    let aux (k: nat { k < n }) : Lemma (Seq.index r k == Seq.index e k)
      = masked_index emBits a b k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro r e

#push-options "--z3rlimit 600"

(** Concatenation of three pieces, pointwise: pure sequence reasoning, kept
    away from any context mentioning [mgf] or [em_len]. *)
let append3_index (#a: Type) (x: Seq.seq a) (y: Seq.seq a) (z: Seq.seq a) (w: Seq.seq a)
  : Lemma (requires
      Seq.length z == 1 /\
      Seq.length w == Seq.length x + Seq.length y + 1 /\
      (forall (k: nat). k < Seq.length x ==> Seq.index w k == Seq.index x k) /\
      (forall (k: nat). k < Seq.length y ==>
         Seq.index w (Seq.length x + k) == Seq.index y k) /\
      Seq.index w (Seq.length w - 1) == Seq.index z 0)
    (ensures w == Seq.append (Seq.append x y) z)
  = let head = Seq.append x y in
    Seq.lemma_len_append x y;
    Seq.lemma_len_append head z;
    let aux (k: nat { k < Seq.length w })
      : Lemma (Seq.index w k == Seq.index (Seq.append head z) k)
      = if k < Seq.length head
        then begin
          Seq.lemma_index_app1 head z k;
          if k < Seq.length x then Seq.lemma_index_app1 x y k
                              else Seq.lemma_index_app2 x y k
        end
        else Seq.lemma_index_app2 head z k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro w (Seq.append head z)

(** Three pointwise facts make an encoding. *)
let pss_encode_index (#t: Type0) {| word t |} (p: params t)
                     (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                     (salt: Seq.lseq S8.t sLen)
                     (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
                     (em: Seq.lseq S8.t (em_len emBits))
  : Lemma (requires
      (let hLen = hash_bytes p in
       let dbLen = em_len emBits - hLen - 1 in
       let h = pss_h p sLen emBits (hash p msg) salt in
       seed_ok_hash p h;
       (forall (k: nat). k < dbLen ==>
          Seq.index em k ==
            Seq.index (clear_top emBits (xor_seq (pss_db p sLen emBits salt) (mgf p h dbLen))) k) /\
       (forall (k: nat). k < hLen ==> Seq.index em (dbLen + k) == Seq.index h k) /\
       Seq.index em (em_len emBits - 1) == S8.classify 0xbcuy))
    (ensures em == pss_encode p sLen emBits salt msg)
  = let hLen = hash_bytes p in
    let emLen = em_len emBits in
    let dbLen = emLen - hLen - 1 in
    let h = pss_h p sLen emBits (hash p msg) salt in
    seed_ok_hash p h;
    let masked = clear_top emBits (xor_seq (pss_db p sLen emBits salt) (mgf p h dbLen)) in
    let trailer = Seq.create 1 (S8.classify 0xbcuy) in
    Seq.lemma_index_create 1 (S8.classify 0xbcuy) 0;
    append3_index masked h trailer em

(** [M'] byte by byte: the implementation zeroes eight bytes, hashes into the
    middle, and copies the salt after it. *)
let m_prime_index (#t: Type0) {| word t |} (p: params t)
                  (mHash: Seq.lseq S8.t (hash_bytes p)) (salt: Seq.seq S8.t)
                  (m: Seq.seq S8.t)
  : Lemma (requires
      Seq.length m == 8 + (hash_bytes p) + Seq.length salt /\
      (forall (k: nat). k < 8 ==> Seq.index m k == S8.zero) /\
      (forall (k: nat). k < (hash_bytes p) ==> Seq.index m (8 + k) == Seq.index mHash k) /\
      (forall (k: nat). k < Seq.length salt ==>
         Seq.index m (8 + (hash_bytes p) + k) == Seq.index salt k))
    (ensures m == m_prime p mHash salt)
  = let pad = Seq.create 8 S8.zero in
    let head = Seq.append pad mHash in
    Seq.lemma_len_append pad mHash;
    Seq.lemma_len_append head salt;
    let aux (k: nat { k < Seq.length m })
      : Lemma (Seq.index m k == Seq.index (Seq.append head salt) k)
      = if k < 8 + (hash_bytes p)
        then begin
          Seq.lemma_index_app1 head salt k;
          if k < 8 then Seq.lemma_index_app1 pad mHash k
                   else Seq.lemma_index_app2 pad mHash k
        end
        else Seq.lemma_index_app2 head salt k
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro m (m_prime p mHash salt)


(** The encoder's final step, as sequence reasoning: [pre] holds [DB] over
    its front and [H] behind it, [post] is [pre] masked, top-truncated and
    stamped with the trailer. *)
let pss_encode_pointwise (#t: Type0) {| word t |} (p: params t)
                         (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                         (salt: Seq.lseq S8.t sLen)
                         (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
                         (h: Seq.seq S8.t)
                         (mask: Seq.seq S8.t)
                         (pre: Seq.seq S8.t)
                         (post: Seq.seq S8.t)
  : Lemma (requires
      (let hLen = hash_bytes p in
       let emLen = em_len emBits in
       let dbLen = emLen - hLen - 1 in
       Seq.length h == hLen /\ Seq.length mask == dbLen /\
       Seq.length pre == emLen /\ Seq.length post == emLen /\
       seed_ok #t h /\
       h == pss_h p sLen emBits (hash p msg) salt /\
       mask == mgf p h dbLen /\
       (forall (k: nat). k < dbLen ==>
          Seq.index pre k == Seq.index (pss_db p sLen emBits salt) k) /\
       (forall (k: nat). k < hLen ==> Seq.index pre (dbLen + k) == Seq.index h k) /\
       Seq.index post 0 ==
         S8.logand (S8.logxor (Seq.index pre 0) (Seq.index mask 0)) (top_mask emBits) /\
       (forall (k: nat). 0 < k /\ k < dbLen ==>
          Seq.index post k == S8.logxor (Seq.index pre k) (Seq.index mask k)) /\
       (forall (k: nat). dbLen <= k /\ k < emLen - 1 ==> Seq.index post k == Seq.index pre k) /\
       Seq.index post (emLen - 1) == S8.classify 0xbcuy))
    (ensures post == pss_encode p sLen emBits salt msg)
  = let hLen = hash_bytes p in
    let emLen = em_len emBits in
    let dbLen = emLen - hLen - 1 in
    let h : Seq.lseq S8.t hLen = h in
    let post : Seq.lseq S8.t emLen = post in
    let db = pss_db p sLen emBits salt in
    let aux (k: nat { k < dbLen })
      : Lemma (Seq.index post k ==
                 Seq.index (clear_top emBits (xor_seq db (mgf p h dbLen))) k)
      = masked_index emBits db (mgf p h dbLen) k
    in
    FStar.Classical.forall_intro aux;
    pss_encode_index p sLen emBits salt msg post


(** What the verifier actually checks.  [db] is the unmasked data block and
    [hp] the hash of [M'] rebuilt from the salt found in it; the five
    machine-checkable facts on the right are exactly [pss_valid]. *)
let pss_valid_intro (#t: Type0) {| word t |} (p: params t)
                    (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                    (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
                    (em: Seq.lseq S8.t (em_len emBits))
                    (db: Seq.lseq S8.t (em_len emBits - (hash_bytes p) - 1))
                    (hp: Seq.lseq S8.t (hash_bytes p))
  : Lemma (requires
      (let hLen = hash_bytes p in
       let dbLen = em_len emBits - hLen - 1 in
       db == clear_top emBits (xor_seq (Seq.slice em 0 dbLen)
                                       (mgf p (Seq.slice em dbLen (dbLen + hLen)) dbLen)) /\
       hp == hash p (m_prime p (hash p msg) (Seq.slice db (dbLen - sLen) dbLen))))
    (ensures
      (let hLen = hash_bytes p in
       let emLen = em_len emBits in
       let dbLen = emLen - hLen - 1 in
       pss_valid p sLen emBits msg em <==>
         (S8.v (Seq.index em (emLen - 1)) == 0xbc /\
          S8.v (S8.logand (Seq.index em 0) (S8.lognot (top_mask emBits))) == 0 /\
          (forall (k: nat). k < dbLen - sLen - 1 ==> S8.v (Seq.index db k) == 0) /\
          S8.v (Seq.index db (dbLen - sLen - 1)) == 1 /\
          (forall (k: nat). k < hLen ==>
             S8.v (Seq.index hp k) == S8.v (Seq.index em (dbLen + k))))))
  = let hLen = hash_bytes p in
    let emLen = em_len emBits in
    let dbLen = emLen - hLen - 1 in
    let masked = Seq.slice em 0 dbLen in
    let h = Seq.slice em dbLen (dbLen + hLen) in
    seed_ok_hash p h;
    let salt = Seq.slice db (dbLen - sLen) dbLen in
    assert (Seq.index masked 0 == Seq.index em 0);
    assert (hp == pss_h p sLen emBits (hash p msg) salt);
    assert (forall (k: nat). k < hLen ==> Seq.index h k == Seq.index em (dbLen + k));
    introduce (forall (k: nat). k < hLen ==>
                 S8.v (Seq.index hp k) == S8.v (Seq.index em (dbLen + k))) ==> h == hp
    with Seq.lemma_eq_intro h hp

#pop-options

#pop-options
