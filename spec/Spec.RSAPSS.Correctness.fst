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

(** RSASSA-PSS is correct: a signature made with a valid key verifies.

    {!Hacl.RSAPSS} specifies its two directions by postconditions.  With
    [emBits = modBits - 1], [n = be_nat nb], and [rsa_pow] the function of
    {!Spec.RSAPSS.Fermat} (which is {!Hacl.RSAPSS.rsa_pow} verbatim), a
    successful [sign] writes [sg] with

    {[ be_nat sg == rsa_pow (be_nat (pss_encode p sLen emBits salt msg)) d n ]}

    and [verify] accepts [sg] under the public exponent [e] exactly when

    {[ 1 < n /\ n % 2 == 1 /\ be_nat sg < n /\
       (exists (em: Seq.lseq S8.t (em_len emBits)).
          be_nat em == rsa_pow (be_nat sg) e n /\
          pss_valid p sLen emBits msg em) ]}

    The headline, [sign_verify], is that the first implies the second when
    [rsa_key n e d p q] (see {!Spec.RSAPSS.Fermat}) and [modBits] is the bit
    length of [n] -- precisely, [pow2 (modBits - 1) <= n]; the upper bound
    is not needed.  [sign_then_verify] is the same with the two postconditions
    taken verbatim, [ok] flags included, so that a verified client can chain
    the two calls.  Neither needs the lengths and size bounds the
    implementation's preconditions impose; they hold anyway for any call.

    {b The proof} has three parts.

    - {b The encoding verifies} ([pss_encode_valid]).  Unmasking undoes
      masking: [x xor m xor m = x], and on the top byte the truncation to
      [emBits] bits commutes with it ([unmask]).  What comes out is [DB]
      truncated, and [DB]'s top byte is [0] or [1], which the truncation
      keeps because it always keeps the lowest bit ([clear_top_small]).  So
      the verifier sees the encoder's [DB], hence its salt, hence the same
      [H].

    - {b The encoding is below the modulus} ([pss_encode_lt]).  Its top byte
      is masked to [8 - (8 emLen - emBits)] bits, so as a number it is below
      [2^emBits = 2^(modBits - 1) <= n].

    - {b The RSA function inverts} ({!Spec.RSAPSS.Fermat.rsa_inverse}): for
      [m < n], [(m^d mod n)^e mod n = m].  So the verifier recomputes the
      encoding itself, which is the witness for the existential. *)
module Spec.RSAPSS.Correctness

open Hacl.Secret.Word
open Spec.SHA2
open Hacl.Spec.Bytes
open Spec.RSAPSS
open Spec.RSAPSS.Fermat

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module U8 = FStar.UInt8
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Bytes} *)

(** The spare bits of the top byte.  [top_mask] keeps the [8 - spare]
    low bits. *)
let spare (emBits: pos) : nat = 8 * em_len emBits - emBits

let top_mask_v (emBits: pos)
  : Lemma (spare emBits < 8 /\
           S8.v (top_mask emBits) == pow2 (8 - spare emBits) - 1)
  = em_len_ok emBits;
    let s = spare emBits in
    assert (S8.v (top_mask emBits) == 255 / pow2 s);
    assert_norm (255 / pow2 0 == pow2 8 - 1);
    assert_norm (255 / pow2 1 == pow2 7 - 1);
    assert_norm (255 / pow2 2 == pow2 6 - 1);
    assert_norm (255 / pow2 3 == pow2 5 - 1);
    assert_norm (255 / pow2 4 == pow2 4 - 1);
    assert_norm (255 / pow2 5 == pow2 3 - 1);
    assert_norm (255 / pow2 6 == pow2 2 - 1);
    assert_norm (255 / pow2 7 == pow2 1 - 1)

(** Masking the top byte twice with the same mask, truncating each time, is
    truncating once. *)
let unmask_byte (d m t: S8.t)
  : Lemma (S8.logand (S8.logxor (S8.logand (S8.logxor d m) t) m) t == S8.logand d t)
  = UInt.nth_lemma #8
      (UInt.logand #8 (UInt.logxor #8 (UInt.logand #8 (UInt.logxor #8 (S8.v d) (S8.v m)) (S8.v t))
                                      (S8.v m)) (S8.v t))
      (UInt.logand #8 (S8.v d) (S8.v t))

let xor_xor_byte (d m: S8.t) : Lemma (S8.logxor (S8.logxor d m) m == d)
  = UInt.logxor_inv #8 (S8.v d) (S8.v m)

(** A truncated byte has no bits outside the mask. *)
let masked_spare (x t: S8.t)
  : Lemma (S8.v (S8.logand (S8.logand x t) (S8.lognot t)) == 0)
  = UInt.nth_lemma #8
      (UInt.logand #8 (UInt.logand #8 (S8.v x) (S8.v t)) (UInt.lognot #8 (S8.v t)))
      (UInt.zero 8)

(** [0] and [1] survive truncation to at least one bit. *)
let small_byte_mask (d t: S8.t)
  : Lemma (requires (S8.v d == 0 \/ S8.v d == 1) /\ S8.v t % 2 == 1)
          (ensures S8.logand d t == d)
  = if S8.v d = 0 then begin
      UInt.logand_commutative #8 (S8.v d) (S8.v t);
      UInt.logand_lemma_1 #8 (S8.v t)
    end else begin
      UInt.logand_mask #8 (S8.v t) 1;
      UInt.logand_commutative #8 (S8.v d) (S8.v t)
    end

(** {2 Sequences} *)

let unmask (emBits: pos) (db: Seq.seq S8.t { 0 < Seq.length db })
           (mask: Seq.seq S8.t { Seq.length mask == Seq.length db })
  : Lemma (clear_top emBits (xor_seq (clear_top emBits (xor_seq db mask)) mask) ==
           clear_top emBits db)
  = let r = clear_top emBits (xor_seq (clear_top emBits (xor_seq db mask)) mask) in
    let aux (k: nat { k < Seq.length db })
      : Lemma (Seq.index r k == Seq.index (clear_top emBits db) k)
      = if k = 0 then unmask_byte (Seq.index db 0) (Seq.index mask 0) (top_mask emBits)
        else xor_xor_byte (Seq.index db k) (Seq.index mask k)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro r (clear_top emBits db)

let clear_top_small (emBits: pos) (db: Seq.seq S8.t { 0 < Seq.length db })
  : Lemma (requires S8.v (Seq.index db 0) == 0 \/ S8.v (Seq.index db 0) == 1)
          (ensures clear_top emBits db == db)
  = top_mask_v emBits;
    let s = spare emBits in
    Math.pow2_double_mult (7 - s);
    Math.lemma_mod_sub (pow2 (8 - s)) 2 (pow2 (7 - s));
    Math.cancel_mul_mod (pow2 (7 - s)) 2;
    assert (S8.v (top_mask emBits) % 2 == 1);
    small_byte_mask (Seq.index db 0) (top_mask emBits);
    Seq.lemma_eq_intro (clear_top emBits db) db

let append3_parts (#a: Type) (x y z: Seq.seq a)
  : Lemma (let w = Seq.append (Seq.append x y) z in
           let lx = Seq.length x in
           let ly = Seq.length y in
           Seq.length w == lx + ly + Seq.length z /\
           Seq.slice w 0 lx == x /\
           Seq.slice w lx (lx + ly) == y /\
           Seq.slice w (lx + ly) (Seq.length w) == z)
  = let w = Seq.append (Seq.append x y) z in
    let lx = Seq.length x in
    let ly = Seq.length y in
    Seq.lemma_len_append x y;
    Seq.lemma_len_append (Seq.append x y) z;
    Seq.lemma_eq_intro (Seq.slice w 0 lx) x;
    Seq.lemma_eq_intro (Seq.slice w lx (lx + ly)) y;
    Seq.lemma_eq_intro (Seq.slice w (lx + ly) (Seq.length w)) z

(** {2 The encoding verifies} *)

let pss_db_salt (#t: Type0) {| word t |} (p: params t)
                (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                (salt: Seq.lseq S8.t sLen)
  : Lemma (let dbLen = em_len emBits - (hash_bytes p) - 1 in
           let db = pss_db p sLen emBits salt in
           Seq.slice db (dbLen - sLen) dbLen == salt /\
           (forall (k: nat). k < dbLen - sLen - 1 ==> S8.v (Seq.index db k) == 0) /\
           S8.v (Seq.index db (dbLen - sLen - 1)) == 1)
  = let dbLen = em_len emBits - (hash_bytes p) - 1 in
    let db = pss_db p sLen emBits salt in
    FStar.Classical.forall_intro (pss_db_index p sLen emBits salt);
    Seq.lemma_eq_intro (Seq.slice db (dbLen - sLen) dbLen) salt

#push-options "--z3rlimit 100"

(** What [pss_encode] is made of. *)
let pss_encode_parts (#t: Type0) {| word t |} (p: params t)
                     (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                     (salt: Seq.lseq S8.t sLen)
                     (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : Lemma (let hLen = hash_bytes p in
           let emLen = em_len emBits in
           let dbLen = emLen - hLen - 1 in
           let em = pss_encode p sLen emBits salt msg in
           let h = pss_h p sLen emBits (hash p msg) salt in
           seed_ok_hash p h;
           Seq.slice em 0 dbLen ==
             clear_top emBits (xor_seq (pss_db p sLen emBits salt) (mgf p h dbLen)) /\
           Seq.slice em dbLen (dbLen + hLen) == h /\
           Seq.index em (emLen - 1) == S8.classify 0xbcuy)
  = let hLen = hash_bytes p in
    let emLen = em_len emBits in
    let dbLen = emLen - hLen - 1 in
    let h = pss_h p sLen emBits (hash p msg) salt in
    seed_ok_hash p h;
    let masked = clear_top emBits (xor_seq (pss_db p sLen emBits salt) (mgf p h dbLen)) in
    let trailer = Seq.create 1 (S8.classify 0xbcuy) in
    let em = pss_encode p sLen emBits salt msg in
    assert (em == Seq.append (Seq.append masked h) trailer);
    append3_parts masked h trailer;
    assert (Seq.index em (emLen - 1) == Seq.index (Seq.slice em (dbLen + hLen) emLen) 0)

#pop-options

#push-options "--z3rlimit 200"

(** EMSA-PSS-VERIFY accepts what EMSA-PSS-ENCODE produces. *)
let pss_encode_valid (#t: Type0) {| word t |} (p: params t)
                     (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                     (salt: Seq.lseq S8.t sLen)
                     (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : Lemma (pss_valid p sLen emBits msg (pss_encode p sLen emBits salt msg))
  = let hLen = hash_bytes p in
    let emLen = em_len emBits in
    let dbLen = emLen - hLen - 1 in
    let em = pss_encode p sLen emBits salt msg in
    let h = pss_h p sLen emBits (hash p msg) salt in
    seed_ok_hash p h;
    let db = pss_db p sLen emBits salt in
    let mask = mgf p h dbLen in
    let masked = clear_top emBits (xor_seq db mask) in
    pss_encode_parts p sLen emBits salt msg;
    pss_db_salt p sLen emBits salt;
    if dbLen - sLen - 1 = 0 then () else assert (S8.v (Seq.index db 0) == 0);
    clear_top_small emBits db;
    unmask emBits db mask;
    assert (clear_top emBits (xor_seq (Seq.slice em 0 dbLen) (mgf p (Seq.slice em dbLen (dbLen + hLen)) dbLen)) == db);
    assert (Seq.index (Seq.slice em 0 dbLen) 0 == Seq.index masked 0);
    masked_spare (S8.logxor (Seq.index db 0) (Seq.index mask 0)) (top_mask emBits)

#pop-options

(** {2 The encoding is below the modulus} *)

let top_byte_bound (s: Seq.seq S8.t { 0 < Seq.length s }) (b: nat)
  : Lemma (requires S8.v (Seq.index s 0) < pow2 b)
          (ensures be_nat s < pow2 (b + 8 * (Seq.length s - 1)))
  = let n = Seq.length s in
    be_nat_split s (n - 1);
    let hd = Seq.slice s 0 1 in
    let tl = Seq.slice s 1 n in
    be_nat_bound tl;
    be_nat_snoc hd 0;
    assert_norm (be_nat (Seq.slice hd 0 0) == 0);
    Seq.lemma_eq_intro (Seq.slice hd 0 1) hd;
    assert (be_nat hd == S8.v (Seq.index s 0));
    Math.lemma_mult_le_right (pow2 (8 * (n - 1))) (be_nat hd + 1) (pow2 b);
    Math.pow2_plus b (8 * (n - 1))

let pss_encode_lt (#t: Type0) {| word t |} (p: params t)
                  (sLen: nat) (emBits: pos { pss_ok p sLen emBits })
                  (salt: Seq.lseq S8.t sLen)
                  (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : Lemma (be_nat (pss_encode p sLen emBits salt msg) < pow2 emBits)
  = let hLen = hash_bytes p in
    let emLen = em_len emBits in
    let dbLen = emLen - hLen - 1 in
    let em = pss_encode p sLen emBits salt msg in
    let h = pss_h p sLen emBits (hash p msg) salt in
    seed_ok_hash p h;
    let db = pss_db p sLen emBits salt in
    let mask = mgf p h dbLen in
    pss_encode_parts p sLen emBits salt msg;
    assert (Seq.index em 0 == Seq.index (Seq.slice em 0 dbLen) 0);
    assert (Seq.index em 0 == S8.logand (S8.logxor (Seq.index db 0) (Seq.index mask 0))
                                        (top_mask emBits));
    UInt.logand_le #8 (S8.v (S8.logxor (Seq.index db 0) (Seq.index mask 0)))
                      (S8.v (top_mask emBits));
    top_mask_v emBits;
    top_byte_bound em (8 - spare emBits)

(** {2 Sign then verify} *)

(** A signature made with a valid key passes verification under the
    matching public key.  [sg] is anything whose number is the signature;
    the conclusion is the right-hand side of [verify]'s [ok <==> ...]. *)
let sign_verify (#t: Type0) {| word t |} (p: params t)
                (modBits: pos { 1 < modBits })
                (salt: Seq.seq S8.t { pss_ok p (Seq.length salt) (modBits - 1) })
                (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
                (n e d: nat) (pr qr: int) (sg: Seq.seq S8.t)
  : Lemma (requires rsa_key n e d pr qr /\ pow2 (modBits - 1) <= n /\
                    be_nat sg == rsa_pow (be_nat (pss_encode p (Seq.length salt) (modBits - 1) salt msg))
                                         d n)
          (ensures 1 < n /\ n % 2 == 1 /\ be_nat sg < n /\
                   (exists (em: Seq.lseq S8.t (em_len (modBits - 1))).
                      be_nat em == rsa_pow (be_nat sg) e n /\
                      pss_valid p (Seq.length salt) (modBits - 1) msg em))
  = let emBits = modBits - 1 in
    let sLen = Seq.length salt in
    let em = pss_encode p sLen emBits salt msg in
    rsa_key_odd n e d pr qr;
    pss_encode_lt p sLen emBits salt msg;
    pss_encode_valid p sLen emBits salt msg;
    rsa_inverse n e d pr qr (be_nat em)

(** The same, with [sign]'s and [verify]'s postconditions as they are
    written in {!Hacl.RSAPSS}: if signing reported success, verification
    reports success. *)
let sign_then_verify (#t: Type0) {| word t |} (p: params t)
                     (modBits: pos { 1 < modBits })
                     (salt: Seq.seq S8.t { pss_ok p (Seq.length salt) (modBits - 1) })
                     (sLen: nat)
                     (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
                     (nb eb db sg: Seq.seq S8.t) (pr qr: int) (okS okV: bool)
  : Lemma (requires
      rsa_key (be_nat nb) (be_nat eb) (be_nat db) pr qr /\
      pow2 (modBits - 1) <= be_nat nb /\
      sLen == Seq.length salt /\
      (okS ==> be_nat sg ==
                 rsa_pow (be_nat (pss_encode p (Seq.length salt) (modBits - 1) salt msg))
                         (be_nat db) (be_nat nb)) /\
      (okV <==> (1 < be_nat nb /\ be_nat nb % 2 == 1 /\ be_nat sg < be_nat nb /\
                 (exists (e: Seq.lseq S8.t (em_len (modBits - 1))).
                    be_nat e == rsa_pow (be_nat sg) (be_nat eb) (be_nat nb) /\
                    pss_valid p sLen (modBits - 1) msg e))) /\
      okS)
    (ensures okV)
  = sign_verify p modBits salt msg (be_nat nb) (be_nat eb) (be_nat db) pr qr sg

#pop-options
