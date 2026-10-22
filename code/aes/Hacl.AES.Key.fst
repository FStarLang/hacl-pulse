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

(** The key expansion of FIPS 197 section 5.2.

    The expanded key is a flat byte slice of [16 * (nr + 1)] bytes: the first
    [keylen] are the key, and every four bytes after that are one word,
    obtained from the word [nk] back and a transform of the word just before.

    Everything here counts in {b bytes}, never in words, so that no
    multiplication ever appears: the loop runs over the byte offset [b] in
    steps of four, and the two conditions that FIPS 197 states on the word
    index become conditions on [b] modulo the key length.  [i mod nk = 0] is
    [b mod keylen = 0], and AES-256's extra substitution at [i mod nk = 4] is
    [b mod keylen = 16].

    The round constant is [x^(j-1)] in GF(2^8), so it is carried in a register
    and squared -- doubled, rather -- each time it is used.  The invariant
    names it by the number of times the loop has passed a key-length boundary,
    which is [ceil(b / keylen)]. *)
module Hacl.AES.Key

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module SW = Hacl.AES.SubWord
module UInt = FStar.UInt
module Vec = Hacl.Vec128
module Sub = Hacl.Impl.Sub
module Mem = Hacl.Mem

(** This module is arithmetic-heavy, and the default SMT encoding boxes
    every integer operation, which hides the structure of the products from
    Z3's arithmetic solver.  Encoding linear arithmetic natively and leaving
    only the nonlinear operators wrapped is measurably faster here. *)
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** {2 Arithmetic of the round-constant counter}

    [rcon] is only defined from one upwards, and a [pure] conjunct cannot use
    an earlier conjunct to justify the argument, so the invariant speaks of
    this total extension instead. *)

let rcon0 (j: nat) : elem = if j = 0 then 0 else rcon j

let rcon0_pos (j: pos) : Lemma (rcon0 j == rcon j) = ()

#push-options "--fuel 1 --ifuel 1"
let rcon_step (j: pos) : Lemma (rcon (j + 1) == xtime (rcon j)) = ()

(** The number of key-length boundaries the loop has passed at byte offset
    [b]: the index of the round constant currently in the register. *)
#pop-options

let rcidx (b: nat) (n: pos) : nat = b / n + (if b % n = 0 then 0 else 1)

let rcidx_init (n: pos) : Lemma (rcidx n n == 1) =
  Math.lemma_div_plus 0 1 n; Math.lemma_mod_plus 0 1 n

let rcidx_at_mul (b: nat) (n: pos)
  : Lemma (requires n <= b /\ b % n == 0)
          (ensures rcidx b n == b / n /\ 1 <= b / n)
  = Math.lemma_div_mod b n

let rcidx_step_mul (b: nat) (n: pos)
  : Lemma (requires n <= b /\ b % n == 0 /\ 4 < n)
          (ensures rcidx (b + 4) n == rcidx b n + 1)
  = Math.lemma_div_mod b n;
    Math.lemma_div_plus 4 (b / n) n;
    Math.lemma_mod_plus 4 (b / n) n;
    Math.small_div 4 n;
    Math.small_mod 4 n

(** A multiple of four below a multiple of four leaves at least four to go;
    this is what says the loop cannot step past a boundary. *)
let mul4_gap (r: nat) (n: pos)
  : Lemma (requires r < n /\ r % 4 == 0 /\ n % 4 == 0) (ensures r + 4 <= n)
  = Math.lemma_div_mod r 4; Math.lemma_div_mod n 4

let mod4_mod (b: nat) (n: pos)
  : Lemma (requires b % 4 == 0 /\ n % 4 == 0) (ensures (b % n) % 4 == 0)
  = Math.lemma_div_mod b n;
    Math.lemma_mod_mul_distr_l n (b / n) 4;
    Math.lemma_mod_add_distr (b % n) (n * (b / n)) 4

let rcidx_val (b: nat) (n: pos) (q: nat) (r: nat)
  : Lemma (requires b / n == q /\ b % n == r)
          (ensures rcidx b n == q + (if r = 0 then 0 else 1))
  = ()

let div_mod_shift (x q: nat) (n: pos)
  : Lemma (requires x < n) (ensures (x + q * n) / n == q /\ (x + q * n) % n == x)
  = Math.lemma_div_plus x q n;
    Math.lemma_mod_plus x q n;
    Math.small_div x n;
    Math.small_mod x n

let div_mod_shift_n (q: nat) (n: pos)
  : Lemma ((n + q * n) / n == q + 1 /\ (n + q * n) % n == 0)
  = Math.lemma_div_plus n q n;
    Math.lemma_mod_plus n q n;
    Math.cancel_mul_div 1 n;
    Math.cancel_mul_mod 1 n

let rcidx_step_other (b: nat) (n: pos)
  : Lemma (requires n <= b /\ b % n <> 0 /\ b % 4 == 0 /\ n % 4 == 0)
          (ensures rcidx (b + 4) n == rcidx b n)
  = let q = b / n in
    let r = b % n in
    Math.lemma_div_mod b n;
    mod4_mod b n;
    mul4_gap r n;
    Math.swap_mul n q;
    assert (b + 4 == (r + 4) + q * n);
    rcidx_val b n q r;
    if r + 4 = n then begin
      div_mod_shift_n q n;
      rcidx_val (b + 4) n (q + 1) 0
    end else begin
      div_mod_shift (r + 4) q n;
      rcidx_val (b + 4) n q (r + 4)
    end

(** Counting in bytes rather than in words: the word index [i] sits at byte
    [4i], and the key length is four times [nk], so both the quotient and the
    remainder survive the scaling. *)
let word_to_byte (i: nat) (n: pos)
  : Lemma ((4 * i) % (4 * n) == 4 * (i % n) /\ (4 * i) / (4 * n) == i / n)
  = Math.lemma_div_mod i n;
    assert (4 * i == 4 * (i % n) + (i / n) * (4 * n));
    Math.lemma_mod_plus (4 * (i % n)) (i / n) (4 * n);
    Math.small_mod (4 * (i % n)) (4 * n);
    Math.lemma_div_plus (4 * (i % n)) (i / n) (4 * n);
    Math.small_div (4 * (i % n)) (4 * n)

(** {2 The pure side}

    Pulse does not unfold specification definitions inside a verification
    condition, so the whole of the correspondence with [key_expansion] lives
    in these lemmas and the Pulse functions below only supply the byte
    equations they establish. *)

let ks_expand_at (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat) (j: nat { j < 4 })
  : Lemma (requires 4 * i + j < xkeylen v)
          (ensures Seq.index (key_expansion v key) (4 * i + j) ==
                   Seq.index (ks_word v key i) j)
  = key_expansion_index v key (4 * i + j);
    Math.lemma_div_plus j i 4;
    Math.small_div j 4;
    Math.lemma_mod_plus j i 4;
    Math.small_mod j 4

(** Below the key length the expanded key is the key itself. *)
#push-options "--fuel 1 --ifuel 1"
let ks_expand_key (v: variant) (key: Seq.lseq elem (keylen v)) (j: nat { j < keylen v })
  : Lemma (Seq.index (key_expansion v key) j == Seq.index key j)
  = Math.lemma_div_mod j 4;
    ks_expand_at v key (j / 4) (j % 4)

#pop-options

(** The three shapes of a step.  They are separate lemmas rather than one
    with a conditional because the caller is in a branch where the condition
    is already decided, and a smaller hypothesis is a smaller query. *)

let xor_word_index (a b: word) (j: nat { j < 4 })
  : Lemma (Seq.index (xor_word a b) j == Seq.index a j ^^ Seq.index b j) = ()

let sub_word_index (a: word) (j: nat { j < 4 })
  : Lemma (Seq.index (sub_word a) j == sbox (Seq.index a j)) = ()

let rot_word_index (a: word) (j: nat { j < 4 })
  : Lemma (Seq.index (rot_word a) j == Seq.index a ((j + 1) % 4)) = ()

let rcon_word_index (r: pos) (j: nat { j < 4 })
  : Lemma (Seq.index (rcon_word r) j == (if j = 0 then rcon r else 0)) = ()

let succ_mod4 (j: nat { j < 4 })
  : Lemma ((j + 1) % 4 == (if j = 3 then 0 else j + 1))
  = if j = 3 then Math.cancel_mul_mod 1 4 else Math.small_mod (j + 1) 4

let one_le_div (i: nat) (n: pos)
  : Lemma (requires n <= i) (ensures 1 <= i / n)
  = Math.lemma_div_le n i n; Math.cancel_mul_div 1 n

#push-options "--fuel 1 --ifuel 1"
let ks_word_mul (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat)
  : Lemma (requires nk v <= i /\ i % nk v == 0 /\ 1 <= i / nk v)
          (ensures ks_word v key i ==
             xor_word (ks_word v key (i - nk v))
               (xor_word (sub_word (rot_word (ks_word v key (i - 1)))) (rcon_word (i / nk v))))
  = ()

let ks_word_sub (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat)
  : Lemma (requires nk v <= i /\ nk v > 6 /\ i % nk v == 4)
          (ensures ks_word v key i ==
             xor_word (ks_word v key (i - nk v)) (sub_word (ks_word v key (i - 1))))
  = ()

let ks_word_plain (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat)
  : Lemma (requires nk v <= i /\ i % nk v <> 0 /\ ~(nk v > 6 /\ i % nk v == 4))
          (ensures ks_word v key i ==
             xor_word (ks_word v key (i - nk v)) (ks_word v key (i - 1)))
  = ()
#pop-options

let ks_step_mul (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat) (j: nat { j < 4 })
  : Lemma (requires nk v <= i /\ i % nk v == 0)
          (ensures 1 <= i / nk v /\
            Seq.index (ks_word v key i) j ==
              Seq.index (ks_word v key (i - nk v)) j ^^
              (if j = 0 then sbox (Seq.index (ks_word v key (i - 1)) 1) ^^ rcon (i / nk v)
               else sbox (Seq.index (ks_word v key (i - 1)) (if j = 3 then 0 else j + 1))))
  = one_le_div i (nk v);
    ks_word_mul v key i;
    let prev = ks_word v key (i - 1) in
    let rw = rot_word prev in
    xor_word_index (ks_word v key (i - nk v))
      (xor_word (sub_word rw) (rcon_word (i / nk v))) j;
    xor_word_index (sub_word rw) (rcon_word (i / nk v)) j;
    sub_word_index rw j;
    rot_word_index prev j;
    succ_mod4 j;
    rcon_word_index (i / nk v) j;
    xor_zero (sbox (Seq.index prev (if j = 3 then 0 else j + 1)))

let ks_step_sub (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat) (j: nat { j < 4 })
  : Lemma (requires nk v <= i /\ nk v > 6 /\ i % nk v == 4)
          (ensures Seq.index (ks_word v key i) j ==
                   Seq.index (ks_word v key (i - nk v)) j ^^
                   sbox (Seq.index (ks_word v key (i - 1)) j))
  = ks_word_sub v key i;
    xor_word_index (ks_word v key (i - nk v)) (sub_word (ks_word v key (i - 1))) j;
    sub_word_index (ks_word v key (i - 1)) j

let ks_step_plain (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat) (j: nat { j < 4 })
  : Lemma (requires nk v <= i /\ i % nk v <> 0 /\ ~(nk v > 6 /\ i % nk v == 4))
          (ensures Seq.index (ks_word v key i) j ==
                   Seq.index (ks_word v key (i - nk v)) j ^^
                   Seq.index (ks_word v key (i - 1)) j)
  = ks_word_plain v key i;
    xor_word_index (ks_word v key (i - nk v)) (ks_word v key (i - 1)) j

(** {2 One byte of a step}

    [b] is the byte offset of the word being written.  Each lemma says that
    if the bytes a step reads agree with [key_expansion], then the byte it
    writes does too.  They speak of plain sequences of elements and mention
    only the handful of indices involved, so the queries stay small. *)

let byte_word (v: variant) (b: nat)
  : Lemma (requires b % 4 == 0)
          (ensures 4 * (b / 4) == b /\
                   b % keylen v == 4 * ((b / 4) % nk v) /\
                   b / keylen v == (b / 4) / nk v)
  = Math.lemma_div_mod b 4;
    word_to_byte (b / 4) (nk v)

let ks_byte_mul (v: variant) (key: Seq.lseq elem (keylen v))
                (s0 s1: Seq.seq elem) (b: nat) (k: nat { k < 4 })
  : Lemma (requires
      Seq.length s0 == xkeylen v /\ Seq.length s1 == xkeylen v /\
      keylen v <= b /\ b + 4 <= xkeylen v /\ b % 4 == 0 /\ b % keylen v == 0 /\
      Seq.index s0 (b - keylen v + k) == Seq.index (key_expansion v key) (b - keylen v + k) /\
      Seq.index s0 (b - 4 + (if k = 3 then 0 else k + 1)) ==
        Seq.index (key_expansion v key) (b - 4 + (if k = 3 then 0 else k + 1)) /\
      Seq.index s1 (b + k) ==
        Seq.index s0 (b - keylen v + k) ^^
        (if k = 0 then sbox (Seq.index s0 (b - 3)) ^^ rcon0 (b / keylen v)
         else sbox (Seq.index s0 (b - 4 + (if k = 3 then 0 else k + 1)))))
    (ensures Seq.index s1 (b + k) == Seq.index (key_expansion v key) (b + k))
  = let i = b / 4 in
    byte_word v b;
    rcidx_at_mul b (keylen v);
    rcon0_pos (b / keylen v);
    ks_expand_at v key (i - nk v) k;
    ks_expand_at v key (i - 1) (if k = 3 then 0 else k + 1);
    ks_expand_at v key i k;
    ks_step_mul v key i k

let ks_byte_sub (v: variant) (key: Seq.lseq elem (keylen v))
                (s0 s1: Seq.seq elem) (b: nat) (k: nat { k < 4 })
  : Lemma (requires
      Seq.length s0 == xkeylen v /\ Seq.length s1 == xkeylen v /\
      keylen v <= b /\ b + 4 <= xkeylen v /\ b % 4 == 0 /\
      keylen v > 24 /\ b % keylen v == 16 /\
      Seq.index s0 (b - keylen v + k) == Seq.index (key_expansion v key) (b - keylen v + k) /\
      Seq.index s0 (b - 4 + k) == Seq.index (key_expansion v key) (b - 4 + k) /\
      Seq.index s1 (b + k) ==
        Seq.index s0 (b - keylen v + k) ^^ sbox (Seq.index s0 (b - 4 + k)))
    (ensures Seq.index s1 (b + k) == Seq.index (key_expansion v key) (b + k))
  = let i = b / 4 in
    byte_word v b;
    ks_expand_at v key (i - nk v) k;
    ks_expand_at v key (i - 1) k;
    ks_expand_at v key i k;
    ks_step_sub v key i k

let ks_byte_plain (v: variant) (key: Seq.lseq elem (keylen v))
                  (s0 s1: Seq.seq elem) (b: nat) (k: nat { k < 4 })
  : Lemma (requires
      Seq.length s0 == xkeylen v /\ Seq.length s1 == xkeylen v /\
      keylen v <= b /\ b + 4 <= xkeylen v /\ b % 4 == 0 /\
      b % keylen v <> 0 /\ ~(keylen v > 24 /\ b % keylen v == 16) /\
      Seq.index s0 (b - keylen v + k) == Seq.index (key_expansion v key) (b - keylen v + k) /\
      Seq.index s0 (b - 4 + k) == Seq.index (key_expansion v key) (b - 4 + k) /\
      Seq.index s1 (b + k) ==
        Seq.index s0 (b - keylen v + k) ^^ Seq.index s0 (b - 4 + k))
    (ensures Seq.index s1 (b + k) == Seq.index (key_expansion v key) (b + k))
  = let i = b / 4 in
    byte_word v b;
    ks_expand_at v key (i - nk v) k;
    ks_expand_at v key (i - 1) k;
    ks_expand_at v key i k;
    ks_step_plain v key i k

(** Four new bytes on top of a prefix that agrees, through a middle
    sequence, with the target. *)
let prefix_extend (s m t: Seq.seq elem) (b: nat)
  : Lemma (requires
      b + 4 <= Seq.length s /\ b + 4 <= Seq.length m /\ b + 4 <= Seq.length t /\
      (forall (j: nat). j < b ==> Seq.index m j == Seq.index t j) /\
      (forall (j: nat). j < b ==> Seq.index s j == Seq.index m j) /\
      Seq.index s b == Seq.index t b /\
      Seq.index s (b + 1) == Seq.index t (b + 1) /\
      Seq.index s (b + 2) == Seq.index t (b + 2) /\
      Seq.index s (b + 3) == Seq.index t (b + 3))
    (ensures forall (j: nat). j < b + 4 ==> Seq.index s j == Seq.index t j)
  = ()

(** {2 Joining a step to the prefix}

    Each lemma says that a slice which agreed with [key_expansion] below [b],
    and whose four new bytes satisfy the equations of one step, agrees with
    it below [b + 4]. *)

let ks_join_mul (v: variant) (key: Seq.lseq elem (keylen v))
                (vw0 vw1: Seq.seq S8.t) (b: nat)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 4 <= xkeylen v /\ b % 4 == 0 /\ b % keylen v == 0 /\
      (forall (j: nat). j < b ==> Seq.index (vals vw0) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      Seq.index (vals vw1) b ==
        Seq.index (vals vw0) (b - keylen v) ^^
        (sbox (Seq.index (vals vw0) (b - 3)) ^^ rcon0 (b / keylen v)) /\
      Seq.index (vals vw1) (b + 1) ==
        Seq.index (vals vw0) (b - keylen v + 1) ^^ sbox (Seq.index (vals vw0) (b - 2)) /\
      Seq.index (vals vw1) (b + 2) ==
        Seq.index (vals vw0) (b - keylen v + 2) ^^ sbox (Seq.index (vals vw0) (b - 1)) /\
      Seq.index (vals vw1) (b + 3) ==
        Seq.index (vals vw0) (b - keylen v + 3) ^^ sbox (Seq.index (vals vw0) (b - 4)))
    (ensures forall (j: nat). j < b + 4 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = let s0 = vals vw0 in
    let s1 = vals vw1 in
    let ke = key_expansion v key in
    assert (Seq.index s0 (b - keylen v) == Seq.index ke (b - keylen v));
    assert (Seq.index s0 (b - keylen v + 1) == Seq.index ke (b - keylen v + 1));
    assert (Seq.index s0 (b - keylen v + 2) == Seq.index ke (b - keylen v + 2));
    assert (Seq.index s0 (b - keylen v + 3) == Seq.index ke (b - keylen v + 3));
    assert (Seq.index s0 (b - 4) == Seq.index ke (b - 4));
    assert (Seq.index s0 (b - 3) == Seq.index ke (b - 3));
    assert (Seq.index s0 (b - 2) == Seq.index ke (b - 2));
    assert (Seq.index s0 (b - 1) == Seq.index ke (b - 1));
    ks_byte_mul v key s0 s1 b 0;
    ks_byte_mul v key s0 s1 b 1;
    ks_byte_mul v key s0 s1 b 2;
    ks_byte_mul v key s0 s1 b 3;
    prefix_extend s1 s0 ke b

let ks_join_sub (v: variant) (key: Seq.lseq elem (keylen v))
                (vw0 vw1: Seq.seq S8.t) (b: nat)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 4 <= xkeylen v /\ b % 4 == 0 /\
      keylen v > 24 /\ b % keylen v == 16 /\
      (forall (j: nat). j < b ==> Seq.index (vals vw0) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 4 ==> Seq.index (vals vw1) (b + j) ==
         Seq.index (vals vw0) (b - keylen v + j) ^^ sbox (Seq.index (vals vw0) (b - 4 + j))))
    (ensures forall (j: nat). j < b + 4 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = let s0 = vals vw0 in
    let s1 = vals vw1 in
    let ke = key_expansion v key in
    let aux (k: nat { k < 4 }) : Lemma (Seq.index s1 (b + k) == Seq.index ke (b + k)) =
      assert (Seq.index s0 (b - keylen v + k) == Seq.index ke (b - keylen v + k));
      assert (Seq.index s0 (b - 4 + k) == Seq.index ke (b - 4 + k));
      ks_byte_sub v key s0 s1 b k
    in
    aux 0; aux 1; aux 2; aux 3;
    prefix_extend s1 s0 ke b

let ks_join_plain (v: variant) (key: Seq.lseq elem (keylen v))
                  (vw0 vw1: Seq.seq S8.t) (b: nat)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 4 <= xkeylen v /\ b % 4 == 0 /\
      b % keylen v <> 0 /\ ~(keylen v > 24 /\ b % keylen v == 16) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw0) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 4 ==> Seq.index (vals vw1) (b + j) ==
         Seq.index (vals vw0) (b - keylen v + j) ^^ Seq.index (vals vw0) (b - 4 + j)))
    (ensures forall (j: nat). j < b + 4 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = let s0 = vals vw0 in
    let s1 = vals vw1 in
    let ke = key_expansion v key in
    let aux (k: nat { k < 4 }) : Lemma (Seq.index s1 (b + k) == Seq.index ke (b + k)) =
      assert (Seq.index s0 (b - keylen v + k) == Seq.index ke (b - keylen v + k));
      assert (Seq.index s0 (b - 4 + k) == Seq.index ke (b - 4 + k));
      ks_byte_plain v key s0 s1 b k
    in
    aux 0; aux 1; aux 2; aux 3;
    prefix_extend s1 s0 ke b

(** The whole expanded key, once the prefix property reaches the end. *)
let ks_done (v: variant) (key: Seq.lseq elem (keylen v)) (vw: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length vw == xkeylen v /\ xkeylen v <= n /\
             (forall (j: nat). j < xkeylen v ==>
                Seq.index (vals vw) j == Seq.index (key_expansion v key) j))
          (ensures vals vw == key_expansion v key)
  = Seq.lemma_eq_intro (vals vw) (key_expansion v key)

(** {2 Glue for the driver loop} *)

let key_prefix (v: variant) (key: Seq.lseq elem (keylen v)) (vw: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length vw == xkeylen v /\ keylen v <= n /\
             (forall (j: nat). j < keylen v ==> Seq.index (vals vw) j == Seq.index key j))
          (ensures forall (j: nat). j < keylen v ==>
             Seq.index (vals vw) j == Seq.index (key_expansion v key) j)
  = FStar.Classical.forall_intro (ks_expand_key v key)

let rcon_prep (v: variant) (b: nat) (r: nat)
  : Lemma (requires keylen v <= b /\ r == rcon0 (rcidx b (keylen v)))
          (ensures b % keylen v == 0 ==> r == rcon0 (b / keylen v))
  = if b % keylen v = 0 then rcidx_at_mul b (keylen v) else ()

let rcon_bump (v: variant) (b: nat) (r: nat) (nr: nat)
  : Lemma (requires keylen v <= b /\ b % keylen v == 0 /\
                    r == rcon0 (rcidx b (keylen v)) /\ nr == xtime r)
          (ensures nr == rcon0 (rcidx (b + 4) (keylen v)))
  = rcidx_at_mul b (keylen v);
    rcidx_step_mul b (keylen v);
    rcon0_pos (rcidx b (keylen v));
    rcon_step (rcidx b (keylen v));
    rcon0_pos (rcidx b (keylen v) + 1)

#push-options "--fuel 1 --ifuel 1"
let rcon_init (n: pos) : Lemma (rcon0 (rcidx n n) == 1) = rcidx_init n
#pop-options

let rcon_keep (v: variant) (b: nat)
  : Lemma (requires keylen v <= b /\ b % keylen v <> 0 /\ b % 4 == 0)
          (ensures rcidx (b + 4) (keylen v) == rcidx b (keylen v))
  = rcidx_step_other b (keylen v)

(** {2 The implementation} *)

(** One word: read the word [keylen] bytes back and the word just before,
    transform the latter as the position demands, and xor.  Doing the whole
    join here keeps the driver loop's verification condition to the prefix
    property alone. *)

fn ks_word_impl ([@@@FStar.Attributes.monomorphize] p: params)
                (w: A.array S8.t) (sb: A.array S8.t) (b: SZ.t) (rc: S8.t)
                (#key: erased (Seq.lseq elem (keylen p.pv)))
                (#vsb: erased (Seq.seq S8.t))
                (#vw0: erased (Seq.seq S8.t))
requires A.pts_to w vw0 ** A.pts_to sb vsb ** pure (
  Seq.length vsb == blocklen /\
  Seq.length vw0 == xkeylen p.pv /\
  keylen p.pv <= SZ.v b /\ SZ.v b + 4 <= xkeylen p.pv /\ SZ.v b % 4 == 0 /\
  (SZ.v b % keylen p.pv == 0 ==> S8.v rc == rcon0 (SZ.v b / keylen p.pv)) /\
  (forall (j: nat). j < SZ.v b ==>
     Seq.index (vals vw0) j == Seq.index (key_expansion p.pv key) j))
ensures exists* (vw1: Seq.seq S8.t) (vsb1: Seq.seq S8.t).
  A.pts_to w vw1 ** A.pts_to sb vsb1 ** pure (
  Seq.length vsb1 == blocklen /\
  Seq.length vw1 == xkeylen p.pv /\ SZ.v b + 4 <= xkeylen p.pv /\
  (forall (j: nat). j < SZ.v b + 4 ==>
     Seq.index (vals vw1) j == Seq.index (key_expansion p.pv key) j))
{
  A.pts_to_len w;
  A.pts_to_len sb;
  let back = SZ.sub b p.pkeylen;
  let prev = SZ.sub b 4sz;
  let a0 = A.(w.(back));
  let a1 = A.(w.(SZ.add back 1sz));
  let a2 = A.(w.(SZ.add back 2sz));
  let a3 = A.(w.(SZ.add back 3sz));
  let p0 = A.(w.(prev));
  let p1 = A.(w.(SZ.add prev 1sz));
  let p2 = A.(w.(SZ.add prev 2sz));
  let p3 = A.(w.(SZ.add prev 3sz));
  let m = SZ.rem b p.pkeylen;
  if (m = 0sz) {
    SW.subword4 sb p1 p2 p3 p0;
    with vsb'. assert A.pts_to sb vsb';
    A.pts_to_len sb;
    vals_index vsb' 8; vals_index vsb' 9; vals_index vsb' 10; vals_index vsb' 11;
    let t0 = bxor A.(sb.(8sz)) rc;
    let t1 = A.(sb.(9sz));
    let t2 = A.(sb.(10sz));
    let t3 = A.(sb.(11sz));
    A.((w.(b) <- bxor a0 t0));
    A.((w.(SZ.add b 1sz) <- bxor a1 t1));
    A.((w.(SZ.add b 2sz) <- bxor a2 t2));
    A.((w.(SZ.add b 3sz) <- bxor a3 t3));
    with vw1. assert A.pts_to w vw1;
    ks_join_mul p.pv key vw0 vw1 (SZ.v b);
    A.pts_to_len w;
  } else {
    if (SZ.gt p.pkeylen 24sz && m = 16sz) {
      SW.subword4 sb p0 p1 p2 p3;
      with vsb'. assert A.pts_to sb vsb';
      A.pts_to_len sb;
      vals_index vsb' 8; vals_index vsb' 9; vals_index vsb' 10; vals_index vsb' 11;
      let s0 = A.(sb.(8sz));
      let s1 = A.(sb.(9sz));
      let s2 = A.(sb.(10sz));
      let s3 = A.(sb.(11sz));
      A.((w.(b) <- bxor a0 s0));
      A.((w.(SZ.add b 1sz) <- bxor a1 s1));
      A.((w.(SZ.add b 2sz) <- bxor a2 s2));
      A.((w.(SZ.add b 3sz) <- bxor a3 s3));
      with vw1. assert A.pts_to w vw1;
      ks_join_sub p.pv key vw0 vw1 (SZ.v b);
      A.pts_to_len w;
    } else {
      A.((w.(b) <- bxor a0 p0));
      A.((w.(SZ.add b 1sz) <- bxor a1 p1));
      A.((w.(SZ.add b 2sz) <- bxor a2 p2));
      A.((w.(SZ.add b 3sz) <- bxor a3 p3));
      with vw1. assert A.pts_to w vw1;
      ks_join_plain p.pv key vw0 vw1 (SZ.v b);
      A.pts_to_len w;
    }
  }
}

(** {2 The key schedule in registers}

    The scalar loop above walks the expanded key a byte at a time and pays a
    store and a load for every [AESKEYGENASSIST]; at two hundred and fifty
    nanoseconds for AES-128 it is most of the fixed cost of a short GCM call.
    The same recurrence fits in one register.  FIPS 197 says that within a
    round key each word is the previous one xored with the word [keylen]
    bytes back, so the whole round key is the prefix xor of the round key
    [keylen] bytes back, plus a term that repeats in all four words:

      K[i] = K[i - 4] (as a running xor, left to right) ^ t,  t period four.

    A prefix xor over four-byte lanes is three byte shifts and three xors,
    and [t] is one [AESKEYGENASSIST] and a shuffle.  Nothing touches memory
    except the single sixteen-byte load and store at each end. *)

(** Refinement subtyping does not cross [erased], so the sixteen-byte window
    a load wants is reached through an explicit coercion. *)
let as_blk (s: Seq.seq S8.t { Seq.length s == blocklen })
  : Pure (Seq.lseq S8.t blocklen) (requires True) (ensures fun r -> r == s)
  = s

let slice_index (s: Seq.seq elem) (lo: nat) (hi: nat { lo <= hi /\ hi <= Seq.length s })
                (i: nat { i < hi - lo })
  : Lemma (Seq.index (Seq.slice s lo hi) i == Seq.index s (lo + i))
  = ()

(** [xor_block] is [Seq.init]-shaped, so its indices have to be given to the
    solver explicitly before it will push a block equation down to a byte. *)
let xor_block_index (a b: block) (i: nat { i < blocklen })
  : Lemma (Seq.index (xor_block a b) i == Seq.index a i ^^ Seq.index b i)
          [SMTPat (Seq.index (xor_block a b) i)]
  = ()

(** A multiple of sixteen is a multiple of thirty-two or sixteen past one,
    which is what says a sixteen-byte step of the AES-256 schedule lands
    alternately on a round-constant word and a plain [SubWord] one. *)
let mod16_split (b: nat) : Lemma (requires b % 16 == 0)
                                 (ensures b % 32 == 0 \/ b % 32 == 16)
  = let k = b / 16 in
    Math.lemma_div_mod b 16;
    let q = k / 2 in
    let r = k % 2 in
    Math.lemma_div_mod k 2;
    assert (b == 16 * r + q * 32);
    Math.lemma_mod_plus (16 * r) q 32;
    Math.small_mod (16 * r) 32

let mod_add_small (n: pos) (b: nat) (d: nat)
  : Lemma (requires b % n + d < n) (ensures (b + d) % n == b % n + d)
  = Math.lemma_div_mod b n;
    Math.lemma_mod_plus (b % n + d) (b / n) n;
    Math.small_mod (b % n + d) n

let mod16_mod4 (b: nat) : Lemma (requires b % 16 == 0) (ensures b % 4 == 0)
  = Math.lemma_div_mod b 16;
    Math.lemma_mod_plus 0 (4 * (b / 16)) 4

let mul16_gap (b: nat) (n: nat)
  : Lemma (requires b % 16 == 0 /\ n % 16 == 0 /\ b < n) (ensures b + 16 <= n)
  = Math.lemma_div_mod b 16; Math.lemma_div_mod n 16

let xkeylen_mod16 (v: variant) : Lemma (xkeylen v % 16 == 0)
  = Math.multiple_modulo_lemma (nr v + 1) 16

(** The round constant over a sixteen-byte step.  The rule is the same as
    over a four-byte one -- advance at a multiple of the key length, hold
    otherwise -- because the three intermediate words never cross a
    boundary. *)
let rcon_bump16 (v: variant) (b: nat) (r: nat) (nr: nat)
  : Lemma (requires keylen v <= b /\ b % 16 == 0 /\ b % keylen v == 0 /\
                    r == rcon0 (rcidx b (keylen v)) /\ nr == xtime r)
          (ensures nr == rcon0 (rcidx (b + 16) (keylen v)))
  = mod16_mod4 b;
    rcon_bump v b r nr;
    mod_add_small (keylen v) b 4;
    mod_add_small (keylen v) b 8;
    mod_add_small (keylen v) b 12;
    rcon_keep v (b + 4); rcon_keep v (b + 8); rcon_keep v (b + 12)

let rcon_keep16 (v: variant) (b: nat)
  : Lemma (requires keylen v <= b /\ b % 16 == 0 /\ b % keylen v <> 0)
          (ensures rcidx (b + 16) (keylen v) == rcidx b (keylen v))
  = mod16_mod4 b;
    mod16_split b;
    mod_add_small (keylen v) b 4;
    mod_add_small (keylen v) b 8;
    mod_add_small (keylen v) b 12;
    rcon_keep v b; rcon_keep v (b + 4);
    rcon_keep v (b + 8); rcon_keep v (b + 12)

(** Byte xor at the integer level.  [( ^^ )] wraps its arguments in
    [UInt8.uint_to_t], and an equation between two integers does not survive
    that wrapper in congruence closure -- knowing [b == 0] does not tell the
    solver that [a ^^ b == a ^^ 0].  [FStar.UInt.logxor] takes integers, so
    the whole of the prefix-xor algebra is done there and brought back across
    one application at a time. *)

let lx (a b: elem) : elem = UInt.logxor #8 a b

let lx_is (a b: elem) : Lemma (a ^^ b == lx a b) = xor_is_logxor a b

let lx_zero (a: elem) : Lemma (lx a 0 == a /\ lx 0 a == a)
  = UInt.logxor_lemma_1 #8 a; UInt.logxor_commutative #8 a 0

let lx_assoc (a b c: elem) : Lemma (lx a (lx b c) == lx (lx a b) c)
  = UInt.logxor_associative #8 a b c

(** [c == a ^^ b] survives rewriting [a] and [b] only at the integer level;
    see [lx]. *)
let xor_cong (a a' b b' c: elem)
  : Lemma (requires c == a ^^ b /\ a == a' /\ b == b') (ensures c == a' ^^ b')
  = lx_is a b; lx_is a' b'

let xor_drop (a b c: elem)
  : Lemma (requires c == a ^^ b /\ b == 0) (ensures c == a)
  = lx_is a b; lx_zero a

(** A byte of a block, or zero off either end, so that the prefix xor can be
    written without a case split at every use. *)
unfold let byte0 (a: block) (i: int) : elem =
  if 0 <= i && i < blocklen then Seq.index a i else 0

(** The running xor of the four-byte lanes at and below [i], associated the
    way the three shifts and three xors below compute it. *)
let pfx (a: block) (i: nat) : elem =
  (byte0 a i ^^ byte0 a (i - 4)) ^^ (byte0 a (i - 8) ^^ byte0 a (i - 12))

let pfx_low (a: block) (i: nat { i < 4 }) : Lemma (pfx a i == Seq.index a i)
  = let x0 = byte0 a i in
    let x1 = byte0 a (i - 4) in
    let x2 = byte0 a (i - 8) in
    let x3 = byte0 a (i - 12) in
    lx_is x0 x1; lx_is x2 x3; lx_is (lx x0 x1) (lx x2 x3);
    lx_zero x0; lx_zero 0

(** The telescoping step: above the first lane the prefix xor is the byte
    itself xored with the prefix xor one lane down.  This is the whole reason
    the shape is worth computing -- it is exactly [ks_join_plain]'s
    equation. *)
let pfx_step (a: block) (i: nat { 4 <= i /\ i < blocklen })
  : Lemma (pfx a i == Seq.index a i ^^ pfx a (i - 4))
  = let x0 = byte0 a i in
    let x1 = byte0 a (i - 4) in
    let x2 = byte0 a (i - 8) in
    let x3 = byte0 a (i - 12) in
    let x4 = byte0 a (i - 16) in
    lx_is x0 x1; lx_is x2 x3; lx_is (lx x0 x1) (lx x2 x3);
    lx_is x1 x2; lx_is x3 x4; lx_is (lx x1 x2) (lx x3 x4);
    lx_is x0 (lx (lx x1 x2) (lx x3 x4));
    lx_zero x3; lx_assoc x1 x2 x3; lx_assoc x0 x1 (lx x2 x3)

(** Three shifts and three xors.  Shifting the argument rather than the
    running total is what makes this a prefix xor and not the identity: in
    GF(2) re-xoring a shifted copy of the *total* would cancel. *)
inline_for_extraction
let prefix_xor (k: Vec.t)
  : Pure Vec.t (requires True)
         (ensures fun r -> forall (i: nat). i < blocklen ==>
                             Seq.index (Vec.bv r) i == pfx (Vec.bv k) i)
  = let s1 = Vec.shift_left_bytes_4 k in
    let s2 = Vec.shift_left_bytes_4 s1 in
    let s3 = Vec.shift_left_bytes_4 s2 in
    Vec.vxor (Vec.vxor k s1) (Vec.vxor s2 s3)

(** A block whose lanes all agree, which is what the round term is. *)
let wper (a: block) : prop =
  forall (i: nat). 4 <= i /\ i < blocklen ==> Seq.index a i == Seq.index a (i - 4)

(** The two facts the join lemmas want, read off the round key
    [r = prefix_xor k ^ t]: in the bottom lane the prefix xor is nothing, and
    above it the round key telescopes because [t] repeats. *)
let round_low (k pb t r: block) (i: nat { i < 4 })
  : Lemma (requires Seq.index pb i == pfx k i /\
                    Seq.index r i == Seq.index pb i ^^ Seq.index t i)
          (ensures Seq.index r i == Seq.index k i ^^ Seq.index t i)
  = xor_cong (Seq.index pb i) (pfx k i)
             (Seq.index t i) (Seq.index t i) (Seq.index r i);
    pfx_low k i

let round_high (k pb t r: block) (i: nat { 4 <= i /\ i < blocklen })
  : Lemma (requires Seq.index pb i == pfx k i /\
                    Seq.index pb (i - 4) == pfx k (i - 4) /\
                    Seq.index t i == Seq.index t (i - 4) /\
                    Seq.index r i == Seq.index pb i ^^ Seq.index t i /\
                    Seq.index r (i - 4) ==
                      Seq.index pb (i - 4) ^^ Seq.index t (i - 4))
          (ensures Seq.index r i == Seq.index k i ^^ Seq.index r (i - 4))
  = pfx_step k i;
    let u = Seq.index k i in
    let v = pfx k (i - 4) in
    let w = Seq.index t i in
    xor_cong (Seq.index pb (i - 4)) v
             (Seq.index t (i - 4)) w (Seq.index r (i - 4));
    xor_cong (Seq.index pb i) (u ^^ v) w w (Seq.index r i);
    lx_is u v; lx_is (lx u v) w; lx_is v w; lx_is u (lx v w);
    lx_assoc u v w

(** Ground equations packed back into a quantifier.  The packing is a lemma
    of its own so that it runs in a context that has never seen [pfx]
    unfolded: sixteen copies of a four-term xor of conditionals is enough to
    make the solver spend its whole budget on the hypotheses. *)
let mk_low (k t r: block)
  : Lemma (requires Seq.index r 0 == Seq.index k 0 ^^ Seq.index t 0 /\
                    Seq.index r 1 == Seq.index k 1 ^^ Seq.index t 1 /\
                    Seq.index r 2 == Seq.index k 2 ^^ Seq.index t 2 /\
                    Seq.index r 3 == Seq.index k 3 ^^ Seq.index t 3)
          (ensures forall (i: nat). i < 4 ==>
                     Seq.index r i == Seq.index k i ^^ Seq.index t i)
  = ()

let mk_high (k r: block)
  : Lemma (requires Seq.index r 4 == Seq.index k 4 ^^ Seq.index r 0 /\
                    Seq.index r 5 == Seq.index k 5 ^^ Seq.index r 1 /\
                    Seq.index r 6 == Seq.index k 6 ^^ Seq.index r 2 /\
                    Seq.index r 7 == Seq.index k 7 ^^ Seq.index r 3 /\
                    Seq.index r 8 == Seq.index k 8 ^^ Seq.index r 4 /\
                    Seq.index r 9 == Seq.index k 9 ^^ Seq.index r 5 /\
                    Seq.index r 10 == Seq.index k 10 ^^ Seq.index r 6 /\
                    Seq.index r 11 == Seq.index k 11 ^^ Seq.index r 7 /\
                    Seq.index r 12 == Seq.index k 12 ^^ Seq.index r 8 /\
                    Seq.index r 13 == Seq.index k 13 ^^ Seq.index r 9 /\
                    Seq.index r 14 == Seq.index k 14 ^^ Seq.index r 10 /\
                    Seq.index r 15 == Seq.index k 15 ^^ Seq.index r 11)
          (ensures forall (i: nat). 4 <= i /\ i < blocklen ==>
                     Seq.index r i == Seq.index k i ^^ Seq.index r (i - 4))
  = ()

(** Both facts at every byte at once, for a round key [r = pb ^ t] whose
    [pb] is the prefix xor of [k]. *)
let round_all (k pb t r: block)
  : Lemma (requires
      (forall (i: nat). i < blocklen ==> Seq.index pb i == pfx k i) /\
      (forall (i: nat). i < blocklen ==>
         Seq.index r i == Seq.index pb i ^^ Seq.index t i) /\
      wper t)
    (ensures
      (forall (i: nat). i < 4 ==>
         Seq.index r i == Seq.index k i ^^ Seq.index t i) /\
      (forall (i: nat). 4 <= i /\ i < blocklen ==>
         Seq.index r i == Seq.index k i ^^ Seq.index r (i - 4)))
  = round_low k pb t r 0; round_low k pb t r 1;
    round_low k pb t r 2; round_low k pb t r 3;
    round_high k pb t r 4;
    round_high k pb t r 5;
    round_high k pb t r 6;
    round_high k pb t r 7;
    round_high k pb t r 8;
    round_high k pb t r 9;
    round_high k pb t r 10;
    round_high k pb t r 11;
    round_high k pb t r 12;
    round_high k pb t r 13;
    round_high k pb t r 14;
    round_high k pb t r 15;
    mk_low k t r;
    mk_high k r

(** The subword axiom is quantified over the word index; the key schedule
    wants it four times at literal byte offsets. *)
let subword_index (a: Vec.t) (i: nat { i < 4 })
  : Lemma (Seq.index (Vec.bv (Vec.subword a)) (8 + i) ==
           sbox (Seq.index (Vec.bv a) (12 + i)))
  = ()

(** The term added to every word of the round key.  At a multiple of the key
    length it is [RotWord (SubWord w)] plus the round constant; halfway
    through an AES-256 round key it is [SubWord w] alone.  Both have all four
    lanes equal, which is what [round_high] needs.  The two shapes are stated
    against the previous round key rather than against the [SubWord] result
    so that the rotation and the broadcast are discharged here, where the
    context is four vectors wide rather than a whole heap. *)

let is_rot_term (pv: Vec.t) (rc: S8.t) (t: block) : prop =
  Seq.index t 0 == sbox (Seq.index (Vec.bv pv) 13) ^^ S8.v rc /\
  Seq.index t 1 == sbox (Seq.index (Vec.bv pv) 14) /\
  Seq.index t 2 == sbox (Seq.index (Vec.bv pv) 15) /\
  Seq.index t 3 == sbox (Seq.index (Vec.bv pv) 12)

let is_sub_term (pv: Vec.t) (t: block) : prop =
  Seq.index t 0 == sbox (Seq.index (Vec.bv pv) 12) /\
  Seq.index t 1 == sbox (Seq.index (Vec.bv pv) 13) /\
  Seq.index t 2 == sbox (Seq.index (Vec.bv pv) 14) /\
  Seq.index t 3 == sbox (Seq.index (Vec.bv pv) 15)

(** The lanes of an xor agree if the lanes of both arguments do. *)
let wper_xor (a b: block) : Lemma (requires wper a /\ wper b)
                                  (ensures wper (xor_block a b)) = ()

inline_for_extraction
let round_term (mul: bool) (pv: Vec.t) (rc: S8.t)
  : r: Vec.t { wper (Vec.bv r) /\
               (mul ==> is_rot_term pv rc (Vec.bv r)) /\
               (~mul ==> is_sub_term pv (Vec.bv r)) }
  = let sw = Vec.subword pv in
    subword_index pv 0; subword_index pv 1;
    subword_index pv 2; subword_index pv 3;
    if mul then begin
      let u = Vec.bcast_rot sw in
      let v = Vec.word_bcast rc in
      wper_xor (Vec.bv u) (Vec.bv v);
      let r = Vec.vxor u v in
      xor_drop (Seq.index (Vec.bv u) 1) (Seq.index (Vec.bv v) 1) (Seq.index (Vec.bv r) 1);
      xor_drop (Seq.index (Vec.bv u) 2) (Seq.index (Vec.bv v) 2) (Seq.index (Vec.bv r) 2);
      xor_drop (Seq.index (Vec.bv u) 3) (Seq.index (Vec.bv v) 3) (Seq.index (Vec.bv r) 3);
      r
    end else Vec.bcast_sub sw

(** {2 The bridge to the join lemmas}

    The equations a register leaves behind are about its own sixteen bytes;
    the join lemmas want them about the expanded key.  The rewriting is done
    in lemmas rather than in assertions inside the Pulse function because
    there the context is a whole heap, four slprops and every byte of the
    key, and the solver spends its budget on the frame instead of on the
    arithmetic. *)

(** The four byte equations of a substitution step, gathered under the
    quantifier [ks_join_sub] states them with. *)
let sub_eqs_intro (s0 s1: Seq.seq elem) (b: nat) (kl: nat)
  : Lemma (requires
      kl + 4 <= b /\ b + 4 <= Seq.length s0 /\ b + 4 <= Seq.length s1 /\
      Seq.index s1 b == Seq.index s0 (b - kl) ^^ sbox (Seq.index s0 (b - 4)) /\
      Seq.index s1 (b + 1) == Seq.index s0 (b - kl + 1) ^^ sbox (Seq.index s0 (b - 3)) /\
      Seq.index s1 (b + 2) == Seq.index s0 (b - kl + 2) ^^ sbox (Seq.index s0 (b - 2)) /\
      Seq.index s1 (b + 3) == Seq.index s0 (b - kl + 3) ^^ sbox (Seq.index s0 (b - 1)))
    (ensures forall (j: nat). j < 4 ==> Seq.index s1 (b + j) ==
               Seq.index s0 (b - kl + j) ^^ sbox (Seq.index s0 (b - 4 + j)))
  = ()

#push-options "--z3rlimit 400"

(** The first word of the round key: the one the round term touches. *)
let block_step (v: variant) (key: Seq.lseq elem (keylen v))
               (vw0 vw1: Seq.seq S8.t) (b: nat) (mul: bool)
               (pv kv t r: block) (rc: elem)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 16 <= xkeylen v /\ b % 16 == 0 /\
      (mul <==> b % keylen v == 0) /\
      (~mul ==> keylen v > 24 /\ b % keylen v == 16) /\
      (mul ==> rc == rcon0 (b / keylen v)) /\
      (forall (j: nat). j < b ==>
         Seq.index (vals vw0) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 4 ==> Seq.index (vals vw1) (b + j) == Seq.index r j) /\
      (forall (j: nat). j < 4 ==>
         Seq.index pv (12 + j) == Seq.index (vals vw0) (b - 4 + j)) /\
      (forall (j: nat). j < 4 ==>
         Seq.index kv j == Seq.index (vals vw0) (b - keylen v + j)) /\
      (mul ==> (Seq.index t 0 == sbox (Seq.index pv 13) ^^ rc /\
                Seq.index t 1 == sbox (Seq.index pv 14) /\
                Seq.index t 2 == sbox (Seq.index pv 15) /\
                Seq.index t 3 == sbox (Seq.index pv 12))) /\
      (~mul ==> (Seq.index t 0 == sbox (Seq.index pv 12) /\
                 Seq.index t 1 == sbox (Seq.index pv 13) /\
                 Seq.index t 2 == sbox (Seq.index pv 14) /\
                 Seq.index t 3 == sbox (Seq.index pv 15))) /\
      (forall (j: nat). j < 4 ==>
         Seq.index r j == Seq.index kv j ^^ Seq.index t j))
    (ensures forall (j: nat). j < b + 4 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = mod16_mod4 b;
    if mul then begin
      xor_cong (sbox (Seq.index pv 13)) (sbox (Seq.index (vals vw0) (b - 3)))
               rc (rcon0 (b / keylen v)) (Seq.index t 0);
      xor_cong (Seq.index kv 0) (Seq.index (vals vw0) (b - keylen v))
               (Seq.index t 0)
               (sbox (Seq.index (vals vw0) (b - 3)) ^^ rcon0 (b / keylen v))
               (Seq.index r 0);
      xor_cong (Seq.index kv 1) (Seq.index (vals vw0) (b - keylen v + 1))
               (Seq.index t 1) (sbox (Seq.index (vals vw0) (b - 2))) (Seq.index r 1);
      xor_cong (Seq.index kv 2) (Seq.index (vals vw0) (b - keylen v + 2))
               (Seq.index t 2) (sbox (Seq.index (vals vw0) (b - 1))) (Seq.index r 2);
      xor_cong (Seq.index kv 3) (Seq.index (vals vw0) (b - keylen v + 3))
               (Seq.index t 3) (sbox (Seq.index (vals vw0) (b - 4))) (Seq.index r 3);
      ks_join_mul v key vw0 vw1 b
    end else begin
      xor_cong (Seq.index kv 0) (Seq.index (vals vw0) (b - keylen v))
               (Seq.index t 0) (sbox (Seq.index (vals vw0) (b - 4))) (Seq.index r 0);
      xor_cong (Seq.index kv 1) (Seq.index (vals vw0) (b - keylen v + 1))
               (Seq.index t 1) (sbox (Seq.index (vals vw0) (b - 3))) (Seq.index r 1);
      xor_cong (Seq.index kv 2) (Seq.index (vals vw0) (b - keylen v + 2))
               (Seq.index t 2) (sbox (Seq.index (vals vw0) (b - 2))) (Seq.index r 2);
      xor_cong (Seq.index kv 3) (Seq.index (vals vw0) (b - keylen v + 3))
               (Seq.index t 3) (sbox (Seq.index (vals vw0) (b - 1))) (Seq.index r 3);
      sub_eqs_intro (vals vw0) (vals vw1) b (keylen v);
      ks_join_sub v key vw0 vw1 b
    end

(** One telescoped word, as an equation between bytes of the expanded key. *)
let block_tele (v: variant) (vw0 vw1: Seq.seq S8.t) (b: nat)
               (kv r: block) (i: nat)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 16 <= xkeylen v /\ 4 <= i /\ i < 16 /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 16 ==> Seq.index (vals vw1) (b + j) == Seq.index r j) /\
      (forall (j: nat). j < 16 ==>
         Seq.index kv j == Seq.index (vals vw0) (b - keylen v + j)) /\
      Seq.index r i == Seq.index kv i ^^ Seq.index r (i - 4))
    (ensures Seq.index (vals vw1) (b + i) ==
             Seq.index (vals vw1) (b - keylen v + i) ^^
             Seq.index (vals vw1) (b + i - 4))
  = xor_cong (Seq.index kv i) (Seq.index (vals vw1) (b - keylen v + i))
             (Seq.index r (i - 4)) (Seq.index (vals vw1) (b + i - 4))
             (Seq.index r i)

(** A register loaded from [s] at [lo], read back one byte at a time.  The
    second offset is the same number written the way the join lemmas want
    it; keeping the rewrite here rather than in an assertion inside the Pulse
    function keeps [vals] and [Seq.slice] out of a query that already
    carries the heap. *)
let load_index (s: Seq.seq S8.t) (lo lo': nat) (x: Vec.t)
  : Lemma (requires lo + 16 <= Seq.length s /\ lo == lo' /\
                    Vec.vv x == Seq.slice s lo (lo + 16))
          (ensures forall (j: nat). j < 16 ==>
                     Seq.index (Vec.bv x) j == Seq.index (vals s) (lo' + j))
  = vals_slice s lo (lo + 16);
    slice_index (vals s) lo (lo + 16) 0; slice_index (vals s) lo (lo + 16) 1;
    slice_index (vals s) lo (lo + 16) 2; slice_index (vals s) lo (lo + 16) 3;
    slice_index (vals s) lo (lo + 16) 4; slice_index (vals s) lo (lo + 16) 5;
    slice_index (vals s) lo (lo + 16) 6; slice_index (vals s) lo (lo + 16) 7;
    slice_index (vals s) lo (lo + 16) 8; slice_index (vals s) lo (lo + 16) 9;
    slice_index (vals s) lo (lo + 16) 10; slice_index (vals s) lo (lo + 16) 11;
    slice_index (vals s) lo (lo + 16) 12; slice_index (vals s) lo (lo + 16) 13;
    slice_index (vals s) lo (lo + 16) 14; slice_index (vals s) lo (lo + 16) 15

let load_index4 (s: Seq.seq S8.t) (lo lo': nat) (x: Vec.t)
  : Lemma (requires lo + 16 <= Seq.length s /\ lo + 12 == lo' /\
                    Vec.vv x == Seq.slice s lo (lo + 16))
          (ensures forall (j: nat). j < 4 ==>
                     Seq.index (Vec.bv x) (12 + j) == Seq.index (vals s) (lo' + j))
  = vals_slice s lo (lo + 16);
    slice_index (vals s) lo (lo + 16) 12; slice_index (vals s) lo (lo + 16) 13;
    slice_index (vals s) lo (lo + 16) 14; slice_index (vals s) lo (lo + 16) 15

(** The round-constant side condition for a plain word, away from the
    quantified hypotheses about the key. *)
let grp_mod (v: variant) (b: nat) (d: nat)
  : Lemma (requires b % 16 == 0 /\ (d == 4 \/ d == 8 \/ d == 12) /\
                    (b % keylen v == 0 \/ (keylen v > 24 /\ b % keylen v == 16)))
          (ensures (b + d) % 4 == 0 /\ (b + d) % keylen v <> 0 /\
                   ~(keylen v > 24 /\ (b + d) % keylen v == 16))
  = mod16_mod4 b;
    mod_add_small (keylen v) b d

(** The four ground equations of one word packed into the quantifier
    [ks_join_plain] asks for. *)
let mk_join4 (v: variant) (vw1: Seq.seq S8.t) (b: nat)
  : Lemma (requires
      Seq.length vw1 == xkeylen v /\ keylen v <= b /\ b + 16 <= xkeylen v /\
      Seq.index (vals vw1) (b + 4) == Seq.index (vals vw1) (b + 4 - keylen v) ^^ Seq.index (vals vw1) (b + 0) /\
      Seq.index (vals vw1) (b + 5) == Seq.index (vals vw1) (b + 5 - keylen v) ^^ Seq.index (vals vw1) (b + 1) /\
      Seq.index (vals vw1) (b + 6) == Seq.index (vals vw1) (b + 6 - keylen v) ^^ Seq.index (vals vw1) (b + 2) /\
      Seq.index (vals vw1) (b + 7) == Seq.index (vals vw1) (b + 7 - keylen v) ^^ Seq.index (vals vw1) (b + 3))
    (ensures forall (j: nat). j < 4 ==>
               Seq.index (vals vw1) (b + 4 + j) ==
               Seq.index (vals vw1) (b + 4 - keylen v + j) ^^
               Seq.index (vals vw1) (b + 4 - 4 + j))
  = ()

(** The four ground equations of one word packed into the quantifier
    [ks_join_plain] asks for. *)
let mk_join8 (v: variant) (vw1: Seq.seq S8.t) (b: nat)
  : Lemma (requires
      Seq.length vw1 == xkeylen v /\ keylen v <= b /\ b + 16 <= xkeylen v /\
      Seq.index (vals vw1) (b + 8) == Seq.index (vals vw1) (b + 8 - keylen v) ^^ Seq.index (vals vw1) (b + 4) /\
      Seq.index (vals vw1) (b + 9) == Seq.index (vals vw1) (b + 9 - keylen v) ^^ Seq.index (vals vw1) (b + 5) /\
      Seq.index (vals vw1) (b + 10) == Seq.index (vals vw1) (b + 10 - keylen v) ^^ Seq.index (vals vw1) (b + 6) /\
      Seq.index (vals vw1) (b + 11) == Seq.index (vals vw1) (b + 11 - keylen v) ^^ Seq.index (vals vw1) (b + 7))
    (ensures forall (j: nat). j < 4 ==>
               Seq.index (vals vw1) (b + 8 + j) ==
               Seq.index (vals vw1) (b + 8 - keylen v + j) ^^
               Seq.index (vals vw1) (b + 8 - 4 + j))
  = ()

(** The four ground equations of one word packed into the quantifier
    [ks_join_plain] asks for. *)
let mk_join12 (v: variant) (vw1: Seq.seq S8.t) (b: nat)
  : Lemma (requires
      Seq.length vw1 == xkeylen v /\ keylen v <= b /\ b + 16 <= xkeylen v /\
      Seq.index (vals vw1) (b + 12) == Seq.index (vals vw1) (b + 12 - keylen v) ^^ Seq.index (vals vw1) (b + 8) /\
      Seq.index (vals vw1) (b + 13) == Seq.index (vals vw1) (b + 13 - keylen v) ^^ Seq.index (vals vw1) (b + 9) /\
      Seq.index (vals vw1) (b + 14) == Seq.index (vals vw1) (b + 14 - keylen v) ^^ Seq.index (vals vw1) (b + 10) /\
      Seq.index (vals vw1) (b + 15) == Seq.index (vals vw1) (b + 15 - keylen v) ^^ Seq.index (vals vw1) (b + 11))
    (ensures forall (j: nat). j < 4 ==>
               Seq.index (vals vw1) (b + 12 + j) ==
               Seq.index (vals vw1) (b + 12 - keylen v + j) ^^
               Seq.index (vals vw1) (b + 12 - 4 + j))
  = ()

(** The other three words, which are plain prefix xors.  One lemma per word
    offset: the join lemma's quantified premise has to be rebuilt from four
    ground equations, and doing all three at once does not close. *)
let block_grp4 (v: variant) (key: Seq.lseq elem (keylen v))
                (vw0 vw1: Seq.seq S8.t) (b: nat) (kv r: block)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 16 <= xkeylen v /\ b % 16 == 0 /\
      (b % keylen v == 0 \/ (keylen v > 24 /\ b % keylen v == 16)) /\
      (forall (j: nat). j < b + 4 ==>
         Seq.index (vals vw1) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 16 ==> Seq.index (vals vw1) (b + j) == Seq.index r j) /\
      (forall (j: nat). j < 16 ==>
         Seq.index kv j == Seq.index (vals vw0) (b - keylen v + j)) /\
      (forall (j: nat). 4 <= j /\ j < 16 ==>
         Seq.index r j == Seq.index kv j ^^ Seq.index r (j - 4)))
    (ensures forall (j: nat). j < b + 4 + 4 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = block_tele v vw0 vw1 b kv r 4;
    block_tele v vw0 vw1 b kv r 5;
    block_tele v vw0 vw1 b kv r 6;
    block_tele v vw0 vw1 b kv r 7;
    grp_mod v b 4;
    mk_join4 v vw1 b;
    ks_join_plain v key vw1 vw1 (b + 4)

let block_grp8 (v: variant) (key: Seq.lseq elem (keylen v))
                (vw0 vw1: Seq.seq S8.t) (b: nat) (kv r: block)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 16 <= xkeylen v /\ b % 16 == 0 /\
      (b % keylen v == 0 \/ (keylen v > 24 /\ b % keylen v == 16)) /\
      (forall (j: nat). j < b + 8 ==>
         Seq.index (vals vw1) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 16 ==> Seq.index (vals vw1) (b + j) == Seq.index r j) /\
      (forall (j: nat). j < 16 ==>
         Seq.index kv j == Seq.index (vals vw0) (b - keylen v + j)) /\
      (forall (j: nat). 4 <= j /\ j < 16 ==>
         Seq.index r j == Seq.index kv j ^^ Seq.index r (j - 4)))
    (ensures forall (j: nat). j < b + 8 + 4 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = block_tele v vw0 vw1 b kv r 8;
    block_tele v vw0 vw1 b kv r 9;
    block_tele v vw0 vw1 b kv r 10;
    block_tele v vw0 vw1 b kv r 11;
    grp_mod v b 8;
    mk_join8 v vw1 b;
    ks_join_plain v key vw1 vw1 (b + 8)

let block_grp12 (v: variant) (key: Seq.lseq elem (keylen v))
                (vw0 vw1: Seq.seq S8.t) (b: nat) (kv r: block)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 16 <= xkeylen v /\ b % 16 == 0 /\
      (b % keylen v == 0 \/ (keylen v > 24 /\ b % keylen v == 16)) /\
      (forall (j: nat). j < b + 12 ==>
         Seq.index (vals vw1) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 16 ==> Seq.index (vals vw1) (b + j) == Seq.index r j) /\
      (forall (j: nat). j < 16 ==>
         Seq.index kv j == Seq.index (vals vw0) (b - keylen v + j)) /\
      (forall (j: nat). 4 <= j /\ j < 16 ==>
         Seq.index r j == Seq.index kv j ^^ Seq.index r (j - 4)))
    (ensures forall (j: nat). j < b + 12 + 4 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = block_tele v vw0 vw1 b kv r 12;
    block_tele v vw0 vw1 b kv r 13;
    block_tele v vw0 vw1 b kv r 14;
    block_tele v vw0 vw1 b kv r 15;
    grp_mod v b 12;
    mk_join12 v vw1 b;
    ks_join_plain v key vw1 vw1 (b + 12)

let block_rest (v: variant) (key: Seq.lseq elem (keylen v))
               (vw0 vw1: Seq.seq S8.t) (b: nat) (kv r: block)
  : Lemma (requires
      Seq.length vw0 == xkeylen v /\ Seq.length vw1 == xkeylen v /\
      keylen v <= b /\ b + 16 <= xkeylen v /\ b % 16 == 0 /\
      (b % keylen v == 0 \/ (keylen v > 24 /\ b % keylen v == 16)) /\
      (forall (j: nat). j < b + 4 ==>
         Seq.index (vals vw1) j == Seq.index (key_expansion v key) j) /\
      (forall (j: nat). j < b ==> Seq.index (vals vw1) j == Seq.index (vals vw0) j) /\
      (forall (j: nat). j < 16 ==> Seq.index (vals vw1) (b + j) == Seq.index r j) /\
      (forall (j: nat). j < 16 ==>
         Seq.index kv j == Seq.index (vals vw0) (b - keylen v + j)) /\
      (forall (j: nat). 4 <= j /\ j < 16 ==>
         Seq.index r j == Seq.index kv j ^^ Seq.index r (j - 4)))
    (ensures forall (j: nat). j < b + 16 ==>
               Seq.index (vals vw1) j == Seq.index (key_expansion v key) j)
  = block_grp4 v key vw0 vw1 b kv r;
    block_grp8 v key vw0 vw1 b kv r;
    block_grp12 v key vw0 vw1 b kv r

#pop-options

#push-options "--z3rlimit 800"

(** One round key.  [prev] is the sixteen bytes just below [b], [kb] the
    sixteen bytes [keylen] below it -- for AES-128 the same register, for
    AES-256 the one before that -- and the store covers a whole round key, so
    the prefix property advances sixteen bytes at a time rather than four. *)

(** A round key from the one below it: the prefix xor of [k] plus the round
    term.  Three [pslldq]s, four [pxor]s, no memory. *)
inline_for_extraction
let ks_round_vec (k t: Vec.t)
  : Pure Vec.t
      (requires wper (Vec.bv t))
      (ensures fun r ->
        (forall (i: nat). i < 4 ==>
           Seq.index (Vec.bv r) i ==
           Seq.index (Vec.bv k) i ^^ Seq.index (Vec.bv t) i) /\
        (forall (i: nat). 4 <= i /\ i < blocklen ==>
           Seq.index (Vec.bv r) i ==
           Seq.index (Vec.bv k) i ^^ Seq.index (Vec.bv r) (i - 4)))
  = let pb = prefix_xor k in
    let r = Vec.vxor pb t in
    round_all (Vec.bv k) (Vec.bv pb) (Vec.bv t) (Vec.bv r);
    r

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))"]
inline_for_extraction
fn ks_block_ni ([@@@FStar.Attributes.monomorphize] p: params)
               (w: A.array S8.t) (b: SZ.t) (rc: S8.t)
               (#key: erased (Seq.lseq elem (keylen p.pv)))
               (#vw0: erased (Seq.seq S8.t))
requires A.pts_to w vw0 ** pure (
  Seq.length vw0 == xkeylen p.pv /\
  keylen p.pv <= SZ.v b /\ SZ.v b + 16 <= xkeylen p.pv /\ SZ.v b % 16 == 0 /\
  keylen p.pv % 16 == 0 /\
  (SZ.v b % keylen p.pv == 0 ==> S8.v rc == rcon0 (SZ.v b / keylen p.pv)) /\
  (forall (j: nat). j < SZ.v b ==>
     Seq.index (vals vw0) j == Seq.index (key_expansion p.pv key) j))
ensures exists* (vw1: Seq.seq S8.t). A.pts_to w vw1 ** pure (
  Seq.length vw1 == xkeylen p.pv /\ SZ.v b + 16 <= xkeylen p.pv /\
  (forall (j: nat). j < SZ.v b + 16 ==>
     Seq.index (vals vw1) j == Seq.index (key_expansion p.pv key) j))
{
  A.pts_to_len w;
  mod16_split (SZ.v b);
  let back = SZ.sub b p.pkeylen;
  let prev = SZ.sub b 16sz;
  let b2 = SZ.add b 16sz;
  let back2 = SZ.add back 16sz;
  let m = SZ.rem b p.pkeylen;
  let mul = (m = 0sz);

  (* Everything the rest of the body needs about the offsets, asserted here
     where the context is still three values wide. *)
  assert (pure (SZ.v m == SZ.v b % keylen p.pv));
  assert (pure (mul <==> SZ.v b % keylen p.pv == 0));
  assert (pure (~mul ==> keylen p.pv > 24 /\ SZ.v b % keylen p.pv == 16));
  assert (pure (S8.v rc < pow2 8));
  assert (pure (SZ.v b2 == SZ.v b + 16 /\ SZ.v back2 == SZ.v back + 16 /\
                SZ.v prev + 16 == SZ.v b /\ SZ.v back + 16 <= SZ.v b /\
                SZ.v b2 <= Seq.length vw0));
  assert (pure (Seq.length (Seq.slice vw0 (SZ.v prev) (SZ.v b)) == 16 /\
                Seq.length (Seq.slice vw0 (SZ.v back) (SZ.v back2)) == 16 /\
                Seq.length (Seq.slice vw0 (SZ.v b) (SZ.v b2)) == 16));

  (* The word the round term is made of, and the round key it extends. *)
  let pb = Sub.sub w prev b;
  let pv = Vec.load pb #(as_blk (Seq.slice vw0 (SZ.v prev) (SZ.v b)));
  Sub.unsub_id w (SZ.v prev) (SZ.v b) pb;

  let kb = Sub.sub w back back2;
  let kv = Vec.load kb #(as_blk (Seq.slice vw0 (SZ.v back) (SZ.v back2)));
  Sub.unsub_id w (SZ.v back) (SZ.v back2) kb;

  let t = round_term mul pv rc;
  let r = ks_round_vec kv t;

  let ob = Sub.sub w b b2;
  Vec.store ob r #(as_blk (Seq.slice vw0 (SZ.v b) (SZ.v b2)));
  Sub.unsub w (SZ.v b) (SZ.v b2) ob;
  with vw1. assert A.pts_to w vw1;
  A.pts_to_len w;

  (* [vw1] is [vw0] with the round key written in, so every byte below [b]
     is untouched and the sixteen new ones are the register's. *)
  assert (pure (forall (j: nat). j < SZ.v b ==>
                  Seq.index (vals vw1) j == Seq.index (vals vw0) j));
  assert (pure (forall (j: nat). j < 16 ==>
                  Seq.index (vals vw1) (SZ.v b + j) == Seq.index (Vec.bv r) j));
  load_index4 vw0 (SZ.v prev) (SZ.v b - 4) pv;
  load_index vw0 (SZ.v back) (SZ.v b - keylen p.pv) kv;
  block_step p.pv key vw0 vw1 (SZ.v b) mul
             (Vec.bv pv) (Vec.bv kv) (Vec.bv t) (Vec.bv r) (S8.v rc);
  block_rest p.pv key vw0 vw1 (SZ.v b) (Vec.bv kv) (Vec.bv r);
  assert (pure (Seq.length vw1 == xkeylen p.pv));
  assert (pure (forall (j: nat). j < SZ.v b + 16 ==>
                  Seq.index (vals vw1) j == Seq.index (key_expansion p.pv key) j));
}


(** The whole schedule, a round key at a time, with the round constant
    carried in a register exactly as the scalar loop carries it. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))"]
fn ks_loop_ni ([@@@FStar.Attributes.monomorphize] p: params)
              (w: A.array S8.t)
              (#key: erased (Seq.lseq elem (keylen p.pv)))
              (#vw0: erased (Seq.seq S8.t))
requires A.pts_to w vw0 ** pure (
  Seq.length vw0 == xkeylen p.pv /\
  (forall (j: nat). j < keylen p.pv ==>
     Seq.index (vals vw0) j == Seq.index (key_expansion p.pv key) j))
ensures exists* (vw1: Seq.seq S8.t). A.pts_to w vw1 ** pure (
  Seq.length vw1 == xkeylen p.pv /\ vals vw1 == key_expansion p.pv key)
{
  A.pts_to_len w;
  xkeylen_mod16 p.pv;
  let mut b = p.pkeylen;
  rcon_init (keylen p.pv);
  let mut rc = S8.classify 1uy;
  while (let vb = !b; SZ.lt vb p.pxkeylen)
  invariant exists* (vb: SZ.t) (vrc: S8.t) (vw: Seq.seq S8.t).
    pts_to b vb ** pts_to rc vrc ** A.pts_to w vw **
    pure (keylen p.pv <= SZ.v vb /\ SZ.v vb <= xkeylen p.pv /\ SZ.v vb % 16 == 0 /\
          Seq.length vw == xkeylen p.pv /\
          S8.v vrc == rcon0 (rcidx (SZ.v vb) (keylen p.pv)) /\
          (forall (j: nat). j < SZ.v vb ==>
             Seq.index (vals vw) j == Seq.index (key_expansion p.pv key) j))
  decreases (xkeylen p.pv - SZ.v (!b))
  {
    let vb = !b;
    let vrc = !rc;
    mul16_gap (SZ.v vb) (xkeylen p.pv);
    rcon_prep p.pv (SZ.v vb) (S8.v vrc);
    ks_block_ni p w vb vrc #key;
    let m = SZ.rem vb p.pkeylen;
    if (m = 0sz) {
      let nrc = xtime_impl vrc;
      rcon_bump16 p.pv (SZ.v vb) (S8.v vrc) (S8.v nrc);
      rc := nrc;
      b := SZ.add vb 16sz;
    } else {
      rcon_keep16 p.pv (SZ.v vb);
      b := SZ.add vb 16sz;
    }
  };
  let nb = !b;
  with vw. assert A.pts_to w vw;
  ks_done p.pv key vw (SZ.v nb);
  A.pts_to_len w;
}

#pop-options

(** The portable driver: one word at a time, through a sixteen-byte scratch
    block that [AESKEYGENASSIST] or the software S-box writes into. *)

fn ks_loop_scalar ([@@@FStar.Attributes.monomorphize] p: params)
                  (w: A.array S8.t)
                  (#key: erased (Seq.lseq elem (keylen p.pv)))
                  (#vw0: erased (Seq.seq S8.t))
requires A.pts_to w vw0 ** pure (
  Seq.length vw0 == xkeylen p.pv /\
  (forall (j: nat). j < keylen p.pv ==>
     Seq.index (vals vw0) j == Seq.index (key_expansion p.pv key) j))
ensures exists* (vw1: Seq.seq S8.t). A.pts_to w vw1 ** pure (
  Seq.length vw1 == xkeylen p.pv /\ vals vw1 == key_expansion p.pv key)
{
  A.pts_to_len w;
  let mut b = p.pkeylen;
  rcon_init (keylen p.pv);
  let mut rc = S8.classify 1uy;
  let z = S8.zero;
  let mut sb = [| z; 16sz |];
  Mem.track sb;
  A.pts_to_len sb;
  while (let vb = !b; SZ.lt vb p.pxkeylen)
  invariant exists* (vb: SZ.t) (vrc: S8.t) (vw: Seq.seq S8.t) (vsb: Seq.seq S8.t).
    pts_to b vb ** pts_to rc vrc ** A.pts_to w vw ** A.pts_to sb vsb **
    pure (keylen p.pv <= SZ.v vb /\ SZ.v vb <= xkeylen p.pv /\ SZ.v vb % 4 == 0 /\
          Seq.length vsb == blocklen /\
          Seq.length vw == xkeylen p.pv /\
          S8.v vrc == rcon0 (rcidx (SZ.v vb) (keylen p.pv)) /\
          (forall (j: nat). j < SZ.v vb ==>
             Seq.index (vals vw) j == Seq.index (key_expansion p.pv key) j))
  decreases (xkeylen p.pv - SZ.v (!b))
  {
    let vb = !b;
    let vrc = !rc;
    rcon_prep p.pv (SZ.v vb) (S8.v vrc);
    ks_word_impl p w sb vb vrc #key;
    let m = SZ.rem vb p.pkeylen;
    if (m = 0sz) {
      let nrc = xtime_impl vrc;
      rcon_bump p.pv (SZ.v vb) (S8.v vrc) (S8.v nrc);
      rc := nrc;
      b := SZ.add vb 4sz;
    } else {
      rcon_keep p.pv (SZ.v vb);
      b := SZ.add vb 4sz;
    }
  };
  let nb = !b;
  with vw. assert A.pts_to w vw;
  ks_done p.pv key vw (SZ.v nb);
  A.pts_to_len w;
  Mem.wipe sb 16sz;
}

(** The expanded key, written into a caller-provided slice of [xkeylen]
    bytes: the key first, then one word at a time. *)

fn key_expansion_impl ([@@@FStar.Attributes.monomorphize] p: params)
                      (w: A.array S8.t) (key: A.array S8.t)
                      (#vw0: erased (Seq.seq S8.t))
                      (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to w vw0 ** A.pts_to key #pk vkey ** pure (
  Seq.length vw0 == xkeylen p.pv /\ Seq.length vkey == keylen p.pv)
ensures exists* (vw1: Seq.seq S8.t). A.pts_to w vw1 ** A.pts_to key #pk vkey ** pure (
  Seq.length vw1 == xkeylen p.pv /\ Seq.length vkey == keylen p.pv /\
  vals vw1 == key_expansion p.pv (vals vkey))
{
  A.pts_to_len w;
  A.pts_to_len key;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc p.pkeylen)
  invariant exists* (vc: SZ.t) (vw: Seq.seq S8.t).
    pts_to c vc ** A.pts_to w vw ** A.pts_to key #pk vkey **
    pure (SZ.v vc <= keylen p.pv /\ Seq.length vw == xkeylen p.pv /\
          Seq.length vkey == keylen p.pv /\
          (forall (j: nat). j < SZ.v vc ==>
             Seq.index (vals vw) j == Seq.index (vals vkey) j))
  decreases (keylen p.pv - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(key.(vc));
    with vw. assert A.pts_to w vw;
    vals_upd vw (SZ.v vc) x;
    A.((w.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  let nc = !c;
  with vw. assert A.pts_to w vw;
  key_prefix p.pv (vals vkey) vw (SZ.v nc);

  if Vec.supported () {
    ks_loop_ni p w #(hide (vals vkey));
  } else {
    ks_loop_scalar p w #(hide (vals vkey));
  }
}

#pop-options
