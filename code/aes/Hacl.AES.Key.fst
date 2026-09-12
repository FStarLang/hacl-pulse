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

let rcidx_step_other (b: nat) (n: pos)
  : Lemma (requires n <= b /\ b % n <> 0 /\ b % 4 == 0 /\ n % 4 == 0)
          (ensures rcidx (b + 4) n == rcidx b n)
  = let q = b / n in
    let r = b % n in
    Math.lemma_div_mod b n;
    mod4_mod b n;
    mul4_gap r n;
    Math.lemma_div_plus (r + 4) q n;
    Math.lemma_mod_plus (r + 4) q n;
    if r + 4 = n then begin
      Math.lemma_div_plus 0 (q + 1) n;
      Math.lemma_mod_plus 0 (q + 1) n
    end else begin
      Math.small_div (r + 4) n;
      Math.small_mod (r + 4) n
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

#push-options "--fuel 1 --ifuel 1"
let ks_step_mul (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat) (j: nat { j < 4 })
  : Lemma (requires nk v <= i /\ i % nk v == 0)
          (ensures 1 <= i / nk v /\
            Seq.index (ks_word v key i) j ==
              Seq.index (ks_word v key (i - nk v)) j ^^
              (if j = 0 then sbox (Seq.index (ks_word v key (i - 1)) 1) ^^ rcon (i / nk v)
               else sbox (Seq.index (ks_word v key (i - 1)) ((j + 1) % 4))))
  = Math.lemma_div_mod i (nk v);
    xor_zero (sbox (Seq.index (ks_word v key (i - 1)) ((j + 1) % 4)))

let ks_step_sub (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat) (j: nat { j < 4 })
  : Lemma (requires nk v <= i /\ nk v > 6 /\ i % nk v == 4)
          (ensures Seq.index (ks_word v key i) j ==
                   Seq.index (ks_word v key (i - nk v)) j ^^
                   sbox (Seq.index (ks_word v key (i - 1)) j))
  = ()

let ks_step_plain (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat) (j: nat { j < 4 })
  : Lemma (requires nk v <= i /\ i % nk v <> 0 /\ ~(nk v > 6 /\ i % nk v == 4))
          (ensures Seq.index (ks_word v key i) j ==
                   Seq.index (ks_word v key (i - nk v)) j ^^
                   Seq.index (ks_word v key (i - 1)) j)
  = ()

#pop-options

(** {2 Joining a step to the prefix}

    [b] is the byte offset of the word being written.  Each lemma says that a
    slice which agreed with [key_expansion] below [b], and whose four new
    bytes satisfy the equations of one step, agrees with it below [b + 4]. *)

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
  = let i = b / 4 in
    Math.lemma_div_mod b 4;
    assert (4 * i == b);
    rcidx_at_mul b (keylen v);
    rcon0_pos (b / keylen v);
    word_to_byte i (nk v);
    ks_expand_at v key (i - nk v) 0; ks_expand_at v key (i - nk v) 1;
    ks_expand_at v key (i - nk v) 2; ks_expand_at v key (i - nk v) 3;
    ks_expand_at v key (i - 1) 0; ks_expand_at v key (i - 1) 1;
    ks_expand_at v key (i - 1) 2; ks_expand_at v key (i - 1) 3;
    ks_expand_at v key i 0; ks_expand_at v key i 1;
    ks_expand_at v key i 2; ks_expand_at v key i 3;
    ks_step_mul v key i 0; ks_step_mul v key i 1;
    ks_step_mul v key i 2; ks_step_mul v key i 3

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
  = let i = b / 4 in
    Math.lemma_div_mod b 4;
    assert (4 * i == b);
    word_to_byte i (nk v);
    ks_expand_at v key (i - nk v) 0; ks_expand_at v key (i - nk v) 1;
    ks_expand_at v key (i - nk v) 2; ks_expand_at v key (i - nk v) 3;
    ks_expand_at v key (i - 1) 0; ks_expand_at v key (i - 1) 1;
    ks_expand_at v key (i - 1) 2; ks_expand_at v key (i - 1) 3;
    ks_expand_at v key i 0; ks_expand_at v key i 1;
    ks_expand_at v key i 2; ks_expand_at v key i 3;
    ks_step_sub v key i 0; ks_step_sub v key i 1;
    ks_step_sub v key i 2; ks_step_sub v key i 3

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
  = let i = b / 4 in
    Math.lemma_div_mod b 4;
    assert (4 * i == b);
    word_to_byte i (nk v);
    ks_expand_at v key (i - nk v) 0; ks_expand_at v key (i - nk v) 1;
    ks_expand_at v key (i - nk v) 2; ks_expand_at v key (i - nk v) 3;
    ks_expand_at v key (i - 1) 0; ks_expand_at v key (i - 1) 1;
    ks_expand_at v key (i - 1) 2; ks_expand_at v key (i - 1) 3;
    ks_expand_at v key i 0; ks_expand_at v key i 1;
    ks_expand_at v key i 2; ks_expand_at v key i 3;
    ks_step_plain v key i 0; ks_step_plain v key i 1;
    ks_step_plain v key i 2; ks_step_plain v key i 3

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
                (w: A.array S8.t) (b: SZ.t) (rc: S8.t)
                (#key: erased (Seq.lseq elem (keylen p.pv)))
                (#vw0: erased (Seq.seq S8.t))
requires A.pts_to w vw0 ** pure (
  Seq.length vw0 == xkeylen p.pv /\
  keylen p.pv <= SZ.v b /\ SZ.v b + 4 <= xkeylen p.pv /\ SZ.v b % 4 == 0 /\
  (SZ.v b % keylen p.pv == 0 ==> S8.v rc == rcon0 (SZ.v b / keylen p.pv)) /\
  (forall (j: nat). j < SZ.v b ==>
     Seq.index (vals vw0) j == Seq.index (key_expansion p.pv key) j))
ensures exists* (vw1: Seq.seq S8.t). A.pts_to w vw1 ** pure (
  Seq.length vw1 == xkeylen p.pv /\ SZ.v b + 4 <= xkeylen p.pv /\
  (forall (j: nat). j < SZ.v b + 4 ==>
     Seq.index (vals vw1) j == Seq.index (key_expansion p.pv key) j))
{
  A.pts_to_len w;
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
    let t0 = bxor (sbox_impl p1) rc;
    let t1 = sbox_impl p2;
    let t2 = sbox_impl p3;
    let t3 = sbox_impl p0;
    A.((w.(b) <- bxor a0 t0));
    A.((w.(SZ.add b 1sz) <- bxor a1 t1));
    A.((w.(SZ.add b 2sz) <- bxor a2 t2));
    A.((w.(SZ.add b 3sz) <- bxor a3 t3));
    with vw1. assert A.pts_to w vw1;
    ks_join_mul p.pv key vw0 vw1 (SZ.v b);
    A.pts_to_len w;
  } else {
    if (SZ.gt p.pkeylen 24sz && m = 16sz) {
      A.((w.(b) <- bxor a0 (sbox_impl p0)));
      A.((w.(SZ.add b 1sz) <- bxor a1 (sbox_impl p1)));
      A.((w.(SZ.add b 2sz) <- bxor a2 (sbox_impl p2)));
      A.((w.(SZ.add b 3sz) <- bxor a3 (sbox_impl p3)));
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

  let mut b = p.pkeylen;
  rcon_init (keylen p.pv);
  let mut rc = S8.classify 1uy;
  while (let vb = !b; SZ.lt vb p.pxkeylen)
  invariant exists* (vb: SZ.t) (vrc: S8.t) (vw: Seq.seq S8.t).
    pts_to b vb ** pts_to rc vrc ** A.pts_to w vw ** A.pts_to key #pk vkey **
    pure (keylen p.pv <= SZ.v vb /\ SZ.v vb <= xkeylen p.pv /\ SZ.v vb % 4 == 0 /\
          Seq.length vw == xkeylen p.pv /\ Seq.length vkey == keylen p.pv /\
          S8.v vrc == rcon0 (rcidx (SZ.v vb) (keylen p.pv)) /\
          (forall (j: nat). j < SZ.v vb ==>
             Seq.index (vals vw) j == Seq.index (key_expansion p.pv (vals vkey)) j))
  decreases (xkeylen p.pv - SZ.v (!b))
  {
    let vb = !b;
    let vrc = !rc;
    rcon_prep p.pv (SZ.v vb) (S8.v vrc);
    ks_word_impl p w vb vrc #(hide (vals vkey));
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
  ks_done p.pv (vals vkey) vw (SZ.v nb);
  A.pts_to_len w;
}

#pop-options
