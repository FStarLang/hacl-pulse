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

(** Reading and writing a big-endian machine word inside a byte slice.

    One loop each, generic in the width.  Custard specializes them per
    instance, so the generated C is the usual straight-line shift-and-or once
    the trip count is a constant. *)
module Hacl.Impl.Bytes

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module UInt = FStar.UInt
module D = Hacl.Secret.Declassify

(* Nothing below needs to unfold a recursive definition or invert a data
   type implicitly: every such step is an explicit lemma call. *)
#set-options "--fuel 0 --ifuel 0"

(** [be_nat] of a prefix of a window is [be_nat] of the corresponding prefix of
    the underlying sequence: the window is only there to name an offset. *)
let slice_prefix (s: Seq.seq S8.t) (off: nat) (n: nat { off + n <= Seq.length s }) (k: nat { k <= n })
  : Lemma (Seq.slice (Seq.slice s off (off + n)) 0 k == Seq.slice s off (off + k))
  = Seq.lemma_eq_intro (Seq.slice (Seq.slice s off (off + n)) 0 k) (Seq.slice s off (off + k))

(** The accumulator after [k] of [n] bytes is below [pow2 (8k)], so shifting it
    up by one more byte cannot overflow a word of [8n] bits. *)
let acc_fits (#t: Type0) {| word t |} (a: t) (s: Seq.seq S8.t) (k: nat { k < bytes #t })
  : Lemma (requires v a == be_nat s /\ Seq.length s == k)
          (ensures v a * 256 < pow2 (bits #t))
  = be_nat_bound s;
    Math.pow2_le_compat (bits #t - 8) (8 * k);
    Math.pow2_plus (bits #t - 8) 8


(** The original one-byte-per-iteration loops, kept as the fallback for a
    width that is neither four nor eight bytes.  Both instances of [word] are
    one of those two, so nothing reaches these; they are here so that the
    code does not depend on which instances happen to exist. *)
let slice_suffix (s: Seq.seq S8.t) (off: nat) (n: nat { off + n <= Seq.length s }) (k: nat { k <= n })
  : Lemma (Seq.slice (Seq.slice s off (off + n)) k n == Seq.slice s (off + k) (off + n))
  = Seq.lemma_eq_intro (Seq.slice (Seq.slice s off (off + n)) k n) (Seq.slice s (off + k) (off + n))

let acc_fits_le (#t: Type0) {| word t |} (a: t) (s: Seq.seq S8.t) (k: nat { k < bytes #t })
  : Lemma (requires v a == le_nat s /\ Seq.length s == k)
          (ensures v a * 256 < pow2 (bits #t))
  = le_nat_bound s;
    Math.pow2_le_compat (bits #t - 8) (8 * k);
    Math.pow2_plus (bits #t - 8) 8

(** The empty window holds zero, either way round. *)
#push-options "--fuel 1"
let nat_empty (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == 0) (ensures be_nat s == 0 /\ le_nat s == 0)
  = ()
#pop-options

(** [bytes] really is the width in bytes; stated once so that the Pulse
    checks of postconditions mentioning [bytes] need no division reasoning. *)
let bytes_ok (#t: Type0) {| w: word t |}
  : Lemma (bits #t / 8 > 0 /\ (bits #t / 8) * 8 == bits #t)
  = ()

(** The byte offsets in [store_be]'s postcondition are natural numbers. *)
let be_offsets_nat (#t: Type0) {| w: word t |}
  : Lemma (forall (k: nat). {:pattern (pow2 (8 * (bytes #t - 1 - k)))}
             k < bytes #t ==> 8 * (bytes #t - 1 - k) >= 0)
  = ()

fn load_be_loop (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
           (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + bytes #t <= Seq.length vb /\
              v r == be_nat (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let z: t = zero #t #w;
  let mut acc = z;
  let mut j = 0sz;
  slice_prefix vb (SZ.v off) (bytes #t) 0;
  nat_empty (Seq.slice vb (SZ.v off) (SZ.v off));
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (a: t).
    pts_to j vj ** pts_to acc a ** A.pts_to b #p vb **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          v a == be_nat (Seq.slice vb (SZ.v off) (SZ.v off + SZ.v vj)))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let byte = A.(b.(SZ.add off vj));
    let a = !acc;
    acc_fits a (Seq.slice vb (SZ.v off) (SZ.v off + SZ.v vj)) (SZ.v vj);
    load_step a byte;
    slice_prefix vb (SZ.v off) (bytes #t) (SZ.v vj);
    slice_prefix vb (SZ.v off) (bytes #t) (SZ.v vj + 1);
    be_nat_snoc (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)) (SZ.v vj);
    acc := logor #t (shift_left a 8ul) (of_byte byte);
    j := SZ.add vj 1sz;
  };
  !acc
}

(** One step of [load_le_loop]'s invariant, stated over plain numbers. *)
let load_le_inv_step (s: Seq.seq S8.t) (off n j: nat) (a r: int)
  : Lemma (requires off + n <= Seq.length s /\ j < n /\
                    a == le_nat (Seq.slice s (off + n - j) (off + n)) /\
                    r == a * 256 + S8.v (Seq.index s (off + n - (j + 1))))
          (ensures r == le_nat (Seq.slice s (off + n - (j + 1)) (off + n)))
  = let w = Seq.slice s off (off + n) in
    let k : nat = n - j - 1 in
    assert (off + (k + 1) == off + n - j /\ off + k == off + n - (j + 1));
    slice_suffix s off n (k + 1);
    slice_suffix s off n k;
    le_nat_cons w k;
    assert (Seq.index w k == Seq.index s (off + n - (j + 1)))

fn load_le_loop (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
           (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + bytes #t <= Seq.length vb /\
              v r == le_nat (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let z: t = zero #t #w;
  let mut acc = z;
  let mut j = 0sz;
  slice_suffix vb (SZ.v off) (bytes #t) (bytes #t);
  nat_empty (Seq.slice vb (SZ.v off + SZ.v n) (SZ.v off + SZ.v n));
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (a: t).
    pts_to j vj ** pts_to acc a ** A.pts_to b #p vb **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          v a == le_nat (Seq.slice vb (SZ.v off + SZ.v n - SZ.v vj) (SZ.v off + SZ.v n)))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let pos = SZ.sub (SZ.add off n) (SZ.add vj 1sz);
    let byte = A.(b.(pos));
    let a = !acc;
    acc_fits_le a (Seq.slice vb (SZ.v off + SZ.v n - SZ.v vj) (SZ.v off + SZ.v n)) (SZ.v vj);
    load_step a byte;
    load_le_inv_step vb (SZ.v off) (SZ.v n) (SZ.v vj) (v a)
      (v (logor #t (shift_left a 8ul) (of_byte byte)));
    acc := logor #t (shift_left a 8ul) (of_byte byte);
    j := SZ.add vj 1sz;
  };
  !acc
}


#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** The arithmetic behind {!load_be4}: four bytes placed at offsets 24, 16, 8
    and 0 and merged left to right.  Every machine value the body computes is
    a parameter, and the equations that relate them are hypotheses, so the
    solver never has to look inside a [logor] and a nested [shift_left] at
    the same time. *)
let be4_ok (#t: Type0) {| w: word t |} (a0 a1 a2 a3: t) (c0 c1 c2 c3: S8.t) (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == 4 /\
                    Seq.index s 0 == c0 /\ Seq.index s 1 == c1 /\
                    Seq.index s 2 == c2 /\ Seq.index s 3 == c3 /\
                    a0 == shift_left #t (of_byte c0) 24ul /\
                    a1 == logor #t a0 (shift_left #t (of_byte c1) 16ul) /\
                    a2 == logor #t a1 (shift_left #t (of_byte c2) 8ul) /\
                    a3 == logor #t a2 (shift_left #t (of_byte c3) 0ul))
          (ensures v a3 == be_nat s)
  = be_nat_one (Seq.slice s 0 1);
    byte_at #t c0 24 24ul;
    assert (v a0 == be_nat (Seq.slice s 0 1) * pow2 24);
    Math.multiple_modulo_lemma (be_nat (Seq.slice s 0 1)) (pow2 24);
    or_byte_be #t a0 c1 16 16ul;
    be_nat_prefix s 1;
    assert (v a1 == be_nat (Seq.slice s 0 2) * pow2 16);
    Math.multiple_modulo_lemma (be_nat (Seq.slice s 0 2)) (pow2 16);
    or_byte_be #t a1 c2 8 8ul;
    be_nat_prefix s 2;
    assert (v a2 == be_nat (Seq.slice s 0 3) * pow2 8);
    Math.multiple_modulo_lemma (be_nat (Seq.slice s 0 3)) (pow2 8);
    or_byte_be #t a2 c3 0 0ul;
    be_nat_prefix s 3;
    Seq.lemma_eq_intro (Seq.slice s 0 4) s

(** The same for {!load_le4}, where byte [k] goes to offset [8k] and the
    accumulator stays below [2^(8k)] until it is extended. *)
let le4_ok (#t: Type0) {| w: word t |} (a0 a1 a2 a3: t) (c0 c1 c2 c3: S8.t) (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == 4 /\
                    Seq.index s 0 == c0 /\ Seq.index s 1 == c1 /\
                    Seq.index s 2 == c2 /\ Seq.index s 3 == c3 /\
                    a0 == of_byte #t c0 /\
                    a1 == logor #t a0 (shift_left #t (of_byte c1) 8ul) /\
                    a2 == logor #t a1 (shift_left #t (of_byte c2) 16ul) /\
                    a3 == logor #t a2 (shift_left #t (of_byte c3) 24ul))
          (ensures v a3 == le_nat s)
  = le_nat_one (Seq.slice s 0 1);
    assert (v a0 == le_nat (Seq.slice s 0 1));
    le_nat_bound (Seq.slice s 0 1);
    or_byte_le #t a0 c1 1 8ul;
    le_nat_prefix s 1;
    assert (v a1 == le_nat (Seq.slice s 0 2));
    le_nat_bound (Seq.slice s 0 2);
    or_byte_le #t a1 c2 2 16ul;
    le_nat_prefix s 2;
    assert (v a2 == le_nat (Seq.slice s 0 3));
    le_nat_bound (Seq.slice s 0 3);
    or_byte_le #t a2 c3 3 24ul;
    le_nat_prefix s 3;
    Seq.lemma_eq_intro (Seq.slice s 0 4) s

#pop-options

(** {2 Straight-line four-byte loads}

    [load_be] and [load_le] below each run one iteration per byte, and the
    iterations depend on one another: the accumulator produced by one is the
    input of the next.  Worse, the trip count is [nbytes], a field of the
    [word] class, which Custard emits as a C global -- so no compiler unrolls
    the loop, and reading a sixty-four bit word costs eight dependent
    shift-or pairs plus eight loop tests.

    These two read exactly four bytes with no loop at all, placing each byte
    at its own bit offset.  The four array reads and the four shifts have no
    dependency between them, so the whole thing is three [or]s deep, and
    clang recognizes the pattern and emits a single word load.  Four is the
    useful width because [bits] is at least thirty-two for every instance of
    the class, so no instance needs a precondition, and a sixty-four bit load
    is two of these joined with {!Hacl.Spec.Bytes.or_half} -- again with no
    dependency between the halves. *)

fn load_be4 (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
            (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + 4 <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + 4 <= Seq.length vb /\
              v r == be_nat (Seq.slice vb (SZ.v off) (SZ.v off + 4)))
{
  A.pts_to_len b;
  let c0 = A.(b.(off));
  let c1 = A.(b.(SZ.add off 1sz));
  let c2 = A.(b.(SZ.add off 2sz));
  let c3 = A.(b.(SZ.add off 3sz));
  let a0 = shift_left #t (of_byte c0) 24ul;
  let a1 = logor #t a0 (shift_left #t (of_byte c1) 16ul);
  let a2 = logor #t a1 (shift_left #t (of_byte c2) 8ul);
  let a3 = logor #t a2 (shift_left #t (of_byte c3) 0ul);
  be4_ok #t a0 a1 a2 a3 c0 c1 c2 c3 (Seq.slice vb (SZ.v off) (SZ.v off + 4));
  a3
}

fn load_le4 (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
            (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + 4 <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + 4 <= Seq.length vb /\
              v r == le_nat (Seq.slice vb (SZ.v off) (SZ.v off + 4)))
{
  A.pts_to_len b;
  let c0 = A.(b.(off));
  let c1 = A.(b.(SZ.add off 1sz));
  let c2 = A.(b.(SZ.add off 2sz));
  let c3 = A.(b.(SZ.add off 3sz));
  let a0 = of_byte #t c0;
  let a1 = logor #t a0 (shift_left #t (of_byte c1) 8ul);
  let a2 = logor #t a1 (shift_left #t (of_byte c2) 16ul);
  let a3 = logor #t a2 (shift_left #t (of_byte c3) 24ul);
  le4_ok #t a0 a1 a2 a3 c0 c1 c2 c3 (Seq.slice vb (SZ.v off) (SZ.v off + 4));
  a3
}

(** Joining two four-byte halves into a sixty-four bit word.  [or_half] does
    the bit-level work; [le_nat_split] and [be_nat_split] say the halves are
    the low and high parts of the number, which for big-endian are the other
    way round in memory. *)
let le8_join (#t: Type0) {| w: word t |} (lo hi: t) (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == 8 /\ bits #t == 64 /\
                    v lo == le_nat (Seq.slice s 0 4) /\ v hi == le_nat (Seq.slice s 4 8))
          (ensures v (logor #t lo (shift_left #t hi 32ul)) == le_nat s)
  = le_nat_bound (Seq.slice s 0 4);
    le_nat_bound (Seq.slice s 4 8);
    or_half #t lo hi 4 32ul;
    le_nat_split s 4

let be8_join (#t: Type0) {| w: word t |} (lo hi: t) (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == 8 /\ bits #t == 64 /\
                    v hi == be_nat (Seq.slice s 0 4) /\ v lo == be_nat (Seq.slice s 4 8))
          (ensures v (logor #t lo (shift_left #t hi 32ul)) == be_nat s)
  = be_nat_bound (Seq.slice s 0 4);
    be_nat_bound (Seq.slice s 4 8);
    or_half #t lo hi 4 32ul;
    be_nat_split s 4;
    assert (be_nat s == be_nat (Seq.slice s 0 4) * pow2 32 + be_nat (Seq.slice s 4 8));
    FStar.Math.Lemmas.swap_mul (be_nat (Seq.slice s 0 4)) (pow2 32)

(** A window of four bytes inside a window of eight is a window of four. *)
let halves (s: Seq.seq S8.t) (off: nat { off + 8 <= Seq.length s })
  : Lemma (Seq.slice (Seq.slice s off (off + 8)) 0 4 == Seq.slice s off (off + 4) /\
           Seq.slice (Seq.slice s off (off + 8)) 4 8 == Seq.slice s (off + 4) (off + 8))
  = Seq.lemma_eq_intro (Seq.slice (Seq.slice s off (off + 8)) 0 4) (Seq.slice s off (off + 4));
    Seq.lemma_eq_intro (Seq.slice (Seq.slice s off (off + 8)) 4 8) (Seq.slice s (off + 4) (off + 8))


fn load_be (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
           (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + bytes #t <= Seq.length vb /\
              v r == be_nat (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)))
{
  A.pts_to_len b;
  bytes_ok #t #w;
  if (SZ.eq (nbytes #t #w) 4sz) {
    load_be4 #t #w b off
  } else {
    if (SZ.eq (nbytes #t #w) 8sz) {
      let hi = load_be4 #t #w b off;
      let lo = load_be4 #t #w b (SZ.add off 4sz);
      assert (pure (bits #t / 8 == 8));
      halves vb (SZ.v off);
      be8_join #t lo hi (Seq.slice vb (SZ.v off) (SZ.v off + 8));
      logor #t lo (shift_left #t hi 32ul)
    } else {
      load_be_loop #t #w b off
    }
  }
}




(** The loop invariants of [store_be] and [store_le], kept opaque so that the
    quantifiers in them stay out of the Pulse verification conditions; the
    three lemmas after each are all the loops need to know about them. *)

(** Byte [k] of a number, little end first.  Opaque, so that the division in
    it stays out of the arithmetic the invariant lemmas below do. *)
[@@"opaque_to_smt"]
let digit (x: nat) (k: nat) : GTot nat = (x / pow2 (8 * k)) % 256

let digit_def (x: nat) (k: nat) : Lemma (digit x k == (x / pow2 (8 * k)) % 256)
  = reveal_opaque (`%digit) (digit x k)

(** The first byte [store_be] and [store_le] write at step [vj]. *)
let digit_step (#t: Type0) {| w: word t |} (x c: t) (vj: nat)
  : Lemma (requires v c == v x / pow2 (8 * vj))
          (ensures S8.v (to_byte c) == digit (v x) vj)
  = digit_def (v x) vj;
    assert_norm (pow2 8 == 256)

(** The invariant spelled out; only the lemmas below look inside it. *)
let store_be_inv_body (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                 (vb vb': Seq.seq S8.t) : prop =
  vj <= n /\ off + n <= Seq.length vb /\ Seq.length vb' == Seq.length vb /\
  v c == v x / pow2 (8 * vj) /\
  (forall (k: nat). k < vj ==>
     S8.v (Seq.index vb' (off + n - 1 - k)) == digit (v x) k) /\
  (forall (k: nat). k < Seq.length vb ==>
     k < off + n - vj \/ k >= off + n ==>
     Seq.index vb' k == Seq.index vb k)

[@@"opaque_to_smt"]
let store_be_inv (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                 (vb vb': Seq.seq S8.t) : prop =
  store_be_inv_body x c off n vj vb vb'

let store_be_inv_def (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                     (vb vb': Seq.seq S8.t)
  : Lemma (store_be_inv x c off n vj vb vb' <==> store_be_inv_body x c off n vj vb vb')
  = reveal_opaque (`%store_be_inv) (store_be_inv x c off n vj vb vb')

let store_be_inv_init (#t: Type0) {| w: word t |} (x: t) (off n: nat) (vb: Seq.seq S8.t)
  : Lemma (requires off + n <= Seq.length vb)
          (ensures store_be_inv x x off n 0 vb vb)
  = store_be_inv_def x x off n 0 vb vb;
    assert_norm (pow2 0 == 1)

let store_be_inv_step (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                      (vb vb': Seq.seq S8.t)
  : Lemma (requires vj < n /\ store_be_inv x c off n vj vb vb')
          (ensures off + n - (vj + 1) < Seq.length vb' /\
                   store_be_inv x (shift_right #t c 8ul) off n (vj + 1) vb
                     (Seq.upd vb' (off + n - (vj + 1)) (to_byte c)))
  = store_be_inv_def x c off n vj vb vb';
    let p = off + n - (vj + 1) in
    let vb'' = Seq.upd vb' p (to_byte c) in
    store_be_inv_def x (shift_right #t c 8ul) off n (vj + 1) vb vb'';
    store_step x c vj;
    digit_step x c vj;
    introduce forall (k: nat). k < vj + 1 ==>
      S8.v (Seq.index vb'' (off + n - 1 - k)) == digit (v x) k
    with introduce _ ==> _
    with (if k = vj then () else
          assert (Seq.index vb'' (off + n - 1 - k) == Seq.index vb' (off + n - 1 - k)));
    introduce forall (k: nat). k < Seq.length vb ==>
      k < off + n - (vj + 1) \/ k >= off + n ==> Seq.index vb'' k == Seq.index vb k
    with introduce _ ==> _
    with introduce _ ==> _
    with assert (Seq.index vb'' k == Seq.index vb' k)

let store_be_inv_final (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                       (vb vb': Seq.seq S8.t)
  : Lemma (requires n * 8 == bits #t /\ n <= vj /\ store_be_inv x c off n vj vb vb')
          (ensures Seq.length vb' == Seq.length vb /\
                   off + bytes #t <= Seq.length vb' /\
                   (forall (k: nat). k < bytes #t ==>
                      S8.v (Seq.index vb' (off + k)) == (v x / pow2 (8 * (bytes #t - 1 - k))) % 256) /\
                   (forall (k: nat). k < Seq.length vb ==> k < off \/ k >= off + bytes #t ==>
                      Seq.index vb' k == Seq.index vb k))
  = store_be_inv_def x c off n vj vb vb';
    bytes_ok #t #w;
    assert (vj == n /\ n == bytes #t);
    introduce forall (k: nat). k < bytes #t ==>
      S8.v (Seq.index vb' (off + k)) == (v x / pow2 (8 * (bytes #t - 1 - k))) % 256
    with introduce _ ==> _
    with (let k' : nat = n - 1 - k in
          assert (k' < vj /\ off + n - 1 - k' == off + k);
          assert (8 * k' == 8 * (bytes #t - 1 - k));
          digit_def (v x) k';
          assert (S8.v (Seq.index vb' (off + n - 1 - k')) == digit (v x) k'))

ghost fn store_be_finish (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t) (x c: t)
                         (n vj: nat) (#vb: erased (Seq.seq S8.t)) (#vb': erased (Seq.seq S8.t))
requires A.pts_to b vb' ** pure (n * 8 == bits #t /\ n <= vj /\ store_be_inv x c (SZ.v off) n vj vb vb')
ensures exists* vb'. A.pts_to b vb' **
        pure (Seq.length vb' == Seq.length vb /\
              SZ.v off + bytes #t <= Seq.length vb' /\
              (forall (k: nat). k < bytes #t ==>
                 S8.v (Seq.index vb' (SZ.v off + k)) == (v x / pow2 (8 * (bytes #t - 1 - k))) % 256) /\
              (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + bytes #t ==>
                 Seq.index vb' k == Seq.index vb k))
{
  store_be_inv_final x c (SZ.v off) n vj vb vb';
  be_offsets_nat #t #w;
  assert pure (Seq.length vb' == Seq.length vb);
}

fn store_be (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t) (x: t)
            (#vb: erased (Seq.seq S8.t))
requires A.pts_to b vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
ensures exists* vb'. A.pts_to b vb' **
        pure (Seq.length vb' == Seq.length vb /\
              SZ.v off + bytes #t <= Seq.length vb' /\
              (forall (k: nat). k < bytes #t ==>
                 S8.v (Seq.index vb' (SZ.v off + k)) == (v x / pow2 (8 * (bytes #t - 1 - k))) % 256) /\
              (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + bytes #t ==>
                 Seq.index vb' k == Seq.index vb k))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let mut cur = x;
  let mut j = 0sz;
  store_be_inv_init x (SZ.v off) (SZ.v n) vb;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (c: t) (vb': Seq.seq S8.t).
    pts_to j vj ** pts_to cur c ** A.pts_to b vb' **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          Seq.length vb' == Seq.length vb /\
          store_be_inv x c (SZ.v off) (SZ.v n) (SZ.v vj) vb vb')
  decreases (SZ.v n - SZ.v (!j))
  {
    with vj0 c0 vb'. assert (pts_to j vj0 ** pts_to cur c0 ** A.pts_to b vb');
    let vj = !j;
    let c = !cur;
    let pos = SZ.sub (SZ.add off n) (SZ.add vj 1sz);
    store_be_inv_step x c (SZ.v off) (SZ.v n) (SZ.v vj) vb vb';
    A.((b.(pos) <- to_byte c));
    cur := shift_right #t c 8ul;
    j := SZ.add vj 1sz;
  };
  with vj c vb'. assert (pts_to j vj ** pts_to cur c ** A.pts_to b vb');
  be_offsets_nat #t #w;
  store_be_finish #t #w b off x c (SZ.v n) (SZ.v vj) #vb #vb';
}

(** {2 The same, little end first}

    [load_le] reads the bytes from the top of the word down, so the
    accumulator holds the value of the *suffix* of the window read so far and
    each step multiplies by 256 and adds one more byte -- the same shape as
    [load_be], with the window traversed the other way.  [store_le] is
    simpler than [store_be]: the low byte comes first, so the write index
    advances with the loop counter instead of retreating. *)

fn load_le (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
           (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + bytes #t <= Seq.length vb /\
              v r == le_nat (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)))
{
  A.pts_to_len b;
  bytes_ok #t #w;
  if (SZ.eq (nbytes #t #w) 4sz) {
    load_le4 #t #w b off
  } else {
    if (SZ.eq (nbytes #t #w) 8sz) {
      let lo = load_le4 #t #w b off;
      let hi = load_le4 #t #w b (SZ.add off 4sz);
      assert (pure (bits #t / 8 == 8));
      halves vb (SZ.v off);
      le8_join #t lo hi (Seq.slice vb (SZ.v off) (SZ.v off + 8));
      logor #t lo (shift_left #t hi 32ul)
    } else {
      load_le_loop #t #w b off
    }
  }
}

(** The invariant spelled out; only the lemmas below look inside it. *)
let store_le_inv_body (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                 (vb vb': Seq.seq S8.t) : prop =
  vj <= n /\ off + n <= Seq.length vb /\ Seq.length vb' == Seq.length vb /\
  v c == v x / pow2 (8 * vj) /\
  (forall (k: nat). k < vj ==>
     S8.v (Seq.index vb' (off + k)) == digit (v x) k) /\
  (forall (k: nat). k < Seq.length vb ==>
     k < off \/ k >= off + vj ==>
     Seq.index vb' k == Seq.index vb k)

[@@"opaque_to_smt"]
let store_le_inv (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                 (vb vb': Seq.seq S8.t) : prop =
  store_le_inv_body x c off n vj vb vb'

let store_le_inv_def (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                     (vb vb': Seq.seq S8.t)
  : Lemma (store_le_inv x c off n vj vb vb' <==> store_le_inv_body x c off n vj vb vb')
  = reveal_opaque (`%store_le_inv) (store_le_inv x c off n vj vb vb')

let store_le_inv_init (#t: Type0) {| w: word t |} (x: t) (off n: nat) (vb: Seq.seq S8.t)
  : Lemma (requires off + n <= Seq.length vb)
          (ensures store_le_inv x x off n 0 vb vb)
  = store_le_inv_def x x off n 0 vb vb;
    assert_norm (pow2 0 == 1)

let store_le_inv_step (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                      (vb vb': Seq.seq S8.t)
  : Lemma (requires vj < n /\ store_le_inv x c off n vj vb vb')
          (ensures off + vj < Seq.length vb' /\
                   store_le_inv x (shift_right #t c 8ul) off n (vj + 1) vb
                     (Seq.upd vb' (off + vj) (to_byte c)))
  = store_le_inv_def x c off n vj vb vb';
    let p = off + vj in
    let vb'' = Seq.upd vb' p (to_byte c) in
    store_le_inv_def x (shift_right #t c 8ul) off n (vj + 1) vb vb'';
    store_step x c vj;
    digit_step x c vj;
    introduce forall (k: nat). k < vj + 1 ==>
      S8.v (Seq.index vb'' (off + k)) == digit (v x) k
    with introduce _ ==> _
    with (if k = vj then () else
          assert (Seq.index vb'' (off + k) == Seq.index vb' (off + k)));
    introduce forall (k: nat). k < Seq.length vb ==>
      k < off \/ k >= off + (vj + 1) ==> Seq.index vb'' k == Seq.index vb k
    with introduce _ ==> _
    with introduce _ ==> _
    with assert (Seq.index vb'' k == Seq.index vb' k)

let store_le_inv_final (#t: Type0) {| w: word t |} (x c: t) (off n vj: nat)
                       (vb vb': Seq.seq S8.t)
  : Lemma (requires n * 8 == bits #t /\ n <= vj /\ store_le_inv x c off n vj vb vb')
          (ensures Seq.length vb' == Seq.length vb /\
                   off + bytes #t <= Seq.length vb' /\
                   (forall (k: nat). k < bytes #t ==>
                      S8.v (Seq.index vb' (off + k)) == (v x / pow2 (8 * k)) % 256) /\
                   (forall (k: nat). k < Seq.length vb ==> k < off \/ k >= off + bytes #t ==>
                      Seq.index vb' k == Seq.index vb k))
  = store_le_inv_def x c off n vj vb vb';
    bytes_ok #t #w;
    assert (vj == n /\ n == bytes #t);
    introduce forall (k: nat). k < bytes #t ==>
      S8.v (Seq.index vb' (off + k)) == (v x / pow2 (8 * k)) % 256
    with introduce _ ==> _
    with digit_def (v x) k

fn store_le (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t) (x: t)
            (#vb: erased (Seq.seq S8.t))
requires A.pts_to b vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
ensures exists* vb'. A.pts_to b vb' **
        pure (Seq.length vb' == Seq.length vb /\
              SZ.v off + bytes #t <= Seq.length vb' /\
              (forall (k: nat). k < bytes #t ==>
                 S8.v (Seq.index vb' (SZ.v off + k)) == (v x / pow2 (8 * k)) % 256) /\
              (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + bytes #t ==>
                 Seq.index vb' k == Seq.index vb k))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let mut cur = x;
  let mut j = 0sz;
  store_le_inv_init x (SZ.v off) (SZ.v n) vb;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (c: t) (vb': Seq.seq S8.t).
    pts_to j vj ** pts_to cur c ** A.pts_to b vb' **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          Seq.length vb' == Seq.length vb /\
          store_le_inv x c (SZ.v off) (SZ.v n) (SZ.v vj) vb vb')
  decreases (SZ.v n - SZ.v (!j))
  {
    with vj0 c0 vb'. assert (pts_to j vj0 ** pts_to cur c0 ** A.pts_to b vb');
    let vj = !j;
    let c = !cur;
    store_le_inv_step x c (SZ.v off) (SZ.v n) (SZ.v vj) vb vb';
    A.((b.(SZ.add off vj) <- to_byte c));
    cur := shift_right #t c 8ul;
    j := SZ.add vj 1sz;
  };
  with vj c vb'. assert (pts_to j vj ** pts_to cur c ** A.pts_to b vb');
  store_le_inv_final x c (SZ.v off) (SZ.v n) (SZ.v vj) vb vb';
  ()
}

(** {2 A whole array of words}

    [store_words_le out ws n] writes [n] words little-endian end to end, which
    is what every keystream and every digest does at the last step.  It is
    here rather than in one of the ciphers because two of them want it. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn store_words_le (#t: Type0) {| w: word t |}
                  (out: A.array S8.t) (ws: A.array t) (n: SZ.t)
                  (#vout: erased (Seq.seq S8.t)) (#pw: perm)
                  (#vw: erased (Seq.seq t))
requires A.pts_to out vout ** A.pts_to ws #pw vw **
         pure (Seq.length vw == SZ.v n /\ Seq.length vout == SZ.v n * bytes #t)
ensures exists* (vo: Seq.seq S8.t). A.pts_to out vo ** A.pts_to ws #pw vw **
  pure (Seq.length vw == SZ.v n /\ Seq.length vo == SZ.v n * bytes #t /\
        vo == words_to_le #t (SZ.v n) vw)
{
  A.pts_to_len out;
  A.pts_to_len ws;
  let nb = nbytes #t #w;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (vo: Seq.seq S8.t).
    pts_to j vj ** A.pts_to out vo ** A.pts_to ws #pw vw **
    pure (SZ.v vj <= SZ.v n /\ Seq.length vw == SZ.v n /\
          Seq.length vo == SZ.v n * bytes #t /\
          (forall (i: nat). i < SZ.v vj * bytes #t ==>
             Seq.index vo i == Seq.index (words_to_le #t (SZ.v n) vw) i))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vj + 1) (SZ.v n);
    Math.distributivity_add_left (SZ.v vj) 1 (bytes #t);
    let x = A.(ws.(vj));
    store_le #t out (SZ.mul vj nb) x;
    with vo. assert (A.pts_to out vo);
    digest_step_le #t (SZ.v n) vw (SZ.v vj) (SZ.v (SZ.mul vj nb)) vo;
    j := SZ.add vj 1sz;
  };
  with vo. assert (A.pts_to out vo);
  Seq.lemma_eq_intro vo (words_to_le #t (SZ.v n) vw);
  Seq.lemma_eq_elim vo (words_to_le #t (SZ.v n) vw);
}

#pop-options

(** {2 Constant-time equality}

    [n] [eq_mask]s folded with [logand]: all-ones exactly when every byte
    agrees, and the loop's shape does not depend on where a mismatch is.  The
    resulting bit is the answer the caller asked for, so it is declassified
    here -- and, apart from a couple of range checks, nowhere else. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn bytes_eq (a: A.array S8.t) (b: A.array S8.t) (n: SZ.t)
            (#pa: perm) (#va: erased (Seq.seq S8.t))
            (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n)
returns res: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n /\
              (res <==> Seq.equal va vb))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut acc = S8.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (m: S8.t).
    pts_to i vi ** pts_to acc m ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length va == SZ.v n /\ Seq.length vb == SZ.v n /\
          (S8.v m == 0 \/ S8.v m == pow2 8 - 1) /\
          (S8.v m == pow2 8 - 1 <==>
           (forall (k: nat). k < SZ.v vi ==>
              S8.v (Seq.index va k) == S8.v (Seq.index vb k))))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let m = !acc;
    let eq = S8.eq_mask x y;
    let m' = S8.logand m eq;
    UInt.logand_lemma_1 #8 (S8.v m);
    UInt.logand_lemma_2 #8 (S8.v m);
    UInt.logand_commutative #8 (S8.v m) (S8.v eq);
    UInt.logand_lemma_1 #8 (S8.v eq);
    UInt.logand_lemma_2 #8 (S8.v eq);
    acc := m';
    i := SZ.add vi 1sz;
  };
  let m = !acc;
  D.bool_of_mask m
}

#pop-options
