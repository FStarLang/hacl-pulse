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

(** Turning bytes into field elements.

    A Poly1305 block is sixteen little-endian bytes plus a one placed just
    above its top byte.  Two sixty-four-bit loads give the bytes; the limb
    boundaries then fall at 26, 52, 78 and 104, so limb 2 is the only one
    that straddles the word boundary, taking twelve bits from the top of the
    low word and fourteen from the bottom of the high one.

    A short final block is handled by padding rather than by moving the extra
    bit: the bytes are copied into a zeroed sixteen-byte buffer with a single
    [1] byte after them, which is worth exactly the [2^(8 len)] the
    specification asks for, and the loader is then the same one a full block
    uses with its top bit switched off.  That is one branch, taken once per
    message, instead of a variable shift in the common path.

    The key's [r] is loaded the same way, after clamping.  Clamping is four
    byte masks, exactly as RFC 8439 writes it, so nothing here needs a
    bit-level argument about a hundred-and-twenty-eight-bit [logand]. *)
module Hacl.Poly1305.Load

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Hacl.Impl.Copy
open Spec.Poly1305.Field
open Hacl.Poly1305.Field

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Spec = Spec.Poly1305

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 Two more masks} *)

inline_for_extraction
let mask14 : m: S64.t { S64.v m == pow2 14 - 1 } =
  assert_norm (pow2 14 - 1 == 0x3fff);
  S64.classify 0x3fffuL

inline_for_extraction
let lo14 (x: S64.t) : r: S64.t { S64.v r == S64.v x % pow2 14 } =
  UInt.logand_mask #64 (S64.v x) 14;
  S64.logand x mask14

inline_for_extraction
let shr (x: S64.t) (s: U32.t { U32.v s < 64 })
  : r: S64.t { S64.v r == S64.v x / pow2 (U32.v s) }
  = S64.shift_right x s

(** [x * 2^s] where the product is known not to wrap. *)
inline_for_extraction
let shl (x: S64.t) (s: U32.t { U32.v s < 64 })
  : Pure S64.t (requires S64.v x * pow2 (U32.v s) < pow2 64)
               (ensures fun r -> S64.v r == S64.v x * pow2 (U32.v s))
  = Math.small_mod (S64.v x * pow2 (U32.v s)) (pow2 64);
    S64.shift_left x s

(** {2 Two words into five limbs}

    [c] is the block's extra bit, already scaled: [2^24] is where [2^128]
    lands in limb 4.  It is a run-time argument only so that the full and the
    padded case share the code; both call sites pass a constant. *)

inline_for_extraction
fn store_limbs (e: S.slice S64.t) (lo: S64.t) (hi: S64.t) (c: S64.t)
               (#ve: erased (Seq.seq S64.t))
requires S.pts_to e ve **
         pure (Seq.length ve == 5 /\ (S64.v c == 0 \/ S64.v c == pow2 24))
ensures exists* (ve': Seq.seq S64.t). S.pts_to e ve' **
  pure (Seq.length ve' == 5 /\ bounded ve' 26 /\
        feval ve' == S64.v lo + pow2 64 * S64.v hi + S64.v c * pow2 104)
{
  S.pts_to_len e;
  let cn: erased nat = hide (S64.v c / pow2 24);
  load_limbs (S64.v lo) (S64.v hi) cn;
  assert_norm (pow2 24 * pow2 104 == pow2 128);
  (* limb 2 is the straddling one: twelve bits of [lo] and fourteen of [hi]. *)
  assert_norm (pow2 14 * pow2 12 == pow2 26);
  Math.lemma_mult_le_right (pow2 12) (S64.v hi % pow2 14) (pow2 14 - 1);
  Math.pow2_lt_compat 64 26;
  Math.lemma_div_lt (S64.v lo) 64 52;
  Math.lemma_div_lt (S64.v hi) 64 40;
  assert_norm (pow2 24 + pow2 24 == pow2 25);
  Math.pow2_lt_compat 64 26;
  S.((e.(0sz) <- lo26 lo));
  S.((e.(1sz) <- lo26 (shr lo 26ul)));
  S.((e.(2sz) <- add2 (shr lo 52ul) (shl (lo14 hi) 12ul)));
  S.((e.(3sz) <- lo26 (shr hi 14ul)));
  S.((e.(4sz) <- add2 (shr hi 40ul) c));
}

(** {2 A full block} *)

(** [e <- the sixteen bytes at [off], with the high bit set]. *)
fn load_full (e: S.slice S64.t) (b: S.slice S8.t) (off: SZ.t)
             (#ve: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires S.pts_to e ve ** S.pts_to b #pb vb **
         pure (Seq.length ve == 5 /\ SZ.v off + 16 <= Seq.length vb)
ensures exists* (ve': Seq.seq S64.t). S.pts_to e ve' ** S.pts_to b #pb vb **
  pure (Seq.length ve' == 5 /\ bounded ve' 26 /\
        SZ.v off + 16 <= Seq.length vb /\
        feval ve' == Spec.block_val (Seq.slice vb (SZ.v off) (SZ.v off + 16)))
{
  S.pts_to_len e;
  S.pts_to_len b;
  let lo = load_le #S64.t b off;
  let hi = load_le #S64.t b (SZ.add off 8sz);
  let blk = hide (Seq.slice vb (SZ.v off) (SZ.v off + 16));
  le_nat_split (reveal blk) 8;
  Seq.lemma_eq_intro (Seq.slice (reveal blk) 0 8) (Seq.slice vb (SZ.v off) (SZ.v off + 8));
  Seq.lemma_eq_intro (Seq.slice (reveal blk) 8 16) (Seq.slice vb (SZ.v off + 8) (SZ.v off + 16));
  assert_norm (pow2 24 * pow2 104 == pow2 128);
  assert_norm (pow2 (8 * 16) == pow2 128);
  assert_norm (pow2 (8 * 8) == pow2 64);
  let c = S64.classify 0x1000000uL;
  assert_norm (pow2 24 == 0x1000000);
  store_limbs e lo hi c;
}

(** {2 A short final block}

    The pad byte does the work of the extra bit, so the loader's own bit is
    off.  [blen] may be zero only if the message is empty, which the caller
    does not do: [nblocks 0] is zero. *)

fn load_last (e: S.slice S64.t) (b: S.slice S8.t) (off: SZ.t) (blen: SZ.t)
             (#ve: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires S.pts_to e ve ** S.pts_to b #pb vb **
         pure (Seq.length ve == 5 /\ SZ.v blen < 16 /\
               SZ.v off + SZ.v blen <= Seq.length vb)
ensures exists* (ve': Seq.seq S64.t). S.pts_to e ve' ** S.pts_to b #pb vb **
  pure (Seq.length ve' == 5 /\ bounded ve' 26 /\
        SZ.v blen < 16 /\ SZ.v off + SZ.v blen <= Seq.length vb /\
        feval ve' ==
          Spec.block_val (Seq.slice vb (SZ.v off) (SZ.v off + SZ.v blen)))
{
  S.pts_to_len e;
  S.pts_to_len b;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; 16sz |];
  A.pts_to_len tarr;
  let tmp = S.from_array tarr 16sz;
  S.pts_to_len tmp;
  copy_range tmp 0sz b off blen;
  S.((tmp.(blen) <- S8.classify 1uy));

  with vt. assert (S.pts_to tmp vt);
  let blk = hide (Seq.slice vb (SZ.v off) (SZ.v off + SZ.v blen));
  le_nat_split vt (SZ.v blen);
  Seq.lemma_eq_intro (Seq.slice vt 0 (SZ.v blen)) (reveal blk);
  le_nat_one_zeros (Seq.slice vt (SZ.v blen) 16);

  let lo = load_le #S64.t tmp 0sz;
  let hi = load_le #S64.t tmp 8sz;
  le_nat_split vt 8;
  Seq.lemma_eq_intro (Seq.slice vt 0 8) (Seq.slice vt 0 8);
  assert_norm (pow2 (8 * 8) == pow2 64);
  store_limbs e lo hi S64.zero;
  S.to_array tmp;
}

#pop-options

(** {2 The key}

    Sixteen bytes of clamped [r] and sixteen bytes of [s].  Clamping is seven
    byte masks, exactly the seven [Spec.Poly1305.clamp_byte] names, done on a
    copy so the caller's key is not disturbed. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn load_r (r: S.slice S64.t) (k: S.slice S8.t)
          (#vr: erased (Seq.seq S64.t)) (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires S.pts_to r vr ** S.pts_to k #pk vk **
         pure (Seq.length vr == 5 /\ Seq.length vk == 32)
ensures exists* (vr': Seq.seq S64.t). S.pts_to r vr' ** S.pts_to k #pk vk **
  pure (Seq.length vr' == 5 /\ bounded vr' 26 /\ Seq.length vk == 32 /\
        feval vr' == Spec.r_of vk)
{
  S.pts_to_len r;
  S.pts_to_len k;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; 16sz |];
  A.pts_to_len tarr;
  let tmp = S.from_array tarr 16sz;
  S.pts_to_len tmp;
  copy_range tmp 0sz k 0sz 16sz;

  let m0f = S8.classify 0x0fuy;
  let mfc = S8.classify 0xfcuy;
  let c3 = S.(tmp.(3sz));   S.((tmp.(3sz) <- S8.logand c3 m0f));
  let c7 = S.(tmp.(7sz));   S.((tmp.(7sz) <- S8.logand c7 m0f));
  let c11 = S.(tmp.(11sz)); S.((tmp.(11sz) <- S8.logand c11 m0f));
  let c15 = S.(tmp.(15sz)); S.((tmp.(15sz) <- S8.logand c15 m0f));
  let c4 = S.(tmp.(4sz));   S.((tmp.(4sz) <- S8.logand c4 mfc));
  let c8 = S.(tmp.(8sz));   S.((tmp.(8sz) <- S8.logand c8 mfc));
  let c12 = S.(tmp.(12sz)); S.((tmp.(12sz) <- S8.logand c12 mfc));

  with vt. assert (S.pts_to tmp vt);
  Spec.clamp_eq (Seq.slice vk 0 16) vt;

  let lo = load_le #S64.t tmp 0sz;
  let hi = load_le #S64.t tmp 8sz;
  le_nat_split vt 8;
  assert_norm (pow2 (8 * 8) == pow2 64);
  store_limbs r lo hi S64.zero;
  S.to_array tmp;
}

#pop-options

(** {2 The tag}

    The accumulator, already canonical, plus the key's second half, modulo
    [2^128] and out as sixteen little-endian bytes.  The top two bits of the
    accumulator fall off: the tag is taken modulo [2^128], so there is
    nothing to carry them into. *)

inline_for_extraction
let lo12 (x: S64.t) : y: S64.t { S64.v y == S64.v x % pow2 12 } =
  assert_norm (pow2 12 - 1 == 0xfff);
  UInt.logand_mask #64 (S64.v x) 12;
  S64.logand x (S64.classify 0xfffuL)

inline_for_extraction
let lo24 (x: S64.t) : y: S64.t { S64.v y == S64.v x % pow2 24 } =
  assert_norm (pow2 24 - 1 == 0xffffff);
  UInt.logand_mask #64 (S64.v x) 24;
  S64.logand x (S64.classify 0xffffffuL)

(** [1] as a mask of the low bit: turns [lt_mask]'s all-ones into a carry. *)
inline_for_extraction
let bit0 (x: S64.t) : y: S64.t { S64.v y == S64.v x % 2 } =
  assert_norm (pow2 1 - 1 == 1);
  UInt.logand_mask #64 (S64.v x) 1;
  S64.logand x (S64.classify 1uL)

(** Sixteen bytes from two words: [le_bytes_split] says which word each byte
    comes from, and [nat_to_le_index] says what the specification puts there. *)
let tag_bytes (vout: Seq.seq S8.t) (tlo thi n: nat)
  : Lemma (requires Seq.length vout == 16 /\ tlo < pow2 64 /\ thi < pow2 64 /\
                    n == tlo + pow2 64 * thi /\
                    (forall (j: nat). j < 8 ==>
                       S8.v (Seq.index vout j) == (tlo / pow2 (8 * j)) % 256) /\
                    (forall (j: nat). j < 8 ==>
                       S8.v (Seq.index vout (8 + j)) == (thi / pow2 (8 * j)) % 256))
          (ensures vout == nat_to_le 16 n)
  = let aux (i: nat { i < 16 })
      : Lemma (Seq.index vout i == Seq.index (nat_to_le 16 n) i)
      = le_bytes_split tlo thi i;
        nat_to_le_index 16 n i
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro vout (nat_to_le 16 n)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn store_tag (out: S.slice S8.t) (h: S.slice S64.t) (k: S.slice S8.t)
             (#vout: erased (Seq.seq S8.t)) (#ph: perm) (#vh: erased (Seq.seq S64.t))
             (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to h #ph vh ** S.pts_to k #pk vk **
         pure (Seq.length vout == 16 /\ Seq.length vh == 5 /\ bounded vh 26 /\
               Seq.length vk == 32)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to h #ph vh ** S.pts_to k #pk vk **
  pure (Seq.length vk == 32 /\ Seq.length vout' == 16 /\
        vout' == Spec.finish (feval vh) (Spec.s_of vk))
{
  S.pts_to_len out;
  S.pts_to_len h;
  S.pts_to_len k;
  let a0 = S.(h.(0sz));
  let a1 = S.(h.(1sz));
  let a2 = S.(h.(2sz));
  let a3 = S.(h.(3sz));
  let a4 = S.(h.(4sz));
  tag_words (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) (S64.v a4);
  Math.pow2_plus 26 26;
  Math.pow2_plus 12 52;
  Math.pow2_plus 14 26;
  Math.pow2_plus 24 40;
  Math.lemma_mult_le_right (pow2 26) (S64.v a1) (pow2 26 - 1);
  Math.lemma_mult_le_right (pow2 52) (S64.v a2 % pow2 12) (pow2 12 - 1);
  Math.lemma_mult_le_right (pow2 14) (S64.v a3) (pow2 26 - 1);
  Math.lemma_mult_le_right (pow2 40) (S64.v a4 % pow2 24) (pow2 24 - 1);
  Math.lemma_div_lt (S64.v a2) 26 12;
  Math.pow2_lt_compat 64 52;
  let lo = add2 (add2 a0 (shl a1 26ul)) (shl (lo12 a2) 52ul);
  let hi = add2 (add2 (shr a2 12ul) (shl a3 14ul)) (shl (lo24 a4) 40ul);

  let slo = load_le #S64.t k 16sz;
  let shi = load_le #S64.t k 24sz;
  le_nat_split (Seq.slice vk 16 32) 8;
  Seq.lemma_eq_intro (Seq.slice (Seq.slice vk 16 32) 0 8) (Seq.slice vk 16 24);
  Seq.lemma_eq_intro (Seq.slice (Seq.slice vk 16 32) 8 16) (Seq.slice vk 24 32);
  assert_norm (pow2 (8 * 8) == pow2 64);

  let tlo = S64.add_mod lo slo;
  wrap_test (S64.v lo) (S64.v slo);
  let carry = bit0 (S64.lt_mask tlo lo);
  let thi = S64.add_mod (S64.add_mod hi shi) carry;
  Math.lemma_mod_add_distr (S64.v carry) (S64.v hi + S64.v shi) (pow2 64);
  add128 (S64.v lo) (S64.v hi) (S64.v slo) (S64.v shi);
  Math.lemma_mod_add_distr (Spec.s_of vk) (feval vh) (pow2 128);

  store_le #S64.t out 0sz tlo;
  store_le #S64.t out 8sz thi;
  with vout'. assert (S.pts_to out vout');
  tag_bytes vout' (S64.v tlo) (S64.v thi)
                  ((feval vh + Spec.s_of vk) % pow2 128);
  S.pts_to_len out;
}

#pop-options
