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

(** Arithmetic modulo the group order.

    Signing needs [(r + k s) mod q] and verification needs [S < q], where
    [q] is the order of the base point and not a prime of any convenient
    shape.  Everything here is the four-limb Montgomery arithmetic of
    {!Hacl.Impl.Mont4} with [qmod] passed as the modulus, so none of it
    duplicates any code in the emitted C: Ed25519's scalar field, P-256's
    two fields and secp256k1's two fields all share the same multiplier.

    Values are kept in *plain* form rather than Montgomery form.  There is
    no chain of operations here to amortise a conversion over -- signing
    does one multiply and one addition -- and staying plain is what makes
    the reduction below cheap.

    {b Reducing a hash.}  A SHA-512 digest is 512 bits and the order is a
    little under 2^253, so the reduction is the expensive part, not the
    multiply.  HACL* does a Barrett reduction in a 5x56-bit representation.
    The cheaper thing to do with Montgomery multiplication already in hand
    is to cut the digest into four 128-bit chunks

    {[ h = c0 + c1 2^128 + c2 2^256 + c3 2^384 ]}

    each of which is below [2^128] and therefore already a residue, and to
    fold in the three radix powers as constants.  [Spec.Ed25519.Scalar]'s
    [mmul_const] says that multiplying a residue by a constant of the form
    [R k mod q] cancels the [R] and leaves [a k mod q], so [c1], [c2] and
    [c3] are multiplied by [2^384 mod q], [2^512 mod q] and [2^640 mod q]
    respectively.  Three multiplications and three additions, with no wide
    division, no quotient estimate and no second representation.

    {b Bytes.}  Ed25519 is little-endian, so the byte layer is
    [Spec.Ed25519.Scalar]'s mirror of {!Spec.Field4}'s rather than
    {!Hacl.Impl.Bignum4}'s [load_be] and [store_be].

    Every branch below is on a length or a loop counter.  The limbs of the
    scalar are secret and never compared except through a mask. *)
module Hacl.Ed25519.Scalar

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.Ed25519.Scalar
open Spec.Mont4
open Hacl.Spec.Bytes
open Hacl.Impl.Limb4
open Hacl.Impl.Table
open Hacl.Impl.Bignum4
open Hacl.Impl.Mont4
open Hacl.Ed25519.Tables

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module Cast = Hacl.Secret.Cast
module Bytes = Hacl.Impl.Bytes
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 What a scalar is} *)

let qelem (v: Seq.seq S64.t) : prop = res qmod (vals v)

let qv (v: Seq.seq S64.t) : GTot nat = eval (vals v)

(** {2 Arithmetic facts the reduction needs}

    All four are about numbers rather than about memory, so they are stated
    and discharged here rather than inside a Pulse function, where they
    would be proved against the whole separation-logic context. *)

(** An all-zero limb sequence is zero. *)
#push-options "--fuel 2 --ifuel 1"
let rec eval_zeros (s: Seq.seq nat)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> Seq.index s i == 0)
          (ensures eval s == 0)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      assert (forall (i: nat). i < n - 1 ==> Seq.index (Seq.slice s 1 n) i == Seq.index s (i + 1));
      eval_zeros (Seq.slice s 1 n)
    end
#pop-options

(** Two limbs and two zeros hold the sixteen bytes they were read from,
    and that number is below [2^128], so it is a residue already. *)
let chunk_eval (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 16 /\ bnd s base /\
                    Seq.index s 0 == le_nat (Seq.slice b 0 8) /\
                    Seq.index s 1 == le_nat (Seq.slice b 8 16) /\
                    Seq.index s 2 == 0 /\ Seq.index s 3 == 0)
          (ensures eval s == le_nat b /\ eval s < pow2 128)
  = let lo = Seq.slice s 0 2 in
    let hi = Seq.slice s 2 4 in
    let aux (k: nat { k < 2 })
      : Lemma (Seq.index lo k == le_nat (Seq.slice b (8 * k) (8 * k + 8)))
      = if k = 0 then Seq.lemma_eq_intro (Seq.slice b 0 8) (Seq.slice b (8 * 0) (8 * 0 + 8))
        else Seq.lemma_eq_intro (Seq.slice b 8 16) (Seq.slice b (8 * 1) (8 * 1 + 8)) in
    Classical.forall_intro aux;
    eval_le b lo;
    eval_split s 2;
    assert (forall (i: nat). i < 2 ==> Seq.index hi i == 0);
    eval_zeros hi;
    assert_norm (rad * 2 == 128);
    le_nat_bound b

(** The same, packaged as the residue predicate the implementation speaks. *)
let chunk_res (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 16 /\ bnd s base /\
                    Seq.index s 0 == le_nat (Seq.slice b 0 8) /\
                    Seq.index s 1 == le_nat (Seq.slice b 8 16) /\
                    Seq.index s 2 == 0 /\ Seq.index s 3 == 0)
          (ensures res qmod s /\ eval s == le_nat b)
  = chunk_eval s b;
    q_bound ();
    qmod_m ();
    assert_norm (pow2 128 < pow2 252 + 27742317777372353535851937790883648493)

(** A table holding [2^e mod q] with [e = 256 + j] is a residue whose value
    is [R 2^j mod q]: the shape {!Spec.Ed25519.Scalar.mmul_const} wants. *)
let pow_res (e: nat) (j: nat)
  : Lemma (requires e == 256 + j)
          (ensures res qmod (limbs (pow2 e % q)) /\
                   eval (limbs (pow2 e % q)) == pow2 256 * pow2 j % q)
  = Math.pow2_plus 256 j;
    q_bound ();
    Math.lemma_mod_lt (pow2 e) q;
    limbs_ok (pow2 e % q)

(** [R^2 mod q] is the same shape with [j = 256]; the modulus bundle
    already carries it. *)
let r2_res (_: unit)
  : Lemma (res qmod qmod.r2 /\ eval qmod.r2 == pow2 256 * pow2 256 % q)
  = qmod_ok ();
    Math.lemma_mod_lt (pow2 256 * pow2 256) q

(** Sixty-four little-endian bytes are four 128-bit chunks. *)
let digest_split (b: Seq.seq S8.t)
  : Lemma (requires Seq.length b == 64)
          (ensures le_nat b == le_nat (Seq.slice b 0 16) +
                               pow2 128 * le_nat (Seq.slice b 16 32) +
                               pow2 256 * le_nat (Seq.slice b 32 48) +
                               pow2 384 * le_nat (Seq.slice b 48 64))
  = le_nat_split b 16;
    let t1 = Seq.slice b 16 64 in
    le_nat_split t1 16;
    Seq.lemma_eq_intro (Seq.slice t1 0 16) (Seq.slice b 16 32);
    let t2 = Seq.slice t1 16 48 in
    Seq.lemma_eq_intro t2 (Seq.slice b 32 64);
    le_nat_split t2 16;
    Seq.lemma_eq_intro (Seq.slice t2 0 16) (Seq.slice b 32 48);
    Seq.lemma_eq_intro (Seq.slice t2 16 32) (Seq.slice b 48 64);
    Math.pow2_plus 128 128;
    Math.pow2_plus 128 256;
    Math.paren_mul_right (pow2 128) (pow2 128) (le_nat (Seq.slice b 32 48));
    Math.paren_mul_right (pow2 128) (pow2 256) (le_nat (Seq.slice b 48 64))

(** Thirty-two of them are two. *)
let half_split (b: Seq.seq S8.t)
  : Lemma (requires Seq.length b == 32)
          (ensures le_nat b == le_nat (Seq.slice b 0 16) +
                               pow2 128 * le_nat (Seq.slice b 16 32))
  = le_nat_split b 16

(** Folding three terms into a running remainder is the same as reducing
    the whole sum once. *)
let fold_ok (a b c d: nat) (r1 r2 r3: nat)
  : Lemma (requires r1 == (a + b) % q /\ r2 == (r1 + c) % q /\ r3 == (r2 + d) % q)
          (ensures r3 == (a + b + c + d) % q)
  = Math.lemma_mod_add_distr c (a + b) q;
    Math.lemma_mod_add_distr d (a + b + c) q

(** The six order tables, each behind an abstract postcondition so that
    the callers never see the literals. *)

inline_for_extraction
fn qms () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.ms)
{ table qms_arr 4sz }

inline_for_extraction
fn qnm () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.nm)
{ table qnm_arr 4sz }

inline_for_extraction
fn qr2t () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == qmod.r2)
{ table qr2_arr 4sz }

inline_for_extraction
fn qp1t () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == limbs (pow2 384 % q))
{ table qp1_arr 4sz }

inline_for_extraction
fn qp3t () requires emp returns s: A.array S64.t
ensures exists* (p: perm) (v: Seq.seq S64.t).
  A.pts_to s #p v ** pure (Seq.length v == nl /\ vals v == limbs (pow2 640 % q))
{ table qp3_arr 4sz }

(** {2 The ring operations} *)

fn qadd (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qv vo' == (qv va + qv vb) % q)
{
  qmod_ok (); qmod_m ();
  madd_ok qmod (vals va) (vals vb);
  let nm = qnm ();
  aadd out a b nm qmod;
  drop_table nm;
}

(** An ordinary product: one [mmul] to cancel a radix and one against
    [R^2] to put it back. *)
fn qmul (out a b: A.array S64.t)
        (#vo: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ qelem va /\ qelem vb)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qv vo' == (qv va * qv vb) % q)
{
  qmod_ok (); qmod_m ();
  mmul_plain (vals va) (vals vb);
  let z = S64.zero;
  let mut t = [| z; 4sz |];
  Mem.track t; A.pts_to_len t; A.pts_to_len t;
  let ms = qms ();
  let nm = qnm ();
  let r2 = table qr2_arr 4sz;
  amul t a b ms nm qmu qmod;
  amul out t r2 ms nm qmu qmod;
  drop_table ms;
  drop_table nm;
  drop_table r2;
  Mem.wipe t 4sz;
}

(** {2 Bytes in}

    A limb is eight bytes, so reading one is [Hacl.Impl.Bytes.load_le] at
    sixty-four bits and nothing else; what has to be said is only that four
    of them in a row are the number.  That is [eval_le], and it is the same
    lemma whether the window is two limbs or four. *)

(** Two limbs from sixteen bytes, and two zeros above them: a chunk of a
    digest, which is below [2^128] and therefore already a residue. *)
#push-options "--z3rlimit 400"
fn load_chunk (out: A.array S64.t) (b: A.array S8.t) (off: SZ.t)
              (#vo: erased (Seq.seq S64.t))
              (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ SZ.v off + 16 <= Seq.length vb /\
        SZ.fits (SZ.v off + 16))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (SZ.v off + 16 <= Seq.length vb /\ qelem vo' /\
        qv vo' == le_nat (Seq.slice vb (SZ.v off) (SZ.v off + 16)))
{
  A.pts_to_len out;
  let w0 = Bytes.load_le #S64.t b off;
  let w1 = Bytes.load_le #S64.t b (SZ.add off 8sz);
  A.((out.(0sz) <- w0));
  A.((out.(1sz) <- w1));
  A.((out.(2sz) <- S64.zero));
  A.((out.(3sz) <- S64.zero));
  with v. assert (A.pts_to out v);
  A.pts_to_len out;
  vals_bnd v;
  Seq.lemma_eq_intro
    (Seq.slice (Seq.slice (reveal vb) (SZ.v off) (SZ.v off + 16)) 0 8)
    (Seq.slice (reveal vb) (SZ.v off) (SZ.v off + 8));
  Seq.lemma_eq_intro
    (Seq.slice (Seq.slice (reveal vb) (SZ.v off) (SZ.v off + 16)) 8 16)
    (Seq.slice (reveal vb) (SZ.v off + 8) (SZ.v off + 16));
  chunk_res (vals v) (Seq.slice (reveal vb) (SZ.v off) (SZ.v off + 16));
  assert (pure (eval (vals v) ==
                le_nat (Seq.slice (reveal vb) (SZ.v off) (SZ.v off + 16))));
}
#pop-options

(** The four unrolled reads, in the quantified form {!eval_le} wants. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let load_le_quant (b: Seq.seq S8.t) (s: Seq.seq nat)
  : Lemma (requires Seq.length b == 32 /\ Seq.length s == nl /\
                    Seq.index s 0 == le_nat (Seq.slice b 0 8) /\
                    Seq.index s 1 == le_nat (Seq.slice b 8 16) /\
                    Seq.index s 2 == le_nat (Seq.slice b 16 24) /\
                    Seq.index s 3 == le_nat (Seq.slice b 24 32))
          (ensures eval s == le_nat b)
  = let aux (k: nat { k < 4 })
      : Lemma (Seq.index s k == le_nat (Seq.slice b (8 * k) (8 * k + 8)))
      = if k = 0 then assert (8 * 0 == 0 /\ 8 * 0 + 8 == 8)
        else if k = 1 then assert (8 * 1 == 8 /\ 8 * 1 + 8 == 16)
        else if k = 2 then assert (8 * 2 == 16 /\ 8 * 2 + 8 == 24)
        else assert (8 * 3 == 24 /\ 8 * 3 + 8 == 32) in
    Classical.forall_intro aux;
    eval_le b s
#pop-options

#push-options "--z3rlimit 400"

(** Four limbs from thirty-two bytes.  The value may be anything below
    [2^256]; deciding whether it is a residue is the caller's business. *)
fn load_le (out: A.array S64.t) (b: A.array S8.t)
           (#vo: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (Seq.length vo' == nl /\ bnd (vals vo') base /\
        eval (vals vo') == le_nat vb)
{
  A.pts_to_len out;
  A.pts_to_len b;
  let w0 = Bytes.load_le #S64.t b 0sz;
  let w1 = Bytes.load_le #S64.t b 8sz;
  let w2 = Bytes.load_le #S64.t b 16sz;
  let w3 = Bytes.load_le #S64.t b 24sz;
  A.((out.(0sz) <- w0));
  A.((out.(1sz) <- w1));
  A.((out.(2sz) <- w2));
  A.((out.(3sz) <- w3));
  with v. assert (A.pts_to out v);
  A.pts_to_len out;
  vals_bnd v;
  assert (pure (Seq.index (vals v) 0 == le_nat (Seq.slice (reveal vb) 0 8)));
  assert (pure (Seq.index (vals v) 1 == le_nat (Seq.slice (reveal vb) 8 16)));
  assert (pure (Seq.index (vals v) 2 == le_nat (Seq.slice (reveal vb) 16 24)));
  assert (pure (Seq.index (vals v) 3 == le_nat (Seq.slice (reveal vb) 24 32)));
  load_le_quant (reveal vb) (vals v);
  assert (pure (eval (vals v) == le_nat (reveal vb)));
}
#pop-options

(** {2 Bytes out} *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"


(** The eight literal shifts the store loop performs, as the quantified
    form {!Spec.Ed25519.Scalar.store_le_ok} asks for. *)
let store_le_byte (s: Seq.seq nat) (b: Seq.seq S8.t)
                  (k: nat { k < nl }) (m: nat { m < 8 })
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\
                    bat b (8 * k) == Seq.index s k % 256 /\
                    bat b (8 * k + 1) == (Seq.index s k / pow2 8) % 256 /\
                    bat b (8 * k + 2) == (Seq.index s k / pow2 16) % 256 /\
                    bat b (8 * k + 3) == (Seq.index s k / pow2 24) % 256 /\
                    bat b (8 * k + 4) == (Seq.index s k / pow2 32) % 256 /\
                    bat b (8 * k + 5) == (Seq.index s k / pow2 40) % 256 /\
                    bat b (8 * k + 6) == (Seq.index s k / pow2 48) % 256 /\
                    bat b (8 * k + 7) == (Seq.index s k / pow2 56) % 256)
          (ensures bat b (8 * k + m) == (Seq.index s k / pow2 (8 * m)) % 256)
  = if m = 0 then (assert_norm (pow2 0 == 1);
                   assert (8 * m == 0);
                   assert (Seq.index s k / 1 == Seq.index s k))
    else if m = 1 then assert (8 * m == 8)
    else if m = 2 then assert (8 * m == 16)
    else if m = 3 then assert (8 * m == 24)
    else if m = 4 then assert (8 * m == 32)
    else if m = 5 then assert (8 * m == 40)
    else if m = 6 then assert (8 * m == 48)
    else assert (8 * m == 56)

let store_le_bridge (s: Seq.seq nat) (b: Seq.seq S8.t)
  : Lemma (requires Seq.length s == nl /\ Seq.length b == 32 /\
                    (forall (k: nat). k < nl ==>
                       bat b (8 * k) == Seq.index s k % 256 /\
                       bat b (8 * k + 1) == (Seq.index s k / pow2 8) % 256 /\
                       bat b (8 * k + 2) == (Seq.index s k / pow2 16) % 256 /\
                       bat b (8 * k + 3) == (Seq.index s k / pow2 24) % 256 /\
                       bat b (8 * k + 4) == (Seq.index s k / pow2 32) % 256 /\
                       bat b (8 * k + 5) == (Seq.index s k / pow2 40) % 256 /\
                       bat b (8 * k + 6) == (Seq.index s k / pow2 48) % 256 /\
                       bat b (8 * k + 7) == (Seq.index s k / pow2 56) % 256))
          (ensures (forall (k: nat) (m: nat). k < nl /\ m < 8 ==>
                      bat b (8 * k + m) == (Seq.index s k / pow2 (8 * m)) % 256))
  = introduce forall (k: nat) (m: nat). (k < nl /\ m < 8) ==>
      bat b (8 * k + m) == (Seq.index s k / pow2 (8 * m)) % 256
    with introduce _ ==> _
    with store_le_byte s b k m

#pop-options

#push-options "--z3rlimit 600"

fn store_le (b: A.array S8.t) (a: A.array S64.t)
            (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ Seq.length va == nl /\ bnd (vals va) base)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == nat_to_le 32 (eval (vals va)))
{
  A.pts_to_len b;
  A.pts_to_len a;
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 0 == 1);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 4sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #pa va **
    pure (SZ.v vi <= 4 /\ Seq.length v == 32 /\
          (forall (k: nat). k < SZ.v vi ==>
             S8.v (Seq.index v (8 * k)) == Seq.index (vals va) k % 256 /\
             S8.v (Seq.index v (8 * k + 1)) == Seq.index (vals va) k / pow2 8 % 256 /\
             S8.v (Seq.index v (8 * k + 2)) == Seq.index (vals va) k / pow2 16 % 256 /\
             S8.v (Seq.index v (8 * k + 3)) == Seq.index (vals va) k / pow2 24 % 256 /\
             S8.v (Seq.index v (8 * k + 4)) == Seq.index (vals va) k / pow2 32 % 256 /\
             S8.v (Seq.index v (8 * k + 5)) == Seq.index (vals va) k / pow2 40 % 256 /\
             S8.v (Seq.index v (8 * k + 6)) == Seq.index (vals va) k / pow2 48 % 256 /\
             S8.v (Seq.index v (8 * k + 7)) == Seq.index (vals va) k / pow2 56 % 256))
  decreases (4 - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let pos = SZ.mul 8sz vi;
    A.((b.(pos) <- Cast.u64_to_u8 x));
    A.((b.(SZ.add pos 1sz) <- Cast.u64_to_u8 (S64.shift_right x 8ul)));
    A.((b.(SZ.add pos 2sz) <- Cast.u64_to_u8 (S64.shift_right x 16ul)));
    A.((b.(SZ.add pos 3sz) <- Cast.u64_to_u8 (S64.shift_right x 24ul)));
    A.((b.(SZ.add pos 4sz) <- Cast.u64_to_u8 (S64.shift_right x 32ul)));
    A.((b.(SZ.add pos 5sz) <- Cast.u64_to_u8 (S64.shift_right x 40ul)));
    A.((b.(SZ.add pos 6sz) <- Cast.u64_to_u8 (S64.shift_right x 48ul)));
    A.((b.(SZ.add pos 7sz) <- Cast.u64_to_u8 (S64.shift_right x 56ul)));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  assert (pure (Seq.length v == 32 /\ bnd (vals va) base));
  store_le_bridge (vals va) v;
  store_le_ok (vals va) v;
  assert (pure (v == nat_to_le 32 (eval (vals va))));
}

#pop-options

(** {2 Comparison}

    Used once, to decide whether the [S] half of a signature is already
    below the order.  The limbs are canonical, so this is
    {!Hacl.Impl.Mont4.aeq}. *)

fn limbs_eq (a b: A.array S64.t)
            (#pa: perm) (#va: erased (Seq.seq S64.t))
            (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length va == nl /\ Seq.length vb == nl /\
        bnd (vals va) base /\ bnd (vals vb) base)
returns r: bool
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (r == (eval (vals va) = eval (vals vb)))
{
  aeq a b
}

(** {2 Reduction of a digest}

    Four chunks and three constants.  The chunks are accumulated from the
    top down so that the running sum is always a residue and the three
    multiplications are independent of each other. *)

#push-options "--z3rlimit 400"

(** One accumulation step, entirely in the specification: multiplying by a
    table that holds [R k mod q] is multiplying by [k]. *)
let fold_step (a c p: Seq.seq nat) (k: nat)
  : Lemma (requires res qmod a /\ res qmod c /\ res qmod p /\
                    eval p == pow2 256 * k % q)
          (ensures res qmod (madd qmod a (mmul qmod c p)) /\
                   eval (madd qmod a (mmul qmod c p)) == (eval a + eval c * k) % q)
  = qmod_ok (); qmod_m ();
    mmul_const c p k;
    madd_ok qmod a (mmul qmod c p);
    Math.lemma_mod_add_distr (eval a) (eval c * k) q

(** One term of the fold: [acc := acc + c k mod q], where [p] is the table
    holding [R k mod q].  [k] is ghost and only the constant is real. *)
inline_for_extraction
fn fold_chunk (acc c p ms nm: A.array S64.t) (k: erased nat)
              (#vacc: erased (Seq.seq S64.t))
              (#pc: perm) (#vc: erased (Seq.seq S64.t))
              (#pp: perm) (#vp: erased (Seq.seq S64.t))
              (#pm: perm) (#vms: erased (Seq.seq S64.t))
              (#pn: perm) (#vnm: erased (Seq.seq S64.t))
requires A.pts_to acc vacc ** A.pts_to c #pc vc ** A.pts_to p #pp vp **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (qelem vacc /\ qelem vc /\ qelem vp /\
        Seq.length vms == nl /\ Seq.length vnm == nl /\
        vals vms == qmod.ms /\ vals vnm == qmod.nm /\
        eval (vals vp) == pow2 256 * reveal k % q)
ensures exists* (vacc': Seq.seq S64.t).
  A.pts_to acc vacc' ** A.pts_to c #pc vc ** A.pts_to p #pp vp **
  A.pts_to ms #pm vms ** A.pts_to nm #pn vnm **
  pure (qelem vacc' /\ qv vacc' == (qv vacc + qv vc * reveal k) % q)
{
  qmod_ok ();
  fold_step (vals vacc) (vals vc) (vals vp) (reveal k);
  let z = S64.zero;
  let mut t = [| z; 4sz |];
  Mem.track t; A.pts_to_len t;
  let mut u = [| z; 4sz |];
  Mem.track u; A.pts_to_len u; A.pts_to_len t; A.pts_to_len u;
  amul t c p ms nm qmu qmod;
  aadd u acc t nm qmod;
  acopy acc u;
  Mem.wipe u 4sz;
  Mem.wipe t 4sz;
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The three folds, chained: the running remainder after the last one is
    the whole digest reduced once. *)
let reduce64_ok (b: Seq.seq S8.t) (r0 r1 r2 r3: nat)
  : Lemma (requires Seq.length b == 64 /\
                    r0 == le_nat (Seq.slice b 0 16) /\
                    r1 == (r0 + le_nat (Seq.slice b 16 32) * pow2 128) % q /\
                    r2 == (r1 + le_nat (Seq.slice b 32 48) * pow2 256) % q /\
                    r3 == (r2 + le_nat (Seq.slice b 48 64) * pow2 384) % q)
          (ensures r3 == le_nat b % q)
  = digest_split b;
    fold_ok r0 (le_nat (Seq.slice b 16 32) * pow2 128)
               (le_nat (Seq.slice b 32 48) * pow2 256)
               (le_nat (Seq.slice b 48 64) * pow2 384) r1 r2 r3

(** The single fold of the short form. *)
let reduce32_ok (b: Seq.seq S8.t) (r0 r1: nat)
  : Lemma (requires Seq.length b == 32 /\
                    r0 == le_nat (Seq.slice b 0 16) /\
                    r1 == (r0 + le_nat (Seq.slice b 16 32) * pow2 128) % q)
          (ensures r1 == le_nat b % q)
  = half_split b

(** Sixty-four little-endian bytes, reduced. *)
fn reduce64 (out: A.array S64.t) (h: A.array S8.t)
            (#vo: erased (Seq.seq S64.t))
            (#ph: perm) (#vh: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to h #ph vh **
  pure (Seq.length vo == nl /\ Seq.length vh == 64)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to h #ph vh **
  pure (qelem vo' /\ qv vo' == le_nat vh % q)
{
  A.pts_to_len h;
  let z = S64.zero;
  let mut c = [| z; 4sz |];
  Mem.track c; A.pts_to_len c; A.pts_to_len c;
  let ms = qms ();
  let nm = qnm ();

  load_chunk out h 0sz;
  with v0. assert (A.pts_to out v0);

  load_chunk c h 16sz;
  let p1 = qp1t ();
  pow_res 384 128;
  fold_chunk out c p1 ms nm (hide (pow2 128));
  drop_table p1;
  with v1. assert (A.pts_to out v1);

  load_chunk c h 32sz;
  let p2 = qr2t ();
  r2_res ();
  fold_chunk out c p2 ms nm (hide (pow2 256));
  drop_table p2;
  with v2. assert (A.pts_to out v2);

  load_chunk c h 48sz;
  let p3 = qp3t ();
  pow_res 640 384;
  fold_chunk out c p3 ms nm (hide (pow2 384));
  drop_table p3;
  with v3. assert (A.pts_to out v3);

  drop_table ms;
  drop_table nm;
  assert (pure (qv v0 == le_nat (Seq.slice (reveal vh) 0 16)));
  assert (pure (qv v1 == (qv v0 + le_nat (Seq.slice (reveal vh) 16 32) * pow2 128) % q));
  assert (pure (qv v2 == (qv v1 + le_nat (Seq.slice (reveal vh) 32 48) * pow2 256) % q));
  assert (pure (qv v3 == (qv v2 + le_nat (Seq.slice (reveal vh) 48 64) * pow2 384) % q));
  reduce64_ok (reveal vh) (qv v0) (qv v1) (qv v2) (qv v3);
  assert (pure (qv v3 == le_nat (reveal vh) % q));
  Mem.wipe c 4sz;
}

(** Thirty-two little-endian bytes, reduced: the same fold over two
    chunks.  The secret scalar and the [S] half of a signature both come
    in this way. *)
fn reduce32 (out: A.array S64.t) (b: A.array S8.t)
            (#vo: erased (Seq.seq S64.t))
            (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to b #pb vb **
  pure (Seq.length vo == nl /\ Seq.length vb == 32)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to b #pb vb **
  pure (qelem vo' /\ qv vo' == le_nat vb % q)
{
  A.pts_to_len b;
  let z = S64.zero;
  let mut c = [| z; 4sz |];
  Mem.track c; A.pts_to_len c; A.pts_to_len c;
  let ms = qms ();
  let nm = qnm ();

  load_chunk out b 0sz;
  with v0. assert (A.pts_to out v0);

  load_chunk c b 16sz;
  let p1 = qp1t ();
  pow_res 384 128;
  fold_chunk out c p1 ms nm (hide (pow2 128));
  drop_table p1;
  with v1. assert (A.pts_to out v1);

  drop_table ms;
  drop_table nm;
  assert (pure (qv v0 == le_nat (Seq.slice (reveal vb) 0 16)));
  assert (pure (qv v1 == (qv v0 + le_nat (Seq.slice (reveal vb) 16 32) * pow2 128) % q));
  reduce32_ok (reveal vb) (qv v0) (qv v1);
  assert (pure (qv v1 == le_nat (reveal vb) % q));
  Mem.wipe c 4sz;
}

#pop-options

#pop-options
