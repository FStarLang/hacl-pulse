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

(** The X25519 field in four sixty-four-bit words.

    The radix-[2^51] field of {!Hacl.Curve25519.Field} keeps its limbs
    short so that a product's columns can be summed in [__int128] without
    carrying, and pays for it with twenty-five multiplications to a product
    and carries that do not use the carry flag.  Here the limbs are full
    words: sixteen multiplications, and every addition is an [adc] chain
    through {!Hacl.Carry64}.  It is the representation HACL*'s fastest
    portable-looking code uses, and with [mulx] it is about a fifth faster
    than radix [2^51] under gcc and a third faster under clang.

    An element is any four words -- any number below [2^256] -- and stands
    for its residue mod [p]; {!Spec.Curve25519.Field64} has the arithmetic.
    No operation needs its inputs reduced and none promises a reduced
    output, which is what lets every operation end with a single fold of
    the carry out of the top word ([2^256 = 38 mod p]).  Only {!freeze}
    produces the canonical representative.

    Every function here is forced inline, and all but the product
    ({!mrow}, {!mrow_add}, {!mul8}) are compiled with [target("bmi2")];
    they are only reached from {!Hacl.Curve25519.Ladder64}, which is only
    called on machines that have BMI2.  The product carries no target so
    that {!Hacl.P256.Field64} can inline it too: inlined into a [bmi2]
    caller it compiles exactly as before. *)
module Hacl.Curve25519.Field64

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Curve25519.Field64
open Hacl.Spec.Bytes
open Hacl.Secret.Word.Instances

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module L = Hacl.Impl.Limb64
module K = Hacl.Carry64
module Bytes = Hacl.Impl.Bytes
module C = Spec.Curve25519
module Mem = Hacl.Mem

(** {2 The view} *)

let ix (s: Seq.seq S64.t) (i: nat) : GTot nat =
  if i < Seq.length s then S64.v (Seq.index s i) else 0

let win (s: Seq.seq S64.t) (k: nat) : GTot nat =
  ev4 (ix s k) (ix s (k + 1)) (ix s (k + 2)) (ix s (k + 3))

(** The number four words stand for. *)
let ev (s: Seq.seq S64.t) : GTot nat = win s 0

(** And eight. *)
let ev8 (s: Seq.seq S64.t) : GTot nat = win s 0 + w4 * win s 4

let fe (s: Seq.seq S64.t) : GTot C.elem = ev s % C.prime

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100 --z3refresh --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn put4 (o: A.array S64.t) (x0 x1 x2 x3: S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo ** pure (Seq.length vo == 4)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 4 /\
        Seq.index vo' 0 == x0 /\ Seq.index vo' 1 == x1 /\
        Seq.index vo' 2 == x2 /\ Seq.index vo' 3 == x3 /\
        ev vo' == ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3))
{
  A.pts_to_len o;
  A.((o.(0sz) <- x0));
  A.((o.(1sz) <- x1));
  A.((o.(2sz) <- x2));
  A.((o.(3sz) <- x3));
}

(** {2 The fold}

    Four words and a fifth, small one above them become four words: the
    fifth times thirty-eight is added at the bottom, and if that carries
    out of the top the carry is worth thirty-eight again -- and this time
    the sum it lands in is below [38 h], so there is room. *)

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fold_top (o: A.array S64.t) (x0 x1 x2 x3 h: S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo ** pure (Seq.length vo == 4 /\ S64.v h < 131072)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 4 /\
        ev vo' % C.prime ==
          (ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) + w4 * S64.v h) % C.prime)
{
  let z0 = S64.classify 0uL;
  consts ();
  let k = S64.mul_mod h (S64.classify 38uL);
  Math.small_mod (S64.v h * 38) (pow2 64);
  let mut r = z0;
  let c = K.addc z0 x0 k r;
  let s0 = !r;
  let c = K.addc c x1 z0 r;
  let s1 = !r;
  let c = K.addc c x2 z0 r;
  let s2 = !r;
  let c = K.addc c x3 z0 r;
  let s3 = !r;
  let m = S64.mul_mod c (S64.classify 38uL);
  Math.small_mod (S64.v c * 38) (pow2 64);
  assert (pure (S64.v s0 + S64.v m < w));
  Math.small_mod (S64.v s0 + S64.v m) (pow2 64);
  let o0 = S64.add_mod s0 m;
  fold38 (ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3)) (S64.v h);
  fold38 (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3)) (S64.v c);
  put4 o o0 s1 s2 s3;
}

(** The same, for a borrow out of the top: [-2^256 = -38 mod p], and when
    subtracting thirty-eight borrows again the difference was at least
    [2^256 - 38], so its bottom word has room. *)

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fold_top_sub (o: A.array S64.t) (x0 x1 x2 x3 b: S64.t) (#vo: erased (Seq.seq S64.t))
requires A.pts_to o vo ** pure (Seq.length vo == 4 /\ S64.v b <= 1)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' **
  pure (Seq.length vo' == 4 /\
        ev vo' % C.prime ==
          (ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) - w4 * S64.v b) % C.prime)
{
  let z0 = S64.classify 0uL;
  consts ();
  let k = S64.mul_mod b (S64.classify 38uL);
  Math.small_mod (S64.v b * 38) (pow2 64);
  let mut r = z0;
  let c = K.subb z0 x0 k r;
  let s0 = !r;
  let c = K.subb c x1 z0 r;
  let s1 = !r;
  let c = K.subb c x2 z0 r;
  let s2 = !r;
  let c = K.subb c x3 z0 r;
  let s3 = !r;
  let m = S64.mul_mod c (S64.classify 38uL);
  Math.small_mod (S64.v c * 38) (pow2 64);
  assert (pure (S64.v m <= S64.v s0));
  Math.small_mod (S64.v s0 - S64.v m) (pow2 64);
  let o0 = S64.sub_mod s0 m;
  fold38 (ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3)) (- (S64.v b));
  fold38 (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3)) (- (S64.v c));
  put4 o o0 s1 s2 s3;
}

(** {2 Addition and subtraction} *)

let fadd_post (vo va vb: Seq.seq S64.t) (t: int)
  : Lemma (requires ev vo % C.prime == t % C.prime /\ t == ev va + ev vb)
          (ensures fe vo == C.fadd (fe va) (fe vb))
  = fadd_ok (ev va) (ev vb)

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fadd (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == 4 /\ Seq.length va == 4 /\ Seq.length vb == 4)
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout' == 4 /\ fe vout' == C.fadd (fe va) (fe vb))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len a;
  A.pts_to_len b;
  consts ();
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  let mut r = z0;
  let c = K.addc z0 a0 b0 r;
  let s0 = !r;
  let c = K.addc c a1 b1 r;
  let s1 = !r;
  let c = K.addc c a2 b2 r;
  let s2 = !r;
  let c = K.addc c a3 b3 r;
  let s3 = !r;
  assert (pure (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) + w4 * S64.v c ==
                ev va + ev vb));
  fold_top out s0 s1 s2 s3 c;
  with vo'. assert (A.pts_to out vo');
  fadd_post vo' va vb (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) + w4 * S64.v c);
  ()
}

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fsub (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == 4 /\ Seq.length va == 4 /\ Seq.length vb == 4)
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout' == 4 /\ fe vout' == C.fsub (fe va) (fe vb))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len a;
  A.pts_to_len b;
  consts ();
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  let mut r = z0;
  let c = K.subb z0 a0 b0 r;
  let s0 = !r;
  let c = K.subb c a1 b1 r;
  let s1 = !r;
  let c = K.subb c a2 b2 r;
  let s2 = !r;
  let c = K.subb c a3 b3 r;
  let s3 = !r;
  assert (pure (ev4 (S64.v s0) (S64.v s1) (S64.v s2) (S64.v s3) - w4 * S64.v c ==
                ev va - ev vb));
  fold_top_sub out s0 s1 s2 s3 c;
  fsub_ok (ev va) (ev vb);
  ()
}

(** {2 Products}

    Schoolbook, a row at a time.  {!mrow} is one word times four, sixteen
    halves chained into five words; {!row} adds such a row into an
    accumulator at offset [k]; four words plus a row always fit in five, so
    neither has a precondition beyond the lengths. *)

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn mrow (q: A.array S64.t) (k: SZ.t) (x b0 b1 b2 b3: S64.t) (#vq: erased (Seq.seq S64.t))
requires A.pts_to q vq ** pure (Seq.length vq == 8 /\ SZ.v k <= 3)
ensures exists* (vq': Seq.seq S64.t).
  A.pts_to q vq' **
  pure (Seq.length vq' == 8 /\
        (forall (i: nat). i < SZ.v k ==> ix vq' i == ix vq i) /\
        S64.v x * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) <= rowmax /\
        win vq' (SZ.v k) + w4 * ix vq' (SZ.v k + 4) ==
          S64.v x * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len q;
  consts ();
  let p0 = S128.mul_wide x b0;
  let l0 = L.lo p0;
  let h0 = L.hi p0;
  L.lo_hi p0;
  let p1 = S128.mul_wide x b1;
  let l1 = L.lo p1;
  let h1 = L.hi p1;
  L.lo_hi p1;
  let p2 = S128.mul_wide x b2;
  let l2 = L.lo p2;
  let h2 = L.hi p2;
  L.lo_hi p2;
  let p3 = S128.mul_wide x b3;
  let l3 = L.lo p3;
  let h3 = L.hi p3;
  L.lo_hi p3;
  let mut r = z0;
  let c1 = K.addc z0 l1 h0 r;
  let r1 = !r;
  let c2 = K.addc c1 l2 h1 r;
  let r2 = !r;
  let c3 = K.addc c2 l3 h2 r;
  let r3 = !r;
  row (S64.v x) (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3)
      (S64.v l0) (S64.v h0) (S64.v l1) (S64.v h1) (S64.v l2) (S64.v h2)
      (S64.v l3) (S64.v h3) (S64.v r1) (S64.v r2) (S64.v r3)
      (S64.v c1) (S64.v c2) (S64.v c3);
  Math.small_mod (S64.v h3 + S64.v c3) (pow2 64);
  let r4 = S64.add_mod h3 c3;
  A.((q.(k) <- l0));
  A.((q.(SZ.add k 1sz) <- r1));
  A.((q.(SZ.add k 2sz) <- r2));
  A.((q.(SZ.add k 3sz) <- r3));
  A.((q.(SZ.add k 4sz) <- r4));
}

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn mrow_add (t: A.array S64.t) (k: SZ.t) (x b0 b1 b2 b3: S64.t) (#vt: erased (Seq.seq S64.t))
requires A.pts_to t vt ** pure (Seq.length vt == 8 /\ SZ.v k <= 3)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' **
  pure (Seq.length vt' == 8 /\
        (forall (i: nat). i < SZ.v k ==> ix vt' i == ix vt i) /\
        win vt' (SZ.v k) + w4 * ix vt' (SZ.v k + 4) ==
          win vt (SZ.v k) + S64.v x * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let z = z0;
  let mut q = [| z; 8sz |];
  Mem.track q;
  A.pts_to_len q;
  mrow q 0sz x b0 b1 b2 b3;
  let q0 = A.(q.(0sz));
  let q1 = A.(q.(1sz));
  let q2 = A.(q.(2sz));
  let q3 = A.(q.(3sz));
  let q4 = A.(q.(4sz));
  let y0 = A.(t.(k));
  let y1 = A.(t.(SZ.add k 1sz));
  let y2 = A.(t.(SZ.add k 2sz));
  let y3 = A.(t.(SZ.add k 3sz));
  let mut r = z0;
  let c = K.addc z0 y0 q0 r;
  let s0 = !r;
  let c = K.addc c y1 q1 r;
  let s1 = !r;
  let c = K.addc c y2 q2 r;
  let s2 = !r;
  let c = K.addc c y3 q3 r;
  let s3 = !r;
  assert (pure (S64.v q4 + S64.v c < w));
  Math.small_mod (S64.v q4 + S64.v c) (pow2 64);
  let s4 = S64.add_mod q4 c;
  A.((t.(k) <- s0));
  A.((t.(SZ.add k 1sz) <- s1));
  A.((t.(SZ.add k 2sz) <- s2));
  A.((t.(SZ.add k 3sz) <- s3));
  A.((t.(SZ.add k 4sz) <- s4));
  Mem.nowipe q;
}

(** Eight words to four, with [2^256 = 38]: the top four times thirty-eight
    are four double words, added in as two chains, the low halves at their
    own positions and the high halves one up; what spills out of the top is
    below forty, and {!fold_top} takes it. *)

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn red (o t: A.array S64.t) (#vo: erased (Seq.seq S64.t))
       (#pt: perm) (#vt: erased (Seq.seq S64.t))
requires A.pts_to o vo ** A.pts_to t #pt vt **
  pure (Seq.length vo == 4 /\ Seq.length vt == 8)
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to o vo' ** A.pts_to t #pt vt **
  pure (Seq.length vo' == 4 /\ ev vo' % C.prime == ev8 vt % C.prime)
{
  let z0 = S64.classify 0uL;
  A.pts_to_len t;
  consts ();
  let k38 = S64.classify 38uL;
  let t0 = A.(t.(0sz));
  let t1 = A.(t.(1sz));
  let t2 = A.(t.(2sz));
  let t3 = A.(t.(3sz));
  let t4 = A.(t.(4sz));
  let t5 = A.(t.(5sz));
  let t6 = A.(t.(6sz));
  let t7 = A.(t.(7sz));
  let p0 = S128.mul_wide t4 k38;
  let l0 = L.lo p0;
  let h0 = L.hi p0;
  L.lo_hi p0;
  let p1 = S128.mul_wide t5 k38;
  let l1 = L.lo p1;
  let h1 = L.hi p1;
  L.lo_hi p1;
  let p2 = S128.mul_wide t6 k38;
  let l2 = L.lo p2;
  let h2 = L.hi p2;
  L.lo_hi p2;
  let p3 = S128.mul_wide t7 k38;
  let l3 = L.lo p3;
  let h3 = L.hi p3;
  L.lo_hi p3;
  assert (pure (S64.v h0 < 38 /\ S64.v h1 < 38 /\ S64.v h2 < 38 /\ S64.v h3 < 38));
  let mut r = z0;
  let c = K.addc z0 t0 l0 r;
  let r0 = !r;
  let c = K.addc c t1 l1 r;
  let r1 = !r;
  let c = K.addc c t2 l2 r;
  let r2 = !r;
  let c = K.addc c t3 l3 r;
  let r3 = !r;
  Math.small_mod (S64.v h3 + S64.v c) (pow2 64);
  let h = S64.add_mod h3 c;
  let d = K.addc z0 r1 h0 r;
  let q1 = !r;
  let d = K.addc d r2 h1 r;
  let q2 = !r;
  let d = K.addc d r3 h2 r;
  let q3 = !r;
  Math.small_mod (S64.v h + S64.v d) (pow2 64);
  let h' = S64.add_mod h d;
  fold38 (win vt 0) (win vt 4);
  assert (pure (ev4 (S64.v r0) (S64.v q1) (S64.v q2) (S64.v q3) + w4 * S64.v h' ==
                win vt 0 + 38 * win vt 4));
  fold_top o r0 q1 q2 q3 h';
}


let fmul_post (o y va vb: Seq.seq S64.t)
  : Lemma (requires ev o % C.prime == ev8 y % C.prime /\ ev8 y == ev va * ev vb)
          (ensures fe o == C.fmul (fe va) (fe vb))
  = fmul_ok (ev va) (ev vb)

let ev8_split (y u v x: Seq.seq S64.t)
  : Lemma (requires ix y 0 == ix u 0 /\ ix y 1 == ix v 1 /\ ix y 2 == ix x 2)
          (ensures ev8 y == ev4 (ix u 0) (ix v 1) (ix x 2) (ix y 3) +
                            w4 * ev4 (ix y 4) (ix y 5) (ix y 6) (ix y 7))
  = ()

let fmul_glue (va vb u v x y: Seq.seq S64.t) (a0 a1 a2 a3 b0 b1 b2 b3: S64.t)
  : Lemma (requires
      Seq.length va == 4 /\ Seq.length vb == 4 /\
      a0 == Seq.index va 0 /\ a1 == Seq.index va 1 /\
      a2 == Seq.index va 2 /\ a3 == Seq.index va 3 /\
      b0 == Seq.index vb 0 /\ b1 == Seq.index vb 1 /\
      b2 == Seq.index vb 2 /\ b3 == Seq.index vb 3 /\
      win u 0 + w4 * ix u 4 == S64.v a0 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) /\
      win v 1 + w4 * ix v 5 == win u 1 + S64.v a1 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) /\
      win x 2 + w4 * ix x 6 == win v 2 + S64.v a2 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) /\
      win y 3 + w4 * ix y 7 == win x 3 + S64.v a3 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) /\
      ix y 0 == ix u 0 /\ ix y 1 == ix v 1 /\ ix y 2 == ix x 2)
    (ensures ev8 y == ev va * ev vb)
  = let bb = ev vb in
    let eb = ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3) in
    let ea = ev4 (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) in
    assert (eb == bb);
    assert (ev va == ea);
    assert (S64.v a0 * eb == S64.v a0 * bb /\ S64.v a1 * eb == S64.v a1 * bb /\
            S64.v a2 * eb == S64.v a2 * bb /\ S64.v a3 * eb == S64.v a3 * bb);
    mul_combine (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3) bb
      (ix u 0) (ix u 1) (ix u 2) (ix u 3) (ix u 4)
      (ix v 1) (ix v 2) (ix v 3) (ix v 4) (ix v 5)
      (ix x 2) (ix x 3) (ix x 4) (ix x 5) (ix x 6)
      (ix y 3) (ix y 4) (ix y 5) (ix y 6) (ix y 7);
    ev8_split y u v x;
    assert (ea * bb == ev va * ev vb)

#push-options "--z3rlimit 200"

[@@ CInline; CPrologue "__attribute__((always_inline))"]
fn mul8 (t a b: A.array S64.t)
        (#vt: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to t vt ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt == 8 /\ Seq.length va == 4 /\ Seq.length vb == 4)
ensures exists* (vt': Seq.seq S64.t).
  A.pts_to t vt' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vt' == 8 /\ ev8 vt' == ev va * ev vb)
{
  A.pts_to_len a;
  A.pts_to_len b;
  A.pts_to_len t;
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  let a0 = A.(a.(0sz));
  mrow t 0sz a0 b0 b1 b2 b3;
  with u. assert (A.pts_to t u);
  assert (pure (win u 0 + w4 * ix u 4 == S64.v a0 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3)));
  let a1 = A.(a.(1sz));
  mrow_add t 1sz a1 b0 b1 b2 b3;
  with v. assert (A.pts_to t v);
  assert (pure (ix v 0 == ix u 0));
  assert (pure (win v 1 + w4 * ix v 5 == win u 1 + S64.v a1 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3)));
  let a2 = A.(a.(2sz));
  mrow_add t 2sz a2 b0 b1 b2 b3;
  with x. assert (A.pts_to t x);
  assert (pure (ix x 0 == ix u 0 /\ ix x 1 == ix v 1));
  assert (pure (win x 2 + w4 * ix x 6 == win v 2 + S64.v a2 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3)));
  let a3 = A.(a.(3sz));
  mrow_add t 3sz a3 b0 b1 b2 b3;
  with y. assert (A.pts_to t y);
  assert (pure (ix y 0 == ix u 0 /\ ix y 1 == ix v 1 /\ ix y 2 == ix x 2));
  assert (pure (win y 3 + w4 * ix y 7 == win x 3 + S64.v a3 * ev4 (S64.v b0) (S64.v b1) (S64.v b2) (S64.v b3)));
  fmul_glue va vb u v x y a0 a1 a2 a3 b0 b1 b2 b3;
  assert (pure (ev8 y == ev va * ev vb));
}

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fmul (out a b: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
        (#pb: perm) (#vb: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout == 4 /\ Seq.length va == 4 /\ Seq.length vb == 4)
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va ** A.pts_to b #pb vb **
  pure (Seq.length vout' == 4 /\ fe vout' == C.fmul (fe va) (fe vb))
{
  let z0 = S64.classify 0uL;
  let z = z0;
  let mut t = [| z; 8sz |];
  Mem.track t;
  A.pts_to_len t;
  mul8 t a b;
  with y. assert (A.pts_to t y);
  red out t;
  with o. assert (A.pts_to out o);
  fmul_post o y va vb;
  assert (pure (fe o == C.fmul (fe va) (fe vb)));
  Mem.nowipe t;
}

#pop-options

(** Squaring is a product with itself: a dedicated squaring saves six of
    the sixteen multiplications but measures within a few percent here. *)
[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fsqr (out a: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == 4 /\ Seq.length va == 4)
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (Seq.length vout' == 4 /\ fe vout' == C.fmul (fe va) (fe va))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len a;
  let x0 = A.(a.(0sz));
  let x1 = A.(a.(1sz));
  let x2 = A.(a.(2sz));
  let x3 = A.(a.(3sz));
  let z = z0;
  let mut b = [| z; 4sz |];
  Mem.track b;
  put4 b x0 x1 x2 x3;
  fmul out a b;
  Mem.nowipe b;
}

(** {2 Times [a24]}

    Four words times [121665] is four words and a fifth below [121665],
    which {!fold_top} takes. *)

(** The sum behind {!fscale}: linear once the products are named. *)
let scale_sum (ea a0 a1 a2 a3 l0 h0 l1 h1 l2 h2 l3 h3 r1 r2 r3 c1 c2 c3 h: int)
  : Lemma (requires ea == ev4 a0 a1 a2 a3 /\
                    l0 + w * h0 == a0 * 121665 /\ l1 + w * h1 == a1 * 121665 /\
                    l2 + w * h2 == a2 * 121665 /\ l3 + w * h3 == a3 * 121665 /\
                    r1 + w * c1 == l1 + h0 /\ r2 + w * c2 == l2 + h1 + c1 /\
                    r3 + w * c3 == l3 + h2 + c2 /\ h == h3 + c3)
          (ensures ev4 l0 r1 r2 r3 + w4 * h == 121665 * ea)
  = ()

let scale_post (vo va: Seq.seq S64.t) (t: int)
  : Lemma (requires ev vo % C.prime == t % C.prime /\ t == 121665 * ev va)
          (ensures fe vo == C.fmul C.a24 (fe va))
  = Math.lemma_mod_mul_distr_r 121665 (ev va) C.prime

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fscale (out a: A.array S64.t)
          (#vout: erased (Seq.seq S64.t))
          (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == 4 /\ Seq.length va == 4)
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (Seq.length vout' == 4 /\ fe vout' == C.fmul C.a24 (fe va))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len a;
  consts ();
  let k = S64.classify 121665uL;
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let p0 = S128.mul_wide a0 k;
  let l0 = L.lo p0;
  let h0 = L.hi p0;
  L.lo_hi p0;
  let p1 = S128.mul_wide a1 k;
  let l1 = L.lo p1;
  let h1 = L.hi p1;
  L.lo_hi p1;
  let p2 = S128.mul_wide a2 k;
  let l2 = L.lo p2;
  let h2 = L.hi p2;
  L.lo_hi p2;
  let p3 = S128.mul_wide a3 k;
  let l3 = L.lo p3;
  let h3 = L.hi p3;
  L.lo_hi p3;
  assert (pure (S64.v h3 < 121665));
  let mut r = z0;
  let c1 = K.addc z0 l1 h0 r;
  let r1 = !r;
  let c2 = K.addc c1 l2 h1 r;
  let r2 = !r;
  let c = K.addc c2 l3 h2 r;
  let r3 = !r;
  Math.small_mod (S64.v h3 + S64.v c) (pow2 64);
  let h = S64.add_mod h3 c;
  scale_sum (ev va) (S64.v a0) (S64.v a1) (S64.v a2) (S64.v a3)
    (S64.v l0) (S64.v h0) (S64.v l1) (S64.v h1) (S64.v l2) (S64.v h2)
    (S64.v l3) (S64.v h3) (S64.v r1) (S64.v r2) (S64.v r3)
    (S64.v c1) (S64.v c2) (S64.v c) (S64.v h);
  assert (pure (ev4 (S64.v l0) (S64.v r1) (S64.v r2) (S64.v r3) + w4 * S64.v h ==
                121665 * ev va));
  fold_top out l0 r1 r2 r3 h;
  with vo'. assert (A.pts_to out vo');
  scale_post vo' va (ev4 (S64.v l0) (S64.v r1) (S64.v r2) (S64.v r3) + w4 * S64.v h);
  ()
}

(** {2 Moves} *)

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn cswap (sel: S64.t) (a b: A.array S64.t)
         (#va: erased (Seq.seq S64.t)) (#vb: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to b vb **
  pure (Seq.length va == 4 /\ Seq.length vb == 4 /\
        (S64.v sel == 0 \/ S64.v sel == pow2 64 - 1))
ensures exists* (va': Seq.seq S64.t) (vb': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b vb' **
  pure (Seq.length va' == 4 /\ Seq.length vb' == 4 /\
        (if S64.v sel = 0 then va' == reveal va /\ vb' == reveal vb
                          else va' == reveal vb /\ vb' == reveal va))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let a0 = A.(a.(0sz));
  let a1 = A.(a.(1sz));
  let a2 = A.(a.(2sz));
  let a3 = A.(a.(3sz));
  let b0 = A.(b.(0sz));
  let b1 = A.(b.(1sz));
  let b2 = A.(b.(2sz));
  let b3 = A.(b.(3sz));
  put4 a (S64.select sel b0 a0) (S64.select sel b1 a1) (S64.select sel b2 a2) (S64.select sel b3 a3);
  put4 b (S64.select sel a0 b0) (S64.select sel a1 b1) (S64.select sel a2 b2) (S64.select sel a3 b3);
  with x. assert (A.pts_to a x);
  with y. assert (A.pts_to b y);
  assert (pure (if S64.v sel = 0 then x `Seq.equal` reveal va /\ y `Seq.equal` reveal vb
                                 else x `Seq.equal` reveal vb /\ y `Seq.equal` reveal va));
}

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn copy (dst src: A.array S64.t)
        (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == 4 /\ Seq.length vs == 4)
ensures exists* (vd': Seq.seq S64.t).
  A.pts_to dst vd' ** A.pts_to src #ps vs ** pure (vd' == reveal vs)
{
  A.pts_to_len src;
  let x0 = A.(src.(0sz));
  let x1 = A.(src.(1sz));
  let x2 = A.(src.(2sz));
  let x3 = A.(src.(3sz));
  put4 dst x0 x1 x2 x3;
  with v. assert (A.pts_to dst v);
  assert (pure (v `Seq.equal` reveal vs));
}

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn set_small (a: A.array S64.t) (x: U64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == 4)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** pure (Seq.length va' == 4 /\ ev va' == U64.v x)
{
  let z0 = S64.classify 0uL;
  put4 a (S64.classify x) z0 z0 z0;
}

(** {2 Bytes} *)

[@@ CPrologue "__attribute__((target(\"bmi2\")))"]
fn load (a: A.array S64.t) (b: A.array S8.t)
        (#va: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to b #pb vb **
  pure (Seq.length va == 4 /\ Seq.length vb == 32)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b #pb vb **
  pure (Seq.length va' == 4 /\ ev va' == le_nat vb % pow2 255)
{
  A.pts_to_len b;
  consts ();
  let l0 = Bytes.load_le #S64.t b 0sz;
  let l1 = Bytes.load_le #S64.t b 8sz;
  let l2 = Bytes.load_le #S64.t b 16sz;
  let l3 = Bytes.load_le #S64.t b 24sz;
  let l3m = S64.logand l3 (S64.mask_low 63ul);
  S64.logand_mask_low l3 63ul;
  load_split vb;
  mask_top (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3);
  put4 a l0 l1 l2 l3m;
}

(** The postcondition of {!Hacl.Impl.Bytes.store_le} at [S64.t]. *)
[@@"opaque_to_smt"]
let store_post (vb vb': Seq.seq S8.t) (off: SZ.t) (x: S64.t) : prop =
  Seq.length vb' == Seq.length vb /\
  SZ.v off + Hacl.Secret.Word.bytes #S64.t <= Seq.length vb' /\
  (forall (k: nat). k < Hacl.Secret.Word.bytes #S64.t ==>
     S8.v (Seq.index vb' (SZ.v off + k)) == (Hacl.Secret.Word.v x / pow2 (8 * k)) % 256) /\
  (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + Hacl.Secret.Word.bytes #S64.t ==>
     Seq.index vb' k == Seq.index vb k)

let store_post_elim (vb vb': Seq.seq S8.t) (off: SZ.t) (x: S64.t) (k: nat)
  : Lemma (requires store_post vb vb' off x)
          (ensures Seq.length vb' == Seq.length vb /\ SZ.v off + 8 <= Seq.length vb' /\
                   (k < 8 ==> S8.v (Seq.index vb' (SZ.v off + k)) == (S64.v x / pow2 (8 * k)) % 256) /\
                   (k < Seq.length vb /\ (k < SZ.v off \/ k >= SZ.v off + 8) ==>
                      Seq.index vb' k == Seq.index vb k))
  = FStar.Pervasives.reveal_opaque (`%store_post) store_post;
    assert_norm (Hacl.Secret.Word.bytes #S64.t == 8);
    assert_norm (Hacl.Secret.Word.v x == S64.v x)

let store4_ok (v0 v1 v2 v3 v4: Seq.seq S8.t) (l0 l1 l2 l3: S64.t)
  : Lemma (requires Seq.length v0 == 32 /\
                    store_post v0 v1 0sz l0 /\ store_post v1 v2 8sz l1 /\
                    store_post v2 v3 16sz l2 /\ store_post v3 v4 24sz l3)
          (ensures stored v4 (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3))
  = assert (SZ.v 0sz == 0 /\ SZ.v 8sz == 8 /\ SZ.v 16sz == 16 /\ SZ.v 24sz == 24);
    store_post_elim v0 v1 0sz l0 0;
    store_post_elim v1 v2 8sz l1 0;
    store_post_elim v2 v3 16sz l2 0;
    store_post_elim v3 v4 24sz l3 0;
    let aux (k: nat { k < 8 })
      : Lemma (S8.v (Seq.index v4 k) == (S64.v l0 / pow2 (8 * k)) % 256 /\
               S8.v (Seq.index v4 (8 + k)) == (S64.v l1 / pow2 (8 * k)) % 256 /\
               S8.v (Seq.index v4 (16 + k)) == (S64.v l2 / pow2 (8 * k)) % 256 /\
               S8.v (Seq.index v4 (24 + k)) == (S64.v l3 / pow2 (8 * k)) % 256)
      = store_post_elim v0 v1 0sz l0 k;
        store_post_elim v1 v2 8sz l1 k;
        store_post_elim v2 v3 16sz l2 k;
        store_post_elim v3 v4 24sz l3 k;
        store_post_elim v2 v3 16sz l2 (8 + k);
        store_post_elim v3 v4 24sz l3 (8 + k);
        store_post_elim v3 v4 24sz l3 (16 + k)
    in
    introduce forall (k: nat). k < 8 ==> S8.v (Seq.index v4 k) == (S64.v l0 / pow2 (8 * k)) % 256
    with introduce _ ==> _ with aux k;
    introduce forall (k: nat). k < 8 ==> S8.v (Seq.index v4 (8 + k)) == (S64.v l1 / pow2 (8 * k)) % 256
    with introduce _ ==> _ with aux k;
    introduce forall (k: nat). k < 8 ==> S8.v (Seq.index v4 (16 + k)) == (S64.v l2 / pow2 (8 * k)) % 256
    with introduce _ ==> _ with aux k;
    introduce forall (k: nat). k < 8 ==> S8.v (Seq.index v4 (24 + k)) == (S64.v l3 / pow2 (8 * k)) % 256
    with introduce _ ==> _ with aux k;
    assert (Seq.length v4 == 32)

[@@ CPrologue "__attribute__((target(\"bmi2\")))"]
fn store (b: A.array S8.t) (a: A.array S64.t)
         (#vb: erased (Seq.seq S8.t)) (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #pa va **
  pure (Seq.length vb == 32 /\ Seq.length va == 4)
ensures exists* (vb': Seq.seq S8.t).
  A.pts_to b vb' ** A.pts_to a #pa va **
  pure (vb' == nat_to_le 32 (ev va))
{
  A.pts_to_len b;
  A.pts_to_len a;
  consts ();
  let l0 = A.(a.(0sz));
  let l1 = A.(a.(1sz));
  let l2 = A.(a.(2sz));
  let l3 = A.(a.(3sz));
  Bytes.store_le #S64.t b 0sz l0;
  with v1. assert (A.pts_to b v1);
  Bytes.store_le #S64.t b 8sz l1;
  with v2. assert (A.pts_to b v2);
  Bytes.store_le #S64.t b 16sz l2;
  with v3. assert (A.pts_to b v3);
  Bytes.store_le #S64.t b 24sz l3;
  with v. assert (A.pts_to b v);
  FStar.Pervasives.reveal_opaque (`%store_post) store_post;
  store4_ok vb v1 v2 v3 v l0 l1 l2 l3;
  assert (pure (stored v (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3)));
  store_ok v (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3);
  assert (pure (ev va == ev4 (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3)));
  assert (pure (v == nat_to_le 32 (ev va)));
}

(** {2 Freezing}

    Twice: bit 255 comes off the top and nineteen goes in at the bottom.
    The first pass leaves less than [2^255 + 19] and the second less than
    [2^255].  Then the number is at least [p] exactly when adding nineteen
    reaches bit 255, and that sum with the bit cleared is the number minus
    [p]. *)

[@@ CInline; CPrologue "__attribute__((target(\"bmi2\"), always_inline))"]
fn fold255 (a: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == 4)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' **
  pure (Seq.length va' == 4 /\ ev va' % C.prime == ev va % C.prime /\
        ev va' < pow2 255 + 19 /\ (ev va < pow2 255 + 19 ==> ev va' < pow2 255))
{
  let z0 = S64.classify 0uL;
  A.pts_to_len a;
  consts ();
  let l0 = A.(a.(0sz));
  let l1 = A.(a.(1sz));
  let l2 = A.(a.(2sz));
  let l3 = A.(a.(3sz));
  let t = S64.shift_right l3 63ul;
  let l3m = S64.logand l3 (S64.mask_low 63ul);
  S64.logand_mask_low l3 63ul;
  split255 (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3);
  let k = S64.mul_mod t (S64.classify 19uL);
  Math.small_mod (S64.v t * 19) (pow2 64);
  let mut r = z0;
  let c = K.addc z0 l0 k r;
  let s0 = !r;
  let c = K.addc c l1 z0 r;
  let s1 = !r;
  let c = K.addc c l2 z0 r;
  let s2 = !r;
  let c = K.addc c l3m z0 r;
  let s3 = !r;
  fold255_ok (ev4 (S64.v l0) (S64.v l1) (S64.v l2) (S64.v l3m)) (S64.v t);
  assert (pure (S64.v c == 0));
  put4 a s0 s1 s2 s3;
}

let carry_out_zero (y x: nat) (c: int)
  : Lemma (requires y + w4 * c == x + 19 /\ x < pow2 255 /\ 0 <= c /\ c <= 1)
          (ensures c == 0)
  = consts ()

[@@ CPrologue "__attribute__((target(\"bmi2\")))"]
fn freeze (a: A.array S64.t) (#va: erased (Seq.seq S64.t))
requires A.pts_to a va ** pure (Seq.length va == 4)
ensures exists* (va': Seq.seq S64.t).
  A.pts_to a va' ** pure (Seq.length va' == 4 /\ ev va' == ev va % C.prime)
{
  let z0 = S64.classify 0uL;
  consts ();
  fold255 a;
  fold255 a;
  with v2. assert (A.pts_to a v2);
  A.pts_to_len a;
  let x0 = A.(a.(0sz));
  let x1 = A.(a.(1sz));
  let x2 = A.(a.(2sz));
  let x3 = A.(a.(3sz));
  let mut r = z0;
  let c = K.addc z0 x0 (S64.classify 19uL) r;
  let y0 = !r;
  let c = K.addc c x1 z0 r;
  let y1 = !r;
  let c = K.addc c x2 z0 r;
  let y2 = !r;
  let c = K.addc c x3 z0 r;
  let y3 = !r;
  assert (pure (ev4 (S64.v y0) (S64.v y1) (S64.v y2) (S64.v y3) + w4 * S64.v c ==
                ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3) + 19));
  assert (pure (ev v2 == ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3)));
  carry_out_zero (ev4 (S64.v y0) (S64.v y1) (S64.v y2) (S64.v y3)) (ev v2) (S64.v c);
  assert (pure (S64.v c == 0));
  let t = S64.shift_right y3 63ul;
  let y3m = S64.logand y3 (S64.mask_low 63ul);
  S64.logand_mask_low y3 63ul;
  split255 (S64.v y0) (S64.v y1) (S64.v y2) (S64.v y3);
  final_ok (ev v2) (S64.v t) (ev4 (S64.v y0) (S64.v y1) (S64.v y2) (S64.v y3m));
  let m = S64.eq_mask t (S64.classify 1uL);
  let o0 = S64.select m y0 x0;
  let o1 = S64.select m y1 x1;
  let o2 = S64.select m y2 x2;
  let o3 = S64.select m y3m x3;
  assert (pure (S64.v t == 1 ==> (o0 == y0 /\ o1 == y1 /\ o2 == y2 /\ o3 == y3m)));
  assert (pure (S64.v t == 0 ==> (o0 == x0 /\ o1 == x1 /\ o2 == x2 /\ o3 == x3)));
  assert (pure (ev v2 == ev4 (S64.v x0) (S64.v x1) (S64.v x2) (S64.v x3)));
  assert (pure (ev4 (S64.v o0) (S64.v o1) (S64.v o2) (S64.v o3) == ev v2 % C.prime));
  assert (pure (ev v2 % C.prime == ev va % C.prime));
  put4 a o0 o1 o2 o3;
  with v3. assert (A.pts_to a v3);
  assert (pure (ev v3 == ev va % C.prime));
}

#pop-options
