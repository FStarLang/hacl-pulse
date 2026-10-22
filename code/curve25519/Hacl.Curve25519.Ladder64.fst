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

(** X25519 over {!Hacl.Curve25519.Field64}.

    {!Hacl.Curve25519}'s ladder, step for step, with the element four full
    words instead of five fifty-one-bit limbs.  The proof is the same
    proof: every field operation has the same specification in terms of
    {!Spec.Curve25519}, so the ladder's bookkeeping carries over unchanged.

    Everything here is compiled with [target("bmi2")], which lets the field
    operations -- forced inline -- use [mulx] and [adc]; {!Hacl.Curve25519}
    calls {!scalarmult64} only when {!Hacl.Carry64.supported} says the
    machine has BMI2. *)
module Hacl.Curve25519.Ladder64

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Spec.Bytes
open Hacl.Curve25519.Field64
open Hacl.Curve25519.Inverse64

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
module Cast = Hacl.Secret.Cast
module Copy = Hacl.Impl.Copy
module Loops = Hacl.Spec.Loops
module C = Spec.Curve25519
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60 --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

(** {2 One ladder step}

    As in {!Hacl.Curve25519}: RFC 7748 section 5's formulas, with the seven temporaries laid out so
    that nothing is read after it has been overwritten:

      [t0 = x2+z2], [t1 = x2-z2], [t2 = x3+z3], [t3 = x3-z3],
      [t4 = t3*t0], [t5 = t2*t1], then [t2 = t0^2] and [t3 = t1^2] reuse the
      two that are finished with. *)

#push-options "--z3rlimit 200"

[@@ CPrologue "__attribute__((target(\"bmi2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn add_and_double (x2 z2 x3 z3 t0 t1 t2 t3 t4 t5: A.array S64.t)
                   (x1: A.array S64.t)
                  (#vx2: erased (Seq.seq S64.t)) (#vz2: erased (Seq.seq S64.t))
                  (#vx3: erased (Seq.seq S64.t)) (#vz3: erased (Seq.seq S64.t))
                  (#v0: erased (Seq.seq S64.t)) (#v1: erased (Seq.seq S64.t))
                  (#v2: erased (Seq.seq S64.t)) (#v3: erased (Seq.seq S64.t))
                  (#v4: erased (Seq.seq S64.t)) (#v5: erased (Seq.seq S64.t))
                  (#p1: perm) (#vx1: erased (Seq.seq S64.t))
requires
  A.pts_to x2 vx2 ** A.pts_to z2 vz2 ** A.pts_to x3 vx3 ** A.pts_to z3 vz3 **
  A.pts_to t0 v0 ** A.pts_to t1 v1 ** A.pts_to t2 v2 ** A.pts_to t3 v3 **
  A.pts_to t4 v4 ** A.pts_to t5 v5 **
  A.pts_to x1 #p1 vx1 **
  pure (Seq.length vx2 == 4 /\ Seq.length vz2 == 4 /\ Seq.length vx3 == 4 /\
        Seq.length vz3 == 4 /\ Seq.length vx1 == 4 /\
        Seq.length v0 == 4 /\ Seq.length v1 == 4 /\ Seq.length v2 == 4 /\
        Seq.length v3 == 4 /\ Seq.length v4 == 4 /\ Seq.length v5 == 4)
ensures exists* (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t).
  A.pts_to x2 wx2 ** A.pts_to z2 wz2 ** A.pts_to x3 wx3 ** A.pts_to z3 wz3 **
  A.pts_to t0 w0 ** A.pts_to t1 w1 ** A.pts_to t2 w2 ** A.pts_to t3 w3 **
  A.pts_to t4 w4 ** A.pts_to t5 w5 **
  A.pts_to x1 #p1 vx1 **
  pure (Seq.length wx2 == 4 /\ Seq.length wz2 == 4 /\ Seq.length wx3 == 4 /\
        Seq.length wz3 == 4 /\
        Seq.length w0 == 4 /\ Seq.length w1 == 4 /\ Seq.length w2 == 4 /\
        Seq.length w3 == 4 /\ Seq.length w4 == 4 /\ Seq.length w5 == 4 /\ 
        ((fe wx2, fe wz2), (fe wx3, fe wz3)) ==
          C.add_and_double (fe vx1)
            (fe vx2, fe vz2)
            (fe vx3, fe vz3))
{
  fadd t0 x2 z2;                          (* a  *)
  fsub t1 x2 z2;                          (* b  *)
  fadd t2 x3 z3;                          (* c  *)
  fsub t3 x3 z3;                          (* d  *)
  fmul t4 t3 t0;                      (* da *)
  fmul t5 t2 t1;                      (* cb *)
  fsqr t2 t0;                             (* aa *)
  fsqr t3 t1;                             (* bb *)
  fadd t0 t4 t5;                          (* da + cb *)
  fsub t1 t4 t5;                          (* da - cb *)
  fsqr x3 t0;                             (* x3' *)
  fsqr t4 t1;
  fmul z3 x1 t4;                      (* z3' *)
  fsub t5 t2 t3;                          (* e = aa - bb *)
  fmul x2 t2 t3;                      (* x2' = aa * bb *)
  with e. assert (A.pts_to t5 e);
  fscale t0 t5;
  with s. assert (A.pts_to t0 s);
  assert (pure (fe s == C.fmul C.a24 (fe e)));
  fadd t1 t2 t0;                          (* aa + a24 e *)
  fmul z2 t5 t1;                      (* z2' *)
}

#pop-options

(** {2 One step of the ladder}

    [ks] is the clamped scalar.  Step [i] consumes bit [255 - i], most
    significant first; the mask is the bit spread across a word, and the
    swaps are the only thing the bit does.  Kept as its own function so that
    the loop below has nothing to prove but the arithmetic on the index. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"

[@@ CPrologue "__attribute__((target(\"bmi2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn ladder_one (x2 z2 x3 z3 t0 t1 t2 t3 t4 t5: A.array S64.t)
               (x1: A.array S64.t)
              (ks: A.array S8.t) (n: SZ.t { SZ.v n < 256 })
              (#vx2: erased (Seq.seq S64.t)) (#vz2: erased (Seq.seq S64.t))
              (#vx3: erased (Seq.seq S64.t)) (#vz3: erased (Seq.seq S64.t))
              (#v0: erased (Seq.seq S64.t)) (#v1: erased (Seq.seq S64.t))
              (#v2: erased (Seq.seq S64.t)) (#v3: erased (Seq.seq S64.t))
              (#v4: erased (Seq.seq S64.t)) (#v5: erased (Seq.seq S64.t))
              (#p1: perm) (#vx1: erased (Seq.seq S64.t))
              (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  A.pts_to x2 vx2 ** A.pts_to z2 vz2 ** A.pts_to x3 vx3 ** A.pts_to z3 vz3 **
  A.pts_to t0 v0 ** A.pts_to t1 v1 ** A.pts_to t2 v2 ** A.pts_to t3 v3 **
  A.pts_to t4 v4 ** A.pts_to t5 v5 **
  A.pts_to x1 #p1 vx1 ** A.pts_to ks #pk vk **
  pure (Seq.length vx2 == 4 /\ Seq.length vz2 == 4 /\ Seq.length vx3 == 4 /\
        Seq.length vz3 == 4 /\ Seq.length vx1 == 4 /\
        Seq.length v0 == 4 /\ Seq.length v1 == 4 /\ Seq.length v2 == 4 /\
        Seq.length v3 == 4 /\ Seq.length v4 == 4 /\ Seq.length v5 == 4)
ensures exists* (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t).
  A.pts_to x2 wx2 ** A.pts_to z2 wz2 ** A.pts_to x3 wx3 ** A.pts_to z3 wz3 **
  A.pts_to t0 w0 ** A.pts_to t1 w1 ** A.pts_to t2 w2 ** A.pts_to t3 w3 **
  A.pts_to t4 w4 ** A.pts_to t5 w5 **
  A.pts_to x1 #p1 vx1 ** A.pts_to ks #pk vk **
  pure (Seq.length wx2 == 4 /\ Seq.length wz2 == 4 /\ Seq.length wx3 == 4 /\
        Seq.length wz3 == 4 /\
        Seq.length w0 == 4 /\ Seq.length w1 == 4 /\ Seq.length w2 == 4 /\
        Seq.length w3 == 4 /\ Seq.length w4 == 4 /\ Seq.length w5 == 4 /\ 
        ((fe wx2, fe wz2), (fe wx3, fe wz3)) ==
          C.ladder_at (fe vx1) vk (SZ.v n)
            ((fe vx2, fe vz2),
             (fe vx3, fe vz3)))
{
  A.pts_to_len ks;
  let bi = SZ.sub 255sz n;
  let bj = SZ.div bi 8sz;
  let sh = SZ.sizet_to_uint32 (SZ.rem bi 8sz);
  assert_norm (pow2 32 > 8);
  Math.small_mod (SZ.v (SZ.rem bi 8sz)) (pow2 32);
  assert (pure (SZ.v bi == 255 - SZ.v n /\ SZ.v bj == SZ.v bi / 8 /\
                U32.v sh == SZ.v bi % 8));
  let byte = A.(ks.(bj));
  let w = Cast.u8_to_u64 byte;
  assert (pure (S64.v w == S8.v (Seq.index vk (SZ.v bi / 8))));
  let sr = S64.shift_right w sh;
  assert (pure (S64.v sr == S64.v w / pow2 (SZ.v bi % 8)));
  UInt.logand_mask #64 (S64.v sr) 1;
  let bit = S64.logand sr (S64.classify 1uL);
  assert (pure (S64.v bit == C.ith_bit vk (SZ.v bi) /\ S64.v bit < 2));
  let sel = S64.eq_mask bit (S64.classify 1uL);
  assert (pure ((S64.v sel == 0) == (S64.v bit <> 1)));

  cswap sel x2 x3;
  cswap sel z2 z3;
  with sx2. assert (A.pts_to x2 sx2);
  with sz2. assert (A.pts_to z2 sz2);
  with sx3. assert (A.pts_to x3 sx3);
  with sz3. assert (A.pts_to z3 sz3);
  assert (pure
    (((fe sx2, fe sz2), (fe sx3, fe sz3)) ==
      C.cswap (C.ith_bit vk (SZ.v bi))
        (fe vx2, fe vz2) (fe vx3, fe vz3)));

  add_and_double x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 x1;
  with ax2. assert (A.pts_to x2 ax2);
  with az2. assert (A.pts_to z2 az2);
  with ax3. assert (A.pts_to x3 ax3);
  with az3. assert (A.pts_to z3 az3);

  cswap sel x2 x3;
  cswap sel z2 z3;
  with ux2. assert (A.pts_to x2 ux2);
  with uz2. assert (A.pts_to z2 uz2);
  with ux3. assert (A.pts_to x3 ux3);
  with uz3. assert (A.pts_to z3 uz3);
  assert (pure
    (((fe ux2, fe uz2), (fe ux3, fe uz3)) ==
      C.cswap (C.ith_bit vk (SZ.v bi))
        (fe ax2, fe az2) (fe ax3, fe az3)));
  assert (pure
    (((fe ux2, fe uz2), (fe ux3, fe uz3)) ==
      C.ladder_step (fe vx1) vk (SZ.v n)
        ((fe vx2, fe vz2),
         (fe vx3, fe vz3))));
}

#pop-options

(** {2 The ladder}

    Two hundred and fifty-six steps, and the only thing left to check is that
    the loop counter walks [Loops.repeati_g]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let ladder_exit (x1: C.elem) (k: Seq.lseq S8.t 32) (vi: SZ.t) (a b c d: C.elem)
  : Lemma (requires SZ.v vi <= 256 /\ false == SZ.lt vi 256sz /\
                    ((a, b), (c, d)) ==
                      Loops.repeati_g (SZ.v vi) (C.ladder_at x1 k) (C.ladder_init x1))
          (ensures (a, b) == fst (C.montgomery_ladder x1 k))
  = ()

[@@ CPrologue "__attribute__((target(\"bmi2\")))";
   custard_c_closure_prologue "__attribute__((target(\"bmi2\")))";
   custard_c_closure_guard "defined(__x86_64__)"]
fn ladder (x2 z2 x3 z3 t0 t1 t2 t3 t4 t5: A.array S64.t)
           (x1: A.array S64.t)
          (ks: A.array S8.t)
          (#vx2: erased (Seq.seq S64.t)) (#vz2: erased (Seq.seq S64.t))
          (#vx3: erased (Seq.seq S64.t)) (#vz3: erased (Seq.seq S64.t))
          (#v0: erased (Seq.seq S64.t)) (#v1: erased (Seq.seq S64.t))
          (#v2: erased (Seq.seq S64.t)) (#v3: erased (Seq.seq S64.t))
          (#v4: erased (Seq.seq S64.t)) (#v5: erased (Seq.seq S64.t))
          (#p1: perm) (#vx1: erased (Seq.seq S64.t))
          (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires
  A.pts_to x2 vx2 ** A.pts_to z2 vz2 ** A.pts_to x3 vx3 ** A.pts_to z3 vz3 **
  A.pts_to t0 v0 ** A.pts_to t1 v1 ** A.pts_to t2 v2 ** A.pts_to t3 v3 **
  A.pts_to t4 v4 ** A.pts_to t5 v5 **
  A.pts_to x1 #p1 vx1 ** A.pts_to ks #pk vk **
  pure (Seq.length vx1 == 4 /\
        Seq.length v0 == 4 /\ Seq.length v1 == 4 /\ Seq.length v2 == 4 /\
        Seq.length v3 == 4 /\ Seq.length v4 == 4 /\ Seq.length v5 == 4 /\ 
        Seq.length vx2 == 4 /\ Seq.length vz2 == 4 /\ Seq.length vx3 == 4 /\
        Seq.length vz3 == 4 /\
        ((fe vx2, fe vz2), (fe vx3, fe vz3)) ==
          C.ladder_init (fe vx1))
ensures exists* (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t).
  A.pts_to x2 wx2 ** A.pts_to z2 wz2 ** A.pts_to x3 wx3 ** A.pts_to z3 wz3 **
  A.pts_to t0 w0 ** A.pts_to t1 w1 ** A.pts_to t2 w2 ** A.pts_to t3 w3 **
  A.pts_to t4 w4 ** A.pts_to t5 w5 **
  A.pts_to x1 #p1 vx1 ** A.pts_to ks #pk vk **
  pure (Seq.length wx2 == 4 /\ Seq.length wz2 == 4 /\
        Seq.length w0 == 4 /\ Seq.length w1 == 4 /\ Seq.length w2 == 4 /\
        Seq.length w3 == 4 /\ Seq.length w4 == 4 /\ Seq.length w5 == 4 /\ 
        (fe wx2, fe wz2) ==
          fst (C.montgomery_ladder (fe vx1) vk))
{
  Loops.repeati_g_zero (C.ladder_at (fe vx1) vk) (C.ladder_init (fe vx1));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t)
                    (wx2: Seq.seq S64.t) (wz2: Seq.seq S64.t)
                    (wx3: Seq.seq S64.t) (wz3: Seq.seq S64.t)
                    (w0: Seq.seq S64.t) (w1: Seq.seq S64.t) (w2: Seq.seq S64.t)
                    (w3: Seq.seq S64.t) (w4: Seq.seq S64.t) (w5: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to x2 wx2 ** A.pts_to z2 wz2 ** A.pts_to x3 wx3 ** A.pts_to z3 wz3 **
    A.pts_to t0 w0 ** A.pts_to t1 w1 ** A.pts_to t2 w2 ** A.pts_to t3 w3 **
    A.pts_to t4 w4 ** A.pts_to t5 w5 **
    A.pts_to x1 #p1 vx1 ** A.pts_to ks #pk vk **
    pure (SZ.v vi <= 256 /\
          Seq.length wx2 == 4 /\ Seq.length wz2 == 4 /\ Seq.length wx3 == 4 /\
          Seq.length wz3 == 4 /\
          Seq.length w0 == 4 /\ Seq.length w1 == 4 /\ Seq.length w2 == 4 /\
          Seq.length w3 == 4 /\ Seq.length w4 == 4 /\ Seq.length w5 == 4 /\ 
          ((fe wx2, fe wz2), (fe wx3, fe wz3)) ==
            Loops.repeati_g (SZ.v vi) (C.ladder_at (fe vx1) vk)
                            (C.ladder_init (fe vx1)))
  decreases (256 - SZ.v (!i))
  {
    let vi = !i;
    with wx2. assert (A.pts_to x2 wx2);
    with wz2. assert (A.pts_to z2 wz2);
    with wx3. assert (A.pts_to x3 wx3);
    with wz3. assert (A.pts_to z3 wz3);
    ladder_one x2 z2 x3 z3 t0 t1 t2 t3 t4 t5 x1 ks vi;
    with ux2. assert (A.pts_to x2 ux2);
    with uz2. assert (A.pts_to z2 uz2);
    with ux3. assert (A.pts_to x3 ux3);
    with uz3. assert (A.pts_to z3 uz3);
    Loops.unfold_repeati_g (SZ.v vi) (C.ladder_at (fe vx1) vk)
                           (C.ladder_init (fe vx1));
    assert (pure
      (((fe ux2, fe uz2), (fe ux3, fe uz3)) ==
        Loops.repeati_g (SZ.v vi + 1) (C.ladder_at (fe vx1) vk)
                        (C.ladder_init (fe vx1))));
    i := SZ.add vi 1sz;
  };
  with vi. assert (pts_to i vi);
  with wx2. assert (A.pts_to x2 wx2);
  with wz2. assert (A.pts_to z2 wz2);
  with wx3. assert (A.pts_to x3 wx3);
  with wz3. assert (A.pts_to z3 wz3);
  ladder_exit (fe vx1) vk vi (fe wx2) (fe wz2) (fe wx3) (fe wz3);
  ()
}

#pop-options

(** {2 Clamping} *)

[@@ CPrologue "__attribute__((target(\"bmi2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn clamp (ks: A.array S8.t) (k: A.array S8.t)
         (#vs: erased (Seq.seq S8.t)) (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires A.pts_to ks vs ** A.pts_to k #pk vk **
  pure (Seq.length vs == 32)
ensures exists* (vs': Seq.seq S8.t).
  A.pts_to ks vs' ** A.pts_to k #pk vk **
  pure (vs' == C.clamp vk)
{
  A.pts_to_len ks;
  A.pts_to_len k;
  Copy.copy_prefix ks k 32sz;
  let b0 = A.(ks.(0sz));
  A.((ks.(0sz) <- S8.logand b0 (S8.classify 0xf8uy)));
  let b31 = A.(ks.(31sz));
  A.((ks.(31sz) <- S8.logor (S8.logand b31 (S8.classify 0x7fuy)) (S8.classify 0x40uy)));
  with v. assert (A.pts_to ks v);
  assert (pure (v `Seq.equal` C.clamp vk));
}

(** {2 The scalar multiplication} *)

#push-options "--z3rlimit 300"

[@@ CPrologue "__attribute__((target(\"bmi2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn scalarmult64 (out k u: A.array S8.t)
                (#vout: erased (Seq.seq S8.t))
                (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
                (#pu: perm) (#vu: erased (Seq.lseq S8.t 32))
requires A.pts_to out vout ** A.pts_to k #pk vk ** A.pts_to u #pu vu **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to k #pk vk ** A.pts_to u #pu vu **
  pure (vout' == C.scalarmult vk vu)
{
  let z = S64.zero;
  let z8 = S8.classify 0uy;
  let mut ka = [| z8; 32sz |];
  Mem.track ka;
  let mut a1 = [| z; 4sz |];
  Mem.track a1;
  let mut a2 = [| z; 4sz |];
  Mem.track a2;
  let mut a3 = [| z; 4sz |];
  Mem.track a3;
  let mut a4 = [| z; 4sz |];
  Mem.track a4;
  let mut a5 = [| z; 4sz |];
  Mem.track a5;
  let mut b0 = [| z; 4sz |];
  Mem.track b0;
  let mut b1 = [| z; 4sz |];
  Mem.track b1;
  let mut b2 = [| z; 4sz |];
  Mem.track b2;
  let mut b3 = [| z; 4sz |];
  Mem.track b3;
  let mut b4 = [| z; 4sz |];
  Mem.track b4;
  let mut b5 = [| z; 4sz |];
  Mem.track b5;
  A.pts_to_len ka; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len a5; A.pts_to_len b0; A.pts_to_len b1;
  A.pts_to_len b2; A.pts_to_len b3; A.pts_to_len b4; A.pts_to_len b5;
  A.pts_to_len out;

  clamp ka k;
  with vks. assert (A.pts_to ka vks);
  assert (pure (Seq.length vks == 32));

  load a1 u;
  with vx1. assert (A.pts_to a1 vx1);
  assert (pure (Seq.length vx1 == 4 /\ fe vx1 == C.decode_point vu));

  set_small a2 1uL;
  set_small a3 0uL;
  copy a4 a1;
  set_small a5 1uL;
  assert_norm (1 < C.prime);
  Math.small_mod 1 C.prime;
  Math.small_mod 0 C.prime;
  assert (pure (C.one == 1));

  ladder a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 a1 ka;
  with wx2. assert (A.pts_to a2 wx2);
  with wz2. assert (A.pts_to a3 wz2);

  finv b0 a3;
  with vi0. assert (A.pts_to b0 vi0);
  assert (pure (fe vi0 == C.finv (fe wz2)));
  fmul b1 a2 b0;
  with vm. assert (A.pts_to b1 vm);
  assert (pure (fe vm == C.fmul (fe wx2) (fe vi0)));
  freeze b1;
  with vr. assert (A.pts_to b1 vr);
  assert (pure (ev vr == fe vm));
  store out b1;
  with vo. assert (A.pts_to out vo);
  assert (pure (vo == C.scalarmult vk vu));
  Mem.wipe b5 4sz;
  Mem.wipe b4 4sz;
  Mem.wipe b3 4sz;
  Mem.wipe b2 4sz;
  Mem.wipe b1 4sz;
  Mem.wipe b0 4sz;
  Mem.wipe a5 4sz;
  Mem.wipe a4 4sz;
  Mem.wipe a3 4sz;
  Mem.wipe a2 4sz;
  Mem.wipe a1 4sz;
  Mem.wipe ka 32sz;
}

#pop-options

#pop-options
