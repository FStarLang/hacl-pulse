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

(** Inversion in Curve25519's field.

    [finv x] is [x^(p-2)], which is [x^-1] when [x] is nonzero and [0] when
    it is not, and it is computed by the addition chain everyone uses: the
    exponent [p - 2 = 2^255 - 21] is a run of two hundred and fifty ones
    followed by [01011], so building [x^(2^k - 1)] for [k = 5, 10, 20, 40,
    50, 100, 200, 250] by repeated doubling costs two hundred and fifty-four
    squarings and eleven multiplications.

    Every line of the chain is one of two moves -- raise to a power of two,
    or multiply by something already computed -- and each is justified by one
    of [Spec.Curve25519.fexp_mul] and [Spec.Curve25519.fexp_add].  So the
    proof is a bookkeeping of exponents: after each step the accumulator is
    [x^e] for a closed number [e], and the last one is [p - 2].

    The operations here are in place, because a chain wants to overwrite its
    accumulator, and [Hacl.Curve25519.Field.fmul] wants a destination
    disjoint from its arguments.  The reconciliation is a copy, which costs
    sixteen moves against two hundred and fifty-six multiplies. *)
module Hacl.Curve25519.Inverse

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Curve25519.Field
open Hacl.Curve25519.Field

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module C = Spec.Curve25519
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 The two moves}

    [c1] and [c2] are scratch field elements and [t] the thirty-one word
    scratch that a multiplication needs; they are threaded through so that
    the chain allocates them once. *)

(** [a := a * a]. *)
fn fsqr_ip (a c1 c2: A.array S64.t) (t: A.array S128.t)
           (#va: erased (Seq.seq S64.t))
           (#vc1: erased (Seq.seq S64.t)) (#vc2: erased (Seq.seq S64.t))
           (#vt: erased (Seq.seq S128.t))
requires A.pts_to a va ** A.pts_to c1 vc1 ** A.pts_to c2 vc2 ** A.pts_to t vt **
  pure (felem (vals va) /\ Seq.length vc1 == nl /\ Seq.length vc2 == nl /\
        Seq.length vt == nw)
ensures exists* (va': Seq.seq S64.t) (vc1': Seq.seq S64.t)
                (vc2': Seq.seq S64.t) (vt': Seq.seq S128.t).
  A.pts_to a va' ** A.pts_to c1 vc1' ** A.pts_to c2 vc2' ** A.pts_to t vt' **
  pure (felem (vals va') /\ Seq.length vc1' == nl /\ Seq.length vc2' == nl /\
        Seq.length vt' == nw /\
        fev (vals va') == C.fexp (fev (vals va)) 2)
{
  copy c1 a;
  with u1. assert (A.pts_to c1 u1);
  assert (pure (vals u1 == vals va));
  fsqr a c1;
  with v'. assert (A.pts_to a v');
  C.fexp_two (fev (vals va));
  assert (pure (fev (vals v') == C.fexp (fev (vals va)) 2));
}

(** [a := a * b]. *)
fn fmul_ip (a b c1: A.array S64.t) (t: A.array S128.t)
           (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#vc1: erased (Seq.seq S64.t)) (#vt: erased (Seq.seq S128.t))
requires A.pts_to a va ** A.pts_to b #pb vb ** A.pts_to c1 vc1 ** A.pts_to t vt **
  pure (felem (vals va) /\ felem (vals vb) /\ Seq.length vc1 == nl /\
        Seq.length vt == nw)
ensures exists* (va': Seq.seq S64.t) (vc1': Seq.seq S64.t) (vt': Seq.seq S128.t).
  A.pts_to a va' ** A.pts_to b #pb vb ** A.pts_to c1 vc1' ** A.pts_to t vt' **
  pure (felem (vals va') /\ Seq.length vc1' == nl /\ Seq.length vt' == nw /\
        fev (vals va') == C.fmul (fev (vals va)) (fev (vals vb)))
{
  copy c1 a;
  fmul a c1 b;
}

(** [a := a^(2^n)], by [n] squarings. *)
fn fpow2_ip (a c1 c2: A.array S64.t) (t: A.array S128.t) (n: SZ.t)
            (#va: erased (Seq.seq S64.t))
            (#vc1: erased (Seq.seq S64.t)) (#vc2: erased (Seq.seq S64.t))
            (#vt: erased (Seq.seq S128.t))
requires A.pts_to a va ** A.pts_to c1 vc1 ** A.pts_to c2 vc2 ** A.pts_to t vt **
  pure (felem (vals va) /\ Seq.length vc1 == nl /\ Seq.length vc2 == nl /\
        Seq.length vt == nw)
ensures exists* (va': Seq.seq S64.t) (vc1': Seq.seq S64.t)
                (vc2': Seq.seq S64.t) (vt': Seq.seq S128.t).
  A.pts_to a va' ** A.pts_to c1 vc1' ** A.pts_to c2 vc2' ** A.pts_to t vt' **
  pure (felem (vals va') /\ Seq.length vc1' == nl /\ Seq.length vc2' == nl /\
        Seq.length vt' == nw /\
        fev (vals va') == C.fexp (fev (vals va)) (pow2 (SZ.v n)))
{
  C.fexp_one (fev (vals va));
  assert_norm (pow2 0 == 1);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t) (u1: Seq.seq S64.t)
                    (u2: Seq.seq S64.t) (w: Seq.seq S128.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to c1 u1 ** A.pts_to c2 u2 ** A.pts_to t w **
    pure (SZ.v vi <= SZ.v n /\ felem (vals v) /\ Seq.length u1 == nl /\
          Seq.length u2 == nl /\ Seq.length w == nw /\
          fev (vals v) == C.fexp (fev (vals va)) (pow2 (SZ.v vi)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to a v);
    fsqr_ip a c1 c2 t;
    with v'. assert (A.pts_to a v');
    C.fexp_two (fev (vals v));
    C.fexp_add (fev (vals va)) (pow2 (SZ.v vi)) (pow2 (SZ.v vi));
    Math.pow2_double_sum (SZ.v vi);
    C.fexp_mul (fev (vals va)) (pow2 (SZ.v vi)) 2;
    assert (pure (fev (vals v') == C.fexp (fev (vals va)) (pow2 (SZ.v vi + 1))));
    i := SZ.add vi 1sz;
  };
}

(** {2 The chain}

    Writing [E k] for [2^k - 1], the accumulator runs through

      [x^2, x^8, x^9, x^11, x^22, E 5, E 10, E 20, E 40, E 50, E 100,
       E 200, E 250],

    and the answer is [(E 250) * 2^5 + 11 = 2^255 - 21 = p - 2].  The seven
    scratch elements hold [x^2], [x^9], [x^11] and [E 5], [E 10] (later
    [E 20]), [E 50] and [E 100], which are the values the chain comes back
    to. *)

#push-options "--z3rlimit 200"

fn finv (out a: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == nl /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (felem (vals vout') /\ fev (vals vout') == C.finv (fev (vals va)))
{
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut arr1 = [| z; 5sz |];
  Mem.track arr1; A.pts_to_len arr1; let mut arr2 = [| z; 5sz |];
  Mem.track arr2; A.pts_to_len arr2; let mut arr3 = [| z; 5sz |];
  Mem.track arr3; A.pts_to_len arr3; let mut arr4 = [| z; 5sz |];
  Mem.track arr4; A.pts_to_len arr4; let mut arr5 = [| z; 5sz |];
  Mem.track arr5; A.pts_to_len arr5; let mut arr6 = [| z; 5sz |];
  Mem.track arr6; A.pts_to_len arr6; let mut arr7 = [| z; 5sz |];
  Mem.track arr7; A.pts_to_len arr7; let mut arrc = [| z; 5sz |];
  Mem.track arrc; A.pts_to_len arrc; let mut arrd = [| z; 5sz |];
  Mem.track arrd; A.pts_to_len arrd; let mut arrt = [| z128; 9sz |];
  Mem.track arrt; A.pts_to_len arrt; A.pts_to_len arr1; A.pts_to_len arr2; A.pts_to_len arr3; A.pts_to_len arr4;
  A.pts_to_len arr5; A.pts_to_len arr6; A.pts_to_len arr7;
  A.pts_to_len arrc; A.pts_to_len arrd; A.pts_to_len arrt;
  A.pts_to_len out; A.pts_to_len a;

  (* arr1 = x^2 *)
  copy arr1 a;
  fsqr_ip arr1 arrc arrd arrt;
  with v1. assert (A.pts_to arr1 v1);
  assert (pure (fev (vals v1) == C.fexp (fev (vals va)) 2));

  (* out = x^8 *)
  copy out arr1;
  fpow2_ip out arrc arrd arrt 2sz;
  with v2. assert (A.pts_to out v2);
  C.fexp_mul (fev (vals va)) 2 (pow2 2);
  assert_norm (2 * pow2 2 == 8);
  assert (pure (fev (vals v2) == C.fexp (fev (vals va)) 8));

  (* arr2 = x^9 *)
  copy arr2 out;
  fmul_ip arr2 a arrc arrt;
  with v3. assert (A.pts_to arr2 v3);
  C.fexp_one (fev (vals va));
  C.fexp_add (fev (vals va)) 8 1;
  assert (pure (fev (vals v3) == C.fexp (fev (vals va)) 9));

  (* arr3 = x^11 *)
  copy arr3 arr2;
  fmul_ip arr3 arr1 arrc arrt;
  with v4. assert (A.pts_to arr3 v4);
  C.fexp_add (fev (vals va)) 9 2;
  assert (pure (fev (vals v4) == C.fexp (fev (vals va)) 11));

  (* out = x^22 *)
  copy out arr3;
  fsqr_ip out arrc arrd arrt;
  with v5. assert (A.pts_to out v5);
  C.fexp_mul (fev (vals va)) 11 2;
  assert (pure (fev (vals v5) == C.fexp (fev (vals va)) 22));

  (* arr4 = E 5 = x^31 *)
  copy arr4 out;
  fmul_ip arr4 arr2 arrc arrt;
  with v6. assert (A.pts_to arr4 v6);
  C.fexp_add (fev (vals va)) 22 9;
  assert_norm (pow2 5 - 1 == 31);
  assert (pure (fev (vals v6) == C.fexp (fev (vals va)) (pow2 5 - 1)));

  (* out = E 10 *)
  copy out arr4;
  fpow2_ip out arrc arrd arrt 5sz;
  with v7. assert (A.pts_to out v7);
  C.fexp_mul (fev (vals va)) (pow2 5 - 1) (pow2 5);
  fmul_ip out arr4 arrc arrt;
  with v8. assert (A.pts_to out v8);
  assert_norm ((pow2 5 - 1) * pow2 5 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 5 - 1) * pow2 5) (pow2 5 - 1);
  assert_norm ((pow2 5 - 1) * pow2 5 + (pow2 5 - 1) == pow2 10 - 1);
  assert (pure (fev (vals v8) == C.fexp (fev (vals va)) (pow2 10 - 1)));

  (* arr5 = E 10 *)
  copy arr5 out;

  (* out = E 20 *)
  fpow2_ip out arrc arrd arrt 10sz;
  with v9. assert (A.pts_to out v9);
  C.fexp_mul (fev (vals va)) (pow2 10 - 1) (pow2 10);
  fmul_ip out arr5 arrc arrt;
  with v10. assert (A.pts_to out v10);
  assert_norm ((pow2 10 - 1) * pow2 10 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 10 - 1) * pow2 10) (pow2 10 - 1);
  assert_norm ((pow2 10 - 1) * pow2 10 + (pow2 10 - 1) == pow2 20 - 1);
  assert (pure (fev (vals v10) == C.fexp (fev (vals va)) (pow2 20 - 1)));

  (* arr2 is dead; it becomes E 20 *)
  copy arr2 out;

  (* out = E 40 *)
  fpow2_ip out arrc arrd arrt 20sz;
  with v11. assert (A.pts_to out v11);
  C.fexp_mul (fev (vals va)) (pow2 20 - 1) (pow2 20);
  fmul_ip out arr2 arrc arrt;
  with v12. assert (A.pts_to out v12);
  assert_norm ((pow2 20 - 1) * pow2 20 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 20 - 1) * pow2 20) (pow2 20 - 1);
  assert_norm ((pow2 20 - 1) * pow2 20 + (pow2 20 - 1) == pow2 40 - 1);
  assert (pure (fev (vals v12) == C.fexp (fev (vals va)) (pow2 40 - 1)));

  (* out = E 50 *)
  fpow2_ip out arrc arrd arrt 10sz;
  with v13. assert (A.pts_to out v13);
  C.fexp_mul (fev (vals va)) (pow2 40 - 1) (pow2 10);
  fmul_ip out arr5 arrc arrt;
  with v14. assert (A.pts_to out v14);
  assert_norm ((pow2 40 - 1) * pow2 10 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 40 - 1) * pow2 10) (pow2 10 - 1);
  assert_norm ((pow2 40 - 1) * pow2 10 + (pow2 10 - 1) == pow2 50 - 1);
  assert (pure (fev (vals v14) == C.fexp (fev (vals va)) (pow2 50 - 1)));

  copy arr6 out;

  (* out = E 100 *)
  fpow2_ip out arrc arrd arrt 50sz;
  with v15. assert (A.pts_to out v15);
  C.fexp_mul (fev (vals va)) (pow2 50 - 1) (pow2 50);
  fmul_ip out arr6 arrc arrt;
  with v16. assert (A.pts_to out v16);
  assert_norm ((pow2 50 - 1) * pow2 50 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 50 - 1) * pow2 50) (pow2 50 - 1);
  assert_norm ((pow2 50 - 1) * pow2 50 + (pow2 50 - 1) == pow2 100 - 1);
  assert (pure (fev (vals v16) == C.fexp (fev (vals va)) (pow2 100 - 1)));

  copy arr7 out;

  (* out = E 200 *)
  fpow2_ip out arrc arrd arrt 100sz;
  with v17. assert (A.pts_to out v17);
  C.fexp_mul (fev (vals va)) (pow2 100 - 1) (pow2 100);
  fmul_ip out arr7 arrc arrt;
  with v18. assert (A.pts_to out v18);
  assert_norm ((pow2 100 - 1) * pow2 100 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 100 - 1) * pow2 100) (pow2 100 - 1);
  assert_norm ((pow2 100 - 1) * pow2 100 + (pow2 100 - 1) == pow2 200 - 1);
  assert (pure (fev (vals v18) == C.fexp (fev (vals va)) (pow2 200 - 1)));

  (* out = E 250 *)
  fpow2_ip out arrc arrd arrt 50sz;
  with v19. assert (A.pts_to out v19);
  C.fexp_mul (fev (vals va)) (pow2 200 - 1) (pow2 50);
  fmul_ip out arr6 arrc arrt;
  with v20. assert (A.pts_to out v20);
  assert_norm ((pow2 200 - 1) * pow2 50 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 200 - 1) * pow2 50) (pow2 50 - 1);
  assert_norm ((pow2 200 - 1) * pow2 50 + (pow2 50 - 1) == pow2 250 - 1);
  assert (pure (fev (vals v20) == C.fexp (fev (vals va)) (pow2 250 - 1)));

  (* out = x^(p-2) *)
  fpow2_ip out arrc arrd arrt 5sz;
  with v21. assert (A.pts_to out v21);
  C.fexp_mul (fev (vals va)) (pow2 250 - 1) (pow2 5);
  fmul_ip out arr3 arrc arrt;
  with v22. assert (A.pts_to out v22);
  assert_norm ((pow2 250 - 1) * pow2 5 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 250 - 1) * pow2 5) 11;
  assert_norm ((pow2 250 - 1) * pow2 5 + 11 == pow2 255 - 19 - 2);
  assert (pure (fev (vals v22) == C.fexp (fev (vals va)) (C.prime - 2)));

  Mem.wipe arrt 9sz;
  Mem.wipe arrd 5sz;
  Mem.wipe arrc 5sz;
  Mem.wipe arr7 5sz;
  Mem.wipe arr6 5sz;
  Mem.wipe arr5 5sz;
  Mem.wipe arr4 5sz;
  Mem.wipe arr3 5sz;
  Mem.wipe arr2 5sz;
  Mem.wipe arr1 5sz;
  ()
}

#pop-options

#pop-options
