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

(** {!Hacl.Curve25519.Inverse}'s chain over {!Hacl.Curve25519.Field64}.

    The same two hundred and fifty-four squarings and eleven
    multiplications, the same exponent bookkeeping, and the same copies to
    make the operations in place; only the element is four full words.
    Every function is compiled for BMI2, so that the field operations inline
    into it. *)
module Hacl.Curve25519.Inverse64

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Curve25519.Field64

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module C = Spec.Curve25519
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60 --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"


(** [a := a * a]. *)
[@@ CPrologue "__attribute__((target(\"bmi2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn fsqr_ip (a c1 c2: A.array S64.t)
           (#va: erased (Seq.seq S64.t))
           (#vc1: erased (Seq.seq S64.t)) (#vc2: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to c1 vc1 ** A.pts_to c2 vc2 **
  pure (Seq.length va == 4 /\ Seq.length vc1 == 4 /\ Seq.length vc2 == 4 )
ensures exists* (va': Seq.seq S64.t) (vc1': Seq.seq S64.t)
                (vc2': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to c1 vc1' ** A.pts_to c2 vc2' **
  pure (Seq.length va' == 4 /\ Seq.length vc1' == 4 /\ Seq.length vc2' == 4  /\
        fe va' == C.fexp (fe va) 2)
{
  copy c1 a;
  with u1. assert (A.pts_to c1 u1);
  assert (pure (u1 == reveal va));
  fsqr a c1;
  with v'. assert (A.pts_to a v');
  C.fexp_two (fe va);
  assert (pure (fe v' == C.fexp (fe va) 2));
}

(** [a := a * b]. *)
[@@ CPrologue "__attribute__((target(\"bmi2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn fmul_ip (a b c1: A.array S64.t)
           (#va: erased (Seq.seq S64.t))
           (#pb: perm) (#vb: erased (Seq.seq S64.t))
           (#vc1: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to b #pb vb ** A.pts_to c1 vc1 **
  pure (Seq.length va == 4 /\ Seq.length vb == 4 /\ Seq.length vc1 == 4 )
ensures exists* (va': Seq.seq S64.t) (vc1': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to b #pb vb ** A.pts_to c1 vc1' **
  pure (Seq.length va' == 4 /\ Seq.length vc1' == 4 /\ 
        fe va' == C.fmul (fe va) (fe vb))
{
  copy c1 a;
  fmul a c1 b;
}

(** [a := a^(2^n)], by [n] squarings. *)
[@@ CPrologue "__attribute__((target(\"bmi2\")))";
   custard_c_closure_prologue "__attribute__((target(\"bmi2\")))";
   custard_c_closure_guard "defined(__x86_64__)"]
fn fpow2_ip (a c1 c2: A.array S64.t) (n: SZ.t)
            (#va: erased (Seq.seq S64.t))
            (#vc1: erased (Seq.seq S64.t)) (#vc2: erased (Seq.seq S64.t))
requires A.pts_to a va ** A.pts_to c1 vc1 ** A.pts_to c2 vc2 **
  pure (Seq.length va == 4 /\ Seq.length vc1 == 4 /\ Seq.length vc2 == 4 )
ensures exists* (va': Seq.seq S64.t) (vc1': Seq.seq S64.t)
                (vc2': Seq.seq S64.t).
  A.pts_to a va' ** A.pts_to c1 vc1' ** A.pts_to c2 vc2' **
  pure (Seq.length va' == 4 /\ Seq.length vc1' == 4 /\ Seq.length vc2' == 4  /\
        fe va' == C.fexp (fe va) (pow2 (SZ.v n)))
{
  C.fexp_one (fe va);
  assert_norm (pow2 0 == 1);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t) (u1: Seq.seq S64.t)
                    (u2: Seq.seq S64.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to c1 u1 ** A.pts_to c2 u2 **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == 4 /\ Seq.length u1 == 4 /\
          Seq.length u2 == 4 /\ 
          fe v == C.fexp (fe va) (pow2 (SZ.v vi)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to a v);
    fsqr_ip a c1 c2;
    with v'. assert (A.pts_to a v');
    C.fexp_two (fe v);
    C.fexp_add (fe va) (pow2 (SZ.v vi)) (pow2 (SZ.v vi));
    Math.pow2_double_sum (SZ.v vi);
    C.fexp_mul (fe va) (pow2 (SZ.v vi)) 2;
    assert (pure (fe v' == C.fexp (fe va) (pow2 (SZ.v vi + 1))));
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

[@@ CPrologue "__attribute__((target(\"bmi2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn finv (out a: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == 4 /\ Seq.length va == 4)
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (Seq.length vout' == 4 /\ fe vout' == C.finv (fe va))
{
  let z0 = S64.classify 0uL;
  let z = z0;
  let mut arr1 = [| z; 4sz |];
  Mem.track arr1; A.pts_to_len arr1; let mut arr2 = [| z; 4sz |];
  Mem.track arr2; A.pts_to_len arr2; let mut arr3 = [| z; 4sz |];
  Mem.track arr3; A.pts_to_len arr3; let mut arr4 = [| z; 4sz |];
  Mem.track arr4; A.pts_to_len arr4; let mut arr5 = [| z; 4sz |];
  Mem.track arr5; A.pts_to_len arr5; let mut arr6 = [| z; 4sz |];
  Mem.track arr6; A.pts_to_len arr6; let mut arr7 = [| z; 4sz |];
  Mem.track arr7; A.pts_to_len arr7; let mut arrc = [| z; 4sz |];
  Mem.track arrc; A.pts_to_len arrc; let mut arrd = [| z; 4sz |];
  Mem.track arrd; A.pts_to_len arrd; A.pts_to_len arr1; A.pts_to_len arr2; A.pts_to_len arr3; A.pts_to_len arr4;
  A.pts_to_len arr5; A.pts_to_len arr6; A.pts_to_len arr7;
  A.pts_to_len arrc; A.pts_to_len arrd;
  A.pts_to_len out; A.pts_to_len a;

  (* arr1 = x^2 *)
  copy arr1 a;
  fsqr_ip arr1 arrc arrd;
  with v1. assert (A.pts_to arr1 v1);
  assert (pure (fe v1 == C.fexp (fe va) 2));

  (* out = x^8 *)
  copy out arr1;
  fpow2_ip out arrc arrd 2sz;
  with v2. assert (A.pts_to out v2);
  C.fexp_mul (fe va) 2 (pow2 2);
  assert_norm (2 * pow2 2 == 8);
  assert (pure (fe v2 == C.fexp (fe va) 8));

  (* arr2 = x^9 *)
  copy arr2 out;
  fmul_ip arr2 a arrc;
  with v3. assert (A.pts_to arr2 v3);
  C.fexp_one (fe va);
  C.fexp_add (fe va) 8 1;
  assert (pure (fe v3 == C.fexp (fe va) 9));

  (* arr3 = x^11 *)
  copy arr3 arr2;
  fmul_ip arr3 arr1 arrc;
  with v4. assert (A.pts_to arr3 v4);
  C.fexp_add (fe va) 9 2;
  assert (pure (fe v4 == C.fexp (fe va) 11));

  (* out = x^22 *)
  copy out arr3;
  fsqr_ip out arrc arrd;
  with v5. assert (A.pts_to out v5);
  C.fexp_mul (fe va) 11 2;
  assert (pure (fe v5 == C.fexp (fe va) 22));

  (* arr4 = E 5 = x^31 *)
  copy arr4 out;
  fmul_ip arr4 arr2 arrc;
  with v6. assert (A.pts_to arr4 v6);
  C.fexp_add (fe va) 22 9;
  assert_norm (pow2 5 - 1 == 31);
  assert (pure (fe v6 == C.fexp (fe va) (pow2 5 - 1)));

  (* out = E 10 *)
  copy out arr4;
  fpow2_ip out arrc arrd 5sz;
  with v7. assert (A.pts_to out v7);
  C.fexp_mul (fe va) (pow2 5 - 1) (pow2 5);
  fmul_ip out arr4 arrc;
  with v8. assert (A.pts_to out v8);
  assert_norm ((pow2 5 - 1) * pow2 5 >= 0);
  C.fexp_add (fe va) ((pow2 5 - 1) * pow2 5) (pow2 5 - 1);
  assert_norm ((pow2 5 - 1) * pow2 5 + (pow2 5 - 1) == pow2 10 - 1);
  assert (pure (fe v8 == C.fexp (fe va) (pow2 10 - 1)));

  (* arr5 = E 10 *)
  copy arr5 out;

  (* out = E 20 *)
  fpow2_ip out arrc arrd 10sz;
  with v9. assert (A.pts_to out v9);
  C.fexp_mul (fe va) (pow2 10 - 1) (pow2 10);
  fmul_ip out arr5 arrc;
  with v10. assert (A.pts_to out v10);
  assert_norm ((pow2 10 - 1) * pow2 10 >= 0);
  C.fexp_add (fe va) ((pow2 10 - 1) * pow2 10) (pow2 10 - 1);
  assert_norm ((pow2 10 - 1) * pow2 10 + (pow2 10 - 1) == pow2 20 - 1);
  assert (pure (fe v10 == C.fexp (fe va) (pow2 20 - 1)));

  (* arr2 is dead; it becomes E 20 *)
  copy arr2 out;

  (* out = E 40 *)
  fpow2_ip out arrc arrd 20sz;
  with v11. assert (A.pts_to out v11);
  C.fexp_mul (fe va) (pow2 20 - 1) (pow2 20);
  fmul_ip out arr2 arrc;
  with v12. assert (A.pts_to out v12);
  assert_norm ((pow2 20 - 1) * pow2 20 >= 0);
  C.fexp_add (fe va) ((pow2 20 - 1) * pow2 20) (pow2 20 - 1);
  assert_norm ((pow2 20 - 1) * pow2 20 + (pow2 20 - 1) == pow2 40 - 1);
  assert (pure (fe v12 == C.fexp (fe va) (pow2 40 - 1)));

  (* out = E 50 *)
  fpow2_ip out arrc arrd 10sz;
  with v13. assert (A.pts_to out v13);
  C.fexp_mul (fe va) (pow2 40 - 1) (pow2 10);
  fmul_ip out arr5 arrc;
  with v14. assert (A.pts_to out v14);
  assert_norm ((pow2 40 - 1) * pow2 10 >= 0);
  C.fexp_add (fe va) ((pow2 40 - 1) * pow2 10) (pow2 10 - 1);
  assert_norm ((pow2 40 - 1) * pow2 10 + (pow2 10 - 1) == pow2 50 - 1);
  assert (pure (fe v14 == C.fexp (fe va) (pow2 50 - 1)));

  copy arr6 out;

  (* out = E 100 *)
  fpow2_ip out arrc arrd 50sz;
  with v15. assert (A.pts_to out v15);
  C.fexp_mul (fe va) (pow2 50 - 1) (pow2 50);
  fmul_ip out arr6 arrc;
  with v16. assert (A.pts_to out v16);
  assert_norm ((pow2 50 - 1) * pow2 50 >= 0);
  C.fexp_add (fe va) ((pow2 50 - 1) * pow2 50) (pow2 50 - 1);
  assert_norm ((pow2 50 - 1) * pow2 50 + (pow2 50 - 1) == pow2 100 - 1);
  assert (pure (fe v16 == C.fexp (fe va) (pow2 100 - 1)));

  copy arr7 out;

  (* out = E 200 *)
  fpow2_ip out arrc arrd 100sz;
  with v17. assert (A.pts_to out v17);
  C.fexp_mul (fe va) (pow2 100 - 1) (pow2 100);
  fmul_ip out arr7 arrc;
  with v18. assert (A.pts_to out v18);
  assert_norm ((pow2 100 - 1) * pow2 100 >= 0);
  C.fexp_add (fe va) ((pow2 100 - 1) * pow2 100) (pow2 100 - 1);
  assert_norm ((pow2 100 - 1) * pow2 100 + (pow2 100 - 1) == pow2 200 - 1);
  assert (pure (fe v18 == C.fexp (fe va) (pow2 200 - 1)));

  (* out = E 250 *)
  fpow2_ip out arrc arrd 50sz;
  with v19. assert (A.pts_to out v19);
  C.fexp_mul (fe va) (pow2 200 - 1) (pow2 50);
  fmul_ip out arr6 arrc;
  with v20. assert (A.pts_to out v20);
  assert_norm ((pow2 200 - 1) * pow2 50 >= 0);
  C.fexp_add (fe va) ((pow2 200 - 1) * pow2 50) (pow2 50 - 1);
  assert_norm ((pow2 200 - 1) * pow2 50 + (pow2 50 - 1) == pow2 250 - 1);
  assert (pure (fe v20 == C.fexp (fe va) (pow2 250 - 1)));

  (* out = x^(p-2) *)
  fpow2_ip out arrc arrd 5sz;
  with v21. assert (A.pts_to out v21);
  C.fexp_mul (fe va) (pow2 250 - 1) (pow2 5);
  fmul_ip out arr3 arrc;
  with v22. assert (A.pts_to out v22);
  assert_norm ((pow2 250 - 1) * pow2 5 >= 0);
  C.fexp_add (fe va) ((pow2 250 - 1) * pow2 5) 11;
  assert_norm ((pow2 250 - 1) * pow2 5 + 11 == pow2 255 - 19 - 2);
  assert (pure (fe v22 == C.fexp (fe va) (C.prime - 2)));
  assert (pure (fe v22 == C.finv (fe va)));
  Mem.wipe arrd 4sz;
  Mem.wipe arrc 4sz;
  Mem.wipe arr7 4sz;
  Mem.wipe arr6 4sz;
  Mem.wipe arr5 4sz;
  Mem.wipe arr4 4sz;
  Mem.wipe arr3 4sz;
  Mem.wipe arr2 4sz;
  Mem.wipe arr1 4sz;
}

#pop-options

#pop-options
