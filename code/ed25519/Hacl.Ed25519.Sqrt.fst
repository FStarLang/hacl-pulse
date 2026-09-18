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

(** The square root that decompression needs.

    Because [p = 5 mod 8], the exponentiation [a^((p+3)/8)] is a *fourth*
    root of [a^2]: it is a square root of [a] when one exists, and
    [sqrt(-1)] times one when it does not, so the caller has to square the
    answer and check.  The exponent is [2^252 - 2], and the addition chain
    is the one [finv] uses as far as [E 250 = a^(2^250 - 1)] -- two more
    squarings and one multiplication finish it, against the five squarings
    and one multiplication that the inverse needs. *)
module Hacl.Ed25519.Sqrt

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Curve25519.Field
open Hacl.Curve25519.Field
open Hacl.Curve25519.Inverse

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128
module C = Spec.Curve25519
module E = Spec.Ed25519

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn fsqrt (out a: A.array S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires A.pts_to out vout ** A.pts_to a #pa va **
  pure (Seq.length vout == nl /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t).
  A.pts_to out vout' ** A.pts_to a #pa va **
  pure (felem (vals vout') /\ fev (vals vout') == E.modp_sqrt (fev (vals va)))
{
  let z = S64.zero;
  let z128 : S128.t = S128.zero;
  let mut arr1 = [| z; 5sz |]; A.pts_to_len arr1; let mut arr2 = [| z; 5sz |]; A.pts_to_len arr2; let mut arr3 = [| z; 5sz |]; A.pts_to_len arr3; let mut arr4 = [| z; 5sz |]; A.pts_to_len arr4; let mut arr5 = [| z; 5sz |]; A.pts_to_len arr5; let mut arr6 = [| z; 5sz |]; A.pts_to_len arr6; let mut arr7 = [| z; 5sz |]; A.pts_to_len arr7; let mut arrc = [| z; 5sz |]; A.pts_to_len arrc; let mut arrd = [| z; 5sz |]; A.pts_to_len arrd; let mut arrt = [| z128; 9sz |]; A.pts_to_len arrt; A.pts_to_len arr1; A.pts_to_len arr2; A.pts_to_len arr3; A.pts_to_len arr4;
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

  (* out = x^(2^251 - 1) *)
  fsqr_ip out arrc arrd arrt;
  with v21. assert (A.pts_to out v21);
  C.fexp_mul (fev (vals va)) (pow2 250 - 1) 2;
  fmul_ip out a arrc arrt;
  with v22. assert (A.pts_to out v22);
  assert_norm ((pow2 250 - 1) * 2 >= 0);
  C.fexp_one (fev (vals va));
  C.fexp_add (fev (vals va)) ((pow2 250 - 1) * 2) 1;
  assert_norm ((pow2 250 - 1) * 2 + 1 == pow2 251 - 1);
  assert (pure (fev (vals v22) == C.fexp (fev (vals va)) (pow2 251 - 1)));

  (* out = x^((p + 3) / 8) *)
  fsqr_ip out arrc arrd arrt;
  with v23. assert (A.pts_to out v23);
  C.fexp_mul (fev (vals va)) (pow2 251 - 1) 2;
  assert_norm ((pow2 251 - 1) * 2 == (C.prime + 3) / 8);
  assert (pure (fev (vals v23) == E.modp_sqrt (fev (vals va))));

  ()
}

#pop-options

