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

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module C = Spec.Curve25519
module E = Spec.Ed25519

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn fsqrt (out a: S.slice S64.t)
        (#vout: erased (Seq.seq S64.t))
        (#pa: perm) (#va: erased (Seq.seq S64.t))
requires S.pts_to out vout ** S.pts_to a #pa va **
  pure (Seq.length vout == nl /\ felem (vals va))
ensures exists* (vout': Seq.seq S64.t).
  S.pts_to out vout' ** S.pts_to a #pa va **
  pure (felem (vals vout') /\ fev (vals vout') == E.modp_sqrt (fev (vals va)))
{
  let z = S64.zero;
  let mut arr1 = [| z; 16sz |]; A.pts_to_len arr1; let b1 = S.from_array arr1 16sz;
  let mut arr2 = [| z; 16sz |]; A.pts_to_len arr2; let b2 = S.from_array arr2 16sz;
  let mut arr3 = [| z; 16sz |]; A.pts_to_len arr3; let b3 = S.from_array arr3 16sz;
  let mut arr4 = [| z; 16sz |]; A.pts_to_len arr4; let b4 = S.from_array arr4 16sz;
  let mut arr5 = [| z; 16sz |]; A.pts_to_len arr5; let b5 = S.from_array arr5 16sz;
  let mut arr6 = [| z; 16sz |]; A.pts_to_len arr6; let b6 = S.from_array arr6 16sz;
  let mut arr7 = [| z; 16sz |]; A.pts_to_len arr7; let b7 = S.from_array arr7 16sz;
  let mut arrc = [| z; 16sz |]; A.pts_to_len arrc; let c1 = S.from_array arrc 16sz;
  let mut arrd = [| z; 16sz |]; A.pts_to_len arrd; let c2 = S.from_array arrd 16sz;
  let mut arrt = [| z; 31sz |]; A.pts_to_len arrt; let t = S.from_array arrt 31sz;
  S.pts_to_len b1; S.pts_to_len b2; S.pts_to_len b3; S.pts_to_len b4;
  S.pts_to_len b5; S.pts_to_len b6; S.pts_to_len b7;
  S.pts_to_len c1; S.pts_to_len c2; S.pts_to_len t;
  S.pts_to_len out; S.pts_to_len a;

  (* b1 = x^2 *)
  copy b1 a;
  fsqr_ip b1 c1 c2 t;
  with v1. assert (S.pts_to b1 v1);
  assert (pure (fev (vals v1) == C.fexp (fev (vals va)) 2));

  (* out = x^8 *)
  copy out b1;
  fpow2_ip out c1 c2 t 2sz;
  with v2. assert (S.pts_to out v2);
  C.fexp_mul (fev (vals va)) 2 (pow2 2);
  assert_norm (2 * pow2 2 == 8);
  assert (pure (fev (vals v2) == C.fexp (fev (vals va)) 8));

  (* b2 = x^9 *)
  copy b2 out;
  fmul_ip b2 a c1 t;
  with v3. assert (S.pts_to b2 v3);
  C.fexp_one (fev (vals va));
  C.fexp_add (fev (vals va)) 8 1;
  assert (pure (fev (vals v3) == C.fexp (fev (vals va)) 9));

  (* b3 = x^11 *)
  copy b3 b2;
  fmul_ip b3 b1 c1 t;
  with v4. assert (S.pts_to b3 v4);
  C.fexp_add (fev (vals va)) 9 2;
  assert (pure (fev (vals v4) == C.fexp (fev (vals va)) 11));

  (* out = x^22 *)
  copy out b3;
  fsqr_ip out c1 c2 t;
  with v5. assert (S.pts_to out v5);
  C.fexp_mul (fev (vals va)) 11 2;
  assert (pure (fev (vals v5) == C.fexp (fev (vals va)) 22));

  (* b4 = E 5 = x^31 *)
  copy b4 out;
  fmul_ip b4 b2 c1 t;
  with v6. assert (S.pts_to b4 v6);
  C.fexp_add (fev (vals va)) 22 9;
  assert_norm (pow2 5 - 1 == 31);
  assert (pure (fev (vals v6) == C.fexp (fev (vals va)) (pow2 5 - 1)));

  (* out = E 10 *)
  copy out b4;
  fpow2_ip out c1 c2 t 5sz;
  with v7. assert (S.pts_to out v7);
  C.fexp_mul (fev (vals va)) (pow2 5 - 1) (pow2 5);
  fmul_ip out b4 c1 t;
  with v8. assert (S.pts_to out v8);
  assert_norm ((pow2 5 - 1) * pow2 5 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 5 - 1) * pow2 5) (pow2 5 - 1);
  assert_norm ((pow2 5 - 1) * pow2 5 + (pow2 5 - 1) == pow2 10 - 1);
  assert (pure (fev (vals v8) == C.fexp (fev (vals va)) (pow2 10 - 1)));

  (* b5 = E 10 *)
  copy b5 out;

  (* out = E 20 *)
  fpow2_ip out c1 c2 t 10sz;
  with v9. assert (S.pts_to out v9);
  C.fexp_mul (fev (vals va)) (pow2 10 - 1) (pow2 10);
  fmul_ip out b5 c1 t;
  with v10. assert (S.pts_to out v10);
  assert_norm ((pow2 10 - 1) * pow2 10 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 10 - 1) * pow2 10) (pow2 10 - 1);
  assert_norm ((pow2 10 - 1) * pow2 10 + (pow2 10 - 1) == pow2 20 - 1);
  assert (pure (fev (vals v10) == C.fexp (fev (vals va)) (pow2 20 - 1)));

  (* b2 is dead; it becomes E 20 *)
  copy b2 out;

  (* out = E 40 *)
  fpow2_ip out c1 c2 t 20sz;
  with v11. assert (S.pts_to out v11);
  C.fexp_mul (fev (vals va)) (pow2 20 - 1) (pow2 20);
  fmul_ip out b2 c1 t;
  with v12. assert (S.pts_to out v12);
  assert_norm ((pow2 20 - 1) * pow2 20 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 20 - 1) * pow2 20) (pow2 20 - 1);
  assert_norm ((pow2 20 - 1) * pow2 20 + (pow2 20 - 1) == pow2 40 - 1);
  assert (pure (fev (vals v12) == C.fexp (fev (vals va)) (pow2 40 - 1)));

  (* out = E 50 *)
  fpow2_ip out c1 c2 t 10sz;
  with v13. assert (S.pts_to out v13);
  C.fexp_mul (fev (vals va)) (pow2 40 - 1) (pow2 10);
  fmul_ip out b5 c1 t;
  with v14. assert (S.pts_to out v14);
  assert_norm ((pow2 40 - 1) * pow2 10 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 40 - 1) * pow2 10) (pow2 10 - 1);
  assert_norm ((pow2 40 - 1) * pow2 10 + (pow2 10 - 1) == pow2 50 - 1);
  assert (pure (fev (vals v14) == C.fexp (fev (vals va)) (pow2 50 - 1)));

  copy b6 out;

  (* out = E 100 *)
  fpow2_ip out c1 c2 t 50sz;
  with v15. assert (S.pts_to out v15);
  C.fexp_mul (fev (vals va)) (pow2 50 - 1) (pow2 50);
  fmul_ip out b6 c1 t;
  with v16. assert (S.pts_to out v16);
  assert_norm ((pow2 50 - 1) * pow2 50 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 50 - 1) * pow2 50) (pow2 50 - 1);
  assert_norm ((pow2 50 - 1) * pow2 50 + (pow2 50 - 1) == pow2 100 - 1);
  assert (pure (fev (vals v16) == C.fexp (fev (vals va)) (pow2 100 - 1)));

  copy b7 out;

  (* out = E 200 *)
  fpow2_ip out c1 c2 t 100sz;
  with v17. assert (S.pts_to out v17);
  C.fexp_mul (fev (vals va)) (pow2 100 - 1) (pow2 100);
  fmul_ip out b7 c1 t;
  with v18. assert (S.pts_to out v18);
  assert_norm ((pow2 100 - 1) * pow2 100 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 100 - 1) * pow2 100) (pow2 100 - 1);
  assert_norm ((pow2 100 - 1) * pow2 100 + (pow2 100 - 1) == pow2 200 - 1);
  assert (pure (fev (vals v18) == C.fexp (fev (vals va)) (pow2 200 - 1)));

  (* out = E 250 *)
  fpow2_ip out c1 c2 t 50sz;
  with v19. assert (S.pts_to out v19);
  C.fexp_mul (fev (vals va)) (pow2 200 - 1) (pow2 50);
  fmul_ip out b6 c1 t;
  with v20. assert (S.pts_to out v20);
  assert_norm ((pow2 200 - 1) * pow2 50 >= 0);
  C.fexp_add (fev (vals va)) ((pow2 200 - 1) * pow2 50) (pow2 50 - 1);
  assert_norm ((pow2 200 - 1) * pow2 50 + (pow2 50 - 1) == pow2 250 - 1);
  assert (pure (fev (vals v20) == C.fexp (fev (vals va)) (pow2 250 - 1)));

  (* out = x^(2^251 - 1) *)
  fsqr_ip out c1 c2 t;
  with v21. assert (S.pts_to out v21);
  C.fexp_mul (fev (vals va)) (pow2 250 - 1) 2;
  fmul_ip out a c1 t;
  with v22. assert (S.pts_to out v22);
  assert_norm ((pow2 250 - 1) * 2 >= 0);
  C.fexp_one (fev (vals va));
  C.fexp_add (fev (vals va)) ((pow2 250 - 1) * 2) 1;
  assert_norm ((pow2 250 - 1) * 2 + 1 == pow2 251 - 1);
  assert (pure (fev (vals v22) == C.fexp (fev (vals va)) (pow2 251 - 1)));

  (* out = x^((p + 3) / 8) *)
  fsqr_ip out c1 c2 t;
  with v23. assert (S.pts_to out v23);
  C.fexp_mul (fev (vals va)) (pow2 251 - 1) 2;
  assert_norm ((pow2 251 - 1) * 2 == (C.prime + 3) / 8);
  assert (pure (fev (vals v23) == E.modp_sqrt (fev (vals va))));

  S.to_array b1; S.to_array b2; S.to_array b3; S.to_array b4;
  S.to_array b5; S.to_array b6; S.to_array b7;
  S.to_array c1; S.to_array c2; S.to_array t;
}

#pop-options

