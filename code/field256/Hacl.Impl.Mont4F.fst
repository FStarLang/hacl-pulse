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

(** {!Hacl.Impl.Mont64} behind the interface of [Hacl.Impl.Mont4.amul].

    [amulf] takes the same modulus record and limbs, and says the same
    thing about its result, so a field over any four-limb odd modulus can
    switch to the word-by-word reduction by changing one call.  It does
    not need the table of [2^256 - m]: the final subtraction works from
    the modulus itself. *)
module Hacl.Impl.Mont4F

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.Montgomery4
open Spec.Field4
open Spec.Mont4
open Hacl.Impl.Limb4

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module S64 = Hacl.Secret.UInt64
module Math = FStar.Math.Lemmas
module F64 = Hacl.Curve25519.Field64
module W = Spec.Curve25519.Field64
module M64 = Hacl.Impl.Mont64

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Two views of four words} *)

#push-options "--fuel 1"
let eval_ev (s: Seq.seq S64.t)
  : Lemma (requires Seq.length s == 4) (ensures eval (vals s) == F64.ev s)
  = let v = vals s in
    let v1 = Seq.slice v 1 4 in
    let v2 = Seq.slice v1 1 3 in
    let v3 = Seq.slice v2 1 2 in
    let v4 = Seq.slice v3 1 1 in
    assert_norm (pow2 64 == W.w);
    eval_empty v4;
    assert (eval v3 == Seq.index v3 0 + base * eval v4);
    assert (eval v2 == Seq.index v2 0 + base * eval v3);
    assert (eval v1 == Seq.index v1 0 + base * eval v2);
    assert (eval v == Seq.index v 0 + base * eval v1)
#pop-options

(** What {!Hacl.Impl.Mont64.mmul} asks of the modulus words. *)
let mod_ok (v: Seq.seq S64.t) (d: modulus)
  : Lemma (requires modulus_ok d /\ Seq.length v == nl /\ vals v == d.ms)
          (ensures F64.ev v == d.m /\ 0 < d.m /\ (F64.ix v 0 * d.mu + 1) % W.w == 0 /\
                   pow2 256 == W.w4)
  = eval_ev v;
    assert_norm (pow2 64 == W.w);
    assert_norm (pow2 256 == W.w4);
    assert (Seq.index (vals v) 0 == F64.ix v 0)

let res_of (s: Seq.seq S64.t) (d: modulus)
  : Lemma (requires Seq.length s == 4 /\ F64.ev s < d.m)
          (ensures res d (vals s) /\ eval (vals s) == F64.ev s)
  = eval_ev s; vals_bnd s

(** Any residue with the right Montgomery equation is the specification's
    product. *)
let mmul_eq (d: modulus) (a b z: Seq.seq nat)
  : Lemma (requires modulus_ok d /\ res d a /\ res d b /\ res d z /\
                    pow2 256 * eval z % d.m == eval a * eval b % d.m)
          (ensures eval z == eval (mmul d a b))
  = mmul_ok d a b;
    rcancel d (eval z) (eval (mmul d a b));
    Math.small_mod (eval z) d.m;
    Math.small_mod (eval (mmul d a b)) d.m

let mul_of (d: modulus) (a b o: Seq.seq S64.t)
  : Lemma (requires modulus_ok d /\ res d (vals a) /\ res d (vals b) /\
                    Seq.length a == 4 /\ Seq.length b == 4 /\ Seq.length o == 4 /\
                    F64.ev o < d.m /\ W.w4 * F64.ev o % d.m == F64.ev a * F64.ev b % d.m)
          (ensures res d (vals o) /\ eval (vals o) == eval (mmul d (vals a) (vals b)))
  = eval_ev a; eval_ev b; res_of o d;
    assert_norm (pow2 256 == W.w4);
    mmul_eq d (vals a) (vals b) (vals o)

(** {2 The product} *)

fn amulf (out a b ms: A.array S64.t) (mu: S64.t) (d: erased modulus)
         (#vo: erased (Seq.seq S64.t))
         (#pa: perm) (#va: erased (Seq.seq S64.t))
         (#pb: perm) (#vb: erased (Seq.seq S64.t))
         (#pm: perm) (#vms: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to ms #pm vms **
  pure (modulus_ok d /\ Seq.length vo == nl /\ Seq.length vms == nl /\
        vals vms == d.ms /\ S64.v mu == d.mu /\
        res d (vals va) /\ res d (vals vb))
ensures exists* (vo': Seq.seq S64.t).
  A.pts_to out vo' ** A.pts_to a #pa va ** A.pts_to b #pb vb ** A.pts_to ms #pm vms **
  pure (Seq.length vo' == nl /\ res d (vals vo') /\
        eval (vals vo') == eval (mmul d (vals va) (vals vb)))
{
  A.pts_to_len a; A.pts_to_len b; A.pts_to_len ms;
  mod_ok vms d;
  eval_ev va; eval_ev vb;
  M64.mmul out a b ms mu (hide (reveal d).m);
  with vo'. assert (A.pts_to out vo');
  mul_of d va vb vo';
  assert (pure (res d (vals vo') /\ eval (vals vo') == eval (mmul d (vals va) (vals vb))));
}

#pop-options
