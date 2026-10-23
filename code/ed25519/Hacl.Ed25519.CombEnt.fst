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

(** What an entry of the base-point comb's table holds, and how a
    normaliser call on the literal list settles it.

    Entry [m] of table [j] sits at limb [135 j + 15 m] and is three field
    elements in a row: [y + x], [y - x] and [2 d t] of [CT.tp j m]. *)
module Hacl.Ed25519.CombEnt

open Hacl.Impl.Limb
open Hacl.Impl.Lit51

module Seq = FStar.Seq
module L = FStar.List.Tot
module S64 = Hacl.Secret.UInt64
module F = Spec.Curve25519.Field
module E = Spec.Ed25519
module CB = Spec.Ed25519.Comb
module CT = Spec.Ed25519.CombTable

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let eoff (j: nat) (m: nat) : nat = 135 * j + 15 * m

(** Five limbs at [o] are a field element of value [x]. *)
let fat (s: Seq.seq S64.t) (o: nat) (x: nat) : prop =
  o + 5 <= Seq.length s /\
  F.felem (vals (Seq.slice s o (o + 5))) /\
  F.fev (vals (Seq.slice s o (o + 5))) == x

(** Fifteen limbs at [o] are the stored form of [q]. *)
let nent (s: Seq.seq S64.t) (o: nat) (q: E.ext_point) : prop =
  let (a, b, c) = CB.to_niels q in
  fat s o a /\ fat s (o + 5) b /\ fat s (o + 10) c

(** The whole table. *)
let ntok (s: Seq.seq S64.t) : prop =
  Seq.length s == 4320 /\
  (forall (j: nat { j < 32 }) (m: nat { m < 9 }). nent s (eoff j m) (CT.tp j m))

(** One entry of a literal list, as a fact about the list.  Opaque, so
    that collecting nine of them under a quantifier is propositional. *)
[@@"opaque_to_smt"]
let lent (l: list S64.t) (j: nat { j < 32 }) (m: nat { m < 9 }) : prop =
  nent (Seq.seq_of_list l) (eoff j m) (CT.tp j m)

(** The same, in the form the normaliser can decide on the list. *)
let nlit (l: list S64.t) (j: nat) (m: nat) (q: E.ext_point) : prop =
  let e = lslice l (eoff j m) 15 in
  let (a, b, c) = CB.to_niels q in
  lbnd (lslice e 0 5) /\ leval (lslice e 0 5) == a /\
  lbnd (lslice e 5 5) /\ leval (lslice e 5 5) == b /\
  lbnd (lslice e 10 5) /\ leval (lslice e 10 5) == c

let lfat (l: list S64.t) (o: nat) (e: list S64.t) (c: nat) (x: nat)
  : Lemma (requires o + 15 <= L.length l /\ c + 5 <= 15 /\
                    Seq.slice (Seq.seq_of_list l) o (o + 15) == Seq.seq_of_list e /\
                    L.length e == 15 /\
                    lbnd (lslice e c 5) /\ leval (lslice e c 5) == x /\
                    x < Spec.Curve25519.prime)
          (ensures fat (Seq.seq_of_list l) (o + c) x)
  = lslice_ok e c 5;
    lslice_felem e c x;
    Seq.slice_slice (Seq.seq_of_list l) o (o + 15) c (c + 5)

let nent_lit (l: list S64.t) (j: nat { j < 32 }) (m: nat { m < 9 }) (q: E.ext_point)
  : Lemma (requires L.length l == 4320 /\ nlit l j m q /\ q == CT.tp j m)
          (ensures lent l j m)
  = let o = eoff j m in
    let e = lslice l o 15 in
    lslice_ok l o 15;
    let (a, b, c) = CB.to_niels q in
    lfat l o e 0 a;
    lfat l o e 5 b;
    lfat l o e 10 c;
    reveal_opaque (`%lent) (lent l j m)

let lent_elim (l: list S64.t) (j: nat { j < 32 }) (m: nat { m < 9 })
  : Lemma (requires lent l j m)
          (ensures nent (Seq.seq_of_list l) (eoff j m) (CT.tp j m))
  = reveal_opaque (`%lent) (lent l j m)

#pop-options
