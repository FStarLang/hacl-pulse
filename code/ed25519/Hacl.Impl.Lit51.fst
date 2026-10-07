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

(** Writing a radix-[2^51] constant down as a list of limbs, and cutting a
    long list into five-limb pieces.

    {!Hacl.Impl.Lit4} does the first half at radix [2^64] and
    {!Hacl.Impl.Lit52} at radix [2^52]; this is the same induction at the
    radix Curve25519 uses.  A list of literals adds up to a number
    ([leval]), a bounded list of the right length that adds up to [x] is
    the sequence of digits of [x] ([lit_limbs]), and a sequence of digits
    of a reduced [x] is a field element of value [x] ([const_ok]).  Three
    [assert_norm]s and one call settle a constant, where going index by
    index costs five case splits inside a query that already carries
    [Seq.init].

    The second half is what a compiled-in window table needs.  The table
    is one array of eighty limbs per coordinate and
    {!Hacl.Ed25519.PointWin.entry} reads entry [d] as
    [Seq.slice v (5d) (5d + 5)].  Rather than give the flat list eighty
    indices and relate each to the entry that contains it, {!chunk} cuts
    the list the way the slice cuts the sequence -- by a [drop] and a
    [take], both of which the normaliser evaluates on a literal list in
    one step -- and {!chunk_slice} says the two cuts agree.  A table then
    needs one [assert_norm] per entry rather than five. *)
module Hacl.Impl.Lit51

open Hacl.Impl.Limb

module Seq = FStar.Seq
module L = FStar.List.Tot
module Classical = FStar.Classical
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module U64 = FStar.UInt64
module F = Spec.Curve25519.Field
module C = Spec.Curve25519

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 A list of limbs} *)

let rec leval (l: list S64.t) : GTot nat =
  match l with
  | [] -> 0
  | h :: t -> S64.v h + F.base * leval t

let rec lbnd (l: list S64.t) : GTot bool =
  match l with
  | [] -> true
  | h :: t -> S64.v h < F.base && lbnd t

(** One induction carries both across [Seq.seq_of_list]. *)
let rec lit_ok (l: list S64.t)
  : Lemma (ensures F.eval (vals (Seq.seq_of_list l)) == leval l /\
                   (lbnd l ==> F.bnd (vals (Seq.seq_of_list l)) F.base))
          (decreases l)
  = match l with
    | [] -> Seq.lemma_eq_intro (Seq.seq_of_list l) Seq.empty
    | h :: t ->
      lit_ok t;
      let s = vals (Seq.seq_of_list l) in
      let n = Seq.length s in
      Classical.forall_intro (Seq.lemma_seq_of_list_index l);
      Classical.forall_intro (Seq.lemma_seq_of_list_index t);
      Seq.lemma_eq_intro (Seq.slice s 1 n) (vals (Seq.seq_of_list t))

(** A bounded sequence is determined by the number it evaluates to, so the
    literals are the limbs as soon as they add up. *)
let lit_limbs (l: list S64.t) (x: nat)
  : Lemma (requires L.length l == F.nl /\ lbnd l /\ leval l == x /\ x < pow2 255)
          (ensures vals (Seq.seq_of_list l) == F.limbs_of x)
  = lit_ok l;
    let s = vals (Seq.seq_of_list l) in
    let aux (k: nat { k < F.nl })
      : Lemma (Seq.index s k == Seq.index (F.limbs_of x) k)
      = F.eval_digit s k;
        F.limbs_index x k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s (F.limbs_of x)

(** A limb sequence that agrees with [limbs_of x] is a field element of
    value [x], as long as [x] is already reduced. *)
let const_ok (s: Seq.seq nat) (x: nat)
  : Lemma (requires x < C.prime /\ s == F.limbs_of x)
          (ensures F.felem s /\ F.fev s == x)
  = assert_norm (C.prime < pow2 255);
    F.limbs_of_ok x;
    assert_norm (F.base <= F.lim);
    Math.small_mod x C.prime

(** The two halves at once, which is what every constant below wants. *)
let lit_felem (l: list S64.t) (x: nat)
  : Lemma (requires L.length l == F.nl /\ lbnd l /\ leval l == x /\ x < C.prime)
          (ensures F.felem (vals (Seq.seq_of_list l)) /\
                   F.fev (vals (Seq.seq_of_list l)) == x)
  = assert_norm (C.prime < pow2 255);
    lit_limbs l x;
    const_ok (vals (Seq.seq_of_list l)) x

#pop-options

(** {2 Cutting a long list into entries} *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let rec ldrop (#a: Type) (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then l
  else match l with
       | [] -> []
       | _ :: t -> ldrop (n - 1) t

let rec ltake (#a: Type) (n: nat) (l: list a) : Tot (list a) (decreases n) =
  if n = 0 then []
  else match l with
       | [] -> []
       | h :: t -> h :: ltake (n - 1) t

(** Entry [d] of a flat list, as a list. *)
let chunk (#a: Type) (l: list a) (d: nat) : list a = ltake 5 (ldrop (d * 5) l)

let rec ldrop_len (#a: Type) (n: nat) (l: list a)
  : Lemma (ensures n <= L.length l ==> L.length (ldrop n l) == L.length l - n)
          (decreases n)
  = if n = 0 then () else match l with [] -> () | _ :: t -> ldrop_len (n - 1) t

let rec ltake_len (#a: Type) (n: nat) (l: list a)
  : Lemma (ensures n <= L.length l ==> L.length (ltake n l) == n)
          (decreases n)
  = if n = 0 then () else match l with [] -> () | _ :: t -> ltake_len (n - 1) t

let rec ldrop_index (#a: Type) (n: nat) (l: list a) (k: nat)
  : Lemma (requires n + k < L.length l)
          (ensures (ldrop_len n l; L.index (ldrop n l) k == L.index l (n + k)))
          (decreases n)
  = ldrop_len n l;
    if n = 0 then ()
    else match l with
         | _ :: t -> ldrop_index (n - 1) t k

let rec ltake_index (#a: Type) (n: nat) (l: list a) (k: nat)
  : Lemma (requires k < n /\ n <= L.length l)
          (ensures (ltake_len n l; L.index (ltake n l) k == L.index l k))
          (decreases n)
  = ltake_len n l;
    if n = 0 then ()
    else match l with
         | h :: t -> if k = 0 then () else ltake_index (n - 1) t (k - 1)

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The list cut and the sequence cut agree.  [e] is given rather than
    computed so that the caller can settle [chunk l d == e] by one
    [assert_norm] and then never mention the long list again. *)
let chunk_slice (l e: list S64.t) (d: nat)
  : Lemma (requires L.length l == 80 /\ d < 16 /\ chunk l d == e)
          (ensures L.length e == 5 /\
                   Seq.slice (Seq.seq_of_list l) (d * 5) (d * 5 + 5) ==
                   Seq.seq_of_list e)
  = Math.lemma_mult_le_right 5 (d + 1) 16;
    ldrop_len (d * 5) l;
    ltake_len 5 (ldrop (d * 5) l);
    let s : Seq.seq S64.t = Seq.seq_of_list l in
    let sl = Seq.slice s (d * 5) (d * 5 + 5) in
    let se : Seq.seq S64.t = Seq.seq_of_list e in
    let aux (k: nat { k < 5 }) : Lemma (Seq.index sl k == Seq.index se k)
      = ltake_index 5 (ldrop (d * 5) l) k;
        ldrop_index (d * 5) l k;
        Seq.lemma_seq_of_list_index l (d * 5 + k);
        Seq.lemma_seq_of_list_index e k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro sl se

(** The whole of one coordinate of one entry: the slice the table reader
    takes is a field element, and its value is the number the chain says
    it is.  The list cut is left in the statement rather than named, so
    that a caller settles it by one [assert_norm]. *)
let entry_felem (l: list S64.t) (d: nat) (x: nat)
  : Lemma (requires L.length l == 80 /\ d < 16 /\
                    L.length (chunk l d) == F.nl /\ lbnd (chunk l d) /\
                    leval (chunk l d) == x /\ x < C.prime)
          (ensures F.felem (vals (Seq.slice (Seq.seq_of_list l)
                                            (d * 5) (d * 5 + 5))) /\
                   F.fev (vals (Seq.slice (Seq.seq_of_list l)
                                          (d * 5) (d * 5 + 5))) == x)
  = chunk_slice l (chunk l d) d;
    lit_felem (chunk l d) x

#pop-options
