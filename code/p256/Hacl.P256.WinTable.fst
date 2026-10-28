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

(** A window table that is a constant rather than a computation.

    {!Hacl.P256.PointMulG} reads four sixteen-entry affine tables, of multiples
    of [G], [2^64 G], [2^128 G] and [2^192 G], and used to build them on
    entry: sixty point additions on every signature and every key
    agreement.  {!Hacl.P256.Win0} .. {!Hacl.P256.Win3} hold them as
    constants instead, and this is the bridge: one lemma that turns two
    lists of sixty-four limbs and a point into one [aent], and one that
    collects sixteen [aent]s into an [atok].

    This is {!Hacl.K256.WinTable} with two differences.  An entry is four
    sixty-four-bit limbs rather than five fifty-two-bit ones, so the list
    cutting is restated here at that width.  And a coordinate is stored in
    Montgomery form, so what a chunk of literals has to add up to is
    [x 2^256 mod p] rather than [x]; the step from there to [fev] is
    {!Hacl.P256.Field.fconst}'s. *)
module Hacl.P256.WinTable

open Spec.Bignum4
open Spec.Field4
open Spec.Mont4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Lit4
open Hacl.P256.Field
open Hacl.P256.Point
open Hacl.P256.PointWin
open Hacl.P256.PointBooth

module Seq = FStar.Seq
module L = FStar.List.Tot
module Classical = FStar.Classical
module Math = FStar.Math.Lemmas
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module GR = Spec.P256.Group
module SM = Spec.P256.Smul

(** {2 Cutting a flat list}

    Entry [d] of a coordinate is limbs [4d] through [4d + 3].  The cut is
    stated with [drop] and [take], both of which the normaliser evaluates
    on a literal list in one step, and {!chunk_slice} says it agrees with
    the slice {!Hacl.P256.PointWin.entry} takes. *)

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

let chunk (#a: Type) (l: list a) (d: nat) : list a = ltake 4 (ldrop (d * 4) l)

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

let chunk_slice (l e: list S64.t) (d: nat)
  : Lemma (requires L.length l == 64 /\ d < 16 /\ chunk l d == e)
          (ensures L.length e == 4 /\
                   Seq.slice (Seq.seq_of_list l) (d * 4) (d * 4 + 4) ==
                   Seq.seq_of_list e)
  = Math.lemma_mult_le_right 4 (d + 1) 16;
    ldrop_len (d * 4) l;
    ltake_len 4 (ldrop (d * 4) l);
    let s : Seq.seq S64.t = Seq.seq_of_list l in
    let sl = Seq.slice s (d * 4) (d * 4 + 4) in
    let se : Seq.seq S64.t = Seq.seq_of_list e in
    let aux (k: nat { k < 4 }) : Lemma (Seq.index sl k == Seq.index se k)
      = ltake_index 4 (ldrop (d * 4) l) k;
        ldrop_index (d * 4) l k;
        Seq.lemma_seq_of_list_index l (d * 4 + k);
        Seq.lemma_seq_of_list_index e k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro sl se

(** One coordinate of one entry: the slice is a field element, and it
    reads as [x], provided its literals add up to [x]'s Montgomery form. *)
let entry_felem (l: list S64.t) (d: nat) (x: P.felem)
  : Lemma (requires L.length l == 64 /\ d < 16 /\
                    L.length (chunk l d) == nl /\ lbnd (chunk l d) /\
                    leval (chunk l d) == x * pow2 256 % P.prime)
          (ensures felem (Seq.slice (Seq.seq_of_list l) (d * 4) (d * 4 + 4)) /\
                   fev (Seq.slice (Seq.seq_of_list l) (d * 4) (d * 4 + 4)) == x)
  = chunk_slice l (chunk l d) d;
    assert_norm (P.prime < pow2 256);
    lit_limbs (chunk l d) (x * pow2 256 % P.prime);
    fmod_ok (); fmod_m ();
    limbs_ok (x * pow2 256 % P.prime);
    mev_uniq fmod x (limbs (x * pow2 256 % P.prime))

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

let qx (q: P.proj_point) : P.felem = let (a, _, _) = q in a
let qy (q: P.proj_point) : P.felem = let (_, b, _) = q in b
let qz (q: P.proj_point) : P.felem = let (_, _, c) = q in c

let pt_eta (q: P.proj_point) : Lemma (q == (qx q, qy q, qz q)) = ()

(** One entry of a constant table: two [leval]s, which the normaliser
    settles on literals, and the two facts the chain in
    [Spec.P256.Win{i}] proved about the point -- entry [d] is the
    [(d + 1)]-th multiple, affine, so its [z] is one and not stored. *)
let aent_lit (lx ly: list S64.t) (d: nat)
             (p: P.proj_point) (n: nat) (q: P.proj_point)
  : Lemma (requires
             L.length lx == 64 /\ L.length ly == 64 /\
             d < 16 /\
             L.length (chunk lx d) == nl /\ lbnd (chunk lx d) /\
             leval (chunk lx d) == qx q * pow2 256 % P.prime /\
             L.length (chunk ly d) == nl /\ lbnd (chunk ly d) /\
             leval (chunk ly d) == qy q * pow2 256 % P.prime /\
             qz q == P.fone /\
             GR.on_curve q /\ GR.peq q (SM.smul ((d + 1) * n) p))
          (ensures aent (Seq.seq_of_list lx) (Seq.seq_of_list ly) p n d)
  = entry_felem lx d (qx q);
    entry_felem ly d (qy q);
    let vx : Seq.seq S64.t = Seq.seq_of_list lx in
    let vy : Seq.seq S64.t = Seq.seq_of_list ly in
    entry_fits d;
    entry_def vx d; entry_def vy d;
    pt_eta q;
    aent_intro vx vy p n d

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

let lt16 (d: nat)
  : Lemma (requires d < 16)
          (ensures d == 0 \/ d == 1 \/ d == 2 \/ d == 3 \/
                   d == 4 \/ d == 5 \/ d == 6 \/ d == 7 \/
                   d == 8 \/ d == 9 \/ d == 10 \/ d == 11 \/
                   d == 12 \/ d == 13 \/ d == 14 \/ d == 15) = ()

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 400"

(** Sixteen entries make a table. *)
let atok_all (tx ty: Seq.seq S64.t) (p: P.proj_point) (n: nat)
  : Lemma (requires
             aent tx ty p n 0 /\ aent tx ty p n 1 /\
             aent tx ty p n 2 /\ aent tx ty p n 3 /\
             aent tx ty p n 4 /\ aent tx ty p n 5 /\
             aent tx ty p n 6 /\ aent tx ty p n 7 /\
             aent tx ty p n 8 /\ aent tx ty p n 9 /\
             aent tx ty p n 10 /\ aent tx ty p n 11 /\
             aent tx ty p n 12 /\ aent tx ty p n 13 /\
             aent tx ty p n 14 /\ aent tx ty p n 15)
          (ensures atok tx ty p n)
  = introduce forall (d: nat). d < 16 ==> aent tx ty p n d
    with introduce _ ==> _
    with lt16 d

#pop-options
