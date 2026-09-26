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

(** [2^256 - q] in the program image.

    The one constant the scalar arithmetic needs.  Its own module because the
    limb values are checked against [Spec.Ed25519.Scalar.qc] one entry at a
    time, which is an eight-line proof that has no business sitting in the
    middle of a Pulse function, and because a [static_array] is a definition:
    two modules declaring it would lay out two arrays. *)
module Hacl.Ed25519.Tables

open Hacl.Curve25519.Field

module G = Pulse.Lib.GlobalArray
module Seq = FStar.Seq
module Classical = FStar.Classical
module S64 = Hacl.Secret.UInt64
module U64 = FStar.UInt64
module F = Spec.Curve25519.Field
module B32 = Spec.Bignum256
module Limb = Hacl.Impl.Limb
module C = Spec.Curve25519
module Math = FStar.Math.Lemmas
module Sc = Spec.Ed25519.Scalar
module Base = Spec.Ed25519.Base

(** [2^256 - q = 0xefffffffffffffffffffffffffffffffeb2106215d086329a7ed9ce5a30a2c13],
    least significant limb first. *)
let qc_list : list S64.t = [
  S64.classify 0xa30a2c13uL; S64.classify 0xa7ed9ce5uL; S64.classify 0x5d086329uL; S64.classify 0xeb210621uL;
  S64.classify 0xffffffffuL; S64.classify 0xffffffffuL; S64.classify 0xffffffffuL; S64.classify 0xefffffffuL
]

[@@FStar.Custard.no_specialize]
let qc_seq : Seq.lseq S64.t 8 =
  assert_norm (List.Tot.length qc_list == 8);
  Seq.seq_of_list qc_list

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** Entry by entry against the specification's [qc], and one query per
    entry.  [qc_index] turns [Seq.init] into an arithmetic expression and
    [assert_norm] evaluates it; the literal comes out of the list rather
    than out of the sequence, because [FStar.Seq]'s representation is
    abstract and the normaliser cannot see through it.  Asking for all
    eight entries in one query is the same proof and a hundred times
    slower: every literal above [2^250] then sits in the context of every
    other one. *)
let qc_len (_: unit) : Lemma (List.Tot.length qc_list == 8) =
  assert_norm (List.Tot.length qc_list == 8)

let entry (k: nat { k < B32.nl }) (x: U64.t)
  : Lemma (requires Seq.index qc_seq k == S64.classify x /\
                    U64.v x == (pow2 256 - Sc.q) / pow2 (B32.rad * k) % B32.base)
          (ensures Seq.index (Limb.vals qc_seq) k == Seq.index Sc.qc k)
  = Sc.qc_index k

let entry_0 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 0 == Seq.index Sc.qc 0) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 0;
  assert_norm (List.Tot.index qc_list 0 == S64.classify 0xa30a2c13uL);
  assert_norm (U64.v 0xa30a2c13uL == (pow2 256 - Sc.q) / pow2 (B32.rad * 0) % B32.base);
  entry 0 0xa30a2c13uL

let entry_1 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 1 == Seq.index Sc.qc 1) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 1;
  assert_norm (List.Tot.index qc_list 1 == S64.classify 0xa7ed9ce5uL);
  assert_norm (U64.v 0xa7ed9ce5uL == (pow2 256 - Sc.q) / pow2 (B32.rad * 1) % B32.base);
  entry 1 0xa7ed9ce5uL

let entry_2 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 2 == Seq.index Sc.qc 2) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 2;
  assert_norm (List.Tot.index qc_list 2 == S64.classify 0x5d086329uL);
  assert_norm (U64.v 0x5d086329uL == (pow2 256 - Sc.q) / pow2 (B32.rad * 2) % B32.base);
  entry 2 0x5d086329uL

let entry_3 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 3 == Seq.index Sc.qc 3) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 3;
  assert_norm (List.Tot.index qc_list 3 == S64.classify 0xeb210621uL);
  assert_norm (U64.v 0xeb210621uL == (pow2 256 - Sc.q) / pow2 (B32.rad * 3) % B32.base);
  entry 3 0xeb210621uL

let entry_4 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 4 == Seq.index Sc.qc 4) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 4;
  assert_norm (List.Tot.index qc_list 4 == S64.classify 0xffffffffuL);
  assert_norm (U64.v 0xffffffffuL == (pow2 256 - Sc.q) / pow2 (B32.rad * 4) % B32.base);
  entry 4 0xffffffffuL

let entry_5 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 5 == Seq.index Sc.qc 5) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 5;
  assert_norm (List.Tot.index qc_list 5 == S64.classify 0xffffffffuL);
  assert_norm (U64.v 0xffffffffuL == (pow2 256 - Sc.q) / pow2 (B32.rad * 5) % B32.base);
  entry 5 0xffffffffuL

let entry_6 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 6 == Seq.index Sc.qc 6) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 6;
  assert_norm (List.Tot.index qc_list 6 == S64.classify 0xffffffffuL);
  assert_norm (U64.v 0xffffffffuL == (pow2 256 - Sc.q) / pow2 (B32.rad * 6) % B32.base);
  entry 6 0xffffffffuL

let entry_7 (_: unit) : Lemma (Seq.index (Limb.vals qc_seq) 7 == Seq.index Sc.qc 7) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 7;
  assert_norm (List.Tot.index qc_list 7 == S64.classify 0xefffffffuL);
  assert_norm (U64.v 0xefffffffuL == (pow2 256 - Sc.q) / pow2 (B32.rad * 7) % B32.base);
  entry 7 0xefffffffuL

(** [Seq.lemma_eq_intro] wants the entries for a symbolic index, and
    nothing tells Z3 that an index below eight is one of eight
    numbers.  So the case split is written out. *)
let qc_at (k: nat { k < B32.nl })
  : Lemma (Seq.index (Limb.vals qc_seq) k == Seq.index Sc.qc k)
  = if k = 0 then entry_0 ()
    else if k = 1 then entry_1 ()
    else if k = 2 then entry_2 ()
    else if k = 3 then entry_3 ()
    else if k = 4 then entry_4 ()
    else if k = 5 then entry_5 ()
    else if k = 6 then entry_6 ()
    else entry_7 ()

let qc_seq_ok (_: unit) : Lemma (Limb.vals qc_seq == Sc.qc) =
  Classical.forall_intro qc_at;
  Seq.lemma_eq_intro (Limb.vals qc_seq) Sc.qc

#pop-options

let qc_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (qc_seq <: Seq.seq S64.t) })
  = G.mk_static_array qc_list

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The curve constants}

    Five field elements that are part of the definition of the curve: [d],
    [2d], a square root of [-1], and the two coordinates of the base point.
    Each is five fifty-one-bit limbs, and each is checked against the
    specification by the same three lines per limb -- the list lookup, the
    arithmetic, and {!limb_at}. *)

(** Limb [k] of a constant below [2^255], from the literal in the list. *)
let limb_at (l: list S64.t) (x: nat) (k: nat { k < F.nl }) (lit: U64.t)
  : Lemma (requires List.Tot.length l == 5 /\
                    List.Tot.index l k == S64.classify lit /\
                    U64.v lit == x / pow2 (F.rad * k) % F.base)
          (ensures Seq.index (vals (Seq.seq_of_list l)) k ==
                   Seq.index (F.limbs_of x) k)
  = Seq.lemma_seq_of_list_index l k;
    F.limbs_index x k

(** A limb sequence that agrees with [limbs_of x] is a field element of
    value [x], as long as [x] is already reduced. *)
let const_ok (s: Seq.seq nat) (x: nat)
  : Lemma (requires x < C.prime /\ s == F.limbs_of x)
          (ensures F.felem s /\ F.fev s == x)
  = assert_norm (C.prime < pow2 255);
    F.limbs_of_ok x;
    assert_norm (F.base <= F.lim);
    Math.small_mod x C.prime


(** [Spec.Ed25519.d]. *)
let d_list : list S64.t = [
  S64.classify 0x34dca135978a3uL; S64.classify 0x1a8283b156ebduL; S64.classify 0x5e7a26001c029uL; S64.classify 0x739c663a03cbbuL; S64.classify 0x52036cee2b6ffuL
]

[@@FStar.Custard.no_specialize]
let d_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length d_list == 5);
  Seq.seq_of_list d_list

let d_at_0 (_: unit)
  : Lemma (Seq.index (vals d_seq) 0 == Seq.index (F.limbs_of Spec.Ed25519.d) 0) =
  assert_norm (List.Tot.length d_list == 5);
  assert_norm (List.Tot.index d_list 0 == S64.classify 0x34dca135978a3uL);
  assert_norm (U64.v 0x34dca135978a3uL == Spec.Ed25519.d / pow2 (F.rad * 0) % F.base);
  limb_at d_list Spec.Ed25519.d 0 0x34dca135978a3uL

let d_at_1 (_: unit)
  : Lemma (Seq.index (vals d_seq) 1 == Seq.index (F.limbs_of Spec.Ed25519.d) 1) =
  assert_norm (List.Tot.length d_list == 5);
  assert_norm (List.Tot.index d_list 1 == S64.classify 0x1a8283b156ebduL);
  assert_norm (U64.v 0x1a8283b156ebduL == Spec.Ed25519.d / pow2 (F.rad * 1) % F.base);
  limb_at d_list Spec.Ed25519.d 1 0x1a8283b156ebduL

let d_at_2 (_: unit)
  : Lemma (Seq.index (vals d_seq) 2 == Seq.index (F.limbs_of Spec.Ed25519.d) 2) =
  assert_norm (List.Tot.length d_list == 5);
  assert_norm (List.Tot.index d_list 2 == S64.classify 0x5e7a26001c029uL);
  assert_norm (U64.v 0x5e7a26001c029uL == Spec.Ed25519.d / pow2 (F.rad * 2) % F.base);
  limb_at d_list Spec.Ed25519.d 2 0x5e7a26001c029uL

let d_at_3 (_: unit)
  : Lemma (Seq.index (vals d_seq) 3 == Seq.index (F.limbs_of Spec.Ed25519.d) 3) =
  assert_norm (List.Tot.length d_list == 5);
  assert_norm (List.Tot.index d_list 3 == S64.classify 0x739c663a03cbbuL);
  assert_norm (U64.v 0x739c663a03cbbuL == Spec.Ed25519.d / pow2 (F.rad * 3) % F.base);
  limb_at d_list Spec.Ed25519.d 3 0x739c663a03cbbuL

let d_at_4 (_: unit)
  : Lemma (Seq.index (vals d_seq) 4 == Seq.index (F.limbs_of Spec.Ed25519.d) 4) =
  assert_norm (List.Tot.length d_list == 5);
  assert_norm (List.Tot.index d_list 4 == S64.classify 0x52036cee2b6ffuL);
  assert_norm (U64.v 0x52036cee2b6ffuL == Spec.Ed25519.d / pow2 (F.rad * 4) % F.base);
  limb_at d_list Spec.Ed25519.d 4 0x52036cee2b6ffuL

let d_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals d_seq) k == Seq.index (F.limbs_of Spec.Ed25519.d) k)
  = assert_norm (F.nl == 5);
    if k = 0 then d_at_0 ()
    else if k = 1 then d_at_1 ()
    else if k = 2 then d_at_2 ()
    else if k = 3 then d_at_3 ()
    else d_at_4 ()

let d_ok (_: unit)
  : Lemma (F.felem (vals d_seq) /\ F.fev (vals d_seq) == Spec.Ed25519.d) =
  Classical.forall_intro d_at;
  Seq.lemma_eq_intro (vals d_seq) (F.limbs_of Spec.Ed25519.d);
  assert_norm (Spec.Ed25519.d < C.prime);
  const_ok (vals d_seq) Spec.Ed25519.d

let d_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (d_seq <: Seq.seq S64.t) })
  = G.mk_static_array d_list


(** [Spec.Ed25519.d2]. *)
let d2_list : list S64.t = [
  S64.classify 0x69b9426b2f159uL; S64.classify 0x35050762add7auL; S64.classify 0x3cf44c0038052uL; S64.classify 0x6738cc7407977uL; S64.classify 0x2406d9dc56dffuL
]

[@@FStar.Custard.no_specialize]
let d2_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length d2_list == 5);
  Seq.seq_of_list d2_list

let d2_at_0 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 0 == Seq.index (F.limbs_of Spec.Ed25519.d2) 0) =
  assert_norm (List.Tot.length d2_list == 5);
  assert_norm (List.Tot.index d2_list 0 == S64.classify 0x69b9426b2f159uL);
  assert_norm (U64.v 0x69b9426b2f159uL == Spec.Ed25519.d2 / pow2 (F.rad * 0) % F.base);
  limb_at d2_list Spec.Ed25519.d2 0 0x69b9426b2f159uL

let d2_at_1 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 1 == Seq.index (F.limbs_of Spec.Ed25519.d2) 1) =
  assert_norm (List.Tot.length d2_list == 5);
  assert_norm (List.Tot.index d2_list 1 == S64.classify 0x35050762add7auL);
  assert_norm (U64.v 0x35050762add7auL == Spec.Ed25519.d2 / pow2 (F.rad * 1) % F.base);
  limb_at d2_list Spec.Ed25519.d2 1 0x35050762add7auL

let d2_at_2 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 2 == Seq.index (F.limbs_of Spec.Ed25519.d2) 2) =
  assert_norm (List.Tot.length d2_list == 5);
  assert_norm (List.Tot.index d2_list 2 == S64.classify 0x3cf44c0038052uL);
  assert_norm (U64.v 0x3cf44c0038052uL == Spec.Ed25519.d2 / pow2 (F.rad * 2) % F.base);
  limb_at d2_list Spec.Ed25519.d2 2 0x3cf44c0038052uL

let d2_at_3 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 3 == Seq.index (F.limbs_of Spec.Ed25519.d2) 3) =
  assert_norm (List.Tot.length d2_list == 5);
  assert_norm (List.Tot.index d2_list 3 == S64.classify 0x6738cc7407977uL);
  assert_norm (U64.v 0x6738cc7407977uL == Spec.Ed25519.d2 / pow2 (F.rad * 3) % F.base);
  limb_at d2_list Spec.Ed25519.d2 3 0x6738cc7407977uL

let d2_at_4 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 4 == Seq.index (F.limbs_of Spec.Ed25519.d2) 4) =
  assert_norm (List.Tot.length d2_list == 5);
  assert_norm (List.Tot.index d2_list 4 == S64.classify 0x2406d9dc56dffuL);
  assert_norm (U64.v 0x2406d9dc56dffuL == Spec.Ed25519.d2 / pow2 (F.rad * 4) % F.base);
  limb_at d2_list Spec.Ed25519.d2 4 0x2406d9dc56dffuL

let d2_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals d2_seq) k == Seq.index (F.limbs_of Spec.Ed25519.d2) k)
  = assert_norm (F.nl == 5);
    if k = 0 then d2_at_0 ()
    else if k = 1 then d2_at_1 ()
    else if k = 2 then d2_at_2 ()
    else if k = 3 then d2_at_3 ()
    else d2_at_4 ()

let d2_ok (_: unit)
  : Lemma (F.felem (vals d2_seq) /\ F.fev (vals d2_seq) == Spec.Ed25519.d2) =
  Classical.forall_intro d2_at;
  Seq.lemma_eq_intro (vals d2_seq) (F.limbs_of Spec.Ed25519.d2);
  assert_norm (Spec.Ed25519.d2 < C.prime);
  const_ok (vals d2_seq) Spec.Ed25519.d2

let d2_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (d2_seq <: Seq.seq S64.t) })
  = G.mk_static_array d2_list


(** [Spec.Ed25519.sqrt_m1]. *)
let sqrtm1_list : list S64.t = [
  S64.classify 0x61b274a0ea0b0uL; S64.classify 0xd5a5fc8f189duL; S64.classify 0x7ef5e9cbd0c60uL; S64.classify 0x78595a6804c9euL; S64.classify 0x2b8324804fc1duL
]

[@@FStar.Custard.no_specialize]
let sqrtm1_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length sqrtm1_list == 5);
  Seq.seq_of_list sqrtm1_list

let sqrtm1_at_0 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 0 == Seq.index (F.limbs_of Spec.Ed25519.sqrt_m1) 0) =
  assert_norm (List.Tot.length sqrtm1_list == 5);
  assert_norm (List.Tot.index sqrtm1_list 0 == S64.classify 0x61b274a0ea0b0uL);
  assert_norm (U64.v 0x61b274a0ea0b0uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 0) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 0 0x61b274a0ea0b0uL

let sqrtm1_at_1 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 1 == Seq.index (F.limbs_of Spec.Ed25519.sqrt_m1) 1) =
  assert_norm (List.Tot.length sqrtm1_list == 5);
  assert_norm (List.Tot.index sqrtm1_list 1 == S64.classify 0xd5a5fc8f189duL);
  assert_norm (U64.v 0xd5a5fc8f189duL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 1) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 1 0xd5a5fc8f189duL

let sqrtm1_at_2 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 2 == Seq.index (F.limbs_of Spec.Ed25519.sqrt_m1) 2) =
  assert_norm (List.Tot.length sqrtm1_list == 5);
  assert_norm (List.Tot.index sqrtm1_list 2 == S64.classify 0x7ef5e9cbd0c60uL);
  assert_norm (U64.v 0x7ef5e9cbd0c60uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 2) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 2 0x7ef5e9cbd0c60uL

let sqrtm1_at_3 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 3 == Seq.index (F.limbs_of Spec.Ed25519.sqrt_m1) 3) =
  assert_norm (List.Tot.length sqrtm1_list == 5);
  assert_norm (List.Tot.index sqrtm1_list 3 == S64.classify 0x78595a6804c9euL);
  assert_norm (U64.v 0x78595a6804c9euL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 3) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 3 0x78595a6804c9euL

let sqrtm1_at_4 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 4 == Seq.index (F.limbs_of Spec.Ed25519.sqrt_m1) 4) =
  assert_norm (List.Tot.length sqrtm1_list == 5);
  assert_norm (List.Tot.index sqrtm1_list 4 == S64.classify 0x2b8324804fc1duL);
  assert_norm (U64.v 0x2b8324804fc1duL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 4) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 4 0x2b8324804fc1duL

let sqrtm1_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals sqrtm1_seq) k == Seq.index (F.limbs_of Spec.Ed25519.sqrt_m1) k)
  = assert_norm (F.nl == 5);
    if k = 0 then sqrtm1_at_0 ()
    else if k = 1 then sqrtm1_at_1 ()
    else if k = 2 then sqrtm1_at_2 ()
    else if k = 3 then sqrtm1_at_3 ()
    else sqrtm1_at_4 ()

let sqrtm1_ok (_: unit)
  : Lemma (F.felem (vals sqrtm1_seq) /\ F.fev (vals sqrtm1_seq) == Spec.Ed25519.sqrt_m1) =
  Classical.forall_intro sqrtm1_at;
  Seq.lemma_eq_intro (vals sqrtm1_seq) (F.limbs_of Spec.Ed25519.sqrt_m1);
  assert_norm (Spec.Ed25519.sqrt_m1 < C.prime);
  const_ok (vals sqrtm1_seq) Spec.Ed25519.sqrt_m1

let sqrtm1_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (sqrtm1_seq <: Seq.seq S64.t) })
  = G.mk_static_array sqrtm1_list


(** [Spec.Ed25519.g_x]. *)
let gx_list : list S64.t = [
  S64.classify 0x62d608f25d51auL; S64.classify 0x412a4b4f6592auL; S64.classify 0x75b7171a4b31duL; S64.classify 0x1ff60527118feuL; S64.classify 0x216936d3cd6e5uL
]

[@@FStar.Custard.no_specialize]
let gx_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length gx_list == 5);
  Seq.seq_of_list gx_list

let gx_at_0 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 0 == Seq.index (F.limbs_of Spec.Ed25519.g_x) 0) =
  assert_norm (List.Tot.length gx_list == 5);
  assert_norm (List.Tot.index gx_list 0 == S64.classify 0x62d608f25d51auL);
  assert_norm (U64.v 0x62d608f25d51auL == Spec.Ed25519.g_x / pow2 (F.rad * 0) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 0 0x62d608f25d51auL

let gx_at_1 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 1 == Seq.index (F.limbs_of Spec.Ed25519.g_x) 1) =
  assert_norm (List.Tot.length gx_list == 5);
  assert_norm (List.Tot.index gx_list 1 == S64.classify 0x412a4b4f6592auL);
  assert_norm (U64.v 0x412a4b4f6592auL == Spec.Ed25519.g_x / pow2 (F.rad * 1) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 1 0x412a4b4f6592auL

let gx_at_2 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 2 == Seq.index (F.limbs_of Spec.Ed25519.g_x) 2) =
  assert_norm (List.Tot.length gx_list == 5);
  assert_norm (List.Tot.index gx_list 2 == S64.classify 0x75b7171a4b31duL);
  assert_norm (U64.v 0x75b7171a4b31duL == Spec.Ed25519.g_x / pow2 (F.rad * 2) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 2 0x75b7171a4b31duL

let gx_at_3 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 3 == Seq.index (F.limbs_of Spec.Ed25519.g_x) 3) =
  assert_norm (List.Tot.length gx_list == 5);
  assert_norm (List.Tot.index gx_list 3 == S64.classify 0x1ff60527118feuL);
  assert_norm (U64.v 0x1ff60527118feuL == Spec.Ed25519.g_x / pow2 (F.rad * 3) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 3 0x1ff60527118feuL

let gx_at_4 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 4 == Seq.index (F.limbs_of Spec.Ed25519.g_x) 4) =
  assert_norm (List.Tot.length gx_list == 5);
  assert_norm (List.Tot.index gx_list 4 == S64.classify 0x216936d3cd6e5uL);
  assert_norm (U64.v 0x216936d3cd6e5uL == Spec.Ed25519.g_x / pow2 (F.rad * 4) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 4 0x216936d3cd6e5uL

let gx_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals gx_seq) k == Seq.index (F.limbs_of Spec.Ed25519.g_x) k)
  = assert_norm (F.nl == 5);
    if k = 0 then gx_at_0 ()
    else if k = 1 then gx_at_1 ()
    else if k = 2 then gx_at_2 ()
    else if k = 3 then gx_at_3 ()
    else gx_at_4 ()

let gx_ok (_: unit)
  : Lemma (F.felem (vals gx_seq) /\ F.fev (vals gx_seq) == Spec.Ed25519.g_x) =
  Classical.forall_intro gx_at;
  Seq.lemma_eq_intro (vals gx_seq) (F.limbs_of Spec.Ed25519.g_x);
  assert_norm (Spec.Ed25519.g_x < C.prime);
  const_ok (vals gx_seq) Spec.Ed25519.g_x

let gx_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (gx_seq <: Seq.seq S64.t) })
  = G.mk_static_array gx_list


(** [Spec.Ed25519.g_y]. *)
let gy_list : list S64.t = [
  S64.classify 0x6666666666658uL; S64.classify 0x4ccccccccccccuL; S64.classify 0x1999999999999uL; S64.classify 0x3333333333333uL; S64.classify 0x6666666666666uL
]

[@@FStar.Custard.no_specialize]
let gy_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length gy_list == 5);
  Seq.seq_of_list gy_list

let gy_at_0 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 0 == Seq.index (F.limbs_of Spec.Ed25519.g_y) 0) =
  assert_norm (List.Tot.length gy_list == 5);
  assert_norm (List.Tot.index gy_list 0 == S64.classify 0x6666666666658uL);
  assert_norm (U64.v 0x6666666666658uL == Spec.Ed25519.g_y / pow2 (F.rad * 0) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 0 0x6666666666658uL

let gy_at_1 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 1 == Seq.index (F.limbs_of Spec.Ed25519.g_y) 1) =
  assert_norm (List.Tot.length gy_list == 5);
  assert_norm (List.Tot.index gy_list 1 == S64.classify 0x4ccccccccccccuL);
  assert_norm (U64.v 0x4ccccccccccccuL == Spec.Ed25519.g_y / pow2 (F.rad * 1) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 1 0x4ccccccccccccuL

let gy_at_2 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 2 == Seq.index (F.limbs_of Spec.Ed25519.g_y) 2) =
  assert_norm (List.Tot.length gy_list == 5);
  assert_norm (List.Tot.index gy_list 2 == S64.classify 0x1999999999999uL);
  assert_norm (U64.v 0x1999999999999uL == Spec.Ed25519.g_y / pow2 (F.rad * 2) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 2 0x1999999999999uL

let gy_at_3 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 3 == Seq.index (F.limbs_of Spec.Ed25519.g_y) 3) =
  assert_norm (List.Tot.length gy_list == 5);
  assert_norm (List.Tot.index gy_list 3 == S64.classify 0x3333333333333uL);
  assert_norm (U64.v 0x3333333333333uL == Spec.Ed25519.g_y / pow2 (F.rad * 3) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 3 0x3333333333333uL

let gy_at_4 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 4 == Seq.index (F.limbs_of Spec.Ed25519.g_y) 4) =
  assert_norm (List.Tot.length gy_list == 5);
  assert_norm (List.Tot.index gy_list 4 == S64.classify 0x6666666666666uL);
  assert_norm (U64.v 0x6666666666666uL == Spec.Ed25519.g_y / pow2 (F.rad * 4) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 4 0x6666666666666uL

let gy_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals gy_seq) k == Seq.index (F.limbs_of Spec.Ed25519.g_y) k)
  = assert_norm (F.nl == 5);
    if k = 0 then gy_at_0 ()
    else if k = 1 then gy_at_1 ()
    else if k = 2 then gy_at_2 ()
    else if k = 3 then gy_at_3 ()
    else gy_at_4 ()

let gy_ok (_: unit)
  : Lemma (F.felem (vals gy_seq) /\ F.fev (vals gy_seq) == Spec.Ed25519.g_y) =
  Classical.forall_intro gy_at;
  Seq.lemma_eq_intro (vals gy_seq) (F.limbs_of Spec.Ed25519.g_y);
  assert_norm (Spec.Ed25519.g_y < C.prime);
  const_ok (vals gy_seq) Spec.Ed25519.g_y

let gy_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (gy_seq <: Seq.seq S64.t) })
  = G.mk_static_array gy_list


(** {2 The fixed-base window's extra base points}

    [2^64 G], [2^128 G] and [2^192 G], affine, from
    {!Spec.Ed25519.Base}.  Nine field constants, in the same shape as the
    generator's two. *)

(** [Spec.Ed25519.Base.b1x]. *)
let b1x_list : list S64.t = [
  S64.classify 0x36b8ff4eda202uL; S64.classify 0x7daa346bd67c1uL; S64.classify 0x2822a5801e36duL; S64.classify 0x4eaea25b067dauL; S64.classify 0x6222bd88bf2dfuL
]

[@@FStar.Custard.no_specialize]
let b1x_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b1x_list == 5);
  Seq.seq_of_list b1x_list

let b1x_at_0 (_: unit)
  : Lemma (Seq.index (vals b1x_seq) 0 == Seq.index (F.limbs_of Base.b1x) 0) =
  assert_norm (List.Tot.length b1x_list == 5);
  assert_norm (List.Tot.index b1x_list 0 == S64.classify 0x36b8ff4eda202uL);
  assert_norm (U64.v 0x36b8ff4eda202uL == Base.b1x / pow2 (F.rad * 0) % F.base);
  limb_at b1x_list Base.b1x 0 0x36b8ff4eda202uL

let b1x_at_1 (_: unit)
  : Lemma (Seq.index (vals b1x_seq) 1 == Seq.index (F.limbs_of Base.b1x) 1) =
  assert_norm (List.Tot.length b1x_list == 5);
  assert_norm (List.Tot.index b1x_list 1 == S64.classify 0x7daa346bd67c1uL);
  assert_norm (U64.v 0x7daa346bd67c1uL == Base.b1x / pow2 (F.rad * 1) % F.base);
  limb_at b1x_list Base.b1x 1 0x7daa346bd67c1uL

let b1x_at_2 (_: unit)
  : Lemma (Seq.index (vals b1x_seq) 2 == Seq.index (F.limbs_of Base.b1x) 2) =
  assert_norm (List.Tot.length b1x_list == 5);
  assert_norm (List.Tot.index b1x_list 2 == S64.classify 0x2822a5801e36duL);
  assert_norm (U64.v 0x2822a5801e36duL == Base.b1x / pow2 (F.rad * 2) % F.base);
  limb_at b1x_list Base.b1x 2 0x2822a5801e36duL

let b1x_at_3 (_: unit)
  : Lemma (Seq.index (vals b1x_seq) 3 == Seq.index (F.limbs_of Base.b1x) 3) =
  assert_norm (List.Tot.length b1x_list == 5);
  assert_norm (List.Tot.index b1x_list 3 == S64.classify 0x4eaea25b067dauL);
  assert_norm (U64.v 0x4eaea25b067dauL == Base.b1x / pow2 (F.rad * 3) % F.base);
  limb_at b1x_list Base.b1x 3 0x4eaea25b067dauL

let b1x_at_4 (_: unit)
  : Lemma (Seq.index (vals b1x_seq) 4 == Seq.index (F.limbs_of Base.b1x) 4) =
  assert_norm (List.Tot.length b1x_list == 5);
  assert_norm (List.Tot.index b1x_list 4 == S64.classify 0x6222bd88bf2dfuL);
  assert_norm (U64.v 0x6222bd88bf2dfuL == Base.b1x / pow2 (F.rad * 4) % F.base);
  limb_at b1x_list Base.b1x 4 0x6222bd88bf2dfuL

let b1x_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b1x_seq) k == Seq.index (F.limbs_of Base.b1x) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b1x_at_0 ()
    else if k = 1 then b1x_at_1 ()
    else if k = 2 then b1x_at_2 ()
    else if k = 3 then b1x_at_3 ()
    else b1x_at_4 ()

let b1x_ok (_: unit)
  : Lemma (F.felem (vals b1x_seq) /\ F.fev (vals b1x_seq) == Base.b1x) =
  Classical.forall_intro b1x_at;
  Seq.lemma_eq_intro (vals b1x_seq) (F.limbs_of Base.b1x);
  assert_norm (Base.b1x < C.prime);
  const_ok (vals b1x_seq) Base.b1x

let b1x_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b1x_seq <: Seq.seq S64.t) })
  = G.mk_static_array b1x_list

(** [Spec.Ed25519.Base.b1y]. *)
let b1y_list : list S64.t = [
  S64.classify 0x6fa5782e45313uL; S64.classify 0x117520560d1e3uL; S64.classify 0x6df13d5042d8uL; S64.classify 0x12eeb5ed7693uL; S64.classify 0x325bb42ea4eduL
]

[@@FStar.Custard.no_specialize]
let b1y_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b1y_list == 5);
  Seq.seq_of_list b1y_list

let b1y_at_0 (_: unit)
  : Lemma (Seq.index (vals b1y_seq) 0 == Seq.index (F.limbs_of Base.b1y) 0) =
  assert_norm (List.Tot.length b1y_list == 5);
  assert_norm (List.Tot.index b1y_list 0 == S64.classify 0x6fa5782e45313uL);
  assert_norm (U64.v 0x6fa5782e45313uL == Base.b1y / pow2 (F.rad * 0) % F.base);
  limb_at b1y_list Base.b1y 0 0x6fa5782e45313uL

let b1y_at_1 (_: unit)
  : Lemma (Seq.index (vals b1y_seq) 1 == Seq.index (F.limbs_of Base.b1y) 1) =
  assert_norm (List.Tot.length b1y_list == 5);
  assert_norm (List.Tot.index b1y_list 1 == S64.classify 0x117520560d1e3uL);
  assert_norm (U64.v 0x117520560d1e3uL == Base.b1y / pow2 (F.rad * 1) % F.base);
  limb_at b1y_list Base.b1y 1 0x117520560d1e3uL

let b1y_at_2 (_: unit)
  : Lemma (Seq.index (vals b1y_seq) 2 == Seq.index (F.limbs_of Base.b1y) 2) =
  assert_norm (List.Tot.length b1y_list == 5);
  assert_norm (List.Tot.index b1y_list 2 == S64.classify 0x6df13d5042d8uL);
  assert_norm (U64.v 0x6df13d5042d8uL == Base.b1y / pow2 (F.rad * 2) % F.base);
  limb_at b1y_list Base.b1y 2 0x6df13d5042d8uL

let b1y_at_3 (_: unit)
  : Lemma (Seq.index (vals b1y_seq) 3 == Seq.index (F.limbs_of Base.b1y) 3) =
  assert_norm (List.Tot.length b1y_list == 5);
  assert_norm (List.Tot.index b1y_list 3 == S64.classify 0x12eeb5ed7693uL);
  assert_norm (U64.v 0x12eeb5ed7693uL == Base.b1y / pow2 (F.rad * 3) % F.base);
  limb_at b1y_list Base.b1y 3 0x12eeb5ed7693uL

let b1y_at_4 (_: unit)
  : Lemma (Seq.index (vals b1y_seq) 4 == Seq.index (F.limbs_of Base.b1y) 4) =
  assert_norm (List.Tot.length b1y_list == 5);
  assert_norm (List.Tot.index b1y_list 4 == S64.classify 0x325bb42ea4eduL);
  assert_norm (U64.v 0x325bb42ea4eduL == Base.b1y / pow2 (F.rad * 4) % F.base);
  limb_at b1y_list Base.b1y 4 0x325bb42ea4eduL

let b1y_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b1y_seq) k == Seq.index (F.limbs_of Base.b1y) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b1y_at_0 ()
    else if k = 1 then b1y_at_1 ()
    else if k = 2 then b1y_at_2 ()
    else if k = 3 then b1y_at_3 ()
    else b1y_at_4 ()

let b1y_ok (_: unit)
  : Lemma (F.felem (vals b1y_seq) /\ F.fev (vals b1y_seq) == Base.b1y) =
  Classical.forall_intro b1y_at;
  Seq.lemma_eq_intro (vals b1y_seq) (F.limbs_of Base.b1y);
  assert_norm (Base.b1y < C.prime);
  const_ok (vals b1y_seq) Base.b1y

let b1y_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b1y_seq <: Seq.seq S64.t) })
  = G.mk_static_array b1y_list

(** [Spec.Ed25519.Base.b1t]. *)
let b1t_list : list S64.t = [
  S64.classify 0x592e9b6740859uL; S64.classify 0x1d39897f0c5bfuL; S64.classify 0x251580ec2af8uL; S64.classify 0x70563ccc07320uL; S64.classify 0x628b09e2c7d3auL
]

[@@FStar.Custard.no_specialize]
let b1t_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b1t_list == 5);
  Seq.seq_of_list b1t_list

let b1t_at_0 (_: unit)
  : Lemma (Seq.index (vals b1t_seq) 0 == Seq.index (F.limbs_of Base.b1t) 0) =
  assert_norm (List.Tot.length b1t_list == 5);
  assert_norm (List.Tot.index b1t_list 0 == S64.classify 0x592e9b6740859uL);
  assert_norm (U64.v 0x592e9b6740859uL == Base.b1t / pow2 (F.rad * 0) % F.base);
  limb_at b1t_list Base.b1t 0 0x592e9b6740859uL

let b1t_at_1 (_: unit)
  : Lemma (Seq.index (vals b1t_seq) 1 == Seq.index (F.limbs_of Base.b1t) 1) =
  assert_norm (List.Tot.length b1t_list == 5);
  assert_norm (List.Tot.index b1t_list 1 == S64.classify 0x1d39897f0c5bfuL);
  assert_norm (U64.v 0x1d39897f0c5bfuL == Base.b1t / pow2 (F.rad * 1) % F.base);
  limb_at b1t_list Base.b1t 1 0x1d39897f0c5bfuL

let b1t_at_2 (_: unit)
  : Lemma (Seq.index (vals b1t_seq) 2 == Seq.index (F.limbs_of Base.b1t) 2) =
  assert_norm (List.Tot.length b1t_list == 5);
  assert_norm (List.Tot.index b1t_list 2 == S64.classify 0x251580ec2af8uL);
  assert_norm (U64.v 0x251580ec2af8uL == Base.b1t / pow2 (F.rad * 2) % F.base);
  limb_at b1t_list Base.b1t 2 0x251580ec2af8uL

let b1t_at_3 (_: unit)
  : Lemma (Seq.index (vals b1t_seq) 3 == Seq.index (F.limbs_of Base.b1t) 3) =
  assert_norm (List.Tot.length b1t_list == 5);
  assert_norm (List.Tot.index b1t_list 3 == S64.classify 0x70563ccc07320uL);
  assert_norm (U64.v 0x70563ccc07320uL == Base.b1t / pow2 (F.rad * 3) % F.base);
  limb_at b1t_list Base.b1t 3 0x70563ccc07320uL

let b1t_at_4 (_: unit)
  : Lemma (Seq.index (vals b1t_seq) 4 == Seq.index (F.limbs_of Base.b1t) 4) =
  assert_norm (List.Tot.length b1t_list == 5);
  assert_norm (List.Tot.index b1t_list 4 == S64.classify 0x628b09e2c7d3auL);
  assert_norm (U64.v 0x628b09e2c7d3auL == Base.b1t / pow2 (F.rad * 4) % F.base);
  limb_at b1t_list Base.b1t 4 0x628b09e2c7d3auL

let b1t_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b1t_seq) k == Seq.index (F.limbs_of Base.b1t) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b1t_at_0 ()
    else if k = 1 then b1t_at_1 ()
    else if k = 2 then b1t_at_2 ()
    else if k = 3 then b1t_at_3 ()
    else b1t_at_4 ()

let b1t_ok (_: unit)
  : Lemma (F.felem (vals b1t_seq) /\ F.fev (vals b1t_seq) == Base.b1t) =
  Classical.forall_intro b1t_at;
  Seq.lemma_eq_intro (vals b1t_seq) (F.limbs_of Base.b1t);
  assert_norm (Base.b1t < C.prime);
  const_ok (vals b1t_seq) Base.b1t

let b1t_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b1t_seq <: Seq.seq S64.t) })
  = G.mk_static_array b1t_list

(** [Spec.Ed25519.Base.b2x]. *)
let b2x_list : list S64.t = [
  S64.classify 0x47ae60b7e824uL; S64.classify 0x1385ce47cbf90uL; S64.classify 0x538a682639a17uL; S64.classify 0x1964a969cc270uL; S64.classify 0x4c27afff3c45fuL
]

[@@FStar.Custard.no_specialize]
let b2x_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b2x_list == 5);
  Seq.seq_of_list b2x_list

let b2x_at_0 (_: unit)
  : Lemma (Seq.index (vals b2x_seq) 0 == Seq.index (F.limbs_of Base.b2x) 0) =
  assert_norm (List.Tot.length b2x_list == 5);
  assert_norm (List.Tot.index b2x_list 0 == S64.classify 0x47ae60b7e824uL);
  assert_norm (U64.v 0x47ae60b7e824uL == Base.b2x / pow2 (F.rad * 0) % F.base);
  limb_at b2x_list Base.b2x 0 0x47ae60b7e824uL

let b2x_at_1 (_: unit)
  : Lemma (Seq.index (vals b2x_seq) 1 == Seq.index (F.limbs_of Base.b2x) 1) =
  assert_norm (List.Tot.length b2x_list == 5);
  assert_norm (List.Tot.index b2x_list 1 == S64.classify 0x1385ce47cbf90uL);
  assert_norm (U64.v 0x1385ce47cbf90uL == Base.b2x / pow2 (F.rad * 1) % F.base);
  limb_at b2x_list Base.b2x 1 0x1385ce47cbf90uL

let b2x_at_2 (_: unit)
  : Lemma (Seq.index (vals b2x_seq) 2 == Seq.index (F.limbs_of Base.b2x) 2) =
  assert_norm (List.Tot.length b2x_list == 5);
  assert_norm (List.Tot.index b2x_list 2 == S64.classify 0x538a682639a17uL);
  assert_norm (U64.v 0x538a682639a17uL == Base.b2x / pow2 (F.rad * 2) % F.base);
  limb_at b2x_list Base.b2x 2 0x538a682639a17uL

let b2x_at_3 (_: unit)
  : Lemma (Seq.index (vals b2x_seq) 3 == Seq.index (F.limbs_of Base.b2x) 3) =
  assert_norm (List.Tot.length b2x_list == 5);
  assert_norm (List.Tot.index b2x_list 3 == S64.classify 0x1964a969cc270uL);
  assert_norm (U64.v 0x1964a969cc270uL == Base.b2x / pow2 (F.rad * 3) % F.base);
  limb_at b2x_list Base.b2x 3 0x1964a969cc270uL

let b2x_at_4 (_: unit)
  : Lemma (Seq.index (vals b2x_seq) 4 == Seq.index (F.limbs_of Base.b2x) 4) =
  assert_norm (List.Tot.length b2x_list == 5);
  assert_norm (List.Tot.index b2x_list 4 == S64.classify 0x4c27afff3c45fuL);
  assert_norm (U64.v 0x4c27afff3c45fuL == Base.b2x / pow2 (F.rad * 4) % F.base);
  limb_at b2x_list Base.b2x 4 0x4c27afff3c45fuL

let b2x_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b2x_seq) k == Seq.index (F.limbs_of Base.b2x) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b2x_at_0 ()
    else if k = 1 then b2x_at_1 ()
    else if k = 2 then b2x_at_2 ()
    else if k = 3 then b2x_at_3 ()
    else b2x_at_4 ()

let b2x_ok (_: unit)
  : Lemma (F.felem (vals b2x_seq) /\ F.fev (vals b2x_seq) == Base.b2x) =
  Classical.forall_intro b2x_at;
  Seq.lemma_eq_intro (vals b2x_seq) (F.limbs_of Base.b2x);
  assert_norm (Base.b2x < C.prime);
  const_ok (vals b2x_seq) Base.b2x

let b2x_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b2x_seq <: Seq.seq S64.t) })
  = G.mk_static_array b2x_list

(** [Spec.Ed25519.Base.b2y]. *)
let b2y_list : list S64.t = [
  S64.classify 0x2bd114bf5a66buL; S64.classify 0x3ca349893cb77uL; S64.classify 0x30a70ea4342f8uL; S64.classify 0x43ecaf88f5b13uL; S64.classify 0x5f2c99e6526dcuL
]

[@@FStar.Custard.no_specialize]
let b2y_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b2y_list == 5);
  Seq.seq_of_list b2y_list

let b2y_at_0 (_: unit)
  : Lemma (Seq.index (vals b2y_seq) 0 == Seq.index (F.limbs_of Base.b2y) 0) =
  assert_norm (List.Tot.length b2y_list == 5);
  assert_norm (List.Tot.index b2y_list 0 == S64.classify 0x2bd114bf5a66buL);
  assert_norm (U64.v 0x2bd114bf5a66buL == Base.b2y / pow2 (F.rad * 0) % F.base);
  limb_at b2y_list Base.b2y 0 0x2bd114bf5a66buL

let b2y_at_1 (_: unit)
  : Lemma (Seq.index (vals b2y_seq) 1 == Seq.index (F.limbs_of Base.b2y) 1) =
  assert_norm (List.Tot.length b2y_list == 5);
  assert_norm (List.Tot.index b2y_list 1 == S64.classify 0x3ca349893cb77uL);
  assert_norm (U64.v 0x3ca349893cb77uL == Base.b2y / pow2 (F.rad * 1) % F.base);
  limb_at b2y_list Base.b2y 1 0x3ca349893cb77uL

let b2y_at_2 (_: unit)
  : Lemma (Seq.index (vals b2y_seq) 2 == Seq.index (F.limbs_of Base.b2y) 2) =
  assert_norm (List.Tot.length b2y_list == 5);
  assert_norm (List.Tot.index b2y_list 2 == S64.classify 0x30a70ea4342f8uL);
  assert_norm (U64.v 0x30a70ea4342f8uL == Base.b2y / pow2 (F.rad * 2) % F.base);
  limb_at b2y_list Base.b2y 2 0x30a70ea4342f8uL

let b2y_at_3 (_: unit)
  : Lemma (Seq.index (vals b2y_seq) 3 == Seq.index (F.limbs_of Base.b2y) 3) =
  assert_norm (List.Tot.length b2y_list == 5);
  assert_norm (List.Tot.index b2y_list 3 == S64.classify 0x43ecaf88f5b13uL);
  assert_norm (U64.v 0x43ecaf88f5b13uL == Base.b2y / pow2 (F.rad * 3) % F.base);
  limb_at b2y_list Base.b2y 3 0x43ecaf88f5b13uL

let b2y_at_4 (_: unit)
  : Lemma (Seq.index (vals b2y_seq) 4 == Seq.index (F.limbs_of Base.b2y) 4) =
  assert_norm (List.Tot.length b2y_list == 5);
  assert_norm (List.Tot.index b2y_list 4 == S64.classify 0x5f2c99e6526dcuL);
  assert_norm (U64.v 0x5f2c99e6526dcuL == Base.b2y / pow2 (F.rad * 4) % F.base);
  limb_at b2y_list Base.b2y 4 0x5f2c99e6526dcuL

let b2y_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b2y_seq) k == Seq.index (F.limbs_of Base.b2y) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b2y_at_0 ()
    else if k = 1 then b2y_at_1 ()
    else if k = 2 then b2y_at_2 ()
    else if k = 3 then b2y_at_3 ()
    else b2y_at_4 ()

let b2y_ok (_: unit)
  : Lemma (F.felem (vals b2y_seq) /\ F.fev (vals b2y_seq) == Base.b2y) =
  Classical.forall_intro b2y_at;
  Seq.lemma_eq_intro (vals b2y_seq) (F.limbs_of Base.b2y);
  assert_norm (Base.b2y < C.prime);
  const_ok (vals b2y_seq) Base.b2y

let b2y_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b2y_seq <: Seq.seq S64.t) })
  = G.mk_static_array b2y_list

(** [Spec.Ed25519.Base.b2t]. *)
let b2t_list : list S64.t = [
  S64.classify 0x731c946f1338auL; S64.classify 0x4ccc75b53d3cuL; S64.classify 0x6492da851e192uL; S64.classify 0x17ea70ab0003uL; S64.classify 0x5a164fd0bf46uL
]

[@@FStar.Custard.no_specialize]
let b2t_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b2t_list == 5);
  Seq.seq_of_list b2t_list

let b2t_at_0 (_: unit)
  : Lemma (Seq.index (vals b2t_seq) 0 == Seq.index (F.limbs_of Base.b2t) 0) =
  assert_norm (List.Tot.length b2t_list == 5);
  assert_norm (List.Tot.index b2t_list 0 == S64.classify 0x731c946f1338auL);
  assert_norm (U64.v 0x731c946f1338auL == Base.b2t / pow2 (F.rad * 0) % F.base);
  limb_at b2t_list Base.b2t 0 0x731c946f1338auL

let b2t_at_1 (_: unit)
  : Lemma (Seq.index (vals b2t_seq) 1 == Seq.index (F.limbs_of Base.b2t) 1) =
  assert_norm (List.Tot.length b2t_list == 5);
  assert_norm (List.Tot.index b2t_list 1 == S64.classify 0x4ccc75b53d3cuL);
  assert_norm (U64.v 0x4ccc75b53d3cuL == Base.b2t / pow2 (F.rad * 1) % F.base);
  limb_at b2t_list Base.b2t 1 0x4ccc75b53d3cuL

let b2t_at_2 (_: unit)
  : Lemma (Seq.index (vals b2t_seq) 2 == Seq.index (F.limbs_of Base.b2t) 2) =
  assert_norm (List.Tot.length b2t_list == 5);
  assert_norm (List.Tot.index b2t_list 2 == S64.classify 0x6492da851e192uL);
  assert_norm (U64.v 0x6492da851e192uL == Base.b2t / pow2 (F.rad * 2) % F.base);
  limb_at b2t_list Base.b2t 2 0x6492da851e192uL

let b2t_at_3 (_: unit)
  : Lemma (Seq.index (vals b2t_seq) 3 == Seq.index (F.limbs_of Base.b2t) 3) =
  assert_norm (List.Tot.length b2t_list == 5);
  assert_norm (List.Tot.index b2t_list 3 == S64.classify 0x17ea70ab0003uL);
  assert_norm (U64.v 0x17ea70ab0003uL == Base.b2t / pow2 (F.rad * 3) % F.base);
  limb_at b2t_list Base.b2t 3 0x17ea70ab0003uL

let b2t_at_4 (_: unit)
  : Lemma (Seq.index (vals b2t_seq) 4 == Seq.index (F.limbs_of Base.b2t) 4) =
  assert_norm (List.Tot.length b2t_list == 5);
  assert_norm (List.Tot.index b2t_list 4 == S64.classify 0x5a164fd0bf46uL);
  assert_norm (U64.v 0x5a164fd0bf46uL == Base.b2t / pow2 (F.rad * 4) % F.base);
  limb_at b2t_list Base.b2t 4 0x5a164fd0bf46uL


let b2t_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b2t_seq) k == Seq.index (F.limbs_of Base.b2t) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b2t_at_0 ()
    else if k = 1 then b2t_at_1 ()
    else if k = 2 then b2t_at_2 ()
    else if k = 3 then b2t_at_3 ()
    else b2t_at_4 ()

let b2t_ok (_: unit)
  : Lemma (F.felem (vals b2t_seq) /\ F.fev (vals b2t_seq) == Base.b2t) =
  Classical.forall_intro b2t_at;
  Seq.lemma_eq_intro (vals b2t_seq) (F.limbs_of Base.b2t);
  assert_norm (Base.b2t < C.prime);
  const_ok (vals b2t_seq) Base.b2t

let b2t_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b2t_seq <: Seq.seq S64.t) })
  = G.mk_static_array b2t_list

(** [Spec.Ed25519.Base.b3x]. *)
let b3x_list : list S64.t = [
  S64.classify 0x2d644c7dad28duL; S64.classify 0x43703afa4db6fuL; S64.classify 0x1f85df5ea777buL; S64.classify 0x73e16c6821b8euL; S64.classify 0x1bc7af1e38185uL
]

[@@FStar.Custard.no_specialize]
let b3x_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b3x_list == 5);
  Seq.seq_of_list b3x_list

let b3x_at_0 (_: unit)
  : Lemma (Seq.index (vals b3x_seq) 0 == Seq.index (F.limbs_of Base.b3x) 0) =
  assert_norm (List.Tot.length b3x_list == 5);
  assert_norm (List.Tot.index b3x_list 0 == S64.classify 0x2d644c7dad28duL);
  assert_norm (U64.v 0x2d644c7dad28duL == Base.b3x / pow2 (F.rad * 0) % F.base);
  limb_at b3x_list Base.b3x 0 0x2d644c7dad28duL

let b3x_at_1 (_: unit)
  : Lemma (Seq.index (vals b3x_seq) 1 == Seq.index (F.limbs_of Base.b3x) 1) =
  assert_norm (List.Tot.length b3x_list == 5);
  assert_norm (List.Tot.index b3x_list 1 == S64.classify 0x43703afa4db6fuL);
  assert_norm (U64.v 0x43703afa4db6fuL == Base.b3x / pow2 (F.rad * 1) % F.base);
  limb_at b3x_list Base.b3x 1 0x43703afa4db6fuL

let b3x_at_2 (_: unit)
  : Lemma (Seq.index (vals b3x_seq) 2 == Seq.index (F.limbs_of Base.b3x) 2) =
  assert_norm (List.Tot.length b3x_list == 5);
  assert_norm (List.Tot.index b3x_list 2 == S64.classify 0x1f85df5ea777buL);
  assert_norm (U64.v 0x1f85df5ea777buL == Base.b3x / pow2 (F.rad * 2) % F.base);
  limb_at b3x_list Base.b3x 2 0x1f85df5ea777buL

let b3x_at_3 (_: unit)
  : Lemma (Seq.index (vals b3x_seq) 3 == Seq.index (F.limbs_of Base.b3x) 3) =
  assert_norm (List.Tot.length b3x_list == 5);
  assert_norm (List.Tot.index b3x_list 3 == S64.classify 0x73e16c6821b8euL);
  assert_norm (U64.v 0x73e16c6821b8euL == Base.b3x / pow2 (F.rad * 3) % F.base);
  limb_at b3x_list Base.b3x 3 0x73e16c6821b8euL

let b3x_at_4 (_: unit)
  : Lemma (Seq.index (vals b3x_seq) 4 == Seq.index (F.limbs_of Base.b3x) 4) =
  assert_norm (List.Tot.length b3x_list == 5);
  assert_norm (List.Tot.index b3x_list 4 == S64.classify 0x1bc7af1e38185uL);
  assert_norm (U64.v 0x1bc7af1e38185uL == Base.b3x / pow2 (F.rad * 4) % F.base);
  limb_at b3x_list Base.b3x 4 0x1bc7af1e38185uL

let b3x_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b3x_seq) k == Seq.index (F.limbs_of Base.b3x) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b3x_at_0 ()
    else if k = 1 then b3x_at_1 ()
    else if k = 2 then b3x_at_2 ()
    else if k = 3 then b3x_at_3 ()
    else b3x_at_4 ()

let b3x_ok (_: unit)
  : Lemma (F.felem (vals b3x_seq) /\ F.fev (vals b3x_seq) == Base.b3x) =
  Classical.forall_intro b3x_at;
  Seq.lemma_eq_intro (vals b3x_seq) (F.limbs_of Base.b3x);
  assert_norm (Base.b3x < C.prime);
  const_ok (vals b3x_seq) Base.b3x

let b3x_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b3x_seq <: Seq.seq S64.t) })
  = G.mk_static_array b3x_list

(** [Spec.Ed25519.Base.b3y]. *)
let b3y_list : list S64.t = [
  S64.classify 0x2f65900314833uL; S64.classify 0x24c6364e1f95euL; S64.classify 0x57701247409f8uL; S64.classify 0x797bd2f77c3bcuL; S64.classify 0x61d909d855661uL
]

[@@FStar.Custard.no_specialize]
let b3y_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b3y_list == 5);
  Seq.seq_of_list b3y_list

let b3y_at_0 (_: unit)
  : Lemma (Seq.index (vals b3y_seq) 0 == Seq.index (F.limbs_of Base.b3y) 0) =
  assert_norm (List.Tot.length b3y_list == 5);
  assert_norm (List.Tot.index b3y_list 0 == S64.classify 0x2f65900314833uL);
  assert_norm (U64.v 0x2f65900314833uL == Base.b3y / pow2 (F.rad * 0) % F.base);
  limb_at b3y_list Base.b3y 0 0x2f65900314833uL

let b3y_at_1 (_: unit)
  : Lemma (Seq.index (vals b3y_seq) 1 == Seq.index (F.limbs_of Base.b3y) 1) =
  assert_norm (List.Tot.length b3y_list == 5);
  assert_norm (List.Tot.index b3y_list 1 == S64.classify 0x24c6364e1f95euL);
  assert_norm (U64.v 0x24c6364e1f95euL == Base.b3y / pow2 (F.rad * 1) % F.base);
  limb_at b3y_list Base.b3y 1 0x24c6364e1f95euL

let b3y_at_2 (_: unit)
  : Lemma (Seq.index (vals b3y_seq) 2 == Seq.index (F.limbs_of Base.b3y) 2) =
  assert_norm (List.Tot.length b3y_list == 5);
  assert_norm (List.Tot.index b3y_list 2 == S64.classify 0x57701247409f8uL);
  assert_norm (U64.v 0x57701247409f8uL == Base.b3y / pow2 (F.rad * 2) % F.base);
  limb_at b3y_list Base.b3y 2 0x57701247409f8uL

let b3y_at_3 (_: unit)
  : Lemma (Seq.index (vals b3y_seq) 3 == Seq.index (F.limbs_of Base.b3y) 3) =
  assert_norm (List.Tot.length b3y_list == 5);
  assert_norm (List.Tot.index b3y_list 3 == S64.classify 0x797bd2f77c3bcuL);
  assert_norm (U64.v 0x797bd2f77c3bcuL == Base.b3y / pow2 (F.rad * 3) % F.base);
  limb_at b3y_list Base.b3y 3 0x797bd2f77c3bcuL

let b3y_at_4 (_: unit)
  : Lemma (Seq.index (vals b3y_seq) 4 == Seq.index (F.limbs_of Base.b3y) 4) =
  assert_norm (List.Tot.length b3y_list == 5);
  assert_norm (List.Tot.index b3y_list 4 == S64.classify 0x61d909d855661uL);
  assert_norm (U64.v 0x61d909d855661uL == Base.b3y / pow2 (F.rad * 4) % F.base);
  limb_at b3y_list Base.b3y 4 0x61d909d855661uL

let b3y_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b3y_seq) k == Seq.index (F.limbs_of Base.b3y) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b3y_at_0 ()
    else if k = 1 then b3y_at_1 ()
    else if k = 2 then b3y_at_2 ()
    else if k = 3 then b3y_at_3 ()
    else b3y_at_4 ()

let b3y_ok (_: unit)
  : Lemma (F.felem (vals b3y_seq) /\ F.fev (vals b3y_seq) == Base.b3y) =
  Classical.forall_intro b3y_at;
  Seq.lemma_eq_intro (vals b3y_seq) (F.limbs_of Base.b3y);
  assert_norm (Base.b3y < C.prime);
  const_ok (vals b3y_seq) Base.b3y

let b3y_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b3y_seq <: Seq.seq S64.t) })
  = G.mk_static_array b3y_list

(** [Spec.Ed25519.Base.b3t]. *)
let b3t_list : list S64.t = [
  S64.classify 0x45216636c2c7uL; S64.classify 0x6cadbcfdf0a37uL; S64.classify 0x47c3ef66ee3c8uL; S64.classify 0x522665b326f25uL; S64.classify 0x1a340b8054b8fuL
]

[@@FStar.Custard.no_specialize]
let b3t_seq : Seq.lseq S64.t 5 =
  assert_norm (List.Tot.length b3t_list == 5);
  Seq.seq_of_list b3t_list

let b3t_at_0 (_: unit)
  : Lemma (Seq.index (vals b3t_seq) 0 == Seq.index (F.limbs_of Base.b3t) 0) =
  assert_norm (List.Tot.length b3t_list == 5);
  assert_norm (List.Tot.index b3t_list 0 == S64.classify 0x45216636c2c7uL);
  assert_norm (U64.v 0x45216636c2c7uL == Base.b3t / pow2 (F.rad * 0) % F.base);
  limb_at b3t_list Base.b3t 0 0x45216636c2c7uL

let b3t_at_1 (_: unit)
  : Lemma (Seq.index (vals b3t_seq) 1 == Seq.index (F.limbs_of Base.b3t) 1) =
  assert_norm (List.Tot.length b3t_list == 5);
  assert_norm (List.Tot.index b3t_list 1 == S64.classify 0x6cadbcfdf0a37uL);
  assert_norm (U64.v 0x6cadbcfdf0a37uL == Base.b3t / pow2 (F.rad * 1) % F.base);
  limb_at b3t_list Base.b3t 1 0x6cadbcfdf0a37uL

let b3t_at_2 (_: unit)
  : Lemma (Seq.index (vals b3t_seq) 2 == Seq.index (F.limbs_of Base.b3t) 2) =
  assert_norm (List.Tot.length b3t_list == 5);
  assert_norm (List.Tot.index b3t_list 2 == S64.classify 0x47c3ef66ee3c8uL);
  assert_norm (U64.v 0x47c3ef66ee3c8uL == Base.b3t / pow2 (F.rad * 2) % F.base);
  limb_at b3t_list Base.b3t 2 0x47c3ef66ee3c8uL

let b3t_at_3 (_: unit)
  : Lemma (Seq.index (vals b3t_seq) 3 == Seq.index (F.limbs_of Base.b3t) 3) =
  assert_norm (List.Tot.length b3t_list == 5);
  assert_norm (List.Tot.index b3t_list 3 == S64.classify 0x522665b326f25uL);
  assert_norm (U64.v 0x522665b326f25uL == Base.b3t / pow2 (F.rad * 3) % F.base);
  limb_at b3t_list Base.b3t 3 0x522665b326f25uL

let b3t_at_4 (_: unit)
  : Lemma (Seq.index (vals b3t_seq) 4 == Seq.index (F.limbs_of Base.b3t) 4) =
  assert_norm (List.Tot.length b3t_list == 5);
  assert_norm (List.Tot.index b3t_list 4 == S64.classify 0x1a340b8054b8fuL);
  assert_norm (U64.v 0x1a340b8054b8fuL == Base.b3t / pow2 (F.rad * 4) % F.base);
  limb_at b3t_list Base.b3t 4 0x1a340b8054b8fuL

let b3t_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals b3t_seq) k == Seq.index (F.limbs_of Base.b3t) k)
  = assert_norm (F.nl == 5);
    if k = 0 then b3t_at_0 ()
    else if k = 1 then b3t_at_1 ()
    else if k = 2 then b3t_at_2 ()
    else if k = 3 then b3t_at_3 ()
    else b3t_at_4 ()

let b3t_ok (_: unit)
  : Lemma (F.felem (vals b3t_seq) /\ F.fev (vals b3t_seq) == Base.b3t) =
  Classical.forall_intro b3t_at;
  Seq.lemma_eq_intro (vals b3t_seq) (F.limbs_of Base.b3t);
  assert_norm (Base.b3t < C.prime);
  const_ok (vals b3t_seq) Base.b3t

let b3t_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (b3t_seq <: Seq.seq S64.t) })
  = G.mk_static_array b3t_list

#pop-options
