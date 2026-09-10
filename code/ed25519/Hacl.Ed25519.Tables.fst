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
    time, which is a sixteen-line proof that has no business sitting in the
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
module C = Spec.Curve25519
module Math = FStar.Math.Lemmas
module Sc = Spec.Ed25519.Scalar

(** [2^256 - q = 0xefffffffffffffffffffffffffffffffeb2106215d086329a7ed9ce5a30a2c13],
    least significant limb first. *)
let qc_list : list S64.t = [
  S64.classify 0x2c13uL; S64.classify 0xa30auL; S64.classify 0x9ce5uL; S64.classify 0xa7eduL;
  S64.classify 0x6329uL; S64.classify 0x5d08uL; S64.classify 0x0621uL; S64.classify 0xeb21uL;
  S64.classify 0xffffuL; S64.classify 0xffffuL; S64.classify 0xffffuL; S64.classify 0xffffuL;
  S64.classify 0xffffuL; S64.classify 0xffffuL; S64.classify 0xffffuL; S64.classify 0xefffuL
]

[@@FStar.Custard.no_specialize]
let qc_seq : Seq.lseq S64.t 16 =
  assert_norm (List.Tot.length qc_list == 16);
  Seq.seq_of_list qc_list

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** Entry by entry against the specification's [qc], and one query per
    entry.  [qc_index] turns [Seq.init] into an arithmetic expression and
    [assert_norm] evaluates it; the literal comes out of the list rather
    than out of the sequence, because [FStar.Seq]'s representation is
    abstract and the normaliser cannot see through it.  Asking for all
    sixteen entries in one query is the same proof and a hundred times
    slower: every literal above [2^250] then sits in the context of every
    other one. *)
let qc_len (_: unit) : Lemma (List.Tot.length qc_list == 16) =
  assert_norm (List.Tot.length qc_list == 16)

let entry (k: nat { k < F.nl }) (x: U64.t)
  : Lemma (requires Seq.index qc_seq k == S64.classify x /\
                    U64.v x == (pow2 256 - Sc.q) / pow2 (F.rad * k) % F.base)
          (ensures Seq.index (vals qc_seq) k == Seq.index Sc.qc k)
  = Sc.qc_index k

let entry_0 (_: unit) : Lemma (Seq.index (vals qc_seq) 0 == Seq.index Sc.qc 0) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 0;
  assert_norm (List.Tot.index qc_list 0 == S64.classify 0x2c13uL);
  assert_norm (U64.v 0x2c13uL == (pow2 256 - Sc.q) / pow2 (F.rad * 0) % F.base);
  entry 0 0x2c13uL

let entry_1 (_: unit) : Lemma (Seq.index (vals qc_seq) 1 == Seq.index Sc.qc 1) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 1;
  assert_norm (List.Tot.index qc_list 1 == S64.classify 0xa30auL);
  assert_norm (U64.v 0xa30auL == (pow2 256 - Sc.q) / pow2 (F.rad * 1) % F.base);
  entry 1 0xa30auL

let entry_2 (_: unit) : Lemma (Seq.index (vals qc_seq) 2 == Seq.index Sc.qc 2) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 2;
  assert_norm (List.Tot.index qc_list 2 == S64.classify 0x9ce5uL);
  assert_norm (U64.v 0x9ce5uL == (pow2 256 - Sc.q) / pow2 (F.rad * 2) % F.base);
  entry 2 0x9ce5uL

let entry_3 (_: unit) : Lemma (Seq.index (vals qc_seq) 3 == Seq.index Sc.qc 3) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 3;
  assert_norm (List.Tot.index qc_list 3 == S64.classify 0xa7eduL);
  assert_norm (U64.v 0xa7eduL == (pow2 256 - Sc.q) / pow2 (F.rad * 3) % F.base);
  entry 3 0xa7eduL

let entry_4 (_: unit) : Lemma (Seq.index (vals qc_seq) 4 == Seq.index Sc.qc 4) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 4;
  assert_norm (List.Tot.index qc_list 4 == S64.classify 0x6329uL);
  assert_norm (U64.v 0x6329uL == (pow2 256 - Sc.q) / pow2 (F.rad * 4) % F.base);
  entry 4 0x6329uL

let entry_5 (_: unit) : Lemma (Seq.index (vals qc_seq) 5 == Seq.index Sc.qc 5) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 5;
  assert_norm (List.Tot.index qc_list 5 == S64.classify 0x5d08uL);
  assert_norm (U64.v 0x5d08uL == (pow2 256 - Sc.q) / pow2 (F.rad * 5) % F.base);
  entry 5 0x5d08uL

let entry_6 (_: unit) : Lemma (Seq.index (vals qc_seq) 6 == Seq.index Sc.qc 6) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 6;
  assert_norm (List.Tot.index qc_list 6 == S64.classify 0x0621uL);
  assert_norm (U64.v 0x0621uL == (pow2 256 - Sc.q) / pow2 (F.rad * 6) % F.base);
  entry 6 0x0621uL

let entry_7 (_: unit) : Lemma (Seq.index (vals qc_seq) 7 == Seq.index Sc.qc 7) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 7;
  assert_norm (List.Tot.index qc_list 7 == S64.classify 0xeb21uL);
  assert_norm (U64.v 0xeb21uL == (pow2 256 - Sc.q) / pow2 (F.rad * 7) % F.base);
  entry 7 0xeb21uL

let entry_8 (_: unit) : Lemma (Seq.index (vals qc_seq) 8 == Seq.index Sc.qc 8) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 8;
  assert_norm (List.Tot.index qc_list 8 == S64.classify 0xffffuL);
  assert_norm (U64.v 0xffffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 8) % F.base);
  entry 8 0xffffuL

let entry_9 (_: unit) : Lemma (Seq.index (vals qc_seq) 9 == Seq.index Sc.qc 9) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 9;
  assert_norm (List.Tot.index qc_list 9 == S64.classify 0xffffuL);
  assert_norm (U64.v 0xffffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 9) % F.base);
  entry 9 0xffffuL

let entry_10 (_: unit) : Lemma (Seq.index (vals qc_seq) 10 == Seq.index Sc.qc 10) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 10;
  assert_norm (List.Tot.index qc_list 10 == S64.classify 0xffffuL);
  assert_norm (U64.v 0xffffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 10) % F.base);
  entry 10 0xffffuL

let entry_11 (_: unit) : Lemma (Seq.index (vals qc_seq) 11 == Seq.index Sc.qc 11) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 11;
  assert_norm (List.Tot.index qc_list 11 == S64.classify 0xffffuL);
  assert_norm (U64.v 0xffffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 11) % F.base);
  entry 11 0xffffuL

let entry_12 (_: unit) : Lemma (Seq.index (vals qc_seq) 12 == Seq.index Sc.qc 12) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 12;
  assert_norm (List.Tot.index qc_list 12 == S64.classify 0xffffuL);
  assert_norm (U64.v 0xffffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 12) % F.base);
  entry 12 0xffffuL

let entry_13 (_: unit) : Lemma (Seq.index (vals qc_seq) 13 == Seq.index Sc.qc 13) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 13;
  assert_norm (List.Tot.index qc_list 13 == S64.classify 0xffffuL);
  assert_norm (U64.v 0xffffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 13) % F.base);
  entry 13 0xffffuL

let entry_14 (_: unit) : Lemma (Seq.index (vals qc_seq) 14 == Seq.index Sc.qc 14) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 14;
  assert_norm (List.Tot.index qc_list 14 == S64.classify 0xffffuL);
  assert_norm (U64.v 0xffffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 14) % F.base);
  entry 14 0xffffuL

let entry_15 (_: unit) : Lemma (Seq.index (vals qc_seq) 15 == Seq.index Sc.qc 15) =
  qc_len ();
  Seq.lemma_seq_of_list_index qc_list 15;
  assert_norm (List.Tot.index qc_list 15 == S64.classify 0xefffuL);
  assert_norm (U64.v 0xefffuL == (pow2 256 - Sc.q) / pow2 (F.rad * 15) % F.base);
  entry 15 0xefffuL

(** [Seq.lemma_eq_intro] wants the entries for a symbolic index, and
    nothing tells Z3 that an index below sixteen is one of sixteen
    numbers.  So the case split is written out. *)
let qc_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals qc_seq) k == Seq.index Sc.qc k)
  = if k = 0 then entry_0 ()
    else if k = 1 then entry_1 ()
    else if k = 2 then entry_2 ()
    else if k = 3 then entry_3 ()
    else if k = 4 then entry_4 ()
    else if k = 5 then entry_5 ()
    else if k = 6 then entry_6 ()
    else if k = 7 then entry_7 ()
    else if k = 8 then entry_8 ()
    else if k = 9 then entry_9 ()
    else if k = 10 then entry_10 ()
    else if k = 11 then entry_11 ()
    else if k = 12 then entry_12 ()
    else if k = 13 then entry_13 ()
    else if k = 14 then entry_14 ()
    else entry_15 ()

let qc_seq_ok (_: unit) : Lemma (vals qc_seq == Sc.qc) =
  Classical.forall_intro qc_at;
  Seq.lemma_eq_intro (vals qc_seq) Sc.qc

#pop-options

let qc_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (qc_seq <: Seq.seq S64.t) })
  = G.mk_static_array qc_list

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The curve constants}

    Five field elements that are part of the definition of the curve: [d],
    [2d], a square root of [-1], and the two coordinates of the base point.
    Each is sixteen sixteen-bit limbs, and each is checked against the
    specification by the same three lines per limb -- the list lookup, the
    arithmetic, and {!limb_at}. *)

(** Limb [k] of a constant below [2^256], from the literal in the list. *)
let limb_at (l: list S64.t) (x: nat) (k: nat { k < F.nl }) (lit: U64.t)
  : Lemma (requires List.Tot.length l == 16 /\
                    List.Tot.index l k == S64.classify lit /\
                    U64.v lit == x / pow2 (F.rad * k) % F.base)
          (ensures Seq.index (vals (Seq.seq_of_list l)) k ==
                   Seq.index (Sc.limbs_of x) k)
  = Seq.lemma_seq_of_list_index l k;
    Seq.init_index F.nl (fun i -> x / pow2 (F.rad * i) % F.base)

(** A limb sequence that agrees with [limbs_of x] is a field element of
    value [x], as long as [x] is already reduced. *)
let const_ok (s: Seq.seq nat) (x: nat)
  : Lemma (requires x < C.prime /\ s == Sc.limbs_of x)
          (ensures F.felem s /\ F.fev s == x)
  = assert_norm (C.prime < pow2 256);
    Sc.limbs_of_ok x;
    assert_norm (F.base <= F.lim);
    Math.small_mod x C.prime


(** [Spec.Ed25519.d]. *)
let d_list : list S64.t = [
  S64.classify 0x78a3uL; S64.classify 0x1359uL; S64.classify 0x4dcauL; S64.classify 0x75ebuL;
  S64.classify 0xd8abuL; S64.classify 0x4141uL; S64.classify 0x0a4duL; S64.classify 0x0070uL;
  S64.classify 0xe898uL; S64.classify 0x7779uL; S64.classify 0x4079uL; S64.classify 0x8cc7uL;
  S64.classify 0xfe73uL; S64.classify 0x2b6fuL; S64.classify 0x6ceeuL; S64.classify 0x5203uL
]

[@@FStar.Custard.no_specialize]
let d_seq : Seq.lseq S64.t 16 =
  assert_norm (List.Tot.length d_list == 16);
  Seq.seq_of_list d_list

let d_at_0 (_: unit)
  : Lemma (Seq.index (vals d_seq) 0 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 0) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 0 == S64.classify 0x78a3uL);
  assert_norm (U64.v 0x78a3uL == Spec.Ed25519.d / pow2 (F.rad * 0) % F.base);
  limb_at d_list Spec.Ed25519.d 0 0x78a3uL

let d_at_1 (_: unit)
  : Lemma (Seq.index (vals d_seq) 1 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 1) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 1 == S64.classify 0x1359uL);
  assert_norm (U64.v 0x1359uL == Spec.Ed25519.d / pow2 (F.rad * 1) % F.base);
  limb_at d_list Spec.Ed25519.d 1 0x1359uL

let d_at_2 (_: unit)
  : Lemma (Seq.index (vals d_seq) 2 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 2) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 2 == S64.classify 0x4dcauL);
  assert_norm (U64.v 0x4dcauL == Spec.Ed25519.d / pow2 (F.rad * 2) % F.base);
  limb_at d_list Spec.Ed25519.d 2 0x4dcauL

let d_at_3 (_: unit)
  : Lemma (Seq.index (vals d_seq) 3 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 3) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 3 == S64.classify 0x75ebuL);
  assert_norm (U64.v 0x75ebuL == Spec.Ed25519.d / pow2 (F.rad * 3) % F.base);
  limb_at d_list Spec.Ed25519.d 3 0x75ebuL

let d_at_4 (_: unit)
  : Lemma (Seq.index (vals d_seq) 4 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 4) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 4 == S64.classify 0xd8abuL);
  assert_norm (U64.v 0xd8abuL == Spec.Ed25519.d / pow2 (F.rad * 4) % F.base);
  limb_at d_list Spec.Ed25519.d 4 0xd8abuL

let d_at_5 (_: unit)
  : Lemma (Seq.index (vals d_seq) 5 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 5) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 5 == S64.classify 0x4141uL);
  assert_norm (U64.v 0x4141uL == Spec.Ed25519.d / pow2 (F.rad * 5) % F.base);
  limb_at d_list Spec.Ed25519.d 5 0x4141uL

let d_at_6 (_: unit)
  : Lemma (Seq.index (vals d_seq) 6 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 6) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 6 == S64.classify 0x0a4duL);
  assert_norm (U64.v 0x0a4duL == Spec.Ed25519.d / pow2 (F.rad * 6) % F.base);
  limb_at d_list Spec.Ed25519.d 6 0x0a4duL

let d_at_7 (_: unit)
  : Lemma (Seq.index (vals d_seq) 7 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 7) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 7 == S64.classify 0x0070uL);
  assert_norm (U64.v 0x0070uL == Spec.Ed25519.d / pow2 (F.rad * 7) % F.base);
  limb_at d_list Spec.Ed25519.d 7 0x0070uL

let d_at_8 (_: unit)
  : Lemma (Seq.index (vals d_seq) 8 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 8) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 8 == S64.classify 0xe898uL);
  assert_norm (U64.v 0xe898uL == Spec.Ed25519.d / pow2 (F.rad * 8) % F.base);
  limb_at d_list Spec.Ed25519.d 8 0xe898uL

let d_at_9 (_: unit)
  : Lemma (Seq.index (vals d_seq) 9 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 9) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 9 == S64.classify 0x7779uL);
  assert_norm (U64.v 0x7779uL == Spec.Ed25519.d / pow2 (F.rad * 9) % F.base);
  limb_at d_list Spec.Ed25519.d 9 0x7779uL

let d_at_10 (_: unit)
  : Lemma (Seq.index (vals d_seq) 10 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 10) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 10 == S64.classify 0x4079uL);
  assert_norm (U64.v 0x4079uL == Spec.Ed25519.d / pow2 (F.rad * 10) % F.base);
  limb_at d_list Spec.Ed25519.d 10 0x4079uL

let d_at_11 (_: unit)
  : Lemma (Seq.index (vals d_seq) 11 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 11) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 11 == S64.classify 0x8cc7uL);
  assert_norm (U64.v 0x8cc7uL == Spec.Ed25519.d / pow2 (F.rad * 11) % F.base);
  limb_at d_list Spec.Ed25519.d 11 0x8cc7uL

let d_at_12 (_: unit)
  : Lemma (Seq.index (vals d_seq) 12 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 12) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 12 == S64.classify 0xfe73uL);
  assert_norm (U64.v 0xfe73uL == Spec.Ed25519.d / pow2 (F.rad * 12) % F.base);
  limb_at d_list Spec.Ed25519.d 12 0xfe73uL

let d_at_13 (_: unit)
  : Lemma (Seq.index (vals d_seq) 13 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 13) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 13 == S64.classify 0x2b6fuL);
  assert_norm (U64.v 0x2b6fuL == Spec.Ed25519.d / pow2 (F.rad * 13) % F.base);
  limb_at d_list Spec.Ed25519.d 13 0x2b6fuL

let d_at_14 (_: unit)
  : Lemma (Seq.index (vals d_seq) 14 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 14) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 14 == S64.classify 0x6ceeuL);
  assert_norm (U64.v 0x6ceeuL == Spec.Ed25519.d / pow2 (F.rad * 14) % F.base);
  limb_at d_list Spec.Ed25519.d 14 0x6ceeuL

let d_at_15 (_: unit)
  : Lemma (Seq.index (vals d_seq) 15 == Seq.index (Sc.limbs_of Spec.Ed25519.d) 15) =
  assert_norm (List.Tot.length d_list == 16);
  assert_norm (List.Tot.index d_list 15 == S64.classify 0x5203uL);
  assert_norm (U64.v 0x5203uL == Spec.Ed25519.d / pow2 (F.rad * 15) % F.base);
  limb_at d_list Spec.Ed25519.d 15 0x5203uL

let d_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals d_seq) k == Seq.index (Sc.limbs_of Spec.Ed25519.d) k)
  = if k = 0 then d_at_0 ()
    else if k = 1 then d_at_1 ()
    else if k = 2 then d_at_2 ()
    else if k = 3 then d_at_3 ()
    else if k = 4 then d_at_4 ()
    else if k = 5 then d_at_5 ()
    else if k = 6 then d_at_6 ()
    else if k = 7 then d_at_7 ()
    else if k = 8 then d_at_8 ()
    else if k = 9 then d_at_9 ()
    else if k = 10 then d_at_10 ()
    else if k = 11 then d_at_11 ()
    else if k = 12 then d_at_12 ()
    else if k = 13 then d_at_13 ()
    else if k = 14 then d_at_14 ()
    else d_at_15 ()

let d_ok (_: unit)
  : Lemma (F.felem (vals d_seq) /\ F.fev (vals d_seq) == Spec.Ed25519.d) =
  Classical.forall_intro d_at;
  Seq.lemma_eq_intro (vals d_seq) (Sc.limbs_of Spec.Ed25519.d);
  assert_norm (Spec.Ed25519.d < C.prime);
  const_ok (vals d_seq) Spec.Ed25519.d

let d_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (d_seq <: Seq.seq S64.t) })
  = G.mk_static_array d_list


(** [Spec.Ed25519.d2]. *)
let d2_list : list S64.t = [
  S64.classify 0xf159uL; S64.classify 0x26b2uL; S64.classify 0x9b94uL; S64.classify 0xebd6uL;
  S64.classify 0xb156uL; S64.classify 0x8283uL; S64.classify 0x149auL; S64.classify 0x00e0uL;
  S64.classify 0xd130uL; S64.classify 0xeef3uL; S64.classify 0x80f2uL; S64.classify 0x198euL;
  S64.classify 0xfce7uL; S64.classify 0x56dfuL; S64.classify 0xd9dcuL; S64.classify 0x2406uL
]

[@@FStar.Custard.no_specialize]
let d2_seq : Seq.lseq S64.t 16 =
  assert_norm (List.Tot.length d2_list == 16);
  Seq.seq_of_list d2_list

let d2_at_0 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 0 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 0) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 0 == S64.classify 0xf159uL);
  assert_norm (U64.v 0xf159uL == Spec.Ed25519.d2 / pow2 (F.rad * 0) % F.base);
  limb_at d2_list Spec.Ed25519.d2 0 0xf159uL

let d2_at_1 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 1 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 1) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 1 == S64.classify 0x26b2uL);
  assert_norm (U64.v 0x26b2uL == Spec.Ed25519.d2 / pow2 (F.rad * 1) % F.base);
  limb_at d2_list Spec.Ed25519.d2 1 0x26b2uL

let d2_at_2 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 2 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 2) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 2 == S64.classify 0x9b94uL);
  assert_norm (U64.v 0x9b94uL == Spec.Ed25519.d2 / pow2 (F.rad * 2) % F.base);
  limb_at d2_list Spec.Ed25519.d2 2 0x9b94uL

let d2_at_3 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 3 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 3) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 3 == S64.classify 0xebd6uL);
  assert_norm (U64.v 0xebd6uL == Spec.Ed25519.d2 / pow2 (F.rad * 3) % F.base);
  limb_at d2_list Spec.Ed25519.d2 3 0xebd6uL

let d2_at_4 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 4 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 4) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 4 == S64.classify 0xb156uL);
  assert_norm (U64.v 0xb156uL == Spec.Ed25519.d2 / pow2 (F.rad * 4) % F.base);
  limb_at d2_list Spec.Ed25519.d2 4 0xb156uL

let d2_at_5 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 5 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 5) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 5 == S64.classify 0x8283uL);
  assert_norm (U64.v 0x8283uL == Spec.Ed25519.d2 / pow2 (F.rad * 5) % F.base);
  limb_at d2_list Spec.Ed25519.d2 5 0x8283uL

let d2_at_6 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 6 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 6) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 6 == S64.classify 0x149auL);
  assert_norm (U64.v 0x149auL == Spec.Ed25519.d2 / pow2 (F.rad * 6) % F.base);
  limb_at d2_list Spec.Ed25519.d2 6 0x149auL

let d2_at_7 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 7 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 7) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 7 == S64.classify 0x00e0uL);
  assert_norm (U64.v 0x00e0uL == Spec.Ed25519.d2 / pow2 (F.rad * 7) % F.base);
  limb_at d2_list Spec.Ed25519.d2 7 0x00e0uL

let d2_at_8 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 8 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 8) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 8 == S64.classify 0xd130uL);
  assert_norm (U64.v 0xd130uL == Spec.Ed25519.d2 / pow2 (F.rad * 8) % F.base);
  limb_at d2_list Spec.Ed25519.d2 8 0xd130uL

let d2_at_9 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 9 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 9) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 9 == S64.classify 0xeef3uL);
  assert_norm (U64.v 0xeef3uL == Spec.Ed25519.d2 / pow2 (F.rad * 9) % F.base);
  limb_at d2_list Spec.Ed25519.d2 9 0xeef3uL

let d2_at_10 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 10 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 10) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 10 == S64.classify 0x80f2uL);
  assert_norm (U64.v 0x80f2uL == Spec.Ed25519.d2 / pow2 (F.rad * 10) % F.base);
  limb_at d2_list Spec.Ed25519.d2 10 0x80f2uL

let d2_at_11 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 11 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 11) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 11 == S64.classify 0x198euL);
  assert_norm (U64.v 0x198euL == Spec.Ed25519.d2 / pow2 (F.rad * 11) % F.base);
  limb_at d2_list Spec.Ed25519.d2 11 0x198euL

let d2_at_12 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 12 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 12) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 12 == S64.classify 0xfce7uL);
  assert_norm (U64.v 0xfce7uL == Spec.Ed25519.d2 / pow2 (F.rad * 12) % F.base);
  limb_at d2_list Spec.Ed25519.d2 12 0xfce7uL

let d2_at_13 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 13 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 13) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 13 == S64.classify 0x56dfuL);
  assert_norm (U64.v 0x56dfuL == Spec.Ed25519.d2 / pow2 (F.rad * 13) % F.base);
  limb_at d2_list Spec.Ed25519.d2 13 0x56dfuL

let d2_at_14 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 14 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 14) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 14 == S64.classify 0xd9dcuL);
  assert_norm (U64.v 0xd9dcuL == Spec.Ed25519.d2 / pow2 (F.rad * 14) % F.base);
  limb_at d2_list Spec.Ed25519.d2 14 0xd9dcuL

let d2_at_15 (_: unit)
  : Lemma (Seq.index (vals d2_seq) 15 == Seq.index (Sc.limbs_of Spec.Ed25519.d2) 15) =
  assert_norm (List.Tot.length d2_list == 16);
  assert_norm (List.Tot.index d2_list 15 == S64.classify 0x2406uL);
  assert_norm (U64.v 0x2406uL == Spec.Ed25519.d2 / pow2 (F.rad * 15) % F.base);
  limb_at d2_list Spec.Ed25519.d2 15 0x2406uL

let d2_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals d2_seq) k == Seq.index (Sc.limbs_of Spec.Ed25519.d2) k)
  = if k = 0 then d2_at_0 ()
    else if k = 1 then d2_at_1 ()
    else if k = 2 then d2_at_2 ()
    else if k = 3 then d2_at_3 ()
    else if k = 4 then d2_at_4 ()
    else if k = 5 then d2_at_5 ()
    else if k = 6 then d2_at_6 ()
    else if k = 7 then d2_at_7 ()
    else if k = 8 then d2_at_8 ()
    else if k = 9 then d2_at_9 ()
    else if k = 10 then d2_at_10 ()
    else if k = 11 then d2_at_11 ()
    else if k = 12 then d2_at_12 ()
    else if k = 13 then d2_at_13 ()
    else if k = 14 then d2_at_14 ()
    else d2_at_15 ()

let d2_ok (_: unit)
  : Lemma (F.felem (vals d2_seq) /\ F.fev (vals d2_seq) == Spec.Ed25519.d2) =
  Classical.forall_intro d2_at;
  Seq.lemma_eq_intro (vals d2_seq) (Sc.limbs_of Spec.Ed25519.d2);
  assert_norm (Spec.Ed25519.d2 < C.prime);
  const_ok (vals d2_seq) Spec.Ed25519.d2

let d2_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (d2_seq <: Seq.seq S64.t) })
  = G.mk_static_array d2_list


(** [Spec.Ed25519.sqrt_m1]. *)
let sqrtm1_list : list S64.t = [
  S64.classify 0xa0b0uL; S64.classify 0x4a0euL; S64.classify 0x1b27uL; S64.classify 0xc4eeuL;
  S64.classify 0xe478uL; S64.classify 0xad2fuL; S64.classify 0x1806uL; S64.classify 0x2f43uL;
  S64.classify 0xd7a7uL; S64.classify 0x3dfbuL; S64.classify 0x0099uL; S64.classify 0x2b4duL;
  S64.classify 0xdf0buL; S64.classify 0x4fc1uL; S64.classify 0x2480uL; S64.classify 0x2b83uL
]

[@@FStar.Custard.no_specialize]
let sqrtm1_seq : Seq.lseq S64.t 16 =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  Seq.seq_of_list sqrtm1_list

let sqrtm1_at_0 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 0 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 0) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 0 == S64.classify 0xa0b0uL);
  assert_norm (U64.v 0xa0b0uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 0) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 0 0xa0b0uL

let sqrtm1_at_1 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 1 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 1) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 1 == S64.classify 0x4a0euL);
  assert_norm (U64.v 0x4a0euL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 1) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 1 0x4a0euL

let sqrtm1_at_2 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 2 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 2) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 2 == S64.classify 0x1b27uL);
  assert_norm (U64.v 0x1b27uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 2) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 2 0x1b27uL

let sqrtm1_at_3 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 3 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 3) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 3 == S64.classify 0xc4eeuL);
  assert_norm (U64.v 0xc4eeuL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 3) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 3 0xc4eeuL

let sqrtm1_at_4 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 4 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 4) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 4 == S64.classify 0xe478uL);
  assert_norm (U64.v 0xe478uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 4) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 4 0xe478uL

let sqrtm1_at_5 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 5 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 5) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 5 == S64.classify 0xad2fuL);
  assert_norm (U64.v 0xad2fuL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 5) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 5 0xad2fuL

let sqrtm1_at_6 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 6 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 6) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 6 == S64.classify 0x1806uL);
  assert_norm (U64.v 0x1806uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 6) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 6 0x1806uL

let sqrtm1_at_7 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 7 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 7) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 7 == S64.classify 0x2f43uL);
  assert_norm (U64.v 0x2f43uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 7) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 7 0x2f43uL

let sqrtm1_at_8 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 8 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 8) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 8 == S64.classify 0xd7a7uL);
  assert_norm (U64.v 0xd7a7uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 8) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 8 0xd7a7uL

let sqrtm1_at_9 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 9 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 9) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 9 == S64.classify 0x3dfbuL);
  assert_norm (U64.v 0x3dfbuL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 9) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 9 0x3dfbuL

let sqrtm1_at_10 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 10 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 10) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 10 == S64.classify 0x0099uL);
  assert_norm (U64.v 0x0099uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 10) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 10 0x0099uL

let sqrtm1_at_11 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 11 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 11) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 11 == S64.classify 0x2b4duL);
  assert_norm (U64.v 0x2b4duL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 11) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 11 0x2b4duL

let sqrtm1_at_12 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 12 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 12) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 12 == S64.classify 0xdf0buL);
  assert_norm (U64.v 0xdf0buL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 12) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 12 0xdf0buL

let sqrtm1_at_13 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 13 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 13) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 13 == S64.classify 0x4fc1uL);
  assert_norm (U64.v 0x4fc1uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 13) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 13 0x4fc1uL

let sqrtm1_at_14 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 14 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 14) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 14 == S64.classify 0x2480uL);
  assert_norm (U64.v 0x2480uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 14) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 14 0x2480uL

let sqrtm1_at_15 (_: unit)
  : Lemma (Seq.index (vals sqrtm1_seq) 15 == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) 15) =
  assert_norm (List.Tot.length sqrtm1_list == 16);
  assert_norm (List.Tot.index sqrtm1_list 15 == S64.classify 0x2b83uL);
  assert_norm (U64.v 0x2b83uL == Spec.Ed25519.sqrt_m1 / pow2 (F.rad * 15) % F.base);
  limb_at sqrtm1_list Spec.Ed25519.sqrt_m1 15 0x2b83uL

let sqrtm1_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals sqrtm1_seq) k == Seq.index (Sc.limbs_of Spec.Ed25519.sqrt_m1) k)
  = if k = 0 then sqrtm1_at_0 ()
    else if k = 1 then sqrtm1_at_1 ()
    else if k = 2 then sqrtm1_at_2 ()
    else if k = 3 then sqrtm1_at_3 ()
    else if k = 4 then sqrtm1_at_4 ()
    else if k = 5 then sqrtm1_at_5 ()
    else if k = 6 then sqrtm1_at_6 ()
    else if k = 7 then sqrtm1_at_7 ()
    else if k = 8 then sqrtm1_at_8 ()
    else if k = 9 then sqrtm1_at_9 ()
    else if k = 10 then sqrtm1_at_10 ()
    else if k = 11 then sqrtm1_at_11 ()
    else if k = 12 then sqrtm1_at_12 ()
    else if k = 13 then sqrtm1_at_13 ()
    else if k = 14 then sqrtm1_at_14 ()
    else sqrtm1_at_15 ()

let sqrtm1_ok (_: unit)
  : Lemma (F.felem (vals sqrtm1_seq) /\ F.fev (vals sqrtm1_seq) == Spec.Ed25519.sqrt_m1) =
  Classical.forall_intro sqrtm1_at;
  Seq.lemma_eq_intro (vals sqrtm1_seq) (Sc.limbs_of Spec.Ed25519.sqrt_m1);
  assert_norm (Spec.Ed25519.sqrt_m1 < C.prime);
  const_ok (vals sqrtm1_seq) Spec.Ed25519.sqrt_m1

let sqrtm1_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (sqrtm1_seq <: Seq.seq S64.t) })
  = G.mk_static_array sqrtm1_list


(** [Spec.Ed25519.g_x]. *)
let gx_list : list S64.t = [
  S64.classify 0xd51auL; S64.classify 0x8f25uL; S64.classify 0x2d60uL; S64.classify 0xc956uL;
  S64.classify 0xa7b2uL; S64.classify 0x9525uL; S64.classify 0xc760uL; S64.classify 0x692cuL;
  S64.classify 0xdc5cuL; S64.classify 0xfdd6uL; S64.classify 0xe231uL; S64.classify 0xc0a4uL;
  S64.classify 0x53feuL; S64.classify 0xcd6euL; S64.classify 0x36d3uL; S64.classify 0x2169uL
]

[@@FStar.Custard.no_specialize]
let gx_seq : Seq.lseq S64.t 16 =
  assert_norm (List.Tot.length gx_list == 16);
  Seq.seq_of_list gx_list

let gx_at_0 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 0 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 0) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 0 == S64.classify 0xd51auL);
  assert_norm (U64.v 0xd51auL == Spec.Ed25519.g_x / pow2 (F.rad * 0) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 0 0xd51auL

let gx_at_1 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 1 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 1) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 1 == S64.classify 0x8f25uL);
  assert_norm (U64.v 0x8f25uL == Spec.Ed25519.g_x / pow2 (F.rad * 1) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 1 0x8f25uL

let gx_at_2 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 2 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 2) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 2 == S64.classify 0x2d60uL);
  assert_norm (U64.v 0x2d60uL == Spec.Ed25519.g_x / pow2 (F.rad * 2) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 2 0x2d60uL

let gx_at_3 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 3 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 3) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 3 == S64.classify 0xc956uL);
  assert_norm (U64.v 0xc956uL == Spec.Ed25519.g_x / pow2 (F.rad * 3) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 3 0xc956uL

let gx_at_4 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 4 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 4) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 4 == S64.classify 0xa7b2uL);
  assert_norm (U64.v 0xa7b2uL == Spec.Ed25519.g_x / pow2 (F.rad * 4) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 4 0xa7b2uL

let gx_at_5 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 5 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 5) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 5 == S64.classify 0x9525uL);
  assert_norm (U64.v 0x9525uL == Spec.Ed25519.g_x / pow2 (F.rad * 5) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 5 0x9525uL

let gx_at_6 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 6 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 6) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 6 == S64.classify 0xc760uL);
  assert_norm (U64.v 0xc760uL == Spec.Ed25519.g_x / pow2 (F.rad * 6) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 6 0xc760uL

let gx_at_7 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 7 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 7) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 7 == S64.classify 0x692cuL);
  assert_norm (U64.v 0x692cuL == Spec.Ed25519.g_x / pow2 (F.rad * 7) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 7 0x692cuL

let gx_at_8 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 8 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 8) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 8 == S64.classify 0xdc5cuL);
  assert_norm (U64.v 0xdc5cuL == Spec.Ed25519.g_x / pow2 (F.rad * 8) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 8 0xdc5cuL

let gx_at_9 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 9 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 9) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 9 == S64.classify 0xfdd6uL);
  assert_norm (U64.v 0xfdd6uL == Spec.Ed25519.g_x / pow2 (F.rad * 9) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 9 0xfdd6uL

let gx_at_10 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 10 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 10) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 10 == S64.classify 0xe231uL);
  assert_norm (U64.v 0xe231uL == Spec.Ed25519.g_x / pow2 (F.rad * 10) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 10 0xe231uL

let gx_at_11 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 11 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 11) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 11 == S64.classify 0xc0a4uL);
  assert_norm (U64.v 0xc0a4uL == Spec.Ed25519.g_x / pow2 (F.rad * 11) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 11 0xc0a4uL

let gx_at_12 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 12 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 12) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 12 == S64.classify 0x53feuL);
  assert_norm (U64.v 0x53feuL == Spec.Ed25519.g_x / pow2 (F.rad * 12) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 12 0x53feuL

let gx_at_13 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 13 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 13) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 13 == S64.classify 0xcd6euL);
  assert_norm (U64.v 0xcd6euL == Spec.Ed25519.g_x / pow2 (F.rad * 13) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 13 0xcd6euL

let gx_at_14 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 14 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 14) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 14 == S64.classify 0x36d3uL);
  assert_norm (U64.v 0x36d3uL == Spec.Ed25519.g_x / pow2 (F.rad * 14) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 14 0x36d3uL

let gx_at_15 (_: unit)
  : Lemma (Seq.index (vals gx_seq) 15 == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) 15) =
  assert_norm (List.Tot.length gx_list == 16);
  assert_norm (List.Tot.index gx_list 15 == S64.classify 0x2169uL);
  assert_norm (U64.v 0x2169uL == Spec.Ed25519.g_x / pow2 (F.rad * 15) % F.base);
  limb_at gx_list Spec.Ed25519.g_x 15 0x2169uL

let gx_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals gx_seq) k == Seq.index (Sc.limbs_of Spec.Ed25519.g_x) k)
  = if k = 0 then gx_at_0 ()
    else if k = 1 then gx_at_1 ()
    else if k = 2 then gx_at_2 ()
    else if k = 3 then gx_at_3 ()
    else if k = 4 then gx_at_4 ()
    else if k = 5 then gx_at_5 ()
    else if k = 6 then gx_at_6 ()
    else if k = 7 then gx_at_7 ()
    else if k = 8 then gx_at_8 ()
    else if k = 9 then gx_at_9 ()
    else if k = 10 then gx_at_10 ()
    else if k = 11 then gx_at_11 ()
    else if k = 12 then gx_at_12 ()
    else if k = 13 then gx_at_13 ()
    else if k = 14 then gx_at_14 ()
    else gx_at_15 ()

let gx_ok (_: unit)
  : Lemma (F.felem (vals gx_seq) /\ F.fev (vals gx_seq) == Spec.Ed25519.g_x) =
  Classical.forall_intro gx_at;
  Seq.lemma_eq_intro (vals gx_seq) (Sc.limbs_of Spec.Ed25519.g_x);
  assert_norm (Spec.Ed25519.g_x < C.prime);
  const_ok (vals gx_seq) Spec.Ed25519.g_x

let gx_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (gx_seq <: Seq.seq S64.t) })
  = G.mk_static_array gx_list


(** [Spec.Ed25519.g_y]. *)
let gy_list : list S64.t = [
  S64.classify 0x6658uL; S64.classify 0x6666uL; S64.classify 0x6666uL; S64.classify 0x6666uL;
  S64.classify 0x6666uL; S64.classify 0x6666uL; S64.classify 0x6666uL; S64.classify 0x6666uL;
  S64.classify 0x6666uL; S64.classify 0x6666uL; S64.classify 0x6666uL; S64.classify 0x6666uL;
  S64.classify 0x6666uL; S64.classify 0x6666uL; S64.classify 0x6666uL; S64.classify 0x6666uL
]

[@@FStar.Custard.no_specialize]
let gy_seq : Seq.lseq S64.t 16 =
  assert_norm (List.Tot.length gy_list == 16);
  Seq.seq_of_list gy_list

let gy_at_0 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 0 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 0) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 0 == S64.classify 0x6658uL);
  assert_norm (U64.v 0x6658uL == Spec.Ed25519.g_y / pow2 (F.rad * 0) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 0 0x6658uL

let gy_at_1 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 1 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 1) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 1 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 1) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 1 0x6666uL

let gy_at_2 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 2 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 2) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 2 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 2) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 2 0x6666uL

let gy_at_3 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 3 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 3) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 3 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 3) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 3 0x6666uL

let gy_at_4 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 4 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 4) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 4 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 4) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 4 0x6666uL

let gy_at_5 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 5 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 5) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 5 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 5) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 5 0x6666uL

let gy_at_6 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 6 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 6) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 6 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 6) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 6 0x6666uL

let gy_at_7 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 7 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 7) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 7 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 7) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 7 0x6666uL

let gy_at_8 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 8 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 8) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 8 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 8) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 8 0x6666uL

let gy_at_9 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 9 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 9) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 9 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 9) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 9 0x6666uL

let gy_at_10 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 10 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 10) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 10 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 10) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 10 0x6666uL

let gy_at_11 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 11 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 11) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 11 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 11) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 11 0x6666uL

let gy_at_12 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 12 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 12) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 12 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 12) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 12 0x6666uL

let gy_at_13 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 13 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 13) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 13 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 13) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 13 0x6666uL

let gy_at_14 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 14 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 14) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 14 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 14) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 14 0x6666uL

let gy_at_15 (_: unit)
  : Lemma (Seq.index (vals gy_seq) 15 == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) 15) =
  assert_norm (List.Tot.length gy_list == 16);
  assert_norm (List.Tot.index gy_list 15 == S64.classify 0x6666uL);
  assert_norm (U64.v 0x6666uL == Spec.Ed25519.g_y / pow2 (F.rad * 15) % F.base);
  limb_at gy_list Spec.Ed25519.g_y 15 0x6666uL

let gy_at (k: nat { k < F.nl })
  : Lemma (Seq.index (vals gy_seq) k == Seq.index (Sc.limbs_of Spec.Ed25519.g_y) k)
  = if k = 0 then gy_at_0 ()
    else if k = 1 then gy_at_1 ()
    else if k = 2 then gy_at_2 ()
    else if k = 3 then gy_at_3 ()
    else if k = 4 then gy_at_4 ()
    else if k = 5 then gy_at_5 ()
    else if k = 6 then gy_at_6 ()
    else if k = 7 then gy_at_7 ()
    else if k = 8 then gy_at_8 ()
    else if k = 9 then gy_at_9 ()
    else if k = 10 then gy_at_10 ()
    else if k = 11 then gy_at_11 ()
    else if k = 12 then gy_at_12 ()
    else if k = 13 then gy_at_13 ()
    else if k = 14 then gy_at_14 ()
    else gy_at_15 ()

let gy_ok (_: unit)
  : Lemma (F.felem (vals gy_seq) /\ F.fev (vals gy_seq) == Spec.Ed25519.g_y) =
  Classical.forall_intro gy_at;
  Seq.lemma_eq_intro (vals gy_seq) (Sc.limbs_of Spec.Ed25519.g_y);
  assert_norm (Spec.Ed25519.g_y < C.prime);
  const_ok (vals gy_seq) Spec.Ed25519.g_y

let gy_arr : (a: G.static_array S64.t
                { G.static_array_elems a == (gy_seq <: Seq.seq S64.t) })
  = G.mk_static_array gy_list


#pop-options
