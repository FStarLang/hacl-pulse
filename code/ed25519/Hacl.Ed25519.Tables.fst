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
