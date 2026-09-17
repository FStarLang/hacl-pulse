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

(** The Keccak round constants and rotation offsets (FIPS 202, tables in
    sections 3.2.2 and 3.2.5).

    The rotation offsets are public -- they are shift amounts, and the number
    of bits a lane is rotated by does not depend on any secret -- so [rotc] is
    an ordinary function returning a [nat] and carries its own bound.  The
    round constants become secret values because they are exclusive-ored into
    the state. *)
module Spec.SHA3.Constants

module S64 = Hacl.Secret.UInt64
module U64 = FStar.UInt64
module Seq = FStar.Seq
module U32 = FStar.UInt32

(** The twenty-four iota constants, RC[0] through RC[23], as a list: this is
    the spine that reaches the C array initializer in [Hacl.Hash.SHA3]. *)
let rc_list : list S64.t = [
  S64.classify 0x0000000000000001uL; S64.classify 0x0000000000008082uL; S64.classify 0x800000000000808auL;
  S64.classify 0x8000000080008000uL; S64.classify 0x000000000000808buL; S64.classify 0x0000000080000001uL;
  S64.classify 0x8000000080008081uL; S64.classify 0x8000000000008009uL; S64.classify 0x000000000000008auL;
  S64.classify 0x0000000000000088uL; S64.classify 0x0000000080008009uL; S64.classify 0x000000008000000auL;
  S64.classify 0x000000008000808buL; S64.classify 0x800000000000008buL; S64.classify 0x8000000000008089uL;
  S64.classify 0x8000000000008003uL; S64.classify 0x8000000000008002uL; S64.classify 0x8000000000000080uL;
  S64.classify 0x000000000000800auL; S64.classify 0x800000008000000auL; S64.classify 0x8000000080008081uL;
  S64.classify 0x8000000000008080uL; S64.classify 0x0000000080000001uL; S64.classify 0x8000000080008008uL
]

(** The same table as a sequence.  [Seq.seq_of_list] of the list above is
    definitionally what a [Pulse.Lib.GlobalArray] holding it contains, so the
    implementation's table and this one need no lemma to relate. *)
[@@FStar.Custard.no_specialize]
let rc : Seq.lseq S64.t 24 =
  assert_norm (List.Tot.length rc_list == 24);
  Seq.seq_of_list rc_list

(** The rho offsets, in the [x + 5 * y] order the state is flattened in.  Note
    [rotc 0] is zero, which is why the specification rotates through
    [Spec.SHA3.rotl] rather than through [Hacl.Secret.UInt64.rotate_left]. *)
let rotc (i: nat { i < 25 }) : n: nat { n < 64 } =
  match i with
  |  0 ->  0
  |  1 ->  1
  |  2 -> 62
  |  3 -> 28
  |  4 -> 27
  |  5 -> 36
  |  6 -> 44
  |  7 ->  6
  |  8 -> 55
  |  9 -> 20
  | 10 ->  3
  | 11 -> 10
  | 12 -> 43
  | 13 -> 25
  | 14 -> 39
  | 15 -> 41
  | 16 -> 45
  | 17 -> 15
  | 18 -> 21
  | 19 ->  8
  | 20 -> 18
  | 21 ->  2
  | 22 -> 61
  | 23 -> 56
  | _  -> 14

(** Twenty-five concrete offsets imply the pointwise characterisation.  This
    is proved here, where nothing else is in scope; asking a Pulse function's
    verification condition to case-split on [rotc] does not go through. *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let rotc_ok (v: Seq.seq U32.t)
  : Lemma (requires Seq.length v == 25 /\
                    Seq.index v  0 ==  0ul /\
                    Seq.index v  1 ==  1ul /\
                    Seq.index v  2 == 62ul /\
                    Seq.index v  3 == 28ul /\
                    Seq.index v  4 == 27ul /\
                    Seq.index v  5 == 36ul /\
                    Seq.index v  6 == 44ul /\
                    Seq.index v  7 ==  6ul /\
                    Seq.index v  8 == 55ul /\
                    Seq.index v  9 == 20ul /\
                    Seq.index v 10 ==  3ul /\
                    Seq.index v 11 == 10ul /\
                    Seq.index v 12 == 43ul /\
                    Seq.index v 13 == 25ul /\
                    Seq.index v 14 == 39ul /\
                    Seq.index v 15 == 41ul /\
                    Seq.index v 16 == 45ul /\
                    Seq.index v 17 == 15ul /\
                    Seq.index v 18 == 21ul /\
                    Seq.index v 19 ==  8ul /\
                    Seq.index v 20 == 18ul /\
                    Seq.index v 21 ==  2ul /\
                    Seq.index v 22 == 61ul /\
                    Seq.index v 23 == 56ul /\
                    Seq.index v 24 == 14ul)
          (ensures forall (j: nat). j < 25 ==> U32.v (Seq.index v j) == rotc j)
  = ()
#pop-options

(** The same twenty-five offsets as ground equalities.

    [rotc] is a [match], so any verification condition that mentions it at a
    symbolic index has to case-split twenty-five ways, and a Pulse context is
    the worst possible place for that.  Proved here in isolation and then
    called once per unrolled step, this puts all twenty-five facts into the
    solver's context as ground terms, which costs nothing. *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let rotc_lit (_: unit)
  : Lemma (
                   rotc  0 ==  0 /\
                   rotc  1 ==  1 /\
                   rotc  2 == 62 /\
                   rotc  3 == 28 /\
                   rotc  4 == 27 /\
                   rotc  5 == 36 /\
                   rotc  6 == 44 /\
                   rotc  7 ==  6 /\
                   rotc  8 == 55 /\
                   rotc  9 == 20 /\
                   rotc 10 ==  3 /\
                   rotc 11 == 10 /\
                   rotc 12 == 43 /\
                   rotc 13 == 25 /\
                   rotc 14 == 39 /\
                   rotc 15 == 41 /\
                   rotc 16 == 45 /\
                   rotc 17 == 15 /\
                   rotc 18 == 21 /\
                   rotc 19 ==  8 /\
                   rotc 20 == 18 /\
                   rotc 21 ==  2 /\
                   rotc 22 == 61 /\
                   rotc 23 == 56 /\
                   rotc 24 == 14)
  = ()
#pop-options

(** The same twenty-five offsets as a list, for the compile-time table.

    Written out a second time rather than derived from [rotc], because a
    [static_array]'s contents have to reduce to a literal spine and
    [Seq.init 25 rotc] is a call, not a list.  {!rotc_seq_ok} is what makes
    the duplication safe: it is a machine-checked cross-check of one table
    against the other, and it is the reason [rotc] can stay the readable
    [match] that the specification wants. *)
let rotc_list : list U32.t = [
   0ul;  1ul; 62ul; 28ul; 27ul;
  36ul; 44ul;  6ul; 55ul; 20ul;
   3ul; 10ul; 43ul; 25ul; 39ul;
  41ul; 45ul; 15ul; 21ul;  8ul;
  18ul;  2ul; 61ul; 56ul; 14ul
]

let rotc_seq : Seq.lseq U32.t 25 =
  assert_norm (List.Tot.length rotc_list == 25);
  Seq.seq_of_list rotc_list

(** The two tables agree.

    [Seq.index] does not reduce through [Seq.seq_of_list] -- a sequence is
    abstract, so the normalizer cannot look inside one -- which is why this
    goes through [Seq.lemma_seq_of_list_index] first and only then normalizes.
    [List.Tot.index] on a literal spine does reduce.  {!rotc_ok} turns the
    twenty-five equalities into the pointwise statement the sponge uses; it
    lives next to [rotc] because a twenty-five-way case split is not something
    to ask of a Pulse verification condition. *)
let rotc_seq_ok (_: unit)
  : Lemma (forall (j: nat). j < 25 ==> U32.v (Seq.index rotc_seq j) == rotc j)
  = let ix (i: nat { i < 25 })
      : Lemma (Seq.index rotc_seq i == List.Tot.index rotc_list i)
      = assert_norm (List.Tot.length rotc_list == 25);
        Seq.lemma_seq_of_list_index rotc_list i in
    ix  0;
    ix  1;
    ix  2;
    ix  3;
    ix  4;
    ix  5;
    ix  6;
    ix  7;
    ix  8;
    ix  9;
    ix 10;
    ix 11;
    ix 12;
    ix 13;
    ix 14;
    ix 15;
    ix 16;
    ix 17;
    ix 18;
    ix 19;
    ix 20;
    ix 21;
    ix 22;
    ix 23;
    ix 24;
    assert_norm (List.Tot.index rotc_list  0 ==  0ul /\
                 List.Tot.index rotc_list  1 ==  1ul /\
                 List.Tot.index rotc_list  2 == 62ul /\
                 List.Tot.index rotc_list  3 == 28ul /\
                 List.Tot.index rotc_list  4 == 27ul /\
                 List.Tot.index rotc_list  5 == 36ul /\
                 List.Tot.index rotc_list  6 == 44ul /\
                 List.Tot.index rotc_list  7 ==  6ul /\
                 List.Tot.index rotc_list  8 == 55ul /\
                 List.Tot.index rotc_list  9 == 20ul /\
                 List.Tot.index rotc_list 10 ==  3ul /\
                 List.Tot.index rotc_list 11 == 10ul /\
                 List.Tot.index rotc_list 12 == 43ul /\
                 List.Tot.index rotc_list 13 == 25ul /\
                 List.Tot.index rotc_list 14 == 39ul /\
                 List.Tot.index rotc_list 15 == 41ul /\
                 List.Tot.index rotc_list 16 == 45ul /\
                 List.Tot.index rotc_list 17 == 15ul /\
                 List.Tot.index rotc_list 18 == 21ul /\
                 List.Tot.index rotc_list 19 ==  8ul /\
                 List.Tot.index rotc_list 20 == 18ul /\
                 List.Tot.index rotc_list 21 ==  2ul /\
                 List.Tot.index rotc_list 22 == 61ul /\
                 List.Tot.index rotc_list 23 == 56ul /\
                 List.Tot.index rotc_list 24 == 14ul);
    rotc_ok rotc_seq
