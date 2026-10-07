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

    {!Hacl.K256.PointWin.build_table} fills sixteen entries by fifteen
    point additions, and the fixed-base window in {!Hacl.K256.PointMulG}
    needs four such tables, so sixty of the hundred and eighty-eight point
    operations a signature performs are spent building tables that are the
    same on every call.  They can be compiled in instead, which is what
    {!Hacl.K256.Win0} and its three siblings do, and this is the bridge:
    one lemma that turns three lists of eighty limbs and a point into one
    [ent], and one that collects sixteen [ent]s into a [tok].

    The point of putting it here rather than in {!Hacl.K256.PointWin} is
    the usual one.  [ent] and [tok] are stated over [rep], which is
    opaque, and this file is the only place that has to open it; the four
    table files then mention neither the curve nor the field, only [leval]
    on a list of literals, which the normaliser settles without the solver
    seeing a single two-hundred-and-fifty-six-bit number.

    This is {!Hacl.Ed25519.WinTable} on a different curve; the missing
    fourth coordinate is the only difference. *)
module Hacl.K256.WinTable

open Spec.Bignum52
open Spec.K256.Freeze
open Hacl.Impl.Limb4
open Hacl.Impl.Lit52
open Hacl.K256.Point
open Hacl.K256.PointWin

module Seq = FStar.Seq
module L = FStar.List.Tot
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module GR = Spec.K256.Group
module SM = Spec.K256.Smul

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

(** The three coordinates, named, so that a table file can state what its
    limbs add up to without writing the numbers down a second time. *)
let qx (q: K.proj_point) : K.felem = let (a, _, _) = q in a
let qy (q: K.proj_point) : K.felem = let (_, b, _) = q in b
let qz (q: K.proj_point) : K.felem = let (_, _, c) = q in c

let pt_eta (q: K.proj_point) : Lemma (q == (qx q, qy q, qz q)) = ()

(** One entry of a constant table.

    The hypotheses are three [leval]s -- arithmetic on a literal list,
    which the normaliser settles without the solver ever seeing a
    two-hundred-and-fifty-six-bit number -- and the two facts the chain in
    [Spec.K256.Win{i}] already proved about the point. *)
let ent_lit (lx ly lz: list S64.t) (d: nat)
            (p: K.proj_point) (n: nat) (q: K.proj_point)
  : Lemma (requires
             L.length lx == 80 /\ L.length ly == 80 /\ L.length lz == 80 /\
             d < 16 /\
             L.length (chunk lx d) == nl /\ lbnd (chunk lx d) /\
             leval (chunk lx d) == qx q /\
             L.length (chunk ly d) == nl /\ lbnd (chunk ly d) /\
             leval (chunk ly d) == qy q /\
             L.length (chunk lz d) == nl /\ lbnd (chunk lz d) /\
             leval (chunk lz d) == qz q /\
             GR.on_curve q /\ GR.peq q (SM.smul (d * n) p))
          (ensures ent (Seq.seq_of_list lx) (Seq.seq_of_list ly)
                       (Seq.seq_of_list lz) p n d)
  = entry_felem lx d (qx q);
    entry_felem ly d (qy q);
    entry_felem lz d (qz q);
    let vx : Seq.seq S64.t = Seq.seq_of_list lx in
    let vy : Seq.seq S64.t = Seq.seq_of_list ly in
    let vz : Seq.seq S64.t = Seq.seq_of_list lz in
    entry_fits d;
    entry_def vx d; entry_def vy d; entry_def vz d;
    pt_eta q;
    assert (pt_ok (entry vx d) (entry vy d) (entry vz d));
    assert (pt (entry vx d) (entry vy d) (entry vz d) == q);
    reveal_opaque (`%rep) rep;
    ent_intro vx vy vz (entry vx d) (entry vy d) (entry vz d) p n d

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(** Sixteen cases, named in a context that holds nothing else: with the
    sixteen [ent]s in scope the same arithmetic does not come back. *)
let lt16 (d: nat)
  : Lemma (requires d < 16)
          (ensures d == 0 \/ d == 1 \/ d == 2 \/ d == 3 \/
                   d == 4 \/ d == 5 \/ d == 6 \/ d == 7 \/
                   d == 8 \/ d == 9 \/ d == 10 \/ d == 11 \/
                   d == 12 \/ d == 13 \/ d == 14 \/ d == 15) = ()

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 400"

(** Sixteen entries make a table. *)
let tok_all (tx ty tz: Seq.seq S64.t) (p: K.proj_point) (n: nat)
  : Lemma (requires
             ent tx ty tz p n 0 /\ ent tx ty tz p n 1 /\
             ent tx ty tz p n 2 /\ ent tx ty tz p n 3 /\
             ent tx ty tz p n 4 /\ ent tx ty tz p n 5 /\
             ent tx ty tz p n 6 /\ ent tx ty tz p n 7 /\
             ent tx ty tz p n 8 /\ ent tx ty tz p n 9 /\
             ent tx ty tz p n 10 /\ ent tx ty tz p n 11 /\
             ent tx ty tz p n 12 /\ ent tx ty tz p n 13 /\
             ent tx ty tz p n 14 /\ ent tx ty tz p n 15)
          (ensures tok tx ty tz p n 16)
  = introduce forall (d: nat). d < 16 ==> ent tx ty tz p n d
    with introduce _ ==> _
    with lt16 d

#pop-options
