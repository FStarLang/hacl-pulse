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

    {!Hacl.Ed25519.PointWin.build_table} fills sixteen entries by fifteen
    point additions, and the fixed-base window in
    {!Hacl.Ed25519.PointMulG} needs four such tables, so sixty of the
    hundred and ninety point operations a key generation performs are
    spent building tables that are the same on every call.  They can be
    compiled in instead, which is what {!Hacl.Ed25519.Win0} and its three
    siblings do, and this is the bridge: one lemma that turns four lists
    of eighty limbs and a point into one [ent], and one that collects
    sixteen [ent]s into a [tok].

    The point of putting it here rather than in
    {!Hacl.Ed25519.PointWin} is the usual one.  [ent] and [tok] are
    stated over [rep], which is opaque, and this file is the only place
    that has to open it; the four table files then mention neither the
    curve nor the field, only [leval] on a list of literals, which the
    normaliser settles without the solver seeing a single
    two-hundred-and-fifty-five-bit number. *)
module Hacl.Ed25519.WinTable

open Hacl.Impl.Limb
open Hacl.Impl.Lit51
open Hacl.Ed25519.Point
open Hacl.Ed25519.PointWin

module Seq = FStar.Seq
module L = FStar.List.Tot
module S64 = Hacl.Secret.UInt64
module F = Spec.Curve25519.Field
module C = Spec.Curve25519
module E = Spec.Ed25519
module GR = Spec.Ed25519.Group
module SM = Spec.Ed25519.Smul

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

(** The four coordinates, named, so that a table file can state what its
    limbs add up to without writing the numbers down a second time. *)
let px (q: E.ext_point) : C.elem = let (a, _, _, _) = q in a
let py (q: E.ext_point) : C.elem = let (_, b, _, _) = q in b
let pz (q: E.ext_point) : C.elem = let (_, _, c, _) = q in c
let pw (q: E.ext_point) : C.elem = let (_, _, _, e) = q in e

let pt_eta (q: E.ext_point) : Lemma (q == (px q, py q, pz q, pw q)) = ()

(** One entry of a constant table.

    The hypotheses are four [leval]s -- arithmetic on a literal list,
    which the normaliser settles without the solver ever seeing a
    two-hundred-and-fifty-five-bit number -- and the two facts the chain
    in [Spec.Ed25519.Win{i}] already proved about the point. *)
let ent_lit (lx ly lz lt: list S64.t) (d: nat)
            (p: E.ext_point) (n: nat) (q: E.ext_point)
  : Lemma (requires
             L.length lx == 80 /\ L.length ly == 80 /\
             L.length lz == 80 /\ L.length lt == 80 /\ d < 16 /\
             L.length (chunk lx d) == F.nl /\ lbnd (chunk lx d) /\
             leval (chunk lx d) == px q /\
             L.length (chunk ly d) == F.nl /\ lbnd (chunk ly d) /\
             leval (chunk ly d) == py q /\
             L.length (chunk lz d) == F.nl /\ lbnd (chunk lz d) /\
             leval (chunk lz d) == pz q /\
             L.length (chunk lt d) == F.nl /\ lbnd (chunk lt d) /\
             leval (chunk lt d) == pw q /\
             GR.on_curve q /\ E.point_equal q (SM.smul (d * n) p))
          (ensures ent (Seq.seq_of_list lx) (Seq.seq_of_list ly)
                       (Seq.seq_of_list lz) (Seq.seq_of_list lt) p n d)
  = entry_felem lx d (px q);
    entry_felem ly d (py q);
    entry_felem lz d (pz q);
    entry_felem lt d (pw q);
    let vx : Seq.seq S64.t = Seq.seq_of_list lx in
    let vy : Seq.seq S64.t = Seq.seq_of_list ly in
    let vz : Seq.seq S64.t = Seq.seq_of_list lz in
    let vt : Seq.seq S64.t = Seq.seq_of_list lt in
    entry_fits d;
    entry_def vx d; entry_def vy d; entry_def vz d; entry_def vt d;
    pt_eta q;
    assert (pt_ok (entry vx d) (entry vy d) (entry vz d) (entry vt d));
    assert (pt (entry vx d) (entry vy d) (entry vz d) (entry vt d) == q);
    pok_intro (entry vx d) (entry vy d) (entry vz d) (entry vt d);
    reveal_opaque (`%rep) rep;
    ent_intro vx vy vz vt (entry vx d) (entry vy d) (entry vz d) (entry vt d)
              p n d

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"

(** Sixteen entries make a table. *)
let tok_all (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (n: nat)
  : Lemma (requires
             ent tx ty tz tt p n 0 /\ ent tx ty tz tt p n 1 /\
             ent tx ty tz tt p n 2 /\ ent tx ty tz tt p n 3 /\
             ent tx ty tz tt p n 4 /\ ent tx ty tz tt p n 5 /\
             ent tx ty tz tt p n 6 /\ ent tx ty tz tt p n 7 /\
             ent tx ty tz tt p n 8 /\ ent tx ty tz tt p n 9 /\
             ent tx ty tz tt p n 10 /\ ent tx ty tz tt p n 11 /\
             ent tx ty tz tt p n 12 /\ ent tx ty tz tt p n 13 /\
             ent tx ty tz tt p n 14 /\ ent tx ty tz tt p n 15)
          (ensures tok tx ty tz tt p n 16)
  = introduce forall (d: nat). d < 16 ==> ent tx ty tz tt p n d
    with introduce _ ==> _
    with (assert (d == 0 \/ d == 1 \/ d == 2 \/ d == 3 \/
                  d == 4 \/ d == 5 \/ d == 6 \/ d == 7 \/
                  d == 8 \/ d == 9 \/ d == 10 \/ d == 11 \/
                  d == 12 \/ d == 13 \/ d == 14 \/ d == 15))

#pop-options
