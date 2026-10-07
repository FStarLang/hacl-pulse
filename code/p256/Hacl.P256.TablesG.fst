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

(** The fixed-base window's six field constants, in a module of their own.

    They are the Montgomery forms of the coordinates of [2^64 G],
    [2^128 G] and [2^192 G], which {!Spec.P256.Base} says are what they
    are.  Everything here is the same four lines as the eight constants in
    {!Hacl.P256.Tables}, and the obvious place for them would have been
    beside those.

    That is where they were, on secp256k1, and it did not work.  Six more
    constants took {!Hacl.K256.Tables52} from sixty seconds to over
    eighteen minutes without finishing.  The values are settled by the
    normaliser and the coordinates are [opaque_to_smt], so the solver has
    no use for them -- but an [assert_norm] leaves its conclusion in the
    context, and the conclusion contains the literal.  A dozen
    two-hundred-and-fifty-six-bit numbers in scope of every later query in
    the file is enough to stop it terminating, whatever the query is
    about.

    Split off into a module whose entire content is these six blocks, it
    costs seconds.  The same reasoning applies here, and more so: P-256's
    constants are Montgomery forms, so each [assert_norm] carries a
    product with [2^256] reduced modulo a seventy-eight-digit prime. *)
module Hacl.P256.TablesG

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Lit4

module Seq = FStar.Seq
module L = FStar.List.Tot
module G = Pulse.Lib.GlobalArray
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module KB = Spec.P256.Base

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** [q1x R mod p]. *)
let q1xm_list : list S64.t = [
  S64.classify 5733697799130763963uL;
  S64.classify 962857090393715865uL;
  S64.classify 10538932452511329419uL;
  S64.classify 3413281437172590207uL
]

let q1xm_arr : (a: G.static_array S64.t
                   { vals (G.static_array_elems a) == limbs (KB.q1x * pow2 256 % P.prime) })
  = assert_norm (L.length q1xm_list == nl);
    assert_norm (lbnd q1xm_list);
    assert_norm (leval q1xm_list == 21425514832639209759702340292309447860610874306785979021775288759118716785339);
    assert_norm ((KB.q1x * pow2 256 % P.prime) == 21425514832639209759702340292309447860610874306785979021775288759118716785339);
    assert_norm (21425514832639209759702340292309447860610874306785979021775288759118716785339 < pow2 256);
    lit_limbs q1xm_list (KB.q1x * pow2 256 % P.prime);
    G.mk_static_array q1xm_list

(** [q1y R mod p]. *)
let q1ym_list : list S64.t = [
  S64.classify 6635428480179771287uL;
  S64.classify 4404718679994229138uL;
  S64.classify 329074170931436370uL;
  S64.classify 17746708206910902139uL
]

let q1ym_arr : (a: G.static_array S64.t
                   { vals (G.static_array_elems a) == limbs (KB.q1y * pow2 256 % P.prime) })
  = assert_norm (L.length q1ym_list == nl);
    assert_norm (lbnd q1ym_list);
    assert_norm (leval q1ym_list == 111397892883001473492263269830992769512294106523772687712582585787732480497559);
    assert_norm ((KB.q1y * pow2 256 % P.prime) == 111397892883001473492263269830992769512294106523772687712582585787732480497559);
    assert_norm (111397892883001473492263269830992769512294106523772687712582585787732480497559 < pow2 256);
    lit_limbs q1ym_list (KB.q1y * pow2 256 % P.prime);
    G.mk_static_array q1ym_list

(** [q2x R mod p]. *)
let q2xm_list : list S64.t = [
  S64.classify 7109145612337154341uL;
  S64.classify 10502845970727626855uL;
  S64.classify 6527587047878193251uL;
  S64.classify 7049690136888681718uL
]

let q2xm_arr : (a: G.static_array S64.t
                   { vals (G.static_array_elems a) == limbs (KB.q2x * pow2 256 % P.prime) })
  = assert_norm (L.length q2xm_list == nl);
    assert_norm (lbnd q2xm_list);
    assert_norm (leval q2xm_list == 44251622192202311083079549847017809893123288771884513885420408573074857920805);
    assert_norm ((KB.q2x * pow2 256 % P.prime) == 44251622192202311083079549847017809893123288771884513885420408573074857920805);
    assert_norm (44251622192202311083079549847017809893123288771884513885420408573074857920805 < pow2 256);
    lit_limbs q2xm_list (KB.q2x * pow2 256 % P.prime);
    G.mk_static_array q2xm_list

(** [q2y R mod p]. *)
let q2ym_list : list S64.t = [
  S64.classify 16750703006415156202uL;
  S64.classify 2559311261501721445uL;
  S64.classify 1222802194566919230uL;
  S64.classify 18019462938525560766uL
]

let q2ym_arr : (a: G.static_array S64.t
                   { vals (G.static_array_elems a) == limbs (KB.q2y * pow2 256 % P.prime) })
  = assert_norm (L.length q2ym_list == nl);
    assert_norm (lbnd q2ym_list);
    assert_norm (leval q2ym_list == 113110002082154775519502389502945293845046009857782795177396813526466668098538);
    assert_norm ((KB.q2y * pow2 256 % P.prime) == 113110002082154775519502389502945293845046009857782795177396813526466668098538);
    assert_norm (113110002082154775519502389502945293845046009857782795177396813526466668098538 < pow2 256);
    lit_limbs q2ym_list (KB.q2y * pow2 256 % P.prime);
    G.mk_static_array q2ym_list

(** [q3x R mod p]. *)
let q3xm_list : list S64.t = [
  S64.classify 6266830413981331818uL;
  S64.classify 10890859480409122410uL;
  S64.classify 738708598357264321uL;
  S64.classify 9241173142142102299uL
]

let q3xm_arr : (a: G.static_array S64.t
                   { vals (G.static_array_elems a) == limbs (KB.q3x * pow2 256 % P.prime) })
  = assert_norm (L.length q3xm_list == nl);
    assert_norm (lbnd q3xm_list);
    assert_norm (leval q3xm_list == 58007783967548975847194048616948358886654663327486331832529474508404217655658);
    assert_norm ((KB.q3x * pow2 256 % P.prime) == 58007783967548975847194048616948358886654663327486331832529474508404217655658);
    assert_norm (58007783967548975847194048616948358886654663327486331832529474508404217655658 < pow2 256);
    lit_limbs q3xm_list (KB.q3x * pow2 256 % P.prime);
    G.mk_static_array q3xm_list

(** [q3y R mod p]. *)
let q3ym_list : list S64.t = [
  S64.classify 9152169484987657321uL;
  S64.classify 12122430118903337055uL;
  S64.classify 14270062735458703743uL;
  S64.classify 13877635605034675649uL
]

let q3ym_arr : (a: G.static_array S64.t
                   { vals (G.static_array_elems a) == limbs (KB.q3y * pow2 256 % P.prime) })
  = assert_norm (L.length q3ym_list == nl);
    assert_norm (lbnd q3ym_list);
    assert_norm (leval q3ym_list == 87111330539427151992345557817963115947045868982289025316844918133291505937513);
    assert_norm ((KB.q3y * pow2 256 % P.prime) == 87111330539427151992345557817963115947045868982289025316844918133291505937513);
    assert_norm (87111330539427151992345557817963115947045868982289025316844918133291505937513 < pow2 256);
    lit_limbs q3ym_list (KB.q3y * pow2 256 % P.prime);
    G.mk_static_array q3ym_list

#pop-options
