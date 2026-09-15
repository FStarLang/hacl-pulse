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

(** The SHA-256 instructions, as statements about [Spec.SHA2].

    [SHA256RNDS2] performs two rounds of the compression function and
    [SHA256MSG1]/[SHA256MSG2] between them perform the message schedule, all
    on four words at a time in a packing of the state that is not the one
    FIPS 180-4 uses.  This module is the dictionary between the two, so that
    the axioms in [Hacl.Vec128] can be read as claims about the hash rather
    than as a second definition of it, and so that the implementation's proof
    is about which register holds which word.

    {2 The packing}

    The eight state words go into two registers as [ABEF] and [CDGH], each
    written from the high lane down:

    {[
      ABEF = [ f; e; b; a ]      CDGH = [ h; g; d; c ]
    ]}

    (lane zero first, as memory has them).  This is what [SHA256RNDS2] reads
    and writes, and the reason for it is that two rounds move [a] into [c],
    [b] into [d], [e] into [g] and [f] into [h]: the instruction produces the
    new [ABEF] and the {i old} [ABEF] is already the new [CDGH], so two
    registers alternate roles and nothing is shuffled between rounds.
    [unpack] below reads the eight words back out of a pair.

    {2 The schedule}

    [ws_at] is defined slotwise from four earlier slots; the instructions
    accumulate the same four terms in a different order and four slots at a
    time, with [SHA256MSG1] contributing the [w + sigma0 w'] half and
    [SHA256MSG2] the [sigma1] half after a rotate-and-add supplies the
    remaining term.  [sched_step] is the arithmetic identity that lets the
    two be matched up. *)
module Spec.SHANI

open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Spec.SHA2
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module G = FStar.Ghost

(** {2 Registers as four words} *)

(** The sixteen bytes a [Hacl.Vec128.t] holds. *)
let reg = Seq.lseq S8.t 16

(** Read as four 32-bit words, lane zero lowest in memory.  This is the
    machine's view of the register, and it is little-endian: the big-endian
    reading that FIPS 180-4 applies to a message block happens once, in the
    byte shuffle on the way in. *)
let lanes (a: reg) : GTot (Seq.lseq S32.t 4) = words_from_le 4 a

let lane (a: reg) (i: nat { i < 4 }) : GTot S32.t = Seq.index (lanes a) i

(** {2 Modular addition is associative}

    Needed because the instructions accumulate [k + w] into the round input
    while [Spec.SHA2.shuffle_core] adds [k] and then [w]. *)

let add_mod_assoc (x y z: S32.t)
  : Lemma (S32.add_mod (S32.add_mod x y) z == S32.add_mod x (S32.add_mod y z))
  = Math.lemma_mod_add_distr (S32.v z) (S32.v x + S32.v y) (pow2 32);
    Math.lemma_mod_add_distr (S32.v x) (S32.v y + S32.v z) (pow2 32);
    S32.v_extensional (S32.add_mod (S32.add_mod x y) z)
                      (S32.add_mod x (S32.add_mod y z))

let add_mod_comm (x y: S32.t)
  : Lemma (S32.add_mod x y == S32.add_mod y x)
  = S32.v_extensional (S32.add_mod x y) (S32.add_mod y x)

(** {2 The SHA-256 round functions, concretely}

    The instructions are SHA-256 and nothing else, so their axioms cannot be
    stated against a [params] record that is only known at run time.  These
    are the four functions with the rotation amounts written out, and
    [is_sha256] is the (decidable, and discharged once at each call site)
    statement that a [params] agrees with them. *)

let cs0 (x: S32.t) : S32.t =
  logxor #S32.t (logxor #S32.t (rotate_right x 2ul) (rotate_right x 13ul))
                (rotate_right x 22ul)

let cs1 (x: S32.t) : S32.t =
  logxor #S32.t (logxor #S32.t (rotate_right x 6ul) (rotate_right x 11ul))
                (rotate_right x 25ul)

let sig0 (x: S32.t) : S32.t =
  logxor #S32.t (logxor #S32.t (rotate_right x 7ul) (rotate_right x 18ul))
                (shift_right x 3ul)

let sig1 (x: S32.t) : S32.t =
  logxor #S32.t (logxor #S32.t (rotate_right x 17ul) (rotate_right x 19ul))
                (shift_right x 10ul)

let is_sha256 (p: params S32.t) =
  p.cs0_a == 2ul /\ p.cs0_b == 13ul /\ p.cs0_c == 22ul /\
  p.cs1_a == 6ul /\ p.cs1_b == 11ul /\ p.cs1_c == 25ul /\
  p.s0_a == 7ul /\ p.s0_b == 18ul /\ p.s0_c == 3ul /\
  p.s1_a == 17ul /\ p.s1_b == 19ul /\ p.s1_c == 10ul /\
  rounds p == 64

let cs0_eq (p: params S32.t) (x: S32.t)
  : Lemma (requires is_sha256 p) (ensures _Sigma0 p x == cs0 x) = ()

let cs1_eq (p: params S32.t) (x: S32.t)
  : Lemma (requires is_sha256 p) (ensures _Sigma1 p x == cs1 x) = ()

let sig0_eq (p: params S32.t) (x: S32.t)
  : Lemma (requires is_sha256 p) (ensures _sigma0 p x == sig0 x) = ()

let sig1_eq (p: params S32.t) (x: S32.t)
  : Lemma (requires is_sha256 p) (ensures _sigma1 p x == sig1 x) = ()

(** {2 Two rounds} *)

(** One round of the compression function, taking the round input [wk] --
    that is, [k.[i] + w.[i]] -- already summed, which is how the instruction
    receives it.  Otherwise this is [Spec.SHA2.shuffle_core] verbatim. *)
let round (h: Seq.lseq S32.t 8) (wk: S32.t) : Seq.lseq S32.t 8 =
  let a = Seq.index h 0 in let b = Seq.index h 1 in
  let c = Seq.index h 2 in let d = Seq.index h 3 in
  let e = Seq.index h 4 in let f = Seq.index h 5 in
  let g = Seq.index h 6 in let hh = Seq.index h 7 in
  let t1 = S32.add_mod (S32.add_mod (S32.add_mod hh (cs1 e)) (_Ch e f g)) wk in
  let t2 = S32.add_mod (cs0 a) (_Maj a b c) in
  set8 h (S32.add_mod t1 t2) a b c (S32.add_mod d t1) e f g

(** The instruction's round input is [k + w] where the specification's is
    [(... + k) + w]; associativity is the whole of the difference. *)
let round_is_core (p: params S32.t) (w: Seq.lseq S32.t (rounds p))
                  (i: nat { i < rounds p }) (h: Seq.lseq S32.t 8)
  : Lemma (requires is_sha256 p)
          (ensures shuffle_core p w i h ==
                   round h (S32.add_mod (Seq.index (G.reveal p.k) i)
                                        (Seq.index w i)))
  = add_mod_assoc
      (S32.add_mod (S32.add_mod (Seq.index h 7) (cs1 (Seq.index h 4)))
                   (_Ch (Seq.index h 4) (Seq.index h 5) (Seq.index h 6)))
      (Seq.index (G.reveal p.k) i) (Seq.index w i)

(** {2 The two registers} *)

(** The eight state words, read out of an [ABEF] and a [CDGH] register. *)
let unpack (abef cdgh: reg) : GTot (Seq.lseq S32.t 8) =
  Seq.init_ghost 8 (fun i ->
    if i = 0 then lane abef 3 else if i = 1 then lane abef 2
    else if i = 2 then lane cdgh 3 else if i = 3 then lane cdgh 2
    else if i = 4 then lane abef 1 else if i = 5 then lane abef 0
    else if i = 6 then lane cdgh 1 else lane cdgh 0)

let unpack_index (abef cdgh: reg) (i: nat { i < 8 })
  : Lemma (Seq.index (unpack abef cdgh) i ==
             (if i = 0 then lane abef 3 else if i = 1 then lane abef 2
              else if i = 2 then lane cdgh 3 else if i = 3 then lane cdgh 2
              else if i = 4 then lane abef 1 else if i = 5 then lane abef 0
              else if i = 6 then lane cdgh 1 else lane cdgh 0)) = ()

(** {2 The message schedule instructions} *)

(** [SHA256MSG1]: the [w + sigma0 w'] half of four slots at once.  Lane [i]
    of [a] is [w.[j+i]] and lane zero of [b] is [w.[j+4]]. *)
let msg1 (a b: reg) (i: nat { i < 4 }) : GTot S32.t =
  S32.add_mod (lane a i) (sig0 (if i < 3 then lane a (i + 1) else lane b 0))

(** [SHA256MSG2]: the [sigma1] half, which is serial within the group of four
    because slots two and three of the group depend on slots zero and one. *)
let msg2_0 (a b: reg) : GTot S32.t = S32.add_mod (lane a 0) (sig1 (lane b 2))
let msg2_1 (a b: reg) : GTot S32.t = S32.add_mod (lane a 1) (sig1 (lane b 3))
let msg2_2 (a b: reg) : GTot S32.t = S32.add_mod (lane a 2) (sig1 (msg2_0 a b))
let msg2_3 (a b: reg) : GTot S32.t = S32.add_mod (lane a 3) (sig1 (msg2_1 a b))

let msg2 (a b: reg) (i: nat { i < 4 }) : GTot S32.t =
  if i = 0 then msg2_0 a b else if i = 1 then msg2_1 a b
  else if i = 2 then msg2_2 a b else msg2_3 a b

(** {2 The schedule identity}

    [ws_at] sums [sigma1 w.[j-2]], [w.[j-7]], [sigma0 w.[j-15]] and
    [w.[j-16]] in that order.  The implementation has, by the time it applies
    [SHA256MSG2], accumulated [w.[j-16] + sigma0 w.[j-15] + w.[j-7]] in that
    order, and adds [sigma1 w.[j-2]] last.  The two agree by commutativity
    and associativity and nothing else. *)
let sched_step (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat { 16 <= j })
  : Lemma (requires is_sha256 p)
          (ensures ws_at p b j ==
                   S32.add_mod
                     (S32.add_mod (S32.add_mod (ws_at p b (j - 16))
                                               (sig0 (ws_at p b (j - 15))))
                                  (ws_at p b (j - 7)))
                     (sig1 (ws_at p b (j - 2))))
  = let s1 = sig1 (ws_at p b (j - 2)) in
    let w7 = ws_at p b (j - 7) in
    let s0 = sig0 (ws_at p b (j - 15)) in
    let w16 = ws_at p b (j - 16) in
    (* The specification's order. *)
    assert (ws_at p b j ==
              S32.add_mod (S32.add_mod (S32.add_mod s1 w7) s0) w16);
    add_mod_assoc (S32.add_mod s1 w7) s0 w16;
    add_mod_comm s0 w16;
    add_mod_assoc s1 w7 (S32.add_mod w16 s0);
    add_mod_comm w7 (S32.add_mod w16 s0);
    add_mod_assoc w16 s0 w7;
    add_mod_comm s1 (S32.add_mod (S32.add_mod w16 s0) w7)
