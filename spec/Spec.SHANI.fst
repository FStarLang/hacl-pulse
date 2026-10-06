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
open Hacl.Spec.Loops

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

(** The four cases of [msg2], named.  Letting the solver reduce the index
    chain itself inside [quad_holds] is what used to make that proof fit. *)
let msg2_cases (a b: reg)
  : Lemma (msg2 a b 0 == msg2_0 a b /\ msg2 a b 1 == msg2_1 a b /\
           msg2 a b 2 == msg2_2 a b /\ msg2 a b 3 == msg2_3 a b)
  = ()

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

(** {2 What the four schedule registers hold}

    The implementation keeps four registers whose roles rotate with period
    four: at the step that produces [w.[j] .. w.[j+3]] they hold
    [w.[j-8..j-5]], [w.[j-4..j-1]] and the two partial sums for [j] and
    [j+4].  [holds_ws] and [holds_half] name those two conditions. *)

let holds_ws (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat) (r: reg) : GTot prop =
  forall (i: nat). i < 4 ==> lane r i == ws_at p b (j + i)

(** The [w.[j-16] + sigma0 w.[j-15]] half of slot [j], which [SHA256MSG1]
    produces twelve rounds before it is needed. *)
let half (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat { 16 <= j }) (i: nat { i < 4 })
  : GTot S32.t
  = S32.add_mod (ws_at p b (j - 16 + i)) (sig0 (ws_at p b (j - 15 + i)))

let holds_half (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat { 16 <= j }) (r: reg) : GTot prop =
  forall (i: nat). i < 4 ==> lane r i == half p b j i

(** [SHA256MSG1] on two consecutive groups is the half for the group twelve
    slots on.  [align_right_4] has the same shape -- three lanes of one
    register followed by lane zero of the other -- so this also says what the
    rotate contributes, one group earlier. *)
(** Four quantifier-free facts make a quantified one.  Stating it separately
    keeps the hypotheses of the lemmas below -- which are themselves
    quantified, over a recursively defined [ws_at] -- out of the query that
    has to introduce the quantifier. *)
let four (r: reg) (f: (i: nat { i < 4 }) -> GTot S32.t)
  : Lemma (requires lane r 0 == f 0 /\ lane r 1 == f 1 /\
                    lane r 2 == f 2 /\ lane r 3 == f 3)
          (ensures forall (i: nat). i < 4 ==> lane r i == f i)
  = ()

let msg1_lane (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat) (x y: reg)
                (i: nat { i < 4 })
  : Lemma (requires
             is_sha256 p /\
             lane x i == ws_at p b (j + i) /\
             (if i < 3 then lane x (i + 1) == ws_at p b (j + i + 1)
                       else lane y 0 == ws_at p b (j + i + 1)))
          (ensures msg1 x y i == half p b (j + 16) i)
  = ()

let msg1_holds (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat) (x y r: reg)
  : Lemma (requires is_sha256 p /\ holds_ws p b j x /\ holds_ws p b (j + 4) y /\
                    (forall (m: nat). m < 4 ==> lane r m == msg1 x y m))
          (ensures holds_half p b (j + 16) r)
  = assert (lane y 0 == ws_at p b (j + 4));
    msg1_lane p b j x y 0;
    assert (lane r 0 == half p b (j + 16) 0);
    msg1_lane p b j x y 1;
    assert (lane r 1 == half p b (j + 16) 1);
    msg1_lane p b j x y 2;
    assert (lane r 2 == half p b (j + 16) 2);
    msg1_lane p b j x y 3;
    assert (lane r 3 == half p b (j + 16) 3);
    four r (half p b (j + 16))

(** {2 One group of four schedule slots}

    [res] is what [SHA256MSG2] leaves after the rotate has been added in.
    The hypotheses are written as what each register holds rather than as the
    instructions that produced it, so that this lemma says nothing about
    [Hacl.Vec128]; the implementation supplies them from the axioms.

    Stated one lane at a time: the conclusion needs four instantiations of
    each hypothesis at once, and a single query with all four quantified
    hypotheses in scope does not close. *)

let quad_lane (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat { 16 <= j })
              (bt: reg) (i: nat { i < 4 }) (s1arg: S32.t)
  : Lemma (requires
             is_sha256 p /\
             s1arg == ws_at p b (j + i - 2) /\
             lane bt i == S32.add_mod (half p b j i) (ws_at p b (j + i - 7)))
          (ensures S32.add_mod (lane bt i) (sig1 s1arg) == ws_at p b (j + i))
  = sched_step p b (j + i)

(** The four lanes together.  [msg2] is serial -- lanes two and three read
    lanes zero and one of the result -- so the last two applications of
    [quad_lane] are given the slots just produced rather than a lane of an
    input register. *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let quad_holds (p: params S32.t) (b: Seq.lseq S32.t 16) (j: nat { 16 <= j })
               (a d bb tmp bt res: reg)
  : Lemma (requires
             is_sha256 p /\
             holds_ws p b (j - 8) d /\ holds_ws p b (j - 4) a /\
             holds_half p b j bb /\
             (forall (m: nat). m < 4 ==>
                lane tmp m == (if m < 3 then lane d (m + 1) else lane a 0)) /\
             (forall (m: nat). m < 4 ==>
                lane bt m == S32.add_mod (lane bb m) (lane tmp m)) /\
             (forall (m: nat). m < 4 ==> lane res m == msg2 bt a m))
          (ensures holds_ws p b j res)
  = (* What the rotate contributed: lane m of [tmp] is slot [j + m - 7]. *)
    assert (lane bt 0 == S32.add_mod (half p b j 0) (ws_at p b (j - 7)));
    assert (lane bt 1 == S32.add_mod (half p b j 1) (ws_at p b (j - 6)));
    assert (lane bt 2 == S32.add_mod (half p b j 2) (ws_at p b (j - 5)));
    assert (lane bt 3 == S32.add_mod (half p b j 3) (ws_at p b (j - 4)));
    assert (lane a 2 == ws_at p b (j - 2));
    assert (lane a 3 == ws_at p b (j - 1));
    quad_lane p b j bt 0 (lane a 2);
    assert (lane res 0 == ws_at p b j);
    quad_lane p b j bt 1 (lane a 3);
    assert (lane res 1 == ws_at p b (j + 1));
    msg2_cases bt a;
    assert (lane res 0 == msg2_0 bt a);
    assert (lane res 1 == msg2_1 bt a);
    quad_lane p b j bt 2 (ws_at p b j);
    assert (lane res 2 == msg2_2 bt a);
    assert (msg2_2 bt a == S32.add_mod (lane bt 2) (sig1 (msg2_0 bt a)));
    assert (msg2_0 bt a == ws_at p b j);
    assert (lane res 2 == S32.add_mod (lane bt 2) (sig1 (ws_at p b j)));
    assert (lane res 2 == ws_at p b (j + 2));
    quad_lane p b j bt 3 (ws_at p b (j + 1));
    assert (lane res 3 == msg2_3 bt a);
    assert (msg2_3 bt a == S32.add_mod (lane bt 3) (sig1 (msg2_1 bt a)));
    assert (msg2_1 bt a == ws_at p b (j + 1));
    assert (lane res 3 == S32.add_mod (lane bt 3) (sig1 (ws_at p b (j + 1))));
    assert (lane res 3 == ws_at p b (j + 3));
    four res (fun i -> ws_at p b (j + i))
#pop-options

(** {2 Four rounds}

    [SHA256RNDS2] twice, which is what the implementation does per iteration:
    the first call reads the round input from the low two lanes of [msg] and
    the second from the high two, brought down by [shuffle_high_pair].  The
    two registers swap roles in between, so no state is permuted.

    The hypotheses are the postconditions of the [Hacl.Vec128] axioms written
    out; the conclusion is four more steps of [Spec.SHA2.shuffle]. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let rnds4 (p: params S32.t) (w: Seq.lseq S32.t (rounds p)) (h0: Seq.lseq S32.t 8)
          (i: nat { i + 4 <= rounds p }) (st0 st1 st0' st1' msg msg': reg)
  : Lemma (requires
             is_sha256 p /\
             unpack st0 st1 == repeati_g i (shuffle_core p w) h0 /\
             (forall (m: nat). m < 4 ==>
                lane msg m == S32.add_mod (Seq.index (G.reveal p.k) (i + m))
                                          (Seq.index w (i + m))) /\
             lane msg' 0 == lane msg 2 /\ lane msg' 1 == lane msg 3 /\
             unpack st1' st0 ==
               round (round (unpack st0 st1) (lane msg 0)) (lane msg 1) /\
             unpack st0' st1' ==
               round (round (unpack st1' st0) (lane msg' 0)) (lane msg' 1))
          (ensures unpack st0' st1' == repeati_g (i + 4) (shuffle_core p w) h0)
  = let f = shuffle_core p w in
    let h1 = repeati_g i f h0 in
    round_is_core p w i h1;
    unfold_repeati_g i f h0;
    let h2 = repeati_g (i + 1) f h0 in
    assert (h2 == round h1 (lane msg 0));
    round_is_core p w (i + 1) h2;
    unfold_repeati_g (i + 1) f h0;
    let h3 = repeati_g (i + 2) f h0 in
    assert (h3 == round h2 (lane msg 1));
    round_is_core p w (i + 2) h3;
    unfold_repeati_g (i + 2) f h0;
    let h4 = repeati_g (i + 3) f h0 in
    assert (h4 == round h3 (lane msg 2));
    round_is_core p w (i + 3) h4;
    unfold_repeati_g (i + 3) f h0;
    assert (repeati_g (i + 4) f h0 == round h4 (lane msg 3))
#pop-options

(** {2 Packing and unpacking the state}

    The eight words arrive as two registers holding [a b c d] and [e f g h],
    and four permutations turn them into [ABEF] and [CDGH].  These two lemmas
    say the permutations are inverse to [unpack], so the implementation only
    has to quote the axioms. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"
let pack_state (lo hi st0 st1: reg) (h: Seq.lseq S32.t 8)
  : Lemma (requires
             (forall (m: nat). m < 4 ==> lane lo m == Seq.index h m) /\
             (forall (m: nat). m < 4 ==> lane hi m == Seq.index h (m + 4)) /\
             lane st0 0 == lane hi 1 /\ lane st0 1 == lane hi 0 /\
             lane st0 2 == lane lo 1 /\ lane st0 3 == lane lo 0 /\
             lane st1 0 == lane hi 3 /\ lane st1 1 == lane hi 2 /\
             lane st1 2 == lane lo 3 /\ lane st1 3 == lane lo 2)
          (ensures unpack st0 st1 == h)
  = Seq.lemma_eq_intro (unpack st0 st1) h

let unpack_state (st0 st1 lo hi: reg) (h: Seq.lseq S32.t 8)
  : Lemma (requires
             unpack st0 st1 == h /\
             lane lo 0 == lane st0 3 /\ lane lo 1 == lane st0 2 /\
             lane lo 2 == lane st1 3 /\ lane lo 3 == lane st1 2 /\
             lane hi 0 == lane st0 1 /\ lane hi 1 == lane st0 0 /\
             lane hi 2 == lane st1 1 /\ lane hi 3 == lane st1 0)
          (ensures (forall (m: nat). m < 4 ==> lane lo m == Seq.index h m) /\
                   (forall (m: nat). m < 4 ==> lane hi m == Seq.index h (m + 4)))
  = ()

(** {2 Adding the saved state back}

    [add_state] is slotwise, and the slots of a pair of registers are the
    slots of the state, so this is [add32] on each register. *)
let add_state_packed (h hs: Seq.lseq S32.t 8) (a0 c0 st0 st1 ra rc: reg)
  : Lemma (requires
             unpack a0 c0 == h /\ unpack st0 st1 == hs /\
             (forall (m: nat). m < 4 ==>
                lane ra m == S32.add_mod (lane a0 m) (lane st0 m)) /\
             (forall (m: nat). m < 4 ==>
                lane rc m == S32.add_mod (lane c0 m) (lane st1 m)))
          (ensures unpack ra rc == add_state h hs)
  = Seq.lemma_eq_intro (unpack ra rc) (add_state h hs)
#pop-options

(** {2 A block, four words at a time}

    The implementation loads sixteen bytes at a time; [Spec.SHA2.update_block]
    reads the whole sixty-four byte block at once.  Both are [word_from_be] of
    the same four bytes. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let block_group (s: Seq.seq S8.t) (off: nat) (q: nat { q < 4 })
  : Lemma (requires off + 64 <= Seq.length s)
          (ensures (Seq.length (Seq.slice s (off + 16 * q) (off + 16 * q + 16)) == 16 /\
                    (forall (m: nat). m < 4 ==>
                       Seq.index (words_from_be block_words (block_at #S32.t s off)) (4 * q + m) ==
                       Seq.index (words_from_be 4 (Seq.slice s (off + 16 * q) (off + 16 * q + 16))) m)))
  = let blk = block_at #S32.t s off in
    assert (blk == Seq.slice s off (off + 64));
    let sl = Seq.slice s (off + 16 * q) (off + 16 * q + 16) in
    Seq.slice_slice s off (off + 64) (16 * q) (16 * q + 16);
    let aux (m: nat { m < 4 }) : Lemma (sub_block #S32.t block_words blk (4 * q + m) == sub_block #S32.t 4 sl m)
      = Seq.slice_slice s off (off + 64) (4 * (4 * q + m)) (4 * (4 * q + m) + 4);
        Seq.slice_slice s (off + 16 * q) (off + 16 * q + 16) (4 * m) (4 * m + 4);
        Seq.lemma_eq_intro (sub_block #S32.t block_words blk (4 * q + m)) (sub_block #S32.t 4 sl m)
    in
    aux 0; aux 1; aux 2; aux 3
#pop-options
