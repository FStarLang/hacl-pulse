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

(** The SHA-1 instructions, as statements about [Spec.SHA1].

    [SHA1RNDS4] performs four rounds, [SHA1NEXTE] supplies the fifth state
    word to the next four, and [SHA1MSG1]/[SHA1MSG2] perform four slots of
    the message schedule.  As in [Spec.SHANI], this module says what each of
    them computes in the specification's terms, so that the axioms in
    [Hacl.Vec128] are claims about SHA-1 rather than a second definition of
    it.

    {2 The packing}

    The instructions keep the earliest word in the high lane: the state
    register [ABCD] is [[ d; c; b; a ]] from lane zero up, and a message
    register holding [w.[j..j+3]] has [w.[j]] in lane three.  The fifth state
    word [e] never lives in a register of its own.  [SHA1RNDS4] takes it
    pre-added to the first message word, and after four rounds it is
    [ROTL^30] of the [a] that went in -- the [a] of four rounds ago has
    become [b], [c], [d] and then [e], rotated once on the way -- so
    [SHA1NEXTE] recomputes it from the previous [ABCD] and adds it to the
    next message word.

    {2 The schedule}

    The implementation stores each group of four schedule words with its
    lanes reversed, which is the order the instructions read; [wsr] is the
    schedule array in that layout. *)
module Spec.SHA1NI

open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Loops
open Spec.SHA1

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S32 = Hacl.Secret.UInt32
module SHANI = Spec.SHANI

let reg = SHANI.reg

let lane (a: reg) (i: nat { i < 4 }) : GTot S32.t = SHANI.lane a i

let rol30 (x: S32.t) : S32.t = S32.rotate_left x 30ul

let rol1 (x: S32.t) : S32.t = S32.rotate_left x 1ul

(** {2 Four rounds} *)

(** The round function and the constant of quarter [q], which is what the
    instruction's immediate selects. *)
let fq (q: nat { q < 4 }) (x y z: S32.t) : S32.t =
  if q = 0 then _Ch x y z else if q = 2 then _Maj x y z else _Par x y z

let kq (q: nat { q < 4 }) : S32.t = k (20 * q)

(** [Spec.SHA1.shuffle_core] with the quarter given rather than the round
    number. *)
let rstep (q: nat { q < 4 }) (h: Seq.lseq S32.t state_words) (w: S32.t)
  : Seq.lseq S32.t state_words
  = let a = Seq.index h 0 in let b = Seq.index h 1 in
    let c = Seq.index h 2 in let d = Seq.index h 3 in
    let e = Seq.index h 4 in
    let t =
      S32.add_mod
        (S32.add_mod (S32.add_mod (S32.add_mod (S32.rotate_left a 5ul) (fq q b c d)) e)
                     (kq q))
        w
    in
    set5 h t a (S32.rotate_left b 30ul) c d

(** The five state words, from an [ABCD] register and an [e]. *)
let unpack (abcd: reg) (e: S32.t) : GTot (Seq.lseq S32.t state_words) =
  set5 (Seq.create state_words e) (lane abcd 3) (lane abcd 2) (lane abcd 1) (lane abcd 0) e

(** [SHA1RNDS4] with immediate [q], following the pseudocode of the Intel
    SDM: the first round adds the message word and no [e] -- the caller has
    added [e] into the message word -- and the next three add the [e] the
    rounds before them produced. *)
let rnds4 (q: nat { q < 4 }) (abcd w: reg) : GTot (Seq.lseq S32.t state_words) =
  let h0 = unpack abcd S32.zero in
  rstep q (rstep q (rstep q (rstep q h0 (lane w 3)) (lane w 2)) (lane w 1)) (lane w 0)

(** The result register holds the first four of those words. *)
let rnds4_out (q: nat { q < 4 }) (abcd w r: reg) : GTot prop =
  let h = rnds4 q abcd w in
  lane r 3 == Seq.index h 0 /\ lane r 2 == Seq.index h 1 /\
  lane r 1 == Seq.index h 2 /\ lane r 0 == Seq.index h 3

(** [SHA1NEXTE]: [ROTL^30] of [a]'s high lane added to [b]'s; [b]'s other
    lanes unchanged. *)
let nexte (a b: reg) (i: nat { i < 4 }) : GTot S32.t =
  if i = 3 then S32.add_mod (rol30 (lane a 3)) (lane b 3) else lane b i

(** {2 The schedule instructions} *)

(** [SHA1MSG1]: [w.[t+i-16] xor w.[t+i-14]] for the four [i], given the
    group at [t-16] in [a] and the one at [t-12] in [b]. *)
let msg1 (a b: reg) (i: nat { i < 4 }) : GTot S32.t =
  if i = 3 then S32.logxor (lane a 1) (lane a 3)
  else if i = 2 then S32.logxor (lane a 0) (lane a 2)
  else if i = 1 then S32.logxor (lane b 3) (lane a 1)
  else S32.logxor (lane b 2) (lane a 0)

(** [SHA1MSG2]: the [w.[t+i-3]] term and the rotation.  The last of the
    four depends on the first, as in SHA-256. *)
let msg2_3 (a b: reg) : GTot S32.t = rol1 (S32.logxor (lane a 3) (lane b 2))
let msg2_2 (a b: reg) : GTot S32.t = rol1 (S32.logxor (lane a 2) (lane b 1))
let msg2_1 (a b: reg) : GTot S32.t = rol1 (S32.logxor (lane a 1) (lane b 0))
let msg2_0 (a b: reg) : GTot S32.t = rol1 (S32.logxor (lane a 0) (msg2_3 a b))

let msg2 (a b: reg) (i: nat { i < 4 }) : GTot S32.t =
  if i = 3 then msg2_3 a b else if i = 2 then msg2_2 a b
  else if i = 1 then msg2_1 a b else msg2_0 a b

(** {2 Arithmetic} *)

let add_zero (x: S32.t) : Lemma (S32.add_mod x S32.zero == x /\ S32.add_mod S32.zero x == x)
  = Math.small_mod (S32.v x) (pow2 32);
    S32.v_extensional (S32.add_mod x S32.zero) x;
    S32.v_extensional (S32.add_mod S32.zero x) x

(** The instruction adds [e] to the message word; the specification adds it
    two terms earlier. *)
let move_e (x e kk w: S32.t)
  : Lemma (S32.add_mod (S32.add_mod (S32.add_mod x S32.zero) kk) (S32.add_mod e w) ==
           S32.add_mod (S32.add_mod (S32.add_mod x e) kk) w)
  = add_zero x;
    SHANI.add_mod_assoc x kk (S32.add_mod e w);
    SHANI.add_mod_assoc kk e w;
    SHANI.add_mod_comm kk e;
    SHANI.add_mod_assoc e kk w;
    SHANI.add_mod_assoc (S32.add_mod x e) kk w;
    SHANI.add_mod_assoc x e (S32.add_mod kk w)

let xor4 (x3 x8 x14 x16: S32.t)
  : Lemma (S32.logxor (S32.logxor (S32.logxor x14 x16) x8) x3 ==
           S32.logxor (S32.logxor (S32.logxor x3 x8) x14) x16)
  = let open FStar.UInt in
    let v3 = S32.v x3 in let v8 = S32.v x8 in
    let v14 = S32.v x14 in let v16 = S32.v x16 in
    logxor_associative #32 v14 v16 v8;
    logxor_commutative #32 v16 v8;
    logxor_associative #32 v14 v8 v16;
    logxor_commutative #32 v14 v8;
    logxor_associative #32 (logxor #32 v8 v14) v16 v3;
    logxor_commutative #32 v16 v3;
    logxor_associative #32 (logxor #32 v8 v14) v3 v16;
    logxor_associative #32 v8 v14 v3;
    logxor_commutative #32 v14 v3;
    logxor_associative #32 v8 v3 v14;
    logxor_commutative #32 v8 v3;
    S32.v_extensional (S32.logxor (S32.logxor (S32.logxor x14 x16) x8) x3)
                      (S32.logxor (S32.logxor (S32.logxor x3 x8) x14) x16)

(** {2 Rounds}

    [shuffle_core] on round [i] is [rstep] on its quarter. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let core_is_rstep (w: Seq.lseq S32.t rounds) (q: nat { q < 4 }) (i: nat)
                  (h: Seq.lseq S32.t state_words)
  : Lemma (requires 20 * q <= i /\ i < 20 * q + 20)
          (ensures shuffle_core w i h == rstep q h (Seq.index w i))
  = assert (_f i (Seq.index h 1) (Seq.index h 2) (Seq.index h 3) ==
            fq q (Seq.index h 1) (Seq.index h 2) (Seq.index h 3));
    assert (k i == kq q)
#pop-options

(** Round one of the instruction, which has [e] in the message word, is
    round one of the specification. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let rstep_e (q: nat { q < 4 }) (abcd: reg) (e w: S32.t)
  : Lemma (rstep q (unpack abcd S32.zero) (S32.add_mod e w) == rstep q (unpack abcd e) w)
  = let a = lane abcd 3 in let b = lane abcd 2 in
    let c = lane abcd 1 in let d = lane abcd 0 in
    move_e (S32.add_mod (S32.rotate_left a 5ul) (fq q b c d)) e (kq q) w;
    set5_irrelevant (unpack abcd S32.zero) (unpack abcd e)
      (S32.add_mod
        (S32.add_mod (S32.add_mod (S32.add_mod (S32.rotate_left a 5ul) (fq q b c d)) e) (kq q))
        w)
      a (S32.rotate_left b 30ul) c d
#pop-options

(** Four rounds of the specification are the instruction, followed by the
    [e] that [SHA1NEXTE] recomputes. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let group (w: Seq.lseq S32.t rounds) (h0: Seq.lseq S32.t state_words)
          (q: nat { q < 4 }) (j: nat) (abcd x r: reg) (e: S32.t)
  : Lemma (requires 20 * q <= j /\ j + 4 <= 20 * q + 20 /\
                    repeati_g j (shuffle_core w) h0 == unpack abcd e /\
                    lane x 3 == S32.add_mod e (Seq.index w j) /\
                    lane x 2 == Seq.index w (j + 1) /\
                    lane x 1 == Seq.index w (j + 2) /\
                    lane x 0 == Seq.index w (j + 3) /\
                    rnds4_out q abcd x r)
          (ensures repeati_g (j + 4) (shuffle_core w) h0 == unpack r (rol30 (lane abcd 3)))
  = let f = shuffle_core w in
    unfold_repeati_g j f h0;
    unfold_repeati_g (j + 1) f h0;
    unfold_repeati_g (j + 2) f h0;
    unfold_repeati_g (j + 3) f h0;
    let s0 = repeati_g j f h0 in
    core_is_rstep w q j s0;
    rstep_e q abcd e (Seq.index w j);
    let s1 = repeati_g (j + 1) f h0 in
    core_is_rstep w q (j + 1) s1;
    let s2 = repeati_g (j + 2) f h0 in
    core_is_rstep w q (j + 2) s2;
    let s3 = repeati_g (j + 3) f h0 in
    core_is_rstep w q (j + 3) s3;
    assert (repeati_g (j + 4) f h0 == rnds4 q abcd x);
    let h = rnds4 q abcd x in
    assert (Seq.index h 4 == rol30 (lane abcd 3));
    Seq.lemma_eq_intro h (unpack r (rol30 (lane abcd 3)))
#pop-options

(** The quarter a group of four starting at a multiple of four is in. *)
let quarter (j: nat)
  : Lemma (requires j % 4 == 0 /\ j < 80)
          (ensures j / 20 < 4 /\ 20 * (j / 20) <= j /\ j + 4 <= 20 * (j / 20) + 20)
  = Math.lemma_div_mod j 20;
    Math.lemma_mod_plus (j % 20) (5 * (j / 20)) 4

(** {2 The schedule} *)

(** The register [r] holds the four schedule words from [t], earliest in the
    high lane. *)
let holds (b: Seq.lseq S32.t block_words) (t: nat) (r: reg) : GTot prop =
  lane r 3 == ws_at b t /\ lane r 2 == ws_at b (t + 1) /\
  lane r 1 == ws_at b (t + 2) /\ lane r 0 == ws_at b (t + 3)

(** The schedule array, each group of four reversed. *)
let wsr (b: Seq.lseq S32.t block_words) (s: nat) : S32.t =
  ws_at b (4 * (s / 4) + 3 - s % 4)

let wsr_group (b: Seq.lseq S32.t block_words) (g: nat) (m: nat { m < 4 })
  : Lemma (wsr b (4 * g + m) == ws_at b (4 * g + 3 - m))
  = Math.lemma_div_plus m g 4;
    Math.small_div m 4;
    Math.lemma_mod_plus m g 4;
    Math.small_mod m 4

let ws_step (b: Seq.lseq S32.t block_words) (n: nat)
  : Lemma (requires 16 <= n)
          (ensures ws_at b n ==
                   rol1 (S32.logxor (S32.logxor (S32.logxor (ws_at b (n - 3)) (ws_at b (n - 8)))
                                                (ws_at b (n - 14)))
                                    (ws_at b (n - 16))))
  = assert_norm (ws_at b n ==
                   S32.rotate_left (S32.logxor (S32.logxor (S32.logxor (ws_at b (n - 3)) (ws_at b (n - 8)))
                                                (ws_at b (n - 14)))
                                    (ws_at b (n - 16))) 1ul)

(** [msg2 (msg1 p16 p12 xor p8) p4] is the next group. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let sched (b: Seq.lseq S32.t block_words) (t: nat) (p16 p12 p8 p4 m1 x m2: reg)
  : Lemma (requires 16 <= t /\
                    holds b (t - 16) p16 /\ holds b (t - 12) p12 /\
                    holds b (t - 8) p8 /\ holds b (t - 4) p4 /\
                    (forall (i: nat). i < 4 ==> lane m1 i == msg1 p16 p12 i) /\
                    (forall (i: nat). i < 4 ==> lane x i == S32.logxor (lane m1 i) (lane p8 i)) /\
                    (forall (i: nat). i < 4 ==> lane m2 i == msg2 x p4 i))
          (ensures holds b t m2)
  = ws_step b t;
    ws_step b (t + 1);
    ws_step b (t + 2);
    ws_step b (t + 3);
    xor4 (ws_at b (t - 3)) (ws_at b (t - 8)) (ws_at b (t - 14)) (ws_at b (t - 16));
    xor4 (ws_at b (t - 2)) (ws_at b (t - 7)) (ws_at b (t - 13)) (ws_at b (t - 15));
    xor4 (ws_at b (t - 1)) (ws_at b (t - 6)) (ws_at b (t - 12)) (ws_at b (t - 14));
    xor4 (ws_at b t) (ws_at b (t - 5)) (ws_at b (t - 11)) (ws_at b (t - 13));
    assert (lane m2 3 == msg2_3 x p4);
    assert (lane m2 2 == msg2_2 x p4);
    assert (lane m2 1 == msg2_1 x p4);
    assert (lane m2 0 == msg2_0 x p4)
#pop-options
