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

(** One SHA-384/SHA-512 block with the message schedule on AVX2.

    [Hacl.Hash.SHA2.Core.update_block_impl] computes all eighty schedule
    words before the first round, and the rounds keep the working state in
    the state array.  Both are latency-bound chains of scalar arithmetic that
    compete for the same integer units, and the state array is reloaded and
    stored every round because the compiler cannot prove that it does not
    alias the schedule.

    Here the sixteen-word window of the schedule lives in four 256-bit
    registers, and each step computes the next four words in the vector unit
    ([next4]) while the integer units run the four rounds that consume the
    previous four.  Each group's [w + k] goes through four slots of the
    schedule array on its way to the rounds, and the working state is eight
    locals.

    The only lane movement is in [next4]: [sigma1] of the first two new words
    depends on the last two old ones, and of the last two on the first two
    new ones, so it is computed in two halves and blended. *)
module Hacl.Hash.SHA2.AVX2

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Hacl.Spec.Loops
open Spec.SHA2
open Spec.SHA2.Lemmas
open Hacl.Hash.SHA2.Core

module A = Pulse.Lib.Array
module V = Hacl.Vec256
module L = Hacl.Vec256.Lane64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U32 = FStar.UInt32
module G = FStar.Ghost
module Mem = Hacl.Mem

(** {2 The parameters} *)

let is_sha512 (p: params S64.t) =
  p.cs0_a == 28ul /\ p.cs0_b == 34ul /\ p.cs0_c == 39ul /\
  p.cs1_a == 14ul /\ p.cs1_b == 18ul /\ p.cs1_c == 41ul /\
  p.s0_a == 1ul /\ p.s0_b == 8ul /\ p.s0_c == 7ul /\
  p.s1_a == 19ul /\ p.s1_b == 61ul /\ p.s1_c == 6ul /\
  rounds p == 80

(** {2 The schedule, four words at a time} *)

inline_for_extraction noextract
let vsig0 (x: V.t) : V.t =
  L.xor64 (L.xor64 (L.rotr64 x 1ul) (L.rotr64 x 8ul)) (V.shr64 x 7ul)

inline_for_extraction noextract
let vsig1 (x: V.t) : V.t =
  L.xor64 (L.xor64 (L.rotr64 x 19ul) (L.rotr64 x 61ul)) (V.shr64 x 6ul)

let sig0 (x: S64.t) : S64.t =
  S64.logxor (S64.logxor (S64.rotate_right x 1ul) (S64.rotate_right x 8ul)) (S64.shift_right x 7ul)

let sig1 (x: S64.t) : S64.t =
  S64.logxor (S64.logxor (S64.rotate_right x 19ul) (S64.rotate_right x 61ul)) (S64.shift_right x 6ul)

let sig0_eq (p: params S64.t) (x: S64.t)
  : Lemma (requires is_sha512 p) (ensures _sigma0 p x == sig0 x) = ()

let sig1_eq (p: params S64.t) (x: S64.t)
  : Lemma (requires is_sha512 p) (ensures _sigma1 p x == sig1 x) = ()

let vsig0_ok (p: params S64.t) (x: V.t) (i: nat { i < 4 })
  : Lemma (requires is_sha512 p) (ensures L.lane_s (vsig0 x) i == _sigma0 p (L.lane_s x i))
  = let r1 = L.rotr64 x 1ul in
    let r2 = L.rotr64 x 8ul in
    let r3 = V.shr64 x 7ul in
    let y = L.xor64 r1 r2 in
    let z = L.xor64 y r3 in
    L.shr64_s x 7ul i;
    assert (L.lane_s y i == S64.logxor (S64.rotate_right (L.lane_s x i) 1ul)
                                       (S64.rotate_right (L.lane_s x i) 8ul));
    assert (L.lane_s z i == S64.logxor (L.lane_s y i) (L.lane_s r3 i));
    sig0_eq p (L.lane_s x i)

let vsig1_ok (p: params S64.t) (x: V.t) (i: nat { i < 4 })
  : Lemma (requires is_sha512 p) (ensures L.lane_s (vsig1 x) i == _sigma1 p (L.lane_s x i))
  = let r1 = L.rotr64 x 19ul in
    let r2 = L.rotr64 x 61ul in
    let r3 = V.shr64 x 6ul in
    let y = L.xor64 r1 r2 in
    let z = L.xor64 y r3 in
    L.shr64_s x 6ul i;
    assert (L.lane_s y i == S64.logxor (S64.rotate_right (L.lane_s x i) 19ul)
                                       (S64.rotate_right (L.lane_s x i) 61ul));
    assert (L.lane_s z i == S64.logxor (L.lane_s y i) (L.lane_s r3 i));
    sig1_eq p (L.lane_s x i)

(** Words [t + 16 .. t + 19] from words [t .. t + 15], held four to a
    register. *)
inline_for_extraction noextract
let next4 (x0 x1 x2 x3: V.t) : V.t =
  let x = V.add64 (V.add64 x0 (vsig0 (L.window64 x0 x1))) (L.window64 x2 x3) in
  let lo = V.add64 x (vsig1 (L.hi_to_lo64 x3)) in
  let hi = V.add64 x (vsig1 (L.lo_to_hi64 lo)) in
  L.blend_lohi64 lo hi

(** The schedule's four-term sum, in the order [next4] adds. *)
let sum4 (s1 w7 s0 w16: S64.t)
  : Lemma (add_mod #S64.t (add_mod #S64.t (add_mod #S64.t s1 w7) s0) w16 ==
           add_mod #S64.t (add_mod #S64.t (add_mod #S64.t w16 s0) w7) s1)
  = let n = pow2 64 in
    let a = S64.v s1 in let b = S64.v w7 in let c = S64.v s0 in let d = S64.v w16 in
    Math.lemma_mod_plus_distr_l (a + b) c n;
    Math.lemma_mod_plus_distr_l ((a + b) % n + c) d n;
    Math.lemma_mod_plus_distr_l (a + b + c) d n;
    Math.lemma_mod_plus_distr_l (d + c) b n;
    Math.lemma_mod_plus_distr_l ((d + c) % n + b) a n;
    Math.lemma_mod_plus_distr_l (d + c + b) a n;
    S64.v_extensional (add_mod #S64.t (add_mod #S64.t (add_mod #S64.t s1 w7) s0) w16)
                      (add_mod #S64.t (add_mod #S64.t (add_mod #S64.t w16 s0) w7) s1)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 20"
let ws_step (p: params S64.t) (b: Seq.lseq S64.t 16) (j: nat)
  : Lemma (requires 16 <= j)
          (ensures ws_at p b j ==
                   add_mod #S64.t (add_mod #S64.t (add_mod #S64.t (ws_at p b (j - 16))
                                                               (_sigma0 p (ws_at p b (j - 15))))
                                                (ws_at p b (j - 7)))
                                 (_sigma1 p (ws_at p b (j - 2))))
  = sum4 (_sigma1 p (ws_at p b (j - 2))) (ws_at p b (j - 7))
         (_sigma0 p (ws_at p b (j - 15))) (ws_at p b (j - 16))
#pop-options

(** What a register holds: as many of the words [j .. j + 3] as there
    are. *)
[@@"opaque_to_smt"]
let reg (p: params S64.t) (b: Seq.lseq S64.t 16) (j: nat) (x: V.t) : prop =
  forall (i: nat). i < 4 /\ j + i < 80 ==> L.lane_s x i == ws_at p b (j + i)

(** What the four registers hold at group [t]. *)
let holds (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (x0 x1 x2 x3: V.t) : prop =
  reg p b t x0 /\ reg p b (t + 4) x1 /\ reg p b (t + 8) x2 /\ reg p b (t + 12) x3

let reg_at (p: params S64.t) (b: Seq.lseq S64.t 16) (j: nat) (x: V.t) (i: nat { i < 4 })
  : Lemma (requires j + i < 80 /\ reg p b j x) (ensures L.lane_s x i == ws_at p b (j + i))
  = reveal_opaque (`%reg) (reg p b j x)

let reg_idx (p: params S64.t) (b: Seq.lseq S64.t 16) (j1 j2: nat) (x: V.t)
  : Lemma (requires j1 == j2 /\ reg p b j1 x) (ensures reg p b j2 x) = ()

let ws_idx (p: params S64.t) (b: Seq.lseq S64.t 16) (j1 j2: nat)
  : Lemma (requires j1 == j2) (ensures ws_at p b j1 == ws_at p b j2) = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let window_lane (lo hi: V.t) (i: nat { i < 4 })
  : Lemma (L.lane_s (L.window64 lo hi) i == (if i < 3 then L.lane_s lo (i + 1) else L.lane_s hi 0))
  = let r = L.window64 lo hi in
    if i = 0 then assert (L.lane_s r 0 == L.lane_s lo 1)
    else if i = 1 then assert (L.lane_s r 1 == L.lane_s lo 2)
    else if i = 2 then assert (L.lane_s r 2 == L.lane_s lo 3)
    else assert (L.lane_s r 3 == L.lane_s hi 0)

let hi_to_lo_lane (a: V.t) (k: nat { k < 2 })
  : Lemma (L.lane_s (L.hi_to_lo64 a) k == L.lane_s a (k + 2))
  = let r = L.hi_to_lo64 a in
    if k = 0 then assert (L.lane_s r 0 == L.lane_s a 2)
    else assert (L.lane_s r 1 == L.lane_s a 3)

let lo_to_hi_lane (a: V.t) (k: nat { 2 <= k /\ k < 4 })
  : Lemma (L.lane_s (L.lo_to_hi64 a) k == L.lane_s a (k - 2))
  = let r = L.lo_to_hi64 a in
    if k = 2 then assert (L.lane_s r 2 == L.lane_s a 0)
    else assert (L.lane_s r 3 == L.lane_s a 1)

let blend_lane (lo hi: V.t) (k: nat { k < 4 })
  : Lemma (L.lane_s (L.blend_lohi64 lo hi) k == (if k < 2 then L.lane_s lo k else L.lane_s hi k))
  = let r = L.blend_lohi64 lo hi in
    if k = 0 then assert (L.lane_s r 0 == L.lane_s lo 0)
    else if k = 1 then assert (L.lane_s r 1 == L.lane_s lo 1)
    else if k = 2 then assert (L.lane_s r 2 == L.lane_s hi 2)
    else assert (L.lane_s r 3 == L.lane_s hi 3)
#pop-options

(** Words [j + 1 .. j + 4]. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let window_reg (p: params S64.t) (b: Seq.lseq S64.t 16) (j: nat) (lo hi: V.t)
  : Lemma (requires j + 8 <= 80 /\ reg p b j lo /\ reg p b (j + 4) hi)
          (ensures reg p b (j + 1) (L.window64 lo hi))
  = reveal_opaque (`%reg) (reg p b (j + 1) (L.window64 lo hi));
    let aux (i: nat { i < 4 }) : Lemma (L.lane_s (L.window64 lo hi) i == ws_at p b (j + 1 + i))
      = window_lane lo hi i;
        if i < 3 then (reg_at p b j lo (i + 1); ws_idx p b (j + (i + 1)) (j + 1 + i))
        else (reg_at p b (j + 4) hi 0; ws_idx p b (j + 4 + 0) (j + 1 + i))
    in
    Classical.forall_intro aux
#pop-options

let ws_step4 (p: params S64.t) (b: Seq.lseq S64.t 16) (t k: nat)
  : Lemma (ws_at p b (t + 16 + k) ==
           add_mod #S64.t (add_mod #S64.t (add_mod #S64.t (ws_at p b (t + k))
                                                       (_sigma0 p (ws_at p b (t + 1 + k))))
                                        (ws_at p b (t + 9 + k)))
                          (_sigma1 p (ws_at p b (t + 14 + k))))
  = ws_step p b (t + 16 + k);
    ws_idx p b (t + 16 + k - 16) (t + k);
    ws_idx p b (t + 16 + k - 15) (t + 1 + k);
    ws_idx p b (t + 16 + k - 7) (t + 9 + k);
    ws_idx p b (t + 16 + k - 2) (t + 14 + k)

let idx_a (p: params S64.t) (b: Seq.lseq S64.t 16) (t k: nat)
  : Lemma (ws_at p b (t + 12 + (k + 2)) == ws_at p b (t + 14 + k))
  = ws_idx p b (t + 12 + (k + 2)) (t + 14 + k)

let idx_b (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (i: nat { 2 <= i })
  : Lemma (ws_at p b (t + 16 + (i - 2)) == ws_at p b (t + 14 + i))
  = ws_idx p b (t + 16 + (i - 2)) (t + 14 + i)

let xsum (x0 x1 x2 x3: V.t) : V.t =
  V.add64 (V.add64 x0 (vsig0 (L.window64 x0 x1))) (L.window64 x2 x3)

let xlo (x0 x1 x2 x3: V.t) : V.t =
  V.add64 (xsum x0 x1 x2 x3) (vsig1 (L.hi_to_lo64 x3))

let xhi (x0 x1 x2 x3: V.t) : V.t =
  V.add64 (xsum x0 x1 x2 x3) (vsig1 (L.lo_to_hi64 (xlo x0 x1 x2 x3)))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
(** Lane [i] of the sum shared by both halves. *)
let partial_ok (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (x0 x1 x2 x3: V.t) (i: nat { i < 4 })
  : Lemma (requires is_sha512 p /\ t + 20 <= 80 /\ holds p b t x0 x1 x2 x3)
          (ensures L.lane_s (xsum x0 x1 x2 x3) i ==
                   add_mod #S64.t (add_mod #S64.t (ws_at p b (t + i)) (_sigma0 p (ws_at p b (t + 1 + i))))
                                  (ws_at p b (t + 9 + i)))
  = window_reg p b t x0 x1;
    reg_idx p b (t + 12) (t + 8 + 4) x3;
    window_reg p b (t + 8) x2 x3;
    reg_idx p b (t + 8 + 1) (t + 9) (L.window64 x2 x3);
    reg_at p b t x0 i;
    reg_at p b (t + 1) (L.window64 x0 x1) i;
    reg_at p b (t + 9) (L.window64 x2 x3) i;
    let w0 = V.add64 x0 (vsig0 (L.window64 x0 x1)) in
    L.add64_s x0 (vsig0 (L.window64 x0 x1)) i;
    L.add64_s w0 (L.window64 x2 x3) i;
    vsig0_ok p (L.window64 x0 x1) i
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let lo_lane (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (x0 x1 x2 x3: V.t) (k: nat { k < 2 })
  : Lemma (requires is_sha512 p /\ t + 20 <= 80 /\ holds p b t x0 x1 x2 x3)
          (ensures L.lane_s (xlo x0 x1 x2 x3) k == ws_at p b (t + 16 + k))
  = partial_ok p b t x0 x1 x2 x3 k;
    L.add64_s (xsum x0 x1 x2 x3) (vsig1 (L.hi_to_lo64 x3)) k;
    vsig1_ok p (L.hi_to_lo64 x3) k;
    hi_to_lo_lane x3 k;
    reg_at p b (t + 12) x3 (k + 2);
    idx_a p b t k;
    ws_step4 p b t k

let hi_lane (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (x0 x1 x2 x3: V.t) (i: nat { 2 <= i /\ i < 4 })
  : Lemma (requires is_sha512 p /\ t + 20 <= 80 /\ holds p b t x0 x1 x2 x3)
          (ensures L.lane_s (xhi x0 x1 x2 x3) i == ws_at p b (t + 16 + i))
  = lo_lane p b t x0 x1 x2 x3 (i - 2);
    idx_b p b t i;
    partial_ok p b t x0 x1 x2 x3 i;
    L.add64_s (xsum x0 x1 x2 x3) (vsig1 (L.lo_to_hi64 (xlo x0 x1 x2 x3))) i;
    vsig1_ok p (L.lo_to_hi64 (xlo x0 x1 x2 x3)) i;
    lo_to_hi_lane (xlo x0 x1 x2 x3) i;
    ws_step4 p b t i

let next4_lane (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (x0 x1 x2 x3: V.t) (i: nat { i < 4 })
  : Lemma (requires is_sha512 p /\ t + 20 <= 80 /\ holds p b t x0 x1 x2 x3)
          (ensures L.lane_s (next4 x0 x1 x2 x3) i == ws_at p b (t + 16 + i))
  = assert (next4 x0 x1 x2 x3 == L.blend_lohi64 (xlo x0 x1 x2 x3) (xhi x0 x1 x2 x3));
    blend_lane (xlo x0 x1 x2 x3) (xhi x0 x1 x2 x3) i;
    if i < 2 then lo_lane p b t x0 x1 x2 x3 i
    else hi_lane p b t x0 x1 x2 x3 i
#pop-options

let tail4 (t: nat)
  : Lemma (requires t % 4 == 0 /\ 80 < t + 20) (ensures 80 <= t + 16) = ()

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let next4_reg (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (x0 x1 x2 x3: V.t)
  : Lemma (requires is_sha512 p /\ t % 4 == 0 /\ t + 4 <= 80 /\ holds p b t x0 x1 x2 x3)
          (ensures reg p b (t + 16) (next4 x0 x1 x2 x3))
  = reveal_opaque (`%reg) (reg p b (t + 16) (next4 x0 x1 x2 x3));
    if t + 20 <= 80 then begin
      let aux (i: nat { i < 4 })
        : Lemma (L.lane_s (next4 x0 x1 x2 x3) i == ws_at p b (t + 16 + i))
        = next4_lane p b t x0 x1 x2 x3 i
      in
      Classical.forall_intro aux
    end
    else tail4 t

let next4_ok (p: params S64.t) (b: Seq.lseq S64.t 16) (t: nat) (x0 x1 x2 x3: V.t)
  : Lemma (requires is_sha512 p /\ t % 4 == 0 /\ t + 4 <= 80 /\ holds p b t x0 x1 x2 x3)
          (ensures holds p b (t + 4) x1 x2 x3 (next4 x0 x1 x2 x3))
  = next4_reg p b t x0 x1 x2 x3;
    reg_idx p b (t + 8) (t + 4 + 4) x2;
    reg_idx p b (t + 12) (t + 4 + 8) x3;
    reg_idx p b (t + 16) (t + 4 + 12) (next4 x0 x1 x2 x3)
#pop-options

(** {2 The rounds} *)

let mk8 (a b c d e f g h: S64.t) : Seq.lseq S64.t 8 =
  set8 (Seq.create 8 a) a b c d e f g h

let t1_of (p: params S64.t) (e f g h wk: S64.t) : S64.t =
  add_mod #S64.t (add_mod #S64.t (add_mod #S64.t h (_Sigma1 p e)) (_Ch e f g)) wk

let t2_of (p: params S64.t) (a b c: S64.t) : S64.t =
  add_mod #S64.t (_Sigma0 p a) (_Maj a b c)

let add_assoc (x k w: S64.t)
  : Lemma (add_mod #S64.t (add_mod #S64.t x k) w == add_mod #S64.t x (add_mod #S64.t k w))
  = let n = pow2 64 in
    Math.lemma_mod_plus_distr_l (S64.v x + S64.v k) (S64.v w) n;
    Math.lemma_mod_plus_distr_r (S64.v x) (S64.v k + S64.v w) n;
    S64.v_extensional (add_mod #S64.t (add_mod #S64.t x k) w)
                      (add_mod #S64.t x (add_mod #S64.t k w))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let round_ok (p: params S64.t) (w: Seq.lseq S64.t (rounds p)) (i: nat { i < rounds p })
             (a b c d e f g h wk: S64.t)
  : Lemma (requires wk == add_mod #S64.t (Seq.index (G.reveal p.k) i) (Seq.index w i))
          (ensures shuffle_core p w i (mk8 a b c d e f g h) ==
                   mk8 (add_mod #S64.t (t1_of p e f g h wk) (t2_of p a b c)) a b c
                       (add_mod #S64.t d (t1_of p e f g h wk)) e f g)
  = add_assoc (add_mod #S64.t (add_mod #S64.t h (_Sigma1 p e)) (_Ch e f g))
              (Seq.index (G.reveal p.k) i) (Seq.index w i);
    let h8 = mk8 a b c d e f g h in
    assert (Seq.index h8 0 == a /\ Seq.index h8 1 == b /\ Seq.index h8 2 == c /\
            Seq.index h8 3 == d /\ Seq.index h8 4 == e /\ Seq.index h8 5 == f /\
            Seq.index h8 6 == g /\ Seq.index h8 7 == h);
    let t1 = t1_of p e f g h wk in
    let t2 = t2_of p a b c in
    set8_irrelevant h8 (Seq.create 8 (add_mod #S64.t t1 t2))
      (add_mod #S64.t t1 t2) a b c (add_mod #S64.t d t1) e f g
#pop-options

let final_ok (h0: Seq.lseq S64.t 8) (a b c d e f g h: S64.t)
  : Lemma (add_state h0 (mk8 a b c d e f g h) ==
           set8 h0 (add_mod #S64.t (Seq.index h0 0) a) (add_mod #S64.t (Seq.index h0 1) b)
                   (add_mod #S64.t (Seq.index h0 2) c) (add_mod #S64.t (Seq.index h0 3) d)
                   (add_mod #S64.t (Seq.index h0 4) e) (add_mod #S64.t (Seq.index h0 5) f)
                   (add_mod #S64.t (Seq.index h0 6) g) (add_mod #S64.t (Seq.index h0 7) h))
  = ()

let state_in (h0: Seq.lseq S64.t 8)
  : Lemma (h0 == mk8 (Seq.index h0 0) (Seq.index h0 1) (Seq.index h0 2) (Seq.index h0 3)
                     (Seq.index h0 4) (Seq.index h0 5) (Seq.index h0 6) (Seq.index h0 7))
  = Seq.lemma_eq_intro h0 (mk8 (Seq.index h0 0) (Seq.index h0 1) (Seq.index h0 2) (Seq.index h0 3)
                               (Seq.index h0 4) (Seq.index h0 5) (Seq.index h0 6) (Seq.index h0 7))

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
inline_for_extraction
fn round ([@@@FStar.Attributes.monomorphize] p: params S64.t)
         (wsb: A.array S64.t) (i: SZ.t)
         (ra rb rc rd re rf rg rh: ref S64.t)
         (#vw: erased (Seq.seq S64.t)) (#w: erased (Seq.lseq S64.t (rounds p)))
         (#a #b #c #d #e #f #g #h: erased S64.t)
requires A.pts_to wsb vw **
         pts_to ra a ** pts_to rb b ** pts_to rc c ** pts_to rd d **
         pts_to re e ** pts_to rf f ** pts_to rg g ** pts_to rh h **
         pure (SZ.v i < rounds p /\ SZ.v i < Seq.length vw /\
               Seq.index vw (SZ.v i) ==
                 add_mod #S64.t (Seq.index (G.reveal p.k) (SZ.v i)) (Seq.index w (SZ.v i)))
ensures exists* a' b' c' d' e' f' g' h'.
         A.pts_to wsb vw **
         pts_to ra a' ** pts_to rb b' ** pts_to rc c' ** pts_to rd d' **
         pts_to re e' ** pts_to rf f' ** pts_to rg g' ** pts_to rh h' **
         pure (mk8 a' b' c' d' e' f' g' h' ==
               shuffle_core p w (SZ.v i) (mk8 a b c d e f g h))
{
  let va = !ra; let vb = !rb; let vc = !rc; let vd = !rd;
  let ve = !re; let vf = !rf; let vg = !rg; let vh = !rh;
  let wk = A.(wsb.(i));
  let t1 = add_mod #S64.t (add_mod #S64.t (add_mod #S64.t vh (_Sigma1 p ve)) (_Ch ve vf vg)) wk;
  let t2 = add_mod #S64.t (_Sigma0 p va) (_Maj va vb vc);
  round_ok p w (SZ.v i) va vb vc vd ve vf vg vh wk;
  rh := vg; rg := vf; rf := ve;
  re := add_mod #S64.t vd t1;
  rd := vc; rc := vb; rb := va;
  ra := add_mod #S64.t t1 t2;
}
#pop-options

(** {2 The block's sixteen words} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"
inline_for_extraction
fn load16 ([@@@FStar.Attributes.monomorphize] p: params S64.t)
          (wsb: A.array S64.t) (block: A.array S8.t) (off: SZ.t)
          (#vw0: erased (Seq.seq S64.t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to block #pb vb **
         pure (Seq.length vw0 == rounds p /\ SZ.v off + block_len #S64.t <= Seq.length vb)
ensures exists* (vw: Seq.seq S64.t). A.pts_to wsb vw ** A.pts_to block #pb vb **
  pure (Seq.length vw == rounds p /\
        (forall (j: nat). j < 16 ==>
           Seq.index vw j == ws_at p (words_from_be block_words (block_at #S64.t vb (SZ.v off))) j))
{
  A.pts_to_len wsb;
  A.pts_to_len block;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vw: Seq.seq S64.t).
    pts_to i vi ** A.pts_to wsb vw ** A.pts_to block #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length vw == rounds p /\
          SZ.v off + block_len #S64.t <= Seq.length vb /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vw j == ws_at p (words_from_be block_words (block_at #S64.t vb (SZ.v off))) j))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (bytes #S64.t) (SZ.v vi + 1) 16;
    Seq.slice_slice vb (SZ.v off) (SZ.v off + block_len #S64.t)
                    (SZ.v vi * bytes #S64.t) (SZ.v vi * bytes #S64.t + bytes #S64.t);
    let x = load_be #S64.t block (SZ.add off (SZ.mul vi 8sz));
    S64.v_extensional x (ws_at p (words_from_be block_words (block_at #S64.t vb (SZ.v off))) (SZ.v vi));
    A.((wsb.(vi) <- x));
    i := SZ.add vi 1sz;
  };
}
#pop-options

(** {2 Four rounds} *)

let init_reg (p: params S64.t) (b: Seq.lseq S64.t 16) (vw: Seq.seq S64.t) (j: nat) (x: V.t)
  : Lemma (requires j + 4 <= 16 /\ Seq.length vw >= 16 /\
                    (forall (i: nat). i < 4 ==> L.lane_s x i == Seq.index vw (j + i)) /\
                    (forall (i: nat). i < 16 ==> Seq.index vw i == ws_at p b i))
          (ensures reg p b j x)
  = reveal_opaque (`%reg) (reg p b j x)

(** What [store64_at] left in slot [t + j]: [k + w] for the round. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let wk_ok (p: params S64.t { rounds p == 80 }) (b: Seq.lseq S64.t 16) (t: nat)
          (vk: Seq.seq S64.t) (kv x0: V.t) (vw: Seq.seq S64.t) (j: nat { j < 4 })
  : Lemma (requires t + 4 <= 80 /\ vk == (G.reveal p.k <: Seq.seq S64.t) /\
                    Seq.length vw == 80 /\ reg p b t x0 /\
                    (forall (i: nat). i < 4 ==> L.lane_s kv i == Seq.index vk (t + i)) /\
                    Seq.index vw (t + j) == L.lane_s (V.add64 kv x0) j)
          (ensures Seq.index vw (t + j) ==
                   add_mod #S64.t (Seq.index (G.reveal p.k) (t + j)) (Seq.index (ws p b) (t + j)))
  = L.add64_s kv x0 j;
    reg_at p b t x0 j
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
inline_for_extraction
fn round_step ([@@@FStar.Attributes.monomorphize] p: params S64.t)
              (wsb: A.array S64.t) (i: SZ.t)
              (ra rb rc rd re rf rg rh: ref S64.t)
              (#vw: erased (Seq.seq S64.t)) (#b: erased (Seq.lseq S64.t 16))
              (#h0: erased (Seq.lseq S64.t 8))
              (#a #bb #c #d #e #f #g #h: erased S64.t)
requires A.pts_to wsb vw **
         pts_to ra a ** pts_to rb bb ** pts_to rc c ** pts_to rd d **
         pts_to re e ** pts_to rf f ** pts_to rg g ** pts_to rh h **
         pure (rounds p == 80 /\ SZ.v i < 80 /\ Seq.length vw == 80 /\
               Seq.index vw (SZ.v i) ==
                 add_mod #S64.t (Seq.index (G.reveal p.k) (SZ.v i)) (Seq.index (ws p b) (SZ.v i)) /\
               mk8 a bb c d e f g h == repeati_g (SZ.v i) (shuffle_core p (ws p b)) h0)
ensures exists* a' b' c' d' e' f' g' h'.
         A.pts_to wsb vw **
         pts_to ra a' ** pts_to rb b' ** pts_to rc c' ** pts_to rd d' **
         pts_to re e' ** pts_to rf f' ** pts_to rg g' ** pts_to rh h' **
         pure (mk8 a' b' c' d' e' f' g' h' == repeati_g (SZ.v i + 1) (shuffle_core p (ws p b)) h0)
{
  let w : erased (Seq.lseq S64.t (rounds p)) = hide (ws p b);
  round p wsb i ra rb rc rd re rf rg rh #vw #w;
  with a' b' c' d' e' f' g' h'. assert (pts_to ra a' ** pts_to rb b' ** pts_to rc c' ** pts_to rd d' **
                                        pts_to re e' ** pts_to rf f' ** pts_to rg g' ** pts_to rh h');
  unfold_repeati_g (SZ.v i) (shuffle_core p (ws p b)) h0;
  assert (pure (mk8 a' b' c' d' e' f' g' h' ==
                shuffle_core p (ws p b) (SZ.v i) (repeati_g (SZ.v i) (shuffle_core p (ws p b)) h0)));
}
#pop-options

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
inline_for_extraction
fn group ([@@@FStar.Attributes.monomorphize] p: params S64.t)
         (kt: A.array S64.t) (wsb: A.array S64.t) (t: SZ.t)
         (x0 x1 x2 x3: ref V.t)
         (ra rb rc rd re rf rg rh: ref S64.t)
         (#pk: perm) (#vk: erased (Seq.seq S64.t)) (#vw: erased (Seq.seq S64.t))
         (#b: erased (Seq.lseq S64.t 16)) (#h0: erased (Seq.lseq S64.t 8))
         (#v0 #v1 #v2 #v3: erased V.t)
         (#a #bb #c #d #e #f #g #h: erased S64.t)
requires A.pts_to kt #pk vk ** A.pts_to wsb vw **
         pts_to x0 v0 ** pts_to x1 v1 ** pts_to x2 v2 ** pts_to x3 v3 **
         pts_to ra a ** pts_to rb bb ** pts_to rc c ** pts_to rd d **
         pts_to re e ** pts_to rf f ** pts_to rg g ** pts_to rh h **
         pure (is_sha512 p /\ reveal vk == (reveal p.k <: Seq.seq S64.t) /\
               Seq.length vw == 80 /\
               SZ.v t + 4 <= 80 /\ SZ.v t % 4 == 0 /\
               holds p b (SZ.v t) v0 v1 v2 v3 /\
               mk8 a bb c d e f g h == repeati_g (SZ.v t) (shuffle_core p (ws p b)) h0)
ensures exists* vw' n0 n1 n2 n3 a' b' c' d' e' f' g' h'.
         A.pts_to kt #pk vk ** A.pts_to wsb vw' **
         pts_to x0 n0 ** pts_to x1 n1 ** pts_to x2 n2 ** pts_to x3 n3 **
         pts_to ra a' ** pts_to rb b' ** pts_to rc c' ** pts_to rd d' **
         pts_to re e' ** pts_to rf f' ** pts_to rg g' ** pts_to rh h' **
         pure (Seq.length vw' == 80 /\
               holds p b (SZ.v t + 4) n0 n1 n2 n3 /\
               mk8 a' b' c' d' e' f' g' h' == repeati_g (SZ.v t + 4) (shuffle_core p (ws p b)) h0)
{
  A.pts_to_len kt;
  let kv = L.load64_at kt t;
  let vx0 = !x0; let vx1 = !x1; let vx2 = !x2; let vx3 = !x3;
  L.store64_at wsb t (V.add64 kv vx0);
  with vw'. assert (A.pts_to wsb vw');
  wk_ok p b (SZ.v t) vk kv vx0 vw' 0;
  wk_ok p b (SZ.v t) vk kv vx0 vw' 1;
  wk_ok p b (SZ.v t) vk kv vx0 vw' 2;
  wk_ok p b (SZ.v t) vk kv vx0 vw' 3;
  next4_ok p b (SZ.v t) vx0 vx1 vx2 vx3;
  x3 := next4 vx0 vx1 vx2 vx3;
  x0 := vx1; x1 := vx2; x2 := vx3;
  round_step p wsb t ra rb rc rd re rf rg rh #vw' #b #h0;
  round_step p wsb (SZ.add t 1sz) ra rb rc rd re rf rg rh #vw' #b #h0;
  round_step p wsb (SZ.add t 2sz) ra rb rc rd re rf rg rh #vw' #b #h0;
  round_step p wsb (SZ.add t 3sz) ra rb rc rd re rf rg rh #vw' #b #h0;
}
#pop-options

(** {2 The block} *)

let finish_ok (p: params S64.t) (blk: Seq.lseq S8.t (block_len #S64.t)) (h0: Seq.lseq S64.t 8)
              (a b c d e f g h: S64.t)
  : Lemma (requires rounds p == 80 /\
                    mk8 a b c d e f g h ==
                      repeati_g 80 (shuffle_core p (ws p (words_from_be block_words blk))) h0)
          (ensures update_block p blk h0 ==
                   set8 h0 (add_mod #S64.t (Seq.index h0 0) a) (add_mod #S64.t (Seq.index h0 1) b)
                           (add_mod #S64.t (Seq.index h0 2) c) (add_mod #S64.t (Seq.index h0 3) d)
                           (add_mod #S64.t (Seq.index h0 4) e) (add_mod #S64.t (Seq.index h0 5) f)
                           (add_mod #S64.t (Seq.index h0 6) g) (add_mod #S64.t (Seq.index h0 7) h))
  = final_ok h0 a b c d e f g h

#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"
[@@CPrologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_prologue "__attribute__((target(\"avx2\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn update_block_avx2 ([@@@FStar.Attributes.monomorphize] p: params S64.t)
                     (kt: A.array S64.t) (wsb: A.array S64.t) (st: A.array S64.t)
                     (block: A.array S8.t) (off: SZ.t)
                     (#pk: perm) (#vk: erased (Seq.seq S64.t))
                     (#vw0: erased (Seq.seq S64.t)) (#vst0: erased (Seq.lseq S64.t 8))
                     (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 **
         A.pts_to block #pb vb **
         pure (is_sha512 p /\ reveal vk == (reveal p.k <: Seq.seq S64.t) /\
               Seq.length vw0 == rounds p /\
               SZ.v off + block_len #S64.t <= Seq.length vb)
ensures exists* (vw: Seq.seq S64.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw **
  A.pts_to st (update_block p (block_at #S64.t vb (SZ.v off)) vst0) **
  A.pts_to block #pb vb ** pure (Seq.length vw == rounds p)
{
  A.pts_to_len st;
  let bw : erased (Seq.lseq S64.t 16) =
    hide (words_from_be block_words (block_at #S64.t vb (SZ.v off)));
  load16 p wsb block off;
  with vw1. assert (A.pts_to wsb vw1);
  let v0 = L.load64_at wsb 0sz;
  let v1 = L.load64_at wsb 4sz;
  let v2 = L.load64_at wsb 8sz;
  let v3 = L.load64_at wsb 12sz;
  init_reg p bw vw1 0 v0;
  init_reg p bw vw1 4 v1;
  init_reg p bw vw1 8 v2;
  init_reg p bw vw1 12 v3;
  let mut x0 = v0; let mut x1 = v1; let mut x2 = v2; let mut x3 = v3;

  let s0 = A.(st.(0sz)); let s1 = A.(st.(1sz)); let s2 = A.(st.(2sz)); let s3 = A.(st.(3sz));
  let s4 = A.(st.(4sz)); let s5 = A.(st.(5sz)); let s6 = A.(st.(6sz)); let s7 = A.(st.(7sz));
  state_in vst0;
  repeati_g_zero (shuffle_core p (ws p bw)) (reveal vst0);
  let mut ra = s0; let mut rb = s1; let mut rc = s2; let mut rd = s3;
  let mut re = s4; let mut rf = s5; let mut rg = s6; let mut rh = s7;

  let mut t = 0sz;
  while (let vt = !t; SZ.lt vt 80sz)
  invariant exists* (vt: SZ.t) (vw: Seq.seq S64.t) n0 n1 n2 n3 a b c d e f g h.
    pts_to t vt ** A.pts_to kt #pk vk ** A.pts_to wsb vw **
    pts_to x0 n0 ** pts_to x1 n1 ** pts_to x2 n2 ** pts_to x3 n3 **
    pts_to ra a ** pts_to rb b ** pts_to rc c ** pts_to rd d **
    pts_to re e ** pts_to rf f ** pts_to rg g ** pts_to rh h **
    pure (SZ.v vt <= 80 /\ SZ.v vt % 4 == 0 /\ Seq.length vw == 80 /\
          holds p bw (SZ.v vt) n0 n1 n2 n3 /\
          mk8 a b c d e f g h == repeati_g (SZ.v vt) (shuffle_core p (ws p bw)) vst0)
  decreases (80 - SZ.v (!t))
  {
    let vt = !t;
    group p kt wsb vt x0 x1 x2 x3 ra rb rc rd re rf rg rh #pk #vk #_ #bw #vst0;
    Math.lemma_mod_plus (SZ.v vt) 1 4;
    t := SZ.add vt 4sz;
  };

  let fa = !ra; let fb = !rb; let fc = !rc; let fd = !rd;
  let fe = !re; let ff = !rf; let fg = !rg; let fh = !rh;
  finish_ok p (block_at #S64.t vb (SZ.v off)) vst0 fa fb fc fd fe ff fg fh;
  A.(st.(0sz) <- add_mod #S64.t s0 fa);
  A.(st.(1sz) <- add_mod #S64.t s1 fb);
  A.(st.(2sz) <- add_mod #S64.t s2 fc);
  A.(st.(3sz) <- add_mod #S64.t s3 fd);
  A.(st.(4sz) <- add_mod #S64.t s4 fe);
  A.(st.(5sz) <- add_mod #S64.t s5 ff);
  A.(st.(6sz) <- add_mod #S64.t s6 fg);
  A.(st.(7sz) <- add_mod #S64.t s7 fh);
}
#pop-options

(** {2 The driver}

    As in [Hacl.Hash.SHA2.NI]: [Hacl.Hash.SHA2.Core]'s [hash_blocks] and
    [hash_impl] specialized to SHA-384/SHA-512 on [update_block_avx2].  The
    padding blocks go through [tail_and_finish] unchanged. *)

(** One step of [hash_blocks_avx2], in a small context: the block it hashes,
    and the size_t facts its offset arithmetic needs. *)
#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
let blocks_avx2_step (p: params S64.t) (pre vin: Seq.seq S8.t) (nprev: nat)
                   (vi2 nfull: SZ.t) (h: Seq.lseq S64.t 8)
  : Lemma (requires Seq.length pre == nprev * block_len #S64.t /\
                    Seq.length pre + Seq.length vin < max_input #S64.t /\
                    SZ.v nfull == Seq.length vin / block_len #S64.t /\
                    SZ.v vi2 < SZ.v nfull /\ SZ.fits (Seq.length vin))
          (ensures SZ.fits (SZ.v vi2 * 128) /\ SZ.fits (SZ.v vi2 + 1) /\
                   SZ.v vi2 * 128 + block_len #S64.t <= Seq.length vin /\
                   update_step p (padded #S64.t (Seq.append pre vin)) (nprev + SZ.v vi2) h ==
                   update_block p (block_at #S64.t vin (SZ.v vi2 * 128)) h)
  = assert_norm (block_len #S64.t == 128);
    hash_blocks_step #S64.t p pre vin nprev (SZ.v vi2) (SZ.v nfull) h;
    SZ.fits_lte (SZ.v vi2 + 1) (SZ.v nfull);
    SZ.fits_lte (SZ.v vi2 * 128) (Seq.length vin)
#pop-options

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"

fn hash_blocks_avx2 ([@@@FStar.Attributes.monomorphize] p: params S64.t)
                  (kt: A.array S64.t) (wsb: A.array S64.t) (st: A.array S64.t)
                  (input: A.array S8.t) (nprev: SZ.t) (nfull: SZ.t)
                  (pre: erased (Seq.seq S8.t))
                  (#pk: perm) (#vk: erased (Seq.seq S64.t))
                  (#vw0: erased (Seq.seq S64.t)) (#vst0: erased (Seq.lseq S64.t 8))
                  (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 **
         A.pts_to input #pin vin **
         pure (is_sha512 p /\ reveal vk == (reveal p.k <: Seq.seq S64.t) /\
               Seq.length vw0 == rounds p /\
               Seq.length pre == SZ.v nprev * block_len #S64.t /\
               Seq.length pre + Seq.length vin < max_input #S64.t /\
               SZ.v nfull == Seq.length vin / block_len #S64.t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #S64.t (Seq.append pre vin)))
                                (reveal p.iv))
ensures exists* (vw: Seq.seq S64.t) (vst: Seq.lseq S64.t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #S64.t /\ Seq.length vw == rounds p /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
{
  A.pts_to_len input;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #S64.t (Seq.append pre vin);
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 nfull)
  invariant exists* (vi2: SZ.t) (vw: Seq.seq S64.t) (vst: Seq.lseq S64.t 8).
    pts_to i vi2 ** A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst **
    A.pts_to input #pin vin **
    pure (SZ.v vi2 <= SZ.v nfull /\ Seq.length vw == rounds p /\
          vst == repeati_g (SZ.v nprev + SZ.v vi2)
                   (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
  decreases (SZ.v nfull - SZ.v (!i))
  {
    let vi2 = !i;
    with vst. assert (A.pts_to st vst);
    blocks_avx2_step p (reveal pre) (reveal vin) (SZ.v nprev) vi2 nfull vst;
    unfold_repeati_g (SZ.v nprev + SZ.v vi2)
      (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv);
    update_block_avx2 p kt wsb st input (SZ.mul vi2 128sz);
    i := SZ.add vi2 1sz;
  };
  with vi2. assert (pts_to i vi2);
  assert (pure (SZ.v vi2 == SZ.v nfull));
}
#pop-options

(** [hash_blocks_avx2] at the type [Hacl.Hash.SHA2.Core.blocks_t]: the
    argument to pass to the streaming hash, [hmac_cat] and HKDF when the
    machine has AVX2. *)
fn blocks_avx2 ([@@@FStar.Attributes.monomorphize] p: params S64.t { is_sha512 p })
             (kt: A.array S64.t) (wsb: A.array S64.t) (st: A.array S64.t) (input: A.array S8.t)
             (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
             (#pk: perm) (#vk: erased (Seq.seq S64.t))
             (#vw0: erased (Seq.seq S64.t)) (#vst0: erased (Seq.lseq S64.t 8))
             (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq S64.t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #S64.t /\
               Seq.length pre + Seq.length vin < max_input #S64.t /\
               SZ.v nfull == Seq.length vin / block_len #S64.t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq S64.t) (vst: Seq.lseq S64.t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #S64.t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
{
  hash_blocks_avx2 p kt wsb st input nprev nfull pre
}

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn hash_impl_avx2 ([@@@FStar.Attributes.monomorphize] p: params S64.t)
                (kt: A.array S64.t) (ivt: A.array S64.t) (out: A.array S8.t)
                (input: A.array S8.t) (len: SZ.t)
                (#pk: perm) (#vk: erased (Seq.seq S64.t))
                (#pi: perm) (#vi: erased (Seq.seq S64.t))
                (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to input #pin vin **
         pure (is_sha512 p /\ reveal vk == (reveal p.k <: Seq.seq S64.t) /\
               reveal vi == (reveal p.iv <: Seq.seq S64.t) /\
               Seq.length vout == hash_bytes p /\
               Seq.length vin < pow2 61 /\ Seq.length vin < max_input #S64.t)
         ** pure (SZ.v len == Seq.length vin)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to input #pin vin **
  pure (Seq.length vin < max_input #S64.t /\ vout' == hash p vin)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len input;
  let nfull = SZ.div len 128sz;
  let rem = SZ.rem len 128sz;
  let z0: S64.t = S64.zero;

  let mut starr = [| z0; 8sz |];
  Mem.track starr;
  A.pts_to_len starr;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq S64.t).
    pts_to c vc ** A.pts_to starr vst ** A.pts_to ivt #pi vi **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==>
             Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq S64.t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(ivt.(vc));
    A.((starr.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq S64.t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq S64.t);

  let mut wsarr = [| z0; p.nrounds |];
  Mem.track wsarr;
  A.pts_to_len wsarr;

  let empty : erased (Seq.seq S8.t) = hide (Seq.empty #S8.t);
  Seq.lemma_eq_elim (Seq.append (reveal empty) (reveal vin)) (reveal vin);
  Math.euclidean_division_definition (SZ.v len) (block_len #S64.t);
  hash_blocks_avx2 p kt wsarr starr input 0sz nfull empty;
  tail_and_finish p kt wsarr starr out input len nfull (SZ.sub len rem) rem empty;
  Mem.wipe wsarr p.nrounds;
  Mem.wipe starr 8sz;
  ()
}
#pop-options

(** {2 The prefixed hash}

    [Hacl.Hash.SHA2.Core.hash_prefixed] specialized, as in
    [Hacl.Hash.SHA2.NI.hash_prefixed_ni]: HMAC's two hashes, each a
    prefix block followed by the caller's message. *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"

fn hash_prefixed_avx2 ([@@@FStar.Attributes.monomorphize] p: params S64.t)
                    (kt: A.array S64.t) (ivt: A.array S64.t) (out: A.array S8.t)
                    (blk: A.array S8.t) (input: A.array S8.t) (lin: SZ.t)
                    (#pk: perm) (#vk: erased (Seq.seq S64.t))
                    (#pi: perm) (#vi: erased (Seq.seq S64.t))
                    (#vout: erased (Seq.seq S8.t))
                    (#pb: perm) (#vb: erased (Seq.seq S8.t))
                    (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to blk #pb vb ** A.pts_to input #pin vin **
         pure (is_sha512 p /\
               reveal vk == (reveal p.k <: Seq.seq S64.t) /\
               reveal vi == (reveal p.iv <: Seq.seq S64.t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vb == block_len #S64.t /\
               SZ.fits (block_len #S64.t + Seq.length vin) /\
               block_len #S64.t + Seq.length vin < pow2 61 /\
               block_len #S64.t + Seq.length vin < max_input #S64.t)
         ** pure (SZ.v lin == Seq.length vin)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to blk #pb vb ** A.pts_to input #pin vin **
  pure (Seq.length vb + Seq.length vin < max_input #S64.t /\
        vout' == hash p (Seq.append vb vin))
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len blk;
  A.pts_to_len input;
  let len = SZ.add 128sz lin;
  let nfull = SZ.div lin 128sz;
  let rem = SZ.rem lin 128sz;
  let z0: S64.t = S64.zero;

  let mut starr = [| z0; 8sz |];
  Mem.track starr;
  A.pts_to_len starr;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq S64.t).
    pts_to c vc ** A.pts_to starr vst ** A.pts_to ivt #pi vi **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==>
             Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq S64.t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(ivt.(vc));
    A.((starr.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq S64.t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq S64.t);

  let mut wsarr = [| z0; p.nrounds |];
  Mem.track wsarr;
  A.pts_to_len wsarr;

  Seq.lemma_len_append (reveal vb) (reveal vin);
  padded_shape #S64.t (Seq.append vb vin);
  padded_index_block #S64.t (Seq.append vb vin) 0;
  append_first_block #S64.t (reveal vb) (reveal vin);
  update_block_avx2 p kt wsarr starr blk 0sz;
  repeati_g_zero (update_step p (padded #S64.t (Seq.append vb vin))) (reveal p.iv);
  unfold_repeati_g 0 (update_step p (padded #S64.t (Seq.append vb vin))) (reveal p.iv);

  Math.lemma_mod_plus (SZ.v lin) 1 (block_len #S64.t);
  assert (pure (SZ.v rem == SZ.v len % block_len #S64.t));
  Math.euclidean_division_definition (SZ.v lin) (block_len #S64.t);
  Math.distributivity_add_left 1 (SZ.v nfull) (block_len #S64.t);
  assert (pure (SZ.v len - SZ.v rem == (1 + SZ.v nfull) * block_len #S64.t));
  Math.multiply_fractions (SZ.v lin) (block_len #S64.t);
  Math.lemma_mult_le_left (SZ.v nfull) 1 (block_len #S64.t);
  SZ.fits_lte (1 + SZ.v nfull) (block_len #S64.t + SZ.v lin);

  hash_blocks_avx2 p kt wsarr starr input 1sz nfull vb;
  let nb = SZ.add 1sz nfull;
  let base_in = SZ.sub lin rem;
  tail_and_finish p kt wsarr starr out input len nb base_in rem vb;

  Mem.wipe wsarr p.nrounds;
  Mem.wipe starr 8sz;
  ()
}

#pop-options
