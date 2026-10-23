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

(** Counter mode: the keystream that [Hacl.AES.Counter.inc32] drives, and
    encryption against it, in place or into a disjoint output.

    The driver is three loops rather than one.  The first takes four blocks
    at a time, so that four independent chains of [AESENC] are in flight
    together and the cipher runs at the throughput of the hardware rather
    than at the latency of one chain.  The second takes single whole blocks,
    for the at most three that are left.  The third handles the at most one
    partial block, a byte at a time, through a scratch keystream block.

    The first two never write the keystream down at all; only the third
    needs it in memory.  [Spec.AES.ctr_keystream] is stated pointwise, which
    is what lets all three loops share one invariant. *)
module Hacl.AES.CTR

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core
open Hacl.AES.Cipher
open Hacl.AES.Block
open Hacl.AES.Counter

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module Copy = Hacl.Impl.Copy
module Mem = Hacl.Mem
module IO = Hacl.Impl.InOut

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"


(** {2 The pure side of the keystream} *)

#push-options "--fuel 1 --ifuel 1"
let counter_block_zero (b: block) : Lemma (counter_block b 0 == b) = ()

let counter_block_step (b: block) (j: nat)
  : Lemma (counter_block b (j + 1) == inc32 (counter_block b j)) = ()
#pop-options

let ks_index (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
             (n: nat) (j: nat) (bi: nat) (t: nat)
  : Lemma (requires j == 16 * bi /\ t < 16 /\ j + t < n)
          (ensures ctr_keystream v w b n (j + t) ==
                   Seq.index (cipher v w (counter_block b bi)) t)
  = Math.lemma_div_plus t bi 16; Math.small_div t 16;
    Math.lemma_mod_plus t bi 16; Math.small_mod t 16

(** The same, for every byte of a whole block at once: what the fused
    counter-mode step establishes, in the terms the loop invariant wants. *)
let ks_index_all (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                 (n: nat) (j: nat) (bi: nat)
  : Lemma (requires j == 16 * bi /\ j + 16 <= n)
          (ensures Seq.length (cipher v w (counter_block b bi)) == blocklen /\
                   (forall (t: nat). t < 16 /\ j + t < n ==>
                      ctr_keystream v w b n (j + t) ==
                        Seq.index (cipher v w (counter_block b bi)) t))
  = let aux (t: nat { t < 16 /\ j + t < n })
      : Lemma (ctr_keystream v w b n (j + t) ==
               Seq.index (cipher v w (counter_block b bi)) t)
      = ks_index v w b n j bi t
    in
    FStar.Classical.forall_intro aux

(** [counter_block] counts, so counting from a counter that is itself a
    count is counting from the start. *)
#push-options "--fuel 1 --ifuel 1"
let rec counter_block_add (b: block) (i j: nat)
  : Lemma (ensures counter_block (counter_block b i) j == counter_block b (i + j))
          (decreases j)
  = if j = 0 then () else counter_block_add b i (j - 1)
#pop-options

(** Byte [k] of the [t]-th block of a four-block step is keystream byte
    [k]: the counter of that block is [bi + t], counted from [b]. *)
let ctr4_byte (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
              (n: nat) (j: nat) (bi: nat) (t: nat) (k: nat)
  : Lemma (requires j == 16 * bi /\ j + 16 * t <= k /\ k < j + 16 * t + 16 /\ k < n)
          (ensures ctr_keystream v w b n k ==
                   Seq.index (cipher v w (counter_block (counter_block b bi) t))
                             (k - j - 16 * t))
  = counter_block_add b bi t;
    Math.distributivity_add_right 16 bi t;
    let j' = j + 16 * t in
    let u = k - j' in
    assert (j' == 16 * (bi + t));
    assert (j' + u == k);
    assert (k - j - 16 * t == u);
    ks_index v w b n j' (bi + t) u

(** One step of the four-block loop, on the pure side.

    [m0] is the input, [m] the output as the invariant has it after [j]
    bytes, [m'] what the four-block step left behind, stated against the
    four counter blocks the step itself used; the conclusion is the
    invariant again, sixty-four bytes further on.  It is a lemma rather than
    a run of assertions inside the loop because the case analysis is over a
    single byte index and does not want the rest of the separation-logic
    context anywhere near it. *)
#push-options "--z3rlimit 20"
let ctr4_step (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
              (m0 m m': Seq.seq elem) (n: nat) (j: nat) (bi: nat) (c: block)
  : Lemma (requires
      j == 16 * bi /\ j + 64 <= n /\ Seq.length m0 == n /\
      Seq.length m == n /\ Seq.length m' == n /\ c == counter_block b bi /\
      (forall (k: nat). k < n /\ k < j ==>
         Seq.index m k == Seq.index m0 k ^^ ctr_keystream v w b n k) /\
      (forall (k: nat). k < n ==>
         Seq.index m' k ==
           (if j <= k && k < j + 16
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 0)) (k - j)
            else if j + 16 <= k && k < j + 32
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 1)) (k - j - 16)
            else if j + 32 <= k && k < j + 48
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 2)) (k - j - 32)
            else if j + 48 <= k && k < j + 64
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 3)) (k - j - 48)
            else Seq.index m k)))
    (ensures forall (k: nat). k < n /\ k < j + 64 ==>
       Seq.index m' k == Seq.index m0 k ^^ ctr_keystream v w b n k)
  = let one (t: nat { t < 4 }) (k: nat { j + 16 * t <= k /\ k < j + 16 * t + 16 /\ k < n })
      : Lemma (requires Seq.index m' k == Seq.index m0 k ^^
                          Seq.index (cipher v w (counter_block c t)) (k - j - 16 * t))
              (ensures Seq.index m' k == Seq.index m0 k ^^ ctr_keystream v w b n k)
      = ctr4_byte v w b n j bi t k
    in
    let aux (k: nat { k < n /\ k < j + 64 })
      : Lemma (Seq.index m' k == Seq.index m0 k ^^ ctr_keystream v w b n k)
      = if k < j then () else
        if k < j + 16 then one 0 k else
        if k < j + 32 then one 1 k else
        if k < j + 48 then one 2 k else one 3 k
    in
    FStar.Classical.forall_intro aux
#pop-options

let ctr_done (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
             (m m': Seq.seq elem) (n: nat)
  : Lemma (requires Seq.length m == n /\ Seq.length m' == n /\
             (forall (k: nat). k < n ==>
                Seq.index m' k == Seq.index m k ^^ ctr_keystream v w b n k))
          (ensures m' == ctr_encrypt v w b m)
  = Seq.lemma_eq_intro m' (ctr_encrypt v w b m)


(** {2 The loop invariant, kept away from the solver}

    Every loop of [ctr_encrypt_impl] says the same thing: the first [j]
    bytes of the output are the encryption of the first [j] bytes of the
    input.  Nothing is said of the output past [j]: it is whatever was
    there, which in place is the rest of the input and otherwise anything.
    As a bare quantifier in a Pulse invariant it sits in the context of
    every query of a long function; behind an opaque name it is only
    opened by the lemmas below, each of which does one step of the
    argument. *)
[@@"opaque_to_smt"]
let ctr_inv (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
            (m0 m: Seq.seq elem) (n: nat) (j: nat) : prop =
  Seq.length m0 == n /\ Seq.length m == n /\
  (forall (k: nat). k < n /\ k < j ==>
     Seq.index m k == Seq.index m0 k ^^ ctr_keystream v w b n k)

let ctr_inv_init (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                 (m0 m: Seq.seq elem) (n: nat)
  : Lemma (requires Seq.length m0 == n /\ Seq.length m == n)
          (ensures ctr_inv v w b m0 m n 0)
  = reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n 0)

(** Moving the boundary without touching the output: either it does not
    move, or it moves between two points both past the end. *)
let ctr_inv_ext (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                (m0 m: Seq.seq elem) (n: nat) (j j': nat)
  : Lemma (requires ctr_inv v w b m0 m n j /\ (j == j' \/ (n <= j /\ n <= j')))
          (ensures ctr_inv v w b m0 m n j')
  = reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n j);
    reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n j')

let ctr_inv_len (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                (m0 m: Seq.seq elem) (n: nat) (j: nat)
  : Lemma (requires ctr_inv v w b m0 m n j)
          (ensures Seq.length m0 == n /\ Seq.length m == n)
  = reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n j)

let ctr4_step_inv (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                  (m0 m m': Seq.seq elem) (n: nat) (j: nat) (bi: nat) (c: block)
  : Lemma (requires
      j == 16 * bi /\ j + 64 <= n /\ ctr_inv v w b m0 m n j /\
      Seq.length m0 == n /\ Seq.length m == n /\ Seq.length m' == n /\ c == counter_block b bi /\
      (forall (k: nat). k < n ==>
         Seq.index m' k ==
           (if j <= k && k < j + 16
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 0)) (k - j)
            else if j + 16 <= k && k < j + 32
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 1)) (k - j - 16)
            else if j + 32 <= k && k < j + 48
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 2)) (k - j - 32)
            else if j + 48 <= k && k < j + 64
            then Seq.index m0 k ^^ Seq.index (cipher v w (counter_block c 3)) (k - j - 48)
            else Seq.index m k)))
    (ensures ctr_inv v w b m0 m' n (j + 64))
  = reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n j);
    reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m' n (j + 64));
    ctr4_step v w b m0 m m' n j bi c

let ctr1_step_inv (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                  (m0 m m': Seq.seq elem) (n: nat) (j: nat) (bi: nat) (c: block)
  : Lemma (requires
      j == 16 * bi /\ j + 16 <= n /\ ctr_inv v w b m0 m n j /\
      Seq.length m0 == n /\ Seq.length m == n /\ Seq.length m' == n /\ c == counter_block b bi /\
      (forall (k: nat). k < n ==>
         Seq.index m' k ==
           (if j <= k && k < j + 16
            then Seq.index m0 k ^^ Seq.index (cipher v w c) (k - j)
            else Seq.index m k)))
    (ensures ctr_inv v w b m0 m' n (j + 16))
  = reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n j);
    reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m' n (j + 16));
    let aux (k: nat { k < n /\ k < j + 16 })
      : Lemma (Seq.index m' k == Seq.index m0 k ^^ ctr_keystream v w b n k)
      = if j <= k then ks_index v w b n j bi (k - j) else ()
    in
    FStar.Classical.forall_intro aux

(** One byte of the partial-block loop, pointwise. *)
let ctr_byte_at (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                (m0 m: Seq.seq elem) (n: nat) (j: nat) (bi: nat) (t: nat)
                (x: elem) (k: nat)
  : Lemma (requires
      j == 16 * bi /\ t < 16 /\ j + t < n /\ k < n /\ k < j + t + 1 /\
      Seq.length m == n /\ Seq.length m0 == n /\
      x == Seq.index m0 (j + t) ^^ Seq.index (cipher v w (counter_block b bi)) t /\
      (k < j + t ==> Seq.index m k == Seq.index m0 k ^^ ctr_keystream v w b n k))
    (ensures Seq.index (Seq.upd m (j + t) x) k ==
               Seq.index m0 k ^^ ctr_keystream v w b n k)
  = if k = j + t
    then begin
      Seq.lemma_index_upd1 m (j + t) x;
      ks_index v w b n j bi t
    end
    else Seq.lemma_index_upd2 m (j + t) x k

let ctr_byte_step_inv (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                      (m0 m m': Seq.seq elem) (n: nat) (j: nat) (bi: nat) (t: nat)
                      (x: elem)
  : Lemma (requires
      j == 16 * bi /\ t < 16 /\ j + t < n /\ Seq.length m == n /\
      Seq.length m0 == n /\ ctr_inv v w b m0 m n (j + t) /\
      m' == Seq.upd m (j + t) x /\
      x == Seq.index m0 (j + t) ^^ Seq.index (cipher v w (counter_block b bi)) t)
    (ensures ctr_inv v w b m0 m' n (j + t + 1))
  = reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n (j + t));
    reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m' n (j + t + 1));
    let aux (k: nat { k < n /\ k < j + t + 1 })
      : Lemma (Seq.index m' k == Seq.index m0 k ^^ ctr_keystream v w b n k)
      = ctr_byte_at v w b m0 m n j bi t x k
    in
    FStar.Classical.forall_intro aux

let ctr_inv_done (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                 (m0 m: Seq.seq elem) (n: nat) (j: nat)
  : Lemma (requires ctr_inv v w b m0 m n j /\ n <= j)
          (ensures m == ctr_encrypt v w b m0)
  = reveal_opaque (`%ctr_inv) (ctr_inv v w b m0 m n j);
    ctr_done v w b m0 m n

let start_facts (s: nat)
  : Lemma (requires s % 16 == 0) (ensures s == 16 * (s / 16))
  = Math.euclidean_division_definition s 16


(** {2 Counter mode}

    The output [out] and the input [inp] are related by [Hacl.Impl.InOut.inout]:
    they are either the same array (in place) or disjoint.  Every byte of
    the output is written only after the input byte at the same index has
    been read, and never before the bytes below it, so the two cases need
    no separate code.

    [ctr] holds the initial counter block and is advanced as the loop runs;
    its final value is left unspecified, since every caller either discards
    it or, in GCM's case, has already saved what it needs. *)

(** At most one partial block is left, and it goes through the general
    path: a scratch keystream block and a byte at a time. *)
#push-options "--z3rlimit 40"
inline_for_extraction noextract
fn ctr_tail ([@@@FStar.Attributes.monomorphize] p: params)
            (out inp: A.array S8.t) (n: SZ.t) (w: A.array S8.t)
            (ctr: A.array S8.t) (ka: A.array S8.t) (j bi: SZ.t)
            (b0: erased block)
            (#pi: perm) (#pos: erased nat) (#vo #vm0 #vw #vc #vk: erased (Seq.seq S8.t))
requires IO.inout out inp pi pos vo vm0 ** A.pts_to w vw ** A.pts_to ctr vc **
         A.pts_to ka vk ** pure (
  pos == SZ.v j /\ SZ.v j == 16 * SZ.v bi /\
  SZ.v j <= SZ.v n /\ SZ.v n < SZ.v j + blocklen /\
  Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
  Seq.length vk == blocklen /\
  Seq.length vo == Seq.length vm0 /\ Seq.length vm0 == SZ.v n /\
  SZ.fits (SZ.v n + blocklen) /\
  vals vc == counter_block b0 (SZ.v bi) /\
  ctr_inv p.pv (vals vw) b0 (vals vm0) (vals vo) (SZ.v n) (SZ.v j))
ensures exists* (vo1 vc1 vk1: Seq.seq S8.t).
  IO.inout out inp pi (SZ.v n) vo1 vm0 ** A.pts_to w vw ** A.pts_to ctr vc1 **
  A.pts_to ka vk1 ** pure (
  Seq.length vw == xkeylen p.pv /\
  Seq.length vc1 == blocklen /\ Seq.length vk1 == blocklen /\
  Seq.length vo1 == Seq.length vm0 /\
  vals vo1 == ctr_encrypt p.pv (vals vw) b0 (vals vm0))
{
  if (SZ.lt j n) {
    Copy.copy_exact ka ctr 16sz;
    cipher_impl p ka w;
    with vk1. assert A.pts_to ka vk1;
    let rem = SZ.sub n j;
    let mut t = 0sz;
    while (let vt = !t; SZ.lt vt rem)
    invariant exists* (vt: SZ.t) (q: nat) (vo1: Seq.seq S8.t).
      pts_to t vt ** IO.inout out inp pi q vo1 vm0 ** A.pts_to w vw ** A.pts_to ka vk1 **
      pure (q == SZ.v j + SZ.v vt /\ SZ.v vt <= SZ.v rem /\
            SZ.v rem == SZ.v n - SZ.v j /\ SZ.v rem < blocklen /\
            SZ.v j == 16 * SZ.v bi /\
            SZ.fits (SZ.v n + blocklen) /\ Seq.length vk1 == blocklen /\
            Seq.length vw == xkeylen p.pv /\
            Seq.length vo1 == Seq.length vm0 /\ Seq.length vm0 == SZ.v n /\
            vals vk1 == cipher p.pv (vals vw) (counter_block b0 (SZ.v bi)) /\
            ctr_inv p.pv (vals vw) b0 (vals vm0) (vals vo1) (SZ.v n)
                    (SZ.v j + SZ.v vt))
    decreases (SZ.v rem - SZ.v (!t))
    {
      let vt = !t;
      let idx = SZ.add j vt;
      let a = IO.read_in out inp idx;
      let b = A.(ka.(vt));
      let y = bxor a b;
      with (q: nat) (vo1: Seq.seq S8.t). assert IO.inout out inp pi q vo1 vm0;
      vals_upd vo1 (SZ.v idx) y;
      ctr_byte_step_inv p.pv (vals vw) b0 (vals vm0) (vals vo1)
                        (vals (Seq.upd vo1 (SZ.v idx) y))
                        (SZ.v n) (SZ.v j) (SZ.v bi) (SZ.v vt) (S8.v y);
      IO.write_out out inp idx y;
      t := SZ.add vt 1sz;
    };
    with (q: nat) (vo1: Seq.seq S8.t). assert IO.inout out inp pi q vo1 vm0;
    ctr_inv_done p.pv (vals vw) b0 (vals vm0) (vals vo1) (SZ.v n) q;
    rewrite IO.inout out inp pi q vo1 vm0 as IO.inout out inp pi (SZ.v n) vo1 vm0;
    ()
  } else {
    ctr_inv_done p.pv (vals vw) b0 (vals vm0) (vals vo) (SZ.v n) (SZ.v j);
    rewrite IO.inout out inp pi pos vo vm0 as IO.inout out inp pi (SZ.v n) vo vm0;
    ()
  }
}
#pop-options

#push-options "--z3rlimit 20"

(** Counter mode from byte [start] on, a multiple of the block size, with
    everything below it already done and [ctr] already advanced to it.
    [b0] is the counter block the whole message started from. *)
fn ctr_encrypt_from ([@@@FStar.Attributes.monomorphize] p: params)
                    (out inp: A.array S8.t) (n: SZ.t) (w: A.array S8.t)
                    (ctr: A.array S8.t) (start: SZ.t) (b0: erased block)
                    (#pi: perm) (#pos: erased nat) (#vo0 #vm0 #vw #vc0: erased (Seq.seq S8.t))
requires IO.inout out inp pi pos vo0 vm0 ** A.pts_to w vw ** A.pts_to ctr vc0 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc0 == blocklen /\
  pos == SZ.v start /\ SZ.v start <= SZ.v n /\ SZ.v start % 16 == 0 /\
  Seq.length vo0 == Seq.length vm0 /\ Seq.length vm0 == SZ.v n /\
  SZ.fits (SZ.v n + blocklen) /\
  vals vc0 == counter_block b0 (SZ.v start / 16) /\
  ctr_inv p.pv (vals vw) b0 (vals vm0) (vals vo0) (SZ.v n) (SZ.v start))
ensures exists* (vo1 vc1: Seq.seq S8.t).
  IO.inout out inp pi (SZ.v n) vo1 vm0 ** A.pts_to w vw ** A.pts_to ctr vc1 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc1 == blocklen /\
  Seq.length vo1 == Seq.length vm0 /\
  vals vo1 == ctr_encrypt p.pv (vals vw) b0 (vals vm0))
{
  IO.inout_len out inp;
  A.pts_to_len w;
  A.pts_to_len ctr;
  let z = S8.zero;
  let mut ka = [| z; 16sz |];
  Mem.track ka;
  A.pts_to_len ka;

  (* The largest index a four-block step may start at, plus one.  The bound
     is computed rather than tested for in the guard because [n] may be
     within sixty-four of the largest representable size, so [j + 64] is not
     in general a size at all. *)
  let mut limr = 0sz;
  if SZ.lte 64sz n {
    limr := SZ.sub n 63sz;
  };
  let lim = !limr;
  assert (pure (SZ.v lim <= SZ.v n /\
                (forall (x: nat). x < SZ.v lim ==> x + 64 <= SZ.v n)));

  start_facts (SZ.v start);
  let mut j = start;
  let mut bi = SZ.div start 16sz;
  (* Four blocks at a time.  This is the loop that does nearly all of the
     work on any message worth measuring: four independent chains of rounds
     run through one shared round-key loop, so the cipher unit stays busy
     instead of waiting on the latency of a single chain.  See
     [Hacl.AES.Block.ctr_block4_impl]. *)
  while (let vj = !j; SZ.lt vj lim)
  invariant exists* (vj: SZ.t) (vbi: SZ.t) (q: nat) (vo: Seq.seq S8.t)
                    (vc: Seq.seq S8.t) (vk: Seq.seq S8.t).
    pts_to j vj ** pts_to bi vbi ** IO.inout out inp pi q vo vm0 ** A.pts_to w vw **
    A.pts_to ctr vc ** A.pts_to ka vk **
    pure (q == SZ.v vj /\ SZ.v vj == 16 * SZ.v vbi /\ Seq.length vk == blocklen /\
          Seq.length vw == xkeylen p.pv /\
          Seq.length vc == blocklen /\
          Seq.length vo == Seq.length vm0 /\ Seq.length vm0 == SZ.v n /\
          SZ.fits (SZ.v n + blocklen) /\ SZ.v vj <= SZ.v n /\
          vals vc == counter_block b0 (SZ.v vbi) /\
          ctr_inv p.pv (vals vw) b0 (vals vm0) (vals vo) (SZ.v n) (SZ.v vj))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let vbi = !bi;
    SZ.fits_lte (SZ.v vj + 4 * blocklen) (SZ.v n + blocklen);
    with vc. assert A.pts_to ctr vc;
    with (q: nat) (vo: Seq.seq S8.t). assert IO.inout out inp pi q vo vm0;
    ctr_block4_impl p out inp vj w ctr ka;
    with vo2. assert IO.inout out inp pi (q + 4 * blocklen) vo2 vm0;
    ctr_inv_len p.pv (vals vw) b0 (vals vm0) (vals vo) (SZ.v n) (SZ.v vj);
    ctr4_step_inv p.pv (vals vw) b0 (vals vm0) (vals vo) (vals vo2)
                  (SZ.v n) (SZ.v vj) (SZ.v vbi) (vals vc);
    counter_block_add b0 (SZ.v vbi) 4;
    j := SZ.add vj 64sz;
    bi := SZ.add vbi 4sz;
  };

  (* At most three whole blocks are left.  The keystream is still never
     written down: the counter is encrypted into a register and exclusive-
     ored straight into the output.  See [Hacl.AES.NI.ctr_block_ni]. *)
  while (let vj = !j; SZ.lte (SZ.add vj 16sz) n)
  invariant exists* (vj: SZ.t) (vbi: SZ.t) (q: nat) (vo: Seq.seq S8.t)
                    (vc: Seq.seq S8.t) (vk: Seq.seq S8.t).
    pts_to j vj ** pts_to bi vbi ** IO.inout out inp pi q vo vm0 ** A.pts_to w vw **
    A.pts_to ctr vc ** A.pts_to ka vk **
    pure (q == SZ.v vj /\ SZ.v vj == 16 * SZ.v vbi /\ Seq.length vk == blocklen /\
          Seq.length vw == xkeylen p.pv /\
          Seq.length vc == blocklen /\
          Seq.length vo == Seq.length vm0 /\ Seq.length vm0 == SZ.v n /\
          SZ.fits (SZ.v n + blocklen) /\ SZ.v vj <= SZ.v n /\
          vals vc == counter_block b0 (SZ.v vbi) /\
          ctr_inv p.pv (vals vw) b0 (vals vm0) (vals vo) (SZ.v n) (SZ.v vj))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let vbi = !bi;
    SZ.fits_lte (SZ.v vj + blocklen) (SZ.v n + blocklen);
    with vc. assert A.pts_to ctr vc;
    with (q: nat) (vo: Seq.seq S8.t). assert IO.inout out inp pi q vo vm0;
    ctr_inv_len p.pv (vals vw) b0 (vals vm0) (vals vo) (SZ.v n) (SZ.v vj);
    ctr_block_impl p out inp vj w ctr ka;
    with vo2. assert IO.inout out inp pi (q + blocklen) vo2 vm0;
    ctr1_step_inv p.pv (vals vw) b0 (vals vm0) (vals vo) (vals vo2)
                  (SZ.v n) (SZ.v vj) (SZ.v vbi) (vals vc);
    counter_block_step b0 (SZ.v vbi);
    inc32_impl ctr;
    j := SZ.add vj 16sz;
    bi := SZ.add vbi 1sz;
  };

  let vj = !j;
  let vbi = !bi;
  ctr_tail p out inp n w ctr ka vj vbi b0;
  Mem.wipe ka 16sz;
  ()
}

(** Counter mode over the whole message, from [ctr]'s initial value.
    [out] is the same array as [inp] or disjoint from it. *)
fn ctr_encrypt_impl ([@@@FStar.Attributes.monomorphize] p: params)
                    (out inp: A.array S8.t) (n: SZ.t) (w: A.array S8.t) (ctr: A.array S8.t)
                    (#pi: perm) (#vo0 #vm0 #vw #vc0: erased (Seq.seq S8.t))
requires IO.inout out inp pi 0 vo0 vm0 ** A.pts_to w vw ** A.pts_to ctr vc0 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc0 == blocklen /\
  Seq.length vo0 == Seq.length vm0 /\
  SZ.fits (Seq.length vm0 + blocklen))
         ** pure (SZ.v n == Seq.length vm0)
ensures exists* (vo1 vc1: Seq.seq S8.t).
  IO.inout out inp pi (SZ.v n) vo1 vm0 ** A.pts_to w vw ** A.pts_to ctr vc1 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vc0 == blocklen /\
  Seq.length vc1 == blocklen /\ Seq.length vo1 == Seq.length vm0 /\
  vals vo1 == ctr_encrypt p.pv (vals vw) (vals vc0) (vals vm0))
{
  A.pts_to_len ctr;
  counter_block_zero (vals vc0);
  ctr_inv_init p.pv (vals vw) (vals vc0) (vals vm0) (vals vo0) (SZ.v n);
  ctr_encrypt_from p out inp n w ctr 0sz (vals vc0);
  ()
}

#pop-options

#pop-options
