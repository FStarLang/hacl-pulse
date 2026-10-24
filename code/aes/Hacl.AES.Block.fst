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

(** The AES block cipher, on whichever implementation the machine has.

    [Hacl.AES.Cipher.cipher_portable] computes the S-box from its algebraic
    definition and runs anywhere; [Hacl.AES.NI.cipher_ni] is one [AESENC] per
    round and needs the AES instructions.  The two have the same
    postcondition, so this dispatcher has nothing to prove: both branches
    leave the same specification value behind, and no caller can tell which
    ran.

    The test is per block rather than per message.  That is one perfectly
    predicted branch against a whole block encryption, which is not
    measurable, and it buys the property that {i every} caller -- CTR, GCM,
    and anything added later -- gets the fast path without a dispatching
    variant of its own.

    Feature detection itself is [__builtin_cpu_supports], which reads a
    cached CPUID result. *)
module Hacl.AES.Block

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core
open Hacl.AES.Counter

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Vec = Hacl.Vec128
module Copy = Hacl.Impl.Copy
module IO = Hacl.Impl.InOut

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn cipher_impl ([@@@FStar.Attributes.monomorphize] p: params)
               (st: A.array S8.t) (w: A.array S8.t)
               (#v0 #vw: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to w vw ** pure (
  Seq.length v0 == blocklen /\ Seq.length vw == xkeylen p.pv)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 ** A.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length v0 == blocklen /\
  Seq.length v1 == blocklen /\
  vals v1 == cipher p.pv (vals vw) (vals v0))
{
  if (Hacl.X64.x86_64) {
    if Vec.supported () {
      Hacl.AES.NI.cipher_ni p st w;
    } else {
      Hacl.AES.Cipher.cipher_portable p st w;
    }
  } else {
    Hacl.AES.Cipher.cipher_portable p st w;
  }
}

(** {2 One counter-mode block}

    Counter mode's inner step -- encrypt the counter, exclusive-or the result
    into the message -- rather than just the block cipher.  Keeping it whole
    is what lets the fast path hold the keystream in a register from the
    moment it is produced to the moment it is consumed; see
    [Hacl.AES.NI.ctr_block_ni] for why that matters.  The portable path has
    to write the keystream down, so it takes a sixteen-byte scratch array,
    which the fast path ignores.  Only a caller with a whole block left may
    use this. *)

fn xor_at (out inp: A.array S8.t) (idx: SZ.t) (ka: A.array S8.t)
          (#pi: perm) (#pos: erased nat) (#vo #vi: erased (Seq.seq S8.t))
          (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires IO.inout out inp pi pos vo vi ** A.pts_to ka #pk vk ** pure (
  Seq.length vk == blocklen /\ pos == SZ.v idx /\
  Seq.length vo == Seq.length vi /\ SZ.v idx + blocklen <= Seq.length vi)
ensures exists* (vo': Seq.seq S8.t).
  IO.inout out inp pi (pos + blocklen) vo' vi ** A.pts_to ka #pk vk ** pure (
  Seq.length vk == blocklen /\ SZ.v idx + blocklen <= Seq.length vi /\
  Seq.length vo' == Seq.length vo /\
  (forall (k: nat). k < Seq.length vo ==>
     Seq.index (vals vo') k ==
       (if SZ.v idx <= k && k < SZ.v idx + blocklen
        then Seq.index (vals vi) k ^^ Seq.index (vals vk) (k - SZ.v idx)
        else Seq.index (vals vo) k)))
{
  IO.inout_len out inp;
  A.pts_to_len ka;
  let mut t = 0sz;
  while (let vt = !t; SZ.lt vt 16sz)
  invariant exists* (vt: SZ.t) (p1: nat) (vo1: Seq.seq S8.t).
    pts_to t vt ** IO.inout out inp pi p1 vo1 vi ** A.pts_to ka #pk vk **
    pure (SZ.v vt <= blocklen /\ p1 == SZ.v idx + SZ.v vt /\
          Seq.length vk == blocklen /\
          SZ.v idx + blocklen <= Seq.length vi /\
          Seq.length vo1 == Seq.length vo /\
          (forall (k: nat). k < Seq.length vo ==>
             Seq.index (vals vo1) k ==
               (if SZ.v idx <= k && k < SZ.v idx + SZ.v vt
                then Seq.index (vals vi) k ^^ Seq.index (vals vk) (k - SZ.v idx)
                else Seq.index (vals vo) k)))
  decreases (blocklen - SZ.v (!t))
  {
    let vt = !t;
    let i = SZ.add idx vt;
    let a = IO.read_in out inp i;
    let b = A.(ka.(vt));
    let y = bxor a b;
    with (p1: nat) (vo1: Seq.seq S8.t). assert IO.inout out inp pi p1 vo1 vi;
    vals_upd vo1 (SZ.v i) y;
    IO.write_out out inp i y;
    t := SZ.add vt 1sz;
  };
  with (p1: nat) (vo1: Seq.seq S8.t). assert IO.inout out inp pi p1 vo1 vi;
  rewrite IO.inout out inp pi p1 vo1 vi as IO.inout out inp pi (pos + blocklen) vo1 vi;
  ()
}

fn ctr_block_impl ([@@@FStar.Attributes.monomorphize] p: params)
                  (out inp: A.array S8.t) (idx: SZ.t) (w: A.array S8.t)
                  (ctr: A.array S8.t) (ka: A.array S8.t)
                  (#pi: perm) (#pos: erased nat) (#vo #vi: erased (Seq.seq S8.t))
                  (#vw #vc #vk: erased (Seq.seq S8.t))
requires IO.inout out inp pi pos vo vi ** A.pts_to w vw ** A.pts_to ctr vc ** A.pts_to ka vk **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vk == blocklen /\ pos == SZ.v idx /\
        Seq.length vo == Seq.length vi /\ SZ.v idx + blocklen <= Seq.length vi)
ensures exists* (vo' vk': Seq.seq S8.t).
  IO.inout out inp pi (pos + blocklen) vo' vi ** A.pts_to w vw ** A.pts_to ctr vc ** A.pts_to ka vk' **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vk' == blocklen /\ SZ.v idx + blocklen <= Seq.length vi /\
        Seq.length vo' == Seq.length vo /\
        (forall (k: nat). k < Seq.length vo ==>
           Seq.index (vals vo') k ==
             (if SZ.v idx <= k && k < SZ.v idx + blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (vals vc)) (k - SZ.v idx)
              else Seq.index (vals vo) k)))
{
  A.pts_to_len ctr;
  A.pts_to_len ka;
  if (Hacl.X64.x86_64) {
    if Vec.supported () {
      Hacl.AES.NI.ctr_block_ni p out inp idx w ctr;
    } else {
      Copy.copy_exact ka ctr 16sz;
      Hacl.AES.Cipher.cipher_portable p ka w;
      xor_at out inp idx ka;
    }
  } else {
    Copy.copy_exact ka ctr 16sz;
    Hacl.AES.Cipher.cipher_portable p ka w;
    xor_at out inp idx ka;
  }
}


(** {2 Four counter-mode blocks}

    Counter mode's blocks are independent, so the machine can have four of
    them in flight at once.  On the AES-NI path that is what makes the
    difference between running at the latency of one chain of [AESENC] and
    running at the throughput of the cipher unit; see
    [Hacl.AES.NI.ctr_block4_ni].  The portable path has nothing to gain from
    it, so it simply does four single blocks, and the two branches meet at
    the same postcondition. *)

(** The portable branch of {!ctr_block4_impl}: four single blocks. *)
inline_for_extraction
fn ctr_block4_portable ([@@@FStar.Attributes.monomorphize] p: params)
                   (out inp: A.array S8.t) (idx: SZ.t) (w: A.array S8.t)
                   (ctr: A.array S8.t) (ka: A.array S8.t)
                   (#pi: perm) (#pos: erased nat) (#vo #vi: erased (Seq.seq S8.t))
                   (#vw #vc #vk: erased (Seq.seq S8.t))
requires IO.inout out inp pi pos vo vi ** A.pts_to w vw ** A.pts_to ctr vc ** A.pts_to ka vk **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vk == blocklen /\ pos == SZ.v idx /\
        Seq.length vo == Seq.length vi /\ SZ.fits (SZ.v idx + 4 * blocklen) /\
        SZ.v idx + 4 * blocklen <= Seq.length vi)
ensures exists* (vo' vc' vk': Seq.seq S8.t).
  IO.inout out inp pi (pos + 4 * blocklen) vo' vi ** A.pts_to w vw ** A.pts_to ctr vc' ** A.pts_to ka vk' **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vc' == blocklen /\ Seq.length vk' == blocklen /\
        SZ.v idx + 4 * blocklen <= Seq.length vi /\
        Seq.length vo' == Seq.length vo /\
        vals vc' == counter_block (vals vc) 4 /\
        (forall (k: nat). k < Seq.length vo ==>
           Seq.index (vals vo') k ==
             (if SZ.v idx <= k && k < SZ.v idx + blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 0))
                             (k - SZ.v idx)
              else if SZ.v idx + blocklen <= k && k < SZ.v idx + 2 * blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 1))
                             (k - SZ.v idx - blocklen)
              else if SZ.v idx + 2 * blocklen <= k && k < SZ.v idx + 3 * blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 2))
                             (k - SZ.v idx - 2 * blocklen)
              else if SZ.v idx + 3 * blocklen <= k && k < SZ.v idx + 4 * blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 3))
                             (k - SZ.v idx - 3 * blocklen)
              else Seq.index (vals vo) k)))
{
  IO.inout_len out inp;
  A.pts_to_len ctr;
  A.pts_to_len ka;
  counter_unfold (vals vc);
  let i1 = SZ.add idx 16sz;
  let i2 = SZ.add idx 32sz;
  let i3 = SZ.add idx 48sz;

  ctr_block_impl p out inp idx w ctr ka;
  with vmA. assert IO.inout out inp pi (pos + blocklen) vmA vi;
  assert (pure (Seq.length vmA == Seq.length vo /\
    (forall (k: nat). k < Seq.length vo ==>
       Seq.index (vals vmA) k ==
         (if SZ.v idx <= k && k < SZ.v idx + blocklen
          then Seq.index (vals vi) k ^^
               Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 0))
                         (k - SZ.v idx)
          else Seq.index (vals vo) k))));
  inc32_impl ctr;

  ctr_block_impl p out inp i1 w ctr ka;
  with vmB. assert IO.inout out inp pi (pos + blocklen + blocklen) vmB vi;
  assert (pure (Seq.length vmB == Seq.length vo /\
    (forall (k: nat). k < Seq.length vo ==>
       Seq.index (vals vmB) k ==
         (if SZ.v i1 <= k && k < SZ.v i1 + blocklen
          then Seq.index (vals vi) k ^^
               Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 1))
                         (k - SZ.v i1)
          else Seq.index (vals vmA) k))));
  inc32_impl ctr;

  ctr_block_impl p out inp i2 w ctr ka;
  with vmC. assert IO.inout out inp pi (pos + blocklen + blocklen + blocklen) vmC vi;
  assert (pure (Seq.length vmC == Seq.length vo /\
    (forall (k: nat). k < Seq.length vo ==>
       Seq.index (vals vmC) k ==
         (if SZ.v i2 <= k && k < SZ.v i2 + blocklen
          then Seq.index (vals vi) k ^^
               Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 2))
                         (k - SZ.v i2)
          else Seq.index (vals vmB) k))));
  inc32_impl ctr;

  ctr_block_impl p out inp i3 w ctr ka;
  with vmD. assert IO.inout out inp pi (pos + blocklen + blocklen + blocklen + blocklen) vmD vi;
  assert (pure (Seq.length vmD == Seq.length vo /\
    (forall (k: nat). k < Seq.length vo ==>
       Seq.index (vals vmD) k ==
         (if SZ.v i3 <= k && k < SZ.v i3 + blocklen
          then Seq.index (vals vi) k ^^
               Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 3))
                         (k - SZ.v i3)
          else Seq.index (vals vmC) k))));
  inc32_impl ctr;
  rewrite IO.inout out inp pi (pos + blocklen + blocklen + blocklen + blocklen) vmD vi
       as IO.inout out inp pi (pos + 4 * blocklen) vmD vi;
  ()
}

fn ctr_block4_impl ([@@@FStar.Attributes.monomorphize] p: params)
                   (out inp: A.array S8.t) (idx: SZ.t) (w: A.array S8.t)
                   (ctr: A.array S8.t) (ka: A.array S8.t)
                   (#pi: perm) (#pos: erased nat) (#vo #vi: erased (Seq.seq S8.t))
                   (#vw #vc #vk: erased (Seq.seq S8.t))
requires IO.inout out inp pi pos vo vi ** A.pts_to w vw ** A.pts_to ctr vc ** A.pts_to ka vk **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vk == blocklen /\ pos == SZ.v idx /\
        Seq.length vo == Seq.length vi /\ SZ.fits (SZ.v idx + 4 * blocklen) /\
        SZ.v idx + 4 * blocklen <= Seq.length vi)
ensures exists* (vo' vc' vk': Seq.seq S8.t).
  IO.inout out inp pi (pos + 4 * blocklen) vo' vi ** A.pts_to w vw ** A.pts_to ctr vc' ** A.pts_to ka vk' **
  pure (Seq.length vw == xkeylen p.pv /\ Seq.length vc == blocklen /\
        Seq.length vc' == blocklen /\ Seq.length vk' == blocklen /\
        SZ.v idx + 4 * blocklen <= Seq.length vi /\
        Seq.length vo' == Seq.length vo /\
        vals vc' == counter_block (vals vc) 4 /\
        (forall (k: nat). k < Seq.length vo ==>
           Seq.index (vals vo') k ==
             (if SZ.v idx <= k && k < SZ.v idx + blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 0))
                             (k - SZ.v idx)
              else if SZ.v idx + blocklen <= k && k < SZ.v idx + 2 * blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 1))
                             (k - SZ.v idx - blocklen)
              else if SZ.v idx + 2 * blocklen <= k && k < SZ.v idx + 3 * blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 2))
                             (k - SZ.v idx - 2 * blocklen)
              else if SZ.v idx + 3 * blocklen <= k && k < SZ.v idx + 4 * blocklen
              then Seq.index (vals vi) k ^^
                   Seq.index (cipher p.pv (vals vw) (counter_block (vals vc) 3))
                             (k - SZ.v idx - 3 * blocklen)
              else Seq.index (vals vo) k)))
{
  IO.inout_len out inp;
  A.pts_to_len ctr;
  A.pts_to_len ka;
  counter_unfold (vals vc);
  if (Hacl.X64.x86_64) {
    if Vec.supported () {
      Hacl.AES.NI.ctr_block4_ni p out inp idx w ctr;
    } else {
      ctr_block4_portable p out inp idx w ctr ka;
    }
  } else {
    ctr_block4_portable p out inp idx w ctr ka;
  }
}

#pop-options
