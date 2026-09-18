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

(** SEC1 point formats.

    Three of the four conversions are byte shuffling.  The fourth recovers
    [y] from [x] and a parity bit, which takes a square root; [p = 3 mod 4],
    so one exponentiation settles it and, unlike Ed25519, there is no second
    candidate to try.

    Note what is and is not checked, because the API has to match HACL*'s:
    [uncompressed_to_raw] validates the header and nothing else, and the
    [raw_to_*] pair validates nothing at all. *)
module Hacl.P256.Sec1

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Spec.Bytes
open Hacl.Impl.Copy
open Hacl.P256.Field
open Hacl.P256.Inverse
open Hacl.P256.Encode

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module Declassify = Hacl.Secret.Declassify
module UInt = FStar.UInt

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Adding a header}

    [0x04] for the uncompressed form, [0x02] or [0x03] for the compressed
    one according to the parity of [y].  That parity is the parity of the
    last byte, so no arithmetic on the coordinate is needed -- and the
    header is computed rather than branched on, which costs nothing and
    keeps the shape of the code the same as everywhere else. *)

(** A Pulse [ensures] is elaborated with no [requires] in scope, so the
    length of the input cannot be assumed there.  Each specification
    function therefore travels in a total wrapper that carries it. *)
let r2u (vp: Seq.seq S8.t) : GTot (Seq.lseq S8.t 65) =
  if Seq.length vp = 64 then P.raw_to_uncompressed vp
  else Seq.create 65 (S8.classify 0uy)

let r2c (vp: Seq.seq S8.t) : GTot (Seq.lseq S8.t 33) =
  if Seq.length vp = 64 then P.raw_to_compressed vp
  else Seq.create 33 (S8.classify 0uy)

let u2r (vp: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vp = 65 then P.uncompressed_to_raw vp else None

fn raw_to_uncompressed (out pk: A.array S8.t)
                       (#vo: erased (Seq.seq S8.t))
                       (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to pk #pp vp **
  pure (Seq.length vo == 65 /\ Seq.length vp == 64)
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to pk #pp vp **
  pure (Seq.length wo == 65 /\ wo == r2u vp)
{
  A.pts_to_len out; A.pts_to_len pk;
  A.((out.(0sz) <- (S8.classify 4uy)));
  copy_at out 1sz pk 64sz;
  with wo. assert (A.pts_to out wo);
  A.pts_to_len out;
  assert (pure (Seq.equal wo (Seq.append (Seq.create 1 (S8.classify 4uy)) vp)));
}

fn raw_to_compressed (out pk: A.array S8.t)
                     (#vo: erased (Seq.seq S8.t))
                     (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to pk #pp vp **
  pure (Seq.length vo == 33 /\ Seq.length vp == 64)
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to pk #pp vp **
  pure (Seq.length wo == 33 /\ wo == r2c vp)
{
  A.pts_to_len out; A.pts_to_len pk;
  let lb = A.(pk.(63sz));
  UInt.logand_mask #8 (S8.v lb) 1;
  assert_norm (pow2 1 - 1 == 1);
  be_nat_parity (Seq.slice vp 32 64);
  let h = S8.add_mod (S8.classify 2uy) (S8.logand lb (S8.classify 1uy));
  A.((out.(0sz) <- h));
  copy_at out 1sz pk 32sz;
  with wo. assert (A.pts_to out wo);
  A.pts_to_len out;
  assert (pure (Seq.equal wo
    (Seq.append (Seq.create 1 h) (Seq.slice vp 0 32))));
}

(** {2 Stripping a header}

    The header is public metadata, so reading it as a plain byte is not a
    leak -- but it is a declassification, and those are spelled out. *)

fn uncompressed_to_raw (out pk: A.array S8.t)
                       (#vo: erased (Seq.seq S8.t))
                       (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to pk #pp vp **
  pure (Seq.length vo == 64 /\ Seq.length vp == 65)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to pk #pp vp **
  pure (Seq.length wo == 64 /\ r == Some? (u2r vp) /\
        (r ==> wo == Some?.v (u2r vp)))
{
  A.pts_to_len out; A.pts_to_len pk;
  let h = Declassify.u8 (A.(pk.(0sz)));
  if (h = 4uy) {
    copy_range out 0sz pk 1sz 64sz;
    with wo. assert (A.pts_to out wo);
    A.pts_to_len out;
    assert (pure (Seq.equal wo (Seq.slice vp 1 65)));
    true
  } else {
    false
  }
}

#pop-options

(** {2 Decompression}

    [y^2 = x^3 - 3x + b] has at most one root of each parity, so the header
    picks which one; if there is no root at all the input was not a point
    and the answer is [false]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Write the root of the requested parity.  [fsqrt] returns whichever of
    the two roots the exponentiation lands on; the other is its negation,
    and the two have opposite parities because the prime is odd. *)
fn store_y (yb: A.array S8.t) (yf nf: A.array S64.t) (odd: bool)
           (#vyb: erased (Seq.seq S8.t)) (#vnf: erased (Seq.seq S64.t))
           (#py: perm) (#vy: erased (Seq.seq S64.t))
requires A.pts_to yb vyb ** A.pts_to yf #py vy ** A.pts_to nf vnf **
  pure (Seq.length vyb == 32 /\ Seq.length vnf == nl /\ felem vy)
ensures exists* (wyb: Seq.seq S8.t) (wnf: Seq.seq S64.t).
  A.pts_to yb wyb ** A.pts_to yf #py vy ** A.pts_to nf wnf **
  pure (Seq.length wnf == nl /\
        wyb == nat_to_be 32 (if (fev vy % 2 = 1) = odd
                             then fev vy else P.fneg (fev vy)))
{
  A.pts_to_len yb;
  fstore yb yf;
  nat_to_be_parity 32 (fev vy);
  let lb = A.(yb.(31sz));
  UInt.logand_mask #8 (S8.v lb) 1;
  assert_norm (pow2 1 - 1 == 1);
  let par = Declassify.u8 (S8.logand lb (S8.classify 1uy));
  if ((par = 1uy) = odd) {
    ()
  } else {
    fneg nf yf;
    fstore yb nf;
  }
}

(** As elsewhere, an [ensures] cannot assume the [requires], so the length
    travels in a total wrapper. *)
let c2r (vp: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vp = 33 then P.compressed_to_raw vp else None

fn compressed_to_raw (out pk: A.array S8.t)
                     (#vo: erased (Seq.seq S8.t))
                     (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to pk #pp vp **
  pure (Seq.length vo == 64 /\ Seq.length vp == 33)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to pk #pp vp **
  pure (Seq.length wo == 64 /\ r == Some? (c2r vp) /\
        (r ==> wo == Some?.v (c2r vp)))
{
  A.pts_to_len out; A.pts_to_len pk;
  let z = S64.zero;
  let mut m0 = [| z; 8sz |]; A.pts_to_len m0; let mut m1 = [| z; 8sz |]; A.pts_to_len m1; let mut m2 = [| z; 8sz |]; A.pts_to_len m2; let mut m3 = [| z; 8sz |]; A.pts_to_len m3; A.pts_to_len m0; A.pts_to_len m1; A.pts_to_len m2; A.pts_to_len m3;
  let z8 = S8.classify 0uy;
  let mut n0 = [| z8; 32sz |]; A.pts_to_len n0; let mut n1 = [| z8; 32sz |]; A.pts_to_len n1; A.pts_to_len n0; A.pts_to_len n1;

  let h = Declassify.u8 (A.(pk.(0sz)));
  if (h = 2uy || h = 3uy) {
    copy_range n0 0sz pk 1sz 32sz;
    with vxb. assert (A.pts_to n0 vxb);
    A.pts_to_len n0;
    assert (pure (Seq.equal vxb (Seq.slice vp 1 33)));
    let okx = fload m0 n0;
    if okx {
      curve_rhs m1 m0;
      let oks = fsqrt m2 m1;
      if oks {
        store_y n1 m2 m3 (h = 3uy);
        with wyb. assert (A.pts_to n1 wyb);
        A.pts_to_len n1;
        copy_at out 0sz n0 32sz;
        copy_at out 32sz n1 32sz;
        with wo. assert (A.pts_to out wo);
        A.pts_to_len out;
        assert (pure (Seq.equal wo (Seq.append vxb wyb)));
      true
      } else {
      false
      }
    } else {
      false
    }
  } else {
      false
  }
}

#pop-options
