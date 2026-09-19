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

(** The two input checks of FIPS 203 section 7.

    The standard keeps them out of the algorithms deliberately: they say
    where a key came from, not what encapsulation does with it, and a
    caller that generated the key itself does not need them.  A caller that
    received one over the wire does.

    Neither runs in constant time, and neither should pretend to: both
    reject malformed input, and whether input was malformed is exactly the
    answer being returned.  The comparison underneath is constant-time
    anyway, because it is the same {!Hacl.Impl.Bytes.bytes_eq} everything
    else uses.

    The modulus check re-encodes what it decoded, which is the standard's
    own phrasing of it and is four lines rather than a bound proof on 256k
    coefficients. *)
module Hacl.Impl.MLKEM.Check

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM
open Spec.MLKEM.Params
open Spec.MLKEM.Zq
open Spec.MLKEM.Encode
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.KPKELemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module HSZ = Hacl.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module Copy = Hacl.Impl.Copy
module Bytes = Hacl.Impl.Bytes
module VC = Hacl.Impl.MLKEM.VecCodec
module Hash = Hacl.Impl.MLKEM.Hash

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Section 7.2, the modulus check: [ByteEncode_12] of [ByteDecode_12] of
    the coefficient half of the key is the coefficient half of the key. *)
fn ek_check (ekey: A.array S8.t) (p: erased params) (k: SZ.t)
            (#pk: perm) (#vek: erased (Seq.seq S8.t))
requires A.pts_to ekey #pk vek **
         pure (SZ.v k == (reveal p).k /\ Seq.length vek == ek_len p)
returns res: bool
ensures A.pts_to ekey #pk vek **
        pure (Seq.length vek == ek_len p /\ (res <==> ek_valid p vek))
{
  A.pts_to_len ekey;
  HSZ.fits32 ();
  assert_norm (4 * 384 < pow2 32);
  assert_norm (4 * n < pow2 32);
  let k384 = SZ.mul k 384sz;
  let kn = SZ.mul k 256sz;
  assert (pure (SZ.v k384 == (reveal p).k * (32 * 12) /\ SZ.v kn == SZ.v k * n));

  let mut tb = [| (S8.zero <: S8.t); k384 |];
  Copy.copy_prefix tb ekey k384;
  with vtb. assert (A.pts_to tb vtb);
  slice_eq vek 0 vtb;
  assert (pure (vtb == Seq.slice vek 0 ((reveal p).k * (32 * 12))));

  let mut t = [| (S16.zero <: zqt); kn |];
  VC.vec_decode_impl t tb 12sz k;
  with vt. assert (A.pts_to t vt);

  let mut re = [| (S8.zero <: S8.t); k384 |];
  VC.vec_encode_impl re t 12sz k;
  with vre. assert (A.pts_to re vre);
  as_ints_widen vt;
  assert (pure (vre == vec_encode_12 (vec_decode 12 (SZ.v k) vtb)));

  let res = Bytes.bytes_eq re tb k384;
  res
}

(** Section 7.3, the hash check: the hash a decapsulation key carries is
    the hash of the encapsulation key it carries. *)
fn dk_check (dkey: A.array S8.t) (p: erased params) (k: SZ.t)
            (#pk: perm) (#vdk: erased (Seq.seq S8.t))
requires A.pts_to dkey #pk vdk **
         pure (SZ.v k == (reveal p).k /\ Seq.length vdk == dk_len p)
returns res: bool
ensures A.pts_to dkey #pk vdk **
        pure (Seq.length vdk == dk_len p /\ (res <==> dk_valid p vdk))
{
  A.pts_to_len dkey;
  HSZ.fits32 ();
  assert_norm (4 * 384 + 32 < pow2 32);
  let k384 = SZ.mul k 384sz;
  let eklen = SZ.add k384 32sz;
  assert (pure (SZ.v k384 == dk_pke_len p /\ SZ.v eklen == ek_len p));

  let mut ek = [| (S8.zero <: S8.t); eklen |];
  Copy.copy_range ek 0sz dkey k384 eklen;
  with vek. assert (A.pts_to ek vek);
  slice_eq vdk (dk_pke_len p) vek;
  assert (pure (vek == Seq.slice vdk (dk_pke_len p) (dk_pke_len p + ek_len p)));

  let mut h = [| (S8.zero <: S8.t); 32sz |];
  let base = SZ.add k384 eklen;
  Copy.copy_range h 0sz dkey base 32sz;
  with vh. assert (A.pts_to h vh);
  slice_eq vdk (dk_pke_len p + ek_len p) vh;
  assert (pure (vh == Seq.slice vdk (dk_pke_len p + ek_len p)
                                    (dk_pke_len p + ek_len p + 32)));

  let mut hd = [| (S8.zero <: S8.t); 32sz |];
  Hash.hash_h_impl hd ek eklen;
  with vhd. assert (A.pts_to hd vhd);
  assert (pure (vhd == hash_h vek));

  let res = Bytes.bytes_eq hd h 32sz;
  res
}

#pop-options
