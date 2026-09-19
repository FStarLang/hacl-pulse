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


(** K-PKE: the public-key encryption scheme ML-KEM is built from.

    FIPS 203 Algorithms 13 to 15.  One implementation covers the three
    parameter sets: the rank, the two noise widths and the two compression
    widths are ordinary arguments, and every buffer is allocated at a size
    computed from them, so there is no per-set duplication.

    The specification is a ghost [params] record; the runtime arguments
    are the machine integers matching its fields.  Nothing here draws
    randomness -- the seeds are arguments, which is what lets ML-KEM
    derive them from the message.

    On stack: the largest buffer is [A-hat], k*k polynomials, which is
    8 KiB at ML-KEM-1024.  It is generated in one go rather than streamed
    a row at a time; that is what the reference implementation does too,
    and it keeps the matrix-vector product a single call. *)
module Hacl.Impl.MLKEM.KPKE

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM
open Spec.MLKEM.Zq
open Spec.MLKEM.Params
open Spec.MLKEM.NTT
open Spec.MLKEM.Encode
open Spec.MLKEM.Sample
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.KPKELemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module HSZ = Hacl.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module Math = FStar.Math.Lemmas
module Cast = FStar.Int.Cast
module Copy = Hacl.Impl.Copy
module Hash = Hacl.Impl.MLKEM.Hash
module Gen = Hacl.Impl.MLKEM.Gen
module Vec = Hacl.Impl.MLKEM.Vec
module VC = Hacl.Impl.MLKEM.VecCodec

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Algorithm 13.  [d] is the 32-byte seed. *)
fn kpke_keygen_impl (ek dk dseed: A.array S8.t) (k eta1: SZ.t)
                    (#p: erased params)
                    (#vek0 #vdk0: erased (Seq.seq S8.t))
                    (#pd: perm) (#vd: erased (Seq.lseq S8.t 32))
requires A.pts_to ek vek0 ** A.pts_to dk vdk0 ** A.pts_to dseed #pd vd **
         pure (SZ.v k == (reveal p).k /\ SZ.v eta1 == (reveal p).eta1 /\
               Seq.length vek0 == ek_len p /\ Seq.length vdk0 == dk_pke_len p /\
               Seq.length vd == 32)
ensures exists* vek vdk.
  A.pts_to ek vek ** A.pts_to dk vdk ** A.pts_to dseed #pd vd **
  pure (Seq.length vek == ek_len p /\ Seq.length vdk == dk_pke_len p /\
        vek == fst (kpke_keygen p vd) /\ vdk == snd (kpke_keygen p vd))
{
  A.pts_to_len ek;
  A.pts_to_len dk;
  A.pts_to_len dseed;
  HSZ.fits32 ();
  assert_norm (4 * 4 * n < pow2 32);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  let kn = SZ.mul k 256sz;
  let kkn = SZ.mul kn k;
  let k384 = SZ.mul k 384sz;
  let kb = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 k);
  Math.small_mod (SZ.v k) 256;
  Math.small_mod (SZ.v k) 4294967296;
  U8.v_inj kb (U8.uint_to_t (reveal p).k);
  assert (pure (kb == U8.uint_to_t (reveal p).k));

  (* G(d || k) *)
  let mut gin = [| (S8.zero <: S8.t); 33sz |];
  Copy.copy_prefix gin dseed 32sz;
  A.((gin.(32sz) <- S8.classify kb));
  with vgin. assert (A.pts_to gin vgin);
  snoc_eq vd (S8.classify kb) vgin;
  let mut g = [| (S8.zero <: S8.t); 64sz |];
  Hash.hash_g_impl g gin 33sz;
  with vg. assert (A.pts_to g vg);
  assert (pure (vg == hash_g (Seq.snoc vd (S8.classify (U8.uint_to_t (reveal p).k)))));

  let mut rho = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_prefix rho g 32sz;
  with vrho. assert (A.pts_to rho vrho);
  slice_eq vg 0 vrho;
  let mut sigma = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_range sigma 0sz g 32sz 32sz;
  with vsigma. assert (A.pts_to sigma vsigma);
  slice_eq vg 32 vsigma;
  assert (pure (vrho == Seq.slice vg 0 32 /\ vsigma == Seq.slice vg 32 64));

  (* A-hat, then the two noise vectors in the NTT domain *)
  let mut a = [| (S16.zero <: zqt); kkn |];
  Gen.gen_matrix_impl a rho false k;
  with va. assert (A.pts_to a va);
  assert (pure (as_zqs va == gen_matrix (SZ.v k) vrho false));

  let mut tmp = [| (S16.zero <: zqt); 256sz |];
  let mut s = [| (S16.zero <: zqt); kn |];
  Gen.noise_vec_impl s sigma 0uy eta1 k;
  with s0. assert (A.pts_to s s0);
  Vec.vec_ntt_impl s tmp k;
  with vs. assert (A.pts_to s vs);
  assert (pure (as_zqs vs == vec_ntt #(SZ.v k)
                  (noise_vec (SZ.v k) (SZ.v eta1) vsigma 0)));

  let mut e = [| (S16.zero <: zqt); kn |];
  Gen.noise_vec_impl e sigma kb eta1 k;
  with e0. assert (A.pts_to e e0);
  Vec.vec_ntt_impl e tmp k;
  with ve. assert (A.pts_to e ve);
  assert (pure (as_zqs ve == vec_ntt #(SZ.v k)
                  (noise_vec (SZ.v k) (SZ.v eta1) vsigma (SZ.v k))));

  (* t-hat = A-hat s-hat + e-hat *)
  let mut t = [| (S16.zero <: zqt); kn |];
  Vec.mat_vec_mul_impl t a s tmp k;
  with t0. assert (A.pts_to t t0);
  Vec.add_inplace t e kn;
  with vt. assert (A.pts_to t vt);
  vec_add_intro (SZ.v k) t0 ve vt;
  assert (pure (as_zqs vt == vec_add #(SZ.v k)
                  (mat_vec_mul #(SZ.v k) (as_zqs va) (as_zqs vs)) (as_zqs ve)));

  (* the two keys *)
  let mut tb = [| (S8.zero <: S8.t); k384 |];
  VC.vec_encode_impl tb t 12sz k;
  with vtb. assert (A.pts_to tb vtb);
  as_ints_widen vt;
  assert (pure (vtb == vec_encode_12 #(SZ.v k) (as_zqs vt)));
  Copy.copy_prefix ek tb k384;
  Copy.copy_at ek k384 rho 32sz;
  with vek. assert (A.pts_to ek vek);
  append2_eq vtb vrho vek;

  VC.vec_encode_impl dk s 12sz k;
  with vdk. assert (A.pts_to dk vdk);
  as_ints_widen vs;
  assert (pure (vdk == vec_encode_12 #(SZ.v k) (as_zqs vs)));

  keygen_eq p vd vek vdk;
  assert (pure (vek == fst (kpke_keygen p vd) /\ vdk == snd (kpke_keygen p vd)));
}
