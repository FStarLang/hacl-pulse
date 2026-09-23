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
module Codec = Hacl.Impl.MLKEM.Codec
module Poly = Hacl.Impl.MLKEM.Poly
module Sampler = Hacl.Impl.MLKEM.Sampler

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Algorithm 13.  [d] is the 32-byte seed. *)
fn kpke_keygen_impl (ek dk dseed: A.array S8.t) (p: erased params) ([@@@FStar.Attributes.monomorphize] k: SZ.t) ([@@@FStar.Attributes.monomorphize] eta1: SZ.t)
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

(** Algorithm 14.  [m] is the 32-byte message and [r] the encryption
    randomness; in ML-KEM both come from the same hash, which is what
    makes the transform work. *)
fn kpke_encrypt_impl (ct ekey msg rnd: A.array S8.t) (p: erased params)
                     ([@@@FStar.Attributes.monomorphize] k: SZ.t) ([@@@FStar.Attributes.monomorphize] eta1: SZ.t)
                     ([@@@FStar.Attributes.monomorphize] eta2: SZ.t) ([@@@FStar.Attributes.monomorphize] du: SZ.t)
                     ([@@@FStar.Attributes.monomorphize] dv: SZ.t)
                     (#vct0: erased (Seq.seq S8.t))
                     (#pe: perm) (#vek: erased (Seq.lseq S8.t (ek_len p)))
                     (#pm: perm) (#vm: erased (Seq.lseq S8.t 32))
                     (#pr: perm) (#vr: erased (Seq.lseq S8.t 32))
requires A.pts_to ct vct0 ** A.pts_to ekey #pe vek ** A.pts_to msg #pm vm **
         A.pts_to rnd #pr vr **
         pure (SZ.v k == (reveal p).k /\ SZ.v eta1 == (reveal p).eta1 /\
               SZ.v eta2 == (reveal p).eta2 /\ SZ.v du == (reveal p).du /\
               SZ.v dv == (reveal p).dv /\ Seq.length vct0 == ct_len p)
ensures exists* vct.
  A.pts_to ct vct ** A.pts_to ekey #pe vek ** A.pts_to msg #pm vm **
  A.pts_to rnd #pr vr **
  pure (Seq.length vct == ct_len p /\ vct == kpke_encrypt p vek vm vr)
{
  A.pts_to_len ct;
  A.pts_to_len ekey;
  A.pts_to_len msg;
  A.pts_to_len rnd;
  HSZ.fits32 ();
  assert_norm (4 * 4 * n < pow2 32);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 1 == 2);
  let kn = SZ.mul k 256sz;
  let kkn = SZ.mul kn k;
  let k384 = SZ.mul k 384sz;
  SZ.fits_u32_implies_fits (32 * SZ.v du);
  SZ.fits_u32_implies_fits (SZ.v k * (32 * SZ.v du));
  SZ.fits_u32_implies_fits (32 * SZ.v dv);
  let c1len = SZ.mul k (SZ.mul 32sz du);
  let c2len = SZ.mul 32sz dv;
  assert (pure (SZ.v c1len == SZ.v k * (32 * SZ.v du) /\
                SZ.v c2len == 32 * SZ.v dv /\
                SZ.v c1len + SZ.v c2len == ct_len p));
  let kb = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 k);
  let k2 = SZ.mul 2sz k;
  let k2b = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 k2);
  Math.small_mod (SZ.v k) 256;
  Math.small_mod (SZ.v k) 4294967296;
  Math.small_mod (2 * SZ.v k) 256;
  Math.small_mod (2 * SZ.v k) 4294967296;
  U8.v_inj k2b (U8.uint_to_t (2 * (reveal p).k));
  assert (pure (U8.v kb == SZ.v k /\ k2b == U8.uint_to_t (2 * (reveal p).k)));

  (* the key: t-hat and rho *)
  let mut tb = [| (S8.zero <: S8.t); k384 |];
  Copy.copy_prefix tb ekey k384;
  with vtb. assert (A.pts_to tb vtb);
  slice_eq vek 0 vtb;
  let mut t = [| (S16.zero <: zqt); kn |];
  VC.vec_decode_impl t tb 12sz k;
  with vt. assert (A.pts_to t vt);
  assert (pure (as_zqs vt == vec_decode 12 (SZ.v k)
                  (Seq.slice vek 0 ((reveal p).k * (32 * 12)))));

  let mut rho = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_range rho 0sz ekey k384 32sz;
  with vrho. assert (A.pts_to rho vrho);
  slice_eq vek ((reveal p).k * (32 * 12)) vrho;
  assert (pure (vrho == Seq.slice vek ((reveal p).k * (32 * 12)) (ek_len p)));

  (* the transpose, the masking vector and the three noise terms *)
  let mut a = [| (S16.zero <: zqt); kkn |];
  Gen.gen_matrix_impl a rho true k;
  with va. assert (A.pts_to a va);

  let mut tmp = [| (S16.zero <: zqt); 256sz |];
  let mut y = [| (S16.zero <: zqt); kn |];
  Gen.noise_vec_impl y rnd 0uy eta1 k;
  Vec.vec_ntt_impl y tmp k;
  with vy. assert (A.pts_to y vy);
  assert (pure (as_zqs vy == vec_ntt #(SZ.v k)
                  (noise_vec (SZ.v k) (SZ.v eta1) vr 0)));

  let mut e1 = [| (S16.zero <: zqt); kn |];
  Gen.noise_vec_impl e1 rnd kb eta2 k;
  with ve1. assert (A.pts_to e1 ve1);
  let mut e2 = [| (S16.zero <: zqt); 256sz |];
  Sampler.sample_poly_cbd_impl e2 rnd k2b eta2;
  with ve2. assert (A.pts_to e2 ve2);
  assert (pure (as_poly ve2 == sample_poly_cbd (SZ.v eta2) vr k2b));

  (* the message as a polynomial *)
  let mut md = [| (S16.zero <: zqt); 256sz |];
  Codec.decode_poly md msg 1sz;
  with vmd. assert (A.pts_to md vmd);
  decode_bound 1 vm vmd;
  let mut mu = [| (S16.zero <: zqt); 256sz |];
  Codec.decompress_poly mu md 1sz;
  with vmu. assert (A.pts_to mu vmu);
  as_nats_widen vmd;
  assert (pure (as_poly vmu == poly_decompress 1 (widen (byte_decode 1 vm))));

  (* u = NTT^-1(A-hat^T y-hat) + e1 *)
  let mut u = [| (S16.zero <: zqt); kn |];
  Vec.mat_vec_mul_impl u a y tmp k;
  Vec.vec_intt_impl u tmp k;
  with u0. assert (A.pts_to u u0);
  Vec.add_inplace u e1 kn;
  with vu. assert (A.pts_to u vu);
  vec_add_intro (SZ.v k) u0 ve1 vu;
  assert (pure (as_zqs vu == vec_add #(SZ.v k)
                  (vec_intt #(SZ.v k)
                     (mat_vec_mul #(SZ.v k) (as_zqs va) (as_zqs vy)))
                  (as_zqs ve1)));

  (* v = NTT^-1(t-hat . y-hat) + e2 + mu *)
  let mut vp = [| (S16.zero <: zqt); 256sz |];
  Vec.dot_impl vp t y tmp k;
  Poly.intt_inplace vp tmp;
  with v0. assert (A.pts_to vp v0);
  Vec.add_inplace vp e2 256sz;
  with v1. assert (A.pts_to vp v1);
  poly_add_intro v0 ve2 v1;
  Vec.add_inplace vp mu 256sz;
  with vv. assert (A.pts_to vp vv);
  poly_add_intro v1 vmu vv;
  assert (pure (as_poly vv ==
                poly_add (poly_add (intt (dot #(SZ.v k) (as_zqs vt) (as_zqs vy)))
                                   (as_poly ve2))
                         (as_poly vmu)));

  (* serialise *)
  let mut uc = [| (S16.zero <: zqt); kn |];
  VC.vec_compress_impl uc u du k;
  with vuc. assert (A.pts_to uc vuc);
  let mut c1 = [| (S8.zero <: S8.t); c1len |];
  VC.vec_encode_impl c1 uc du k;
  with vc1. assert (A.pts_to c1 vc1);
  assert (pure (vc1 == vec_encode (SZ.v du) (SZ.v k)
                         (vec_compress (SZ.v du) #(SZ.v k) (as_zqs vu))));

  let mut vc = [| (S16.zero <: zqt); 256sz |];
  Codec.compress_poly vc vp dv;
  with vvc. assert (A.pts_to vc vvc);
  let mut c2 = [| (S8.zero <: S8.t); c2len |];
  Codec.encode_poly c2 vc dv;
  with vc2. assert (A.pts_to c2 vc2);
  assert (pure (vc2 == byte_encode (SZ.v dv)
                         (poly_compress (SZ.v dv) (as_poly vv))));

  Copy.copy_prefix ct c1 c1len;
  Copy.copy_at ct c1len c2 c2len;
  with vct. assert (A.pts_to ct vct);
  append2_eq vc1 vc2 vct;
  encrypt_eq p vek vm vr vct;
  assert (pure (vct == kpke_encrypt p vek vm vr));
}

(** Algorithm 15.  The subtraction is where the noise has to fit: [w] is
    the message plus everything the two rounds of compression and the
    three noise terms contributed, and [Compress_1] recovers the message
    exactly when that sum stays inside a quarter turn. *)
fn kpke_decrypt_impl (out dkey ct: A.array S8.t) (p: erased params)
                     ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                     ([@@@FStar.Attributes.monomorphize] du: SZ.t) ([@@@FStar.Attributes.monomorphize] dv: SZ.t)
                     (#vo0: erased (Seq.seq S8.t))
                     (#pd: perm) (#vdk: erased (Seq.lseq S8.t (dk_pke_len p)))
                     (#pc: perm) (#vc: erased (Seq.lseq S8.t (ct_len p)))
requires A.pts_to out vo0 ** A.pts_to dkey #pd vdk ** A.pts_to ct #pc vc **
         pure (SZ.v k == (reveal p).k /\ SZ.v du == (reveal p).du /\
               SZ.v dv == (reveal p).dv /\ Seq.length vo0 == 32)
ensures exists* vout.
  A.pts_to out vout ** A.pts_to dkey #pd vdk ** A.pts_to ct #pc vc **
  pure (Seq.length vout == 32 /\ vout == kpke_decrypt p vdk vc)
{
  A.pts_to_len out;
  A.pts_to_len dkey;
  A.pts_to_len ct;
  HSZ.fits32 ();
  assert_norm (4 * 4 * n < pow2 32);
  assert_norm (pow2 1 == 2);
  let kn = SZ.mul k 256sz;
  SZ.fits_u32_implies_fits (32 * SZ.v du);
  SZ.fits_u32_implies_fits (SZ.v k * (32 * SZ.v du));
  SZ.fits_u32_implies_fits (32 * SZ.v dv);
  let c1len = SZ.mul k (SZ.mul 32sz du);
  let c2len = SZ.mul 32sz dv;
  assert (pure (SZ.v c1len == SZ.v k * (32 * SZ.v du) /\
                SZ.v c2len == 32 * SZ.v dv /\
                SZ.v c1len + SZ.v c2len == ct_len p));

  (* the two ciphertext components *)
  let mut c1 = [| (S8.zero <: S8.t); c1len |];
  Copy.copy_prefix c1 ct c1len;
  with vc1. assert (A.pts_to c1 vc1);
  slice_eq vc 0 vc1;
  let mut c2 = [| (S8.zero <: S8.t); c2len |];
  Copy.copy_range c2 0sz ct c1len c2len;
  with vc2. assert (A.pts_to c2 vc2);
  slice_eq vc ((reveal p).k * (32 * (reveal p).du)) vc2;

  let mut ud = [| (S16.zero <: zqt); kn |];
  VC.vec_decode_impl ud c1 du k;
  with vud. assert (A.pts_to ud vud);
  vec_decode_bound_arr (SZ.v du) (SZ.v k) vc1 vud;
  let mut u = [| (S16.zero <: zqt); kn |];
  VC.vec_decompress_impl u ud du k;
  with vu. assert (A.pts_to u vu);
  as_ints_widen vud;
  assert (pure (as_zqs vu == vec_decompress (SZ.v du) (SZ.v k)
                  (widen (vec_decode (SZ.v du) (SZ.v k) vc1))));

  let mut vd = [| (S16.zero <: zqt); 256sz |];
  Codec.decode_poly vd c2 dv;
  with vvd. assert (A.pts_to vd vvd);
  decode_bound (SZ.v dv) vc2 vvd;
  let mut vp = [| (S16.zero <: zqt); 256sz |];
  Codec.decompress_poly vp vd dv;
  with vv. assert (A.pts_to vp vv);
  as_nats_widen vvd;
  assert (pure (as_poly vv == poly_decompress (SZ.v dv)
                  (widen (byte_decode (SZ.v dv) vc2))));

  (* w = v - NTT^-1(s-hat . NTT(u)) *)
  let mut s = [| (S16.zero <: zqt); kn |];
  VC.vec_decode_impl s dkey 12sz k;
  with vs. assert (A.pts_to s vs);
  let mut tmp = [| (S16.zero <: zqt); 256sz |];
  Vec.vec_ntt_impl u tmp k;
  with vun. assert (A.pts_to u vun);
  let mut w = [| (S16.zero <: zqt); 256sz |];
  Vec.dot_impl w s u tmp k;
  Poly.intt_inplace w tmp;
  with vw. assert (A.pts_to w vw);
  Vec.sub_inplace vp w 256sz;
  with vres. assert (A.pts_to vp vres);
  poly_sub_intro vv vw vres;
  assert (pure (as_poly vres ==
                poly_sub (as_poly vv)
                  (intt (dot #(SZ.v k) (as_zqs vs) (vec_ntt #(SZ.v k) (as_zqs vu))))));

  (* Compress_1 back to a message *)
  let mut wc = [| (S16.zero <: zqt); 256sz |];
  Codec.compress_poly wc vp 1sz;
  with vwc. assert (A.pts_to wc vwc);
  Codec.encode_poly out wc 1sz;
  with vout. assert (A.pts_to out vout);
  decrypt_eq p vdk vc vout;
  assert (pure (vout == kpke_decrypt p vdk vc));
}
