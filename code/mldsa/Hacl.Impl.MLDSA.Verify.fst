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


(** Algorithm 8, [ML-DSA.Verify_internal], from the message
    representative [mu].

    Everything here is public: the key, the signature and the verdict.
    The comparison of the recomputed challenge goes through
    {!Hacl.Impl.Bytes.bytes_eq} all the same. *)
module Hacl.Impl.MLDSA.Verify

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.NTT
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample
open Spec.MLDSA.Rounding
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Poly
open Hacl.Impl.MLDSA.Vec
open Hacl.Impl.MLDSA.VecRound
open Hacl.Impl.MLDSA.Hint
open Hacl.Impl.MLDSA.Sampler
open Hacl.Impl.MLDSA.Pack
open Hacl.Impl.MLDSA.Glue

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module HSZ = Hacl.SizeT
module Sub = Hacl.Impl.Sub
module M = Spec.MLDSA
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [gamma1 - beta], the bound on [z]. *)
inline_for_extraction
let z_bound (#p: erased params) (g1bits tau eta: SZ.t)
  : Pure S32.t
      (requires SZ.v g1bits == p.gamma1_bits /\ SZ.v tau == p.tau /\ SZ.v eta == p.eta)
      (ensures fun r -> S32.v r == gamma1 p - beta p /\ S32.v r <= half_q)
  = assert_norm (pow2 17 == 131072);
    assert_norm (pow2 19 == 524288);
    assert_norm (pow2 32 == 4294967296);
    beta_lt p;
    let g = if g1bits = 17sz then 131072ul else 524288ul in
    let b = U32.mul (SZ.sizet_to_uint32 tau) (SZ.sizet_to_uint32 eta) in
    S32.classify (U32.sub g b)

(** [w' = NTT^-1(A NTT(z) - NTT(c) NTT(t1 2^d))].  [z], [t1] and [c] are
    consumed. *)
fn verify_w_impl (p: erased params) (w a z t1 c: A.array zqt)
                 ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                 (t1s: erased (Seq.lseq nat (p.k * n)))
                 (#vw: erased (Seq.seq zqt)) (#pa: perm)
                 (#va #vz #vt #vc: erased (Seq.seq zqt))
requires A.pts_to w vw ** A.pts_to a #pa va ** A.pts_to z vz ** A.pts_to t1 vt ** A.pts_to c vc **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\
               Seq.length vw == p.k * n /\ Seq.length va == p.k * p.l * n /\
               Seq.length vz == p.l * n /\ Seq.length vt == p.k * n /\ Seq.length vc == n /\
               as_ints vt == reveal t1s /\
               (forall (i: nat). i < p.k * n ==> S32.v (Seq.index vt i) < 1024))
ensures exists* (r vz' vt' vc': Seq.seq zqt).
  A.pts_to w r ** A.pts_to a #pa va ** A.pts_to z vz' ** A.pts_to t1 vt' ** A.pts_to c vc' **
  pure (Seq.length r == p.k * n /\ Seq.length va == p.k * p.l * n /\
        Seq.length vz == p.l * n /\ Seq.length vc == n /\
        as_zqs r == M.verify_w p (as_zqs va) t1s (as_poly vc) (as_zqs vz))
{
  HSZ.fits32 ();
  let kn = SZ.mul k 256sz;
  vec_ntt_impl z l;
  let mut tmp = [| (S32.zero <: zqt); 256sz |];
  Mem.track tmp;
  mat_vec_mul_impl w a z tmp k l;
  with u. assert (A.pts_to w u);
  ntt_inplace c;
  t1_shift_impl t1 k;
  with ts. assert (A.pts_to t1 ts);
  t1_shift_eq p.k ts vt t1s;
  vec_ntt_impl t1 k;
  let mut ct1 = [| (S32.zero <: zqt); kn |];
  Mem.track ct1;
  vec_scale_impl ct1 c t1 k;
  with uc. assert (A.pts_to ct1 uc);
  sub_inplace w ct1 kn;
  with u'. assert (A.pts_to w u');
  sub_eq p.k u' u uc;
  vec_intt_impl w k;
  Mem.wipe ct1 kn;
  Mem.wipe tmp 256sz;
  ()
}

#push-options "--ifuel 1"
let verify_reject (p: params) (vpk: Seq.lseq S8.t (pk_len p)) (vmu: Seq.lseq S8.t 64)
                  (vsg: Seq.lseq S8.t (sig_len p)) (zs: pvec p.l) (hv: Seq.lseq bool (p.k * n))
  : Lemma (requires (let (_, z, ho) = sig_decode p vsg in
                     z == zs /\ (ho == None \/
                                 (ho == Some hv /\ (beta_lt p; not (all_lt zs (gamma1 p - beta p)))))))
          (ensures M.verify_mu p vpk vmu vsg == false)
  = ()

let verify_accept (p: params) (vpk: Seq.lseq S8.t (pk_len p)) (vmu: Seq.lseq S8.t 64)
                  (vsg: Seq.lseq S8.t (sig_len p)) (zs: pvec p.l) (hv: Seq.lseq bool (p.k * n))
                  (res: bool)
  : Lemma (requires (let (ct, z, ho) = sig_decode p vsg in
                     z == zs /\ ho == Some hv /\
                     (beta_lt p; all_lt zs (gamma1 p - beta p)) /\
                     (exists (w': pvec p.k) (ct': Seq.lseq S8.t (ct_len p)).
                        w' == M.verify_w p (expand_a p (Seq.slice vpk 0 32)) (snd (pk_decode p vpk))
                                         (sample_in_ball p (Seq.slice vsg 0 (ct_len p))) zs /\
                        ct' == M.challenge_hash p vmu (vec_use_hint p hv w') /\
                        (res <==> Seq.equal ct' (Seq.slice vsg 0 (ct_len p))))))
          (ensures M.verify_mu p vpk vmu vsg == res)
  = ()
#pop-options

(** The accepting path: [z] decoded and short, the hint well formed. *)
fn verify_tail (pk mu sg: A.array S8.t) (z t1: A.array zqt) (h: A.array S32.t) (p: erased params)
               ([@@@FStar.Attributes.monomorphize] k: SZ.t)
               ([@@@FStar.Attributes.monomorphize] l: SZ.t)
               ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
               ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
               (gd: U32.t)
               (#pp #pm #ps: perm)
               (#vpk #vmu #vsg: erased (Seq.seq S8.t))
               (#vz #vt: erased (Seq.seq zqt)) (#vh: erased (Seq.seq S32.t))
requires A.pts_to pk #pp vpk ** A.pts_to mu #pm vmu ** A.pts_to sg #ps vsg **
         A.pts_to z vz ** A.pts_to t1 vt ** A.pts_to h vh **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ U32.v gd == p.gamma2_div /\
               Seq.length vpk == pk_len p /\ Seq.length vmu == 64 /\
               Seq.length vsg == sig_len p /\
               Seq.length vz == p.l * n /\ Seq.length vt == p.k * n /\
               Seq.length vh == p.k * n /\ hint_bits vh /\
               as_ints vt == snd (pk_decode p vpk) /\
               (forall (i: nat). i < p.k * n ==> S32.v (Seq.index vt i) < 1024))
returns res: bool
ensures exists* (vz' vt': Seq.seq zqt).
  A.pts_to pk #pp vpk ** A.pts_to mu #pm vmu ** A.pts_to sg #ps vsg **
  A.pts_to z vz' ** A.pts_to t1 vt' ** A.pts_to h vh **
  pure (Seq.length vpk == pk_len p /\ Seq.length vmu == 64 /\ Seq.length vsg == sig_len p /\
        Seq.length vz == p.l * n /\ Seq.length vh == p.k * n /\
        (exists (w': pvec p.k) (ct': Seq.lseq S8.t (ct_len p)).
           w' == M.verify_w p (expand_a p (Seq.slice vpk 0 32)) (snd (pk_decode p vpk))
                             (sample_in_ball p (Seq.slice vsg 0 (ct_len p))) (as_zqs vz) /\
           ct' == M.challenge_hash p vmu (vec_use_hint p (hint_view vh) w') /\
           (res <==> Seq.equal ct' (Seq.slice vsg 0 (ct_len p)))))
{
  A.pts_to_len pk;
  A.pts_to_len sg;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sig_len p);
  assert (pure (ct_len p <= sig_len p));
  let kn = SZ.mul k 256sz;
  let kln = SZ.mul (SZ.mul k l) 256sz;
  let a = Mem.alloc (S32.zero <: zqt) kln;
  let rho = Sub.sub pk 0sz 32sz;
  expand_a_impl p a rho k l;
  Sub.unsub_id pk 0 32 rho;
  let mut c = [| (S32.zero <: zqt); 256sz |];
  Mem.track c;
  let ct = Sub.sub sg 0sz ctl;
  sample_in_ball_impl p c ct ctl tau;
  Sub.unsub_id sg 0 (SZ.v ctl) ct;
  let w = Mem.alloc (S32.zero <: zqt) kn;
  verify_w_impl p w a z t1 c k l (snd (pk_decode p vpk));
  with vw. assert (A.pts_to w vw);
  Mem.free a kln;
  Mem.wipe c 256sz;
  let w1 = Mem.alloc (S32.zero <: zqt) kn;
  use_hint_impl w1 h w p gd k;
  Mem.free w kn;
  let mut ct' = [| (S8.zero <: S8.t); ctl |];
  Mem.track ct';
  challenge_impl p ct' mu w1 k ctl gd;
  Mem.free w1 kn;
  with vct. assert (A.pts_to ct' vct);
  let ct2 = Sub.sub sg 0sz ctl;
  let res = Hacl.Impl.Bytes.bytes_eq ct' ct2 ctl;
  Sub.unsub_id sg 0 (SZ.v ctl) ct2;
  Mem.wipe ct' ctl;
  assert (pure (as_zqs vw == M.verify_w p (expand_a p (Seq.slice vpk 0 32)) (snd (pk_decode p vpk))
                             (sample_in_ball p (Seq.slice vsg 0 (ct_len p))) (as_zqs vz)));
  res
}

fn verify_mu_impl (pk mu sg: A.array S8.t) (p: erased params)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] tau: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                  (gd: U32.t)
                  (#pp #pm #ps: perm)
                  (#vpk #vmu #vsg: erased (Seq.seq S8.t))
requires A.pts_to pk #pp vpk ** A.pts_to mu #pm vmu ** A.pts_to sg #ps vsg **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\ SZ.v tau == p.tau /\
               SZ.v ctl == ct_len p /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v omega == p.omega /\ U32.v gd == p.gamma2_div /\
               Seq.length vpk == pk_len p /\ Seq.length vmu == 64 /\
               Seq.length vsg == sig_len p)
returns res: bool
ensures A.pts_to pk #pp vpk ** A.pts_to mu #pm vmu ** A.pts_to sg #ps vsg **
  pure (Seq.length vpk == pk_len p /\ Seq.length vmu == 64 /\ Seq.length vsg == sig_len p /\
        res == M.verify_mu p vpk vmu vsg)
{
  A.pts_to_len pk;
  A.pts_to_len sg;
  HSZ.fits32 ();
  let kn = SZ.mul k 256sz;
  let ln = SZ.mul l 256sz;
  let t1 = Mem.alloc (S32.zero <: zqt) kn;
  pk_decode_impl p t1 pk k;
  with vt. assert (A.pts_to t1 vt);
  let mut z = [| (S32.zero <: zqt); ln |];
  Mem.track z;
  let mut h = [| (S32.zero <: S32.t); kn |];
  Mem.track h;
  let ok = sig_decode_impl p z h sg k l ctl g1bits omega;
  with vz. assert (A.pts_to z vz);
  with vh. assert (A.pts_to h vh);
  if (not ok) {
    verify_reject p vpk vmu vsg (as_zqs vz) (hint_view vh);
    Mem.wipe h kn;
    Mem.wipe z ln;
    Mem.free t1 kn;
    false
  } else {
    let zok = all_lt_impl z ln (z_bound #p g1bits tau eta);
    if (not zok) {
      verify_reject p vpk vmu vsg (as_zqs vz) (hint_view vh);
      Mem.wipe h kn;
      Mem.wipe z ln;
      Mem.free t1 kn;
      false
    } else {
      let res = verify_tail pk mu sg z t1 h p k l tau ctl gd;
      verify_accept p vpk vmu vsg (as_zqs vz) (hint_view vh) res;
      Mem.wipe h kn;
      Mem.wipe z ln;
      Mem.free t1 kn;
      res
    }
  }
}


#pop-options
