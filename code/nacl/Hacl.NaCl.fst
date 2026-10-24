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

(** NaCl's secretbox and box.

    The whole of the interesting part is the key schedule, and it is three
    lines: HSalsa20 turns the key and the first sixteen nonce bytes into a
    subkey, Salsa20's block zero under that subkey and the remaining eight
    nonce bytes is generated once, its first half is the one-time Poly1305
    key, and its second half encrypts the first thirty-two message bytes.
    Everything past that is {!Hacl.Salsa20.encrypt} from counter one, on the
    message shifted by thirty-two.  {!Spec.NaCl} proves that this is the same
    thing as NaCl's zero-padded single pass.

    Box is the same with X25519 and one more HSalsa20 in front.

    Two conventions here are not the library's.  These functions return
    [0] for success and [0xffffffff] for failure, because that is what
    NaCl-compatible callers expect; internally everything returns [bool] and
    the conversion happens in the entry points.  And the names are NaCl's --
    [crypto_secretbox_easy] and friends -- because a compatibility layer whose
    names do not match is not one.

    As in HACL*, the detached functions take the ciphertext and the message
    either as the same buffer (in place) or as buffers that do not overlap
    at all ({!Hacl.Impl.InOut.inout}).  The combined ("easy") ones put the
    tag in front of the ciphertext, so the two can never be exactly the same
    buffer; there they must not overlap. *)
module Hacl.NaCl

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Spec.Bytes
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Impl.Bytes
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module G = FStar.Ghost
module S8 = Hacl.Secret.UInt8
module Sub = Hacl.Impl.Sub
module S = Spec.Salsa20
module P = Spec.Poly1305
module C = Spec.Curve25519
module Spec = Spec.NaCl
module Salsa = Hacl.Salsa20
module Poly = Hacl.Poly1305
module Curve = Hacl.Curve25519
module Mem = Hacl.Mem
module IO = Hacl.Impl.InOut
module IOS = Hacl.Impl.InOut.Sub

(** {2 The key schedule}

    [derive] leaves the subkey in [subk], the eight-byte Salsa20 nonce in
    [tn] and keystream block zero in [b0]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn derive (subk: A.array S8.t) (tn: A.array S8.t) (b0: A.array S8.t)
          (key: A.array S8.t) (nonce: A.array S8.t)
          (#vsub: erased (Seq.seq S8.t)) (#vtn: erased (Seq.seq S8.t))
          (#vb0: erased (Seq.seq S8.t))
          (#pk: perm) (#vkey: erased (Seq.seq S8.t))
          (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires A.pts_to subk vsub ** A.pts_to tn vtn ** A.pts_to b0 vb0 **
         A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
         pure (Seq.length vsub == 32 /\ Seq.length vtn == 8 /\ Seq.length vb0 == 64 /\
               Seq.length vkey == 32 /\ Seq.length vnon == 24)
ensures exists* (ws: Seq.seq S8.t) (wt: Seq.seq S8.t) (wb: Seq.seq S8.t).
  A.pts_to subk ws ** A.pts_to tn wt ** A.pts_to b0 wb **
  A.pts_to key #pk vkey ** A.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        Seq.length ws == 32 /\ Seq.length wt == 8 /\ Seq.length wb == 64 /\
        ws == S.xkey vkey vnon /\ wt == S.xnonce_tail vnon /\
        wb == S.key_block0 (S.xkey vkey vnon) (S.xnonce_tail vnon))
{
  A.pts_to_len subk;
  A.pts_to_len tn;
  A.pts_to_len b0;
  A.pts_to_len key;
  A.pts_to_len nonce;

  let z8 = S8.classify 0uy;
  let mut hn = [| z8; 16sz |];
  Mem.track hn;
  A.pts_to_len hn;

  copy_range hn 0sz nonce 0sz 16sz;
  with vh. assert (A.pts_to hn vh);
  Seq.lemma_eq_intro vh (Seq.slice vnon 0 16);
  Seq.lemma_eq_elim vh (Seq.slice vnon 0 16);
  Salsa.hsalsa20 subk key hn;

  copy_range tn 0sz nonce 16sz 8sz;
  with wt. assert (A.pts_to tn wt);
  Seq.lemma_eq_intro wt (S.xnonce_tail vnon);
  Seq.lemma_eq_elim wt (S.xnonce_tail vnon);

  Salsa.key_block0 b0 subk tn;
  Mem.wipe hn 16sz;
  ()
}

#pop-options

(** {2 The authenticator}

    Poly1305 over the ciphertext and nothing else -- secretbox predates AEAD,
    so there is no additional data, no padding and no length block.  The
    one-time key is the first half of block zero, which is handed to Poly1305
    as a window rather than copied. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn sb_tag (tag: A.array S8.t) (ct: A.array S8.t) (clen: SZ.t) (b0: A.array S8.t)
          (gk: G.erased S.key) (gn: G.erased S.xnonce)
          (#vtag: erased (Seq.seq S8.t))
          (#pc: perm) (#vct: erased (Seq.seq S8.t))
          (#pb: perm) (#vb0: erased (Seq.seq S8.t))
requires A.pts_to tag vtag ** A.pts_to ct #pc vct ** A.pts_to b0 #pb vb0 **
         pure (Seq.length vtag == 16 /\ Seq.length vct == SZ.v clen /\
               Seq.length vb0 == 64 /\
               reveal vb0 == S.key_block0 (S.xkey gk gn) (S.xnonce_tail gn))
ensures exists* (wt: Seq.seq S8.t).
  A.pts_to tag wt ** A.pts_to ct #pc vct ** A.pts_to b0 #pb vb0 **
  pure (Seq.length wt == 16 /\ wt == Spec.tag_of gk gn vct)
{
  A.pts_to_len tag;
  A.pts_to_len ct;
  A.pts_to_len b0;
  let otk = Sub.sub b0 0sz 32sz;
  Spec.otk_is_block0 gk gn;
  Poly.mac tag ct clen otk;
  Sub.unsub_id b0 0 32 otk;
  ()
}

#pop-options

(** {2 Encryption}

    The first thirty-two bytes come out of block zero's tail; the rest is an
    ordinary Salsa20 encryption of the message shifted by thirty-two, at
    counter one.  Both halves are proved one byte at a time against
    {!Spec.NaCl.cipher}, which is itself pointwise. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn sb_cipher (c: A.array S8.t) (m: A.array S8.t) (mlen: SZ.t)
             (subk: A.array S8.t) (tn: A.array S8.t) (b0: A.array S8.t)
             (gk: G.erased S.key) (gn: G.erased S.xnonce)
             (#vc: erased (Seq.seq S8.t))
             (#pm: perm) (#vm: erased (Seq.seq S8.t))
             (#ps: perm) (#vsub: erased (Seq.seq S8.t))
             (#pt: perm) (#vtn: erased (Seq.seq S8.t))
             (#pb: perm) (#vb0: erased (Seq.seq S8.t))
requires IO.inout c m pm 0 vc vm ** A.pts_to subk #ps vsub **
         A.pts_to tn #pt vtn ** A.pts_to b0 #pb vb0 **
         pure (Seq.length vc == SZ.v mlen /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= Spec.max_len /\
               Seq.length vsub == 32 /\ Seq.length vtn == 8 /\ Seq.length vb0 == 64 /\
               reveal vsub == S.xkey gk gn /\ reveal vtn == S.xnonce_tail gn /\
               reveal vb0 == S.key_block0 (S.xkey gk gn) (S.xnonce_tail gn))
ensures exists* (w: Seq.seq S8.t).
  IO.inout c m pm (SZ.v mlen) w vm ** A.pts_to subk #ps vsub **
  A.pts_to tn #pt vtn ** A.pts_to b0 #pb vb0 **
  pure (Seq.length vm <= Spec.max_len /\ Seq.length w == SZ.v mlen /\
        w == Spec.cipher gk gn vm)
{
  A.pts_to_len subk;
  A.pts_to_len tn;
  A.pts_to_len b0;
  IO.inout_len c m;

  let n0 = szmin mlen 32sz;
  let mut i = 0sz;
  rewrite IO.inout c m pm 0 vc vm as IO.inout c m pm (SZ.v 0sz) vc vm;
  while (let vi = !i; SZ.lt vi n0)
  invariant exists* (vi: SZ.t) (w: Seq.seq S8.t).
    pts_to i vi ** IO.inout c m pm (SZ.v vi) w vm ** A.pts_to subk #ps vsub **
    A.pts_to tn #pt vtn ** A.pts_to b0 #pb vb0 **
    pure (SZ.v vi <= SZ.v n0 /\ Seq.length w == SZ.v mlen /\
          Seq.length vm <= Spec.max_len /\
          (forall (p: nat). p < SZ.v vi ==>
             Seq.index w p == Seq.index (Spec.cipher gk gn vm) p))
  decreases (SZ.v n0 - SZ.v (!i))
  {
    let vi = !i;
    let x = IO.read_in c m vi;
    let y = A.(b0.(SZ.add 32sz vi));
    Spec.cipher_head gk gn vm (SZ.v vi);
    IO.write_out c m vi (S8.logxor x y);
    i := SZ.add vi 1sz;
    with (w: Seq.seq S8.t). assert (IO.inout c m pm (SZ.v vi + 1) w vm);
    rewrite IO.inout c m pm (SZ.v vi + 1) w vm as IO.inout c m pm (SZ.v (SZ.add vi 1sz)) w vm;
  };
  with (vi: SZ.t) (w: Seq.seq S8.t). assert (pts_to i vi ** IO.inout c m pm (SZ.v vi) w vm);

  if (SZ.gt mlen 32sz) {
    rewrite IO.inout c m pm (SZ.v vi) w vm as IO.inout c m pm 32 w vm;
    unfold IO.inout;
    A.pts_to_len c;
    let cs = Sub.sub c 32sz mlen;
    let ms = IOS.sub_in c m cs 32sz mlen;
    Salsa.encrypt cs ms (SZ.sub mlen 32sz) subk tn 1ul;
    with (ws: Seq.seq S8.t). assert (IO.inout cs ms pm (SZ.v (SZ.sub mlen 32sz)) ws (Seq.slice vm 32 (SZ.v mlen)));
    rewrite IO.inout cs ms pm (SZ.v (SZ.sub mlen 32sz)) ws (Seq.slice vm 32 (SZ.v mlen))
         as IO.inout cs ms pm (SZ.v mlen - 32) ws (Seq.slice vm 32 (SZ.v mlen));
    Spec.cipher_tail gk gn vm;
    IOS.unsub_inout c m cs ms 32 (SZ.v mlen);
    with (w': Seq.seq S8.t). assert (IO.inout c m pm (SZ.v mlen) w' vm);
    Seq.lemma_eq_intro w' (Spec.cipher gk gn vm);
    Seq.lemma_eq_elim w' (Spec.cipher gk gn vm);
    ()
  } else {
    rewrite IO.inout c m pm (SZ.v vi) w vm as IO.inout c m pm (SZ.v mlen) w vm;
    Seq.lemma_eq_intro w (Spec.cipher gk gn vm);
    Seq.lemma_eq_elim w (Spec.cipher gk gn vm);
    ()
  }
}

#pop-options

(** {2 Secretbox, detached} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn sb_detached (c: A.array S8.t) (tag: A.array S8.t) (m: A.array S8.t) (mlen: SZ.t)
               (nonce: A.array S8.t) (key: A.array S8.t)
               (#vc: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
               (#pm: perm) (#vm: erased (Seq.seq S8.t))
               (#pn: perm) (#vnon: erased (Seq.seq S8.t))
               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires IO.inout c m pm 0 vc vm ** A.pts_to tag vtag **
         A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
         pure (Seq.length vc == SZ.v mlen /\ Seq.length vtag == 16 /\
               Seq.length vm == SZ.v mlen /\ Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
ensures exists* (w: Seq.seq S8.t) (wt: Seq.seq S8.t).
  IO.inout c m pm (SZ.v mlen) w vm ** A.pts_to tag wt **
  A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
  pure (Seq.length vm <= Spec.max_len /\ Seq.length vnon == 24 /\ Seq.length vkey == 32 /\
        Seq.length w == SZ.v mlen /\ Seq.length wt == 16 /\
        w == fst (Spec.secretbox vkey vnon vm) /\
        wt == snd (Spec.secretbox vkey vnon vm))
{
  let z8 = S8.classify 0uy;
  let mut subk = [| z8; 32sz |];
  Mem.track subk;
  A.pts_to_len subk;
  let mut tn = [| z8; 8sz |];
  Mem.track tn;
  A.pts_to_len tn;
  let mut b0 = [| z8; 64sz |];
  Mem.track b0;
  A.pts_to_len b0;
  A.pts_to_len subk;
  A.pts_to_len tn;

  derive subk tn b0 key nonce;
  sb_cipher c m mlen subk tn b0 (G.hide (reveal vkey)) (G.hide (reveal vnon));
  with w. assert (IO.inout c m pm (SZ.v mlen) w vm);
  unfold IO.inout;
  sb_tag tag c mlen b0 (G.hide (reveal vkey)) (G.hide (reveal vnon));
  fold (IO.inout c m pm (SZ.v mlen) w vm);
  Mem.wipe b0 64sz;
  Mem.wipe tn 8sz;
  Mem.wipe subk 32sz;
  ()
}

fn sb_open_detached (m: A.array S8.t) (c: A.array S8.t) (tag: A.array S8.t) (mlen: SZ.t)
                    (nonce: A.array S8.t) (key: A.array S8.t)
                    (#vm: erased (Seq.seq S8.t))
                    (#pc: perm) (#vc: erased (Seq.seq S8.t))
                    (#pt: perm) (#vtag: erased (Seq.seq S8.t))
                    (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires IO.inout m c pc 0 vm vc ** A.pts_to tag #pt vtag **
         A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
         pure (Seq.length vm == SZ.v mlen /\ Seq.length vc == SZ.v mlen /\
               Seq.length vc <= Spec.max_len /\ Seq.length vtag == 16 /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns ok: bool
ensures exists* (pos: nat) (w: Seq.seq S8.t).
  IO.inout m c pc pos w vc ** A.pts_to tag #pt vtag **
  A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\ Seq.length vtag == 16 /\
        Seq.length vc <= Spec.max_len /\ Seq.length w == SZ.v mlen /\
        (ok <==> Spec.secretbox_open_ok vkey vnon vc vtag) /\
        (ok ==> w == Spec.cipher vkey vnon vc))
{
  A.pts_to_len tag;
  let z8 = S8.classify 0uy;
  let mut subk = [| z8; 32sz |];
  Mem.track subk;
  A.pts_to_len subk;
  let mut tn = [| z8; 8sz |];
  Mem.track tn;
  A.pts_to_len tn;
  let mut b0 = [| z8; 64sz |];
  Mem.track b0;
  A.pts_to_len b0;
  let mut tarr = [| z8; 16sz |];
  Mem.track tarr;
  A.pts_to_len tarr;
  A.pts_to_len subk;
  A.pts_to_len tn;
  A.pts_to_len b0;

  derive subk tn b0 key nonce;
  IO.borrow_in m c;
  with q v. assert (A.pts_to c #q v);
  A.pts_to_len c;
  assert (pure (Seq.equal v vc));
  sb_tag tarr c mlen b0 (G.hide (reveal vkey)) (G.hide (reveal vnon));
  IO.return_in m c;
  let ok = bytes_eq tarr tag 16sz;
  if ok {
    sb_cipher m c mlen subk tn b0 (G.hide (reveal vkey)) (G.hide (reveal vnon));
    Mem.wipe tarr 16sz;
    Mem.wipe b0 64sz;
    Mem.wipe tn 8sz;
    Mem.wipe subk 32sz;
    true
  } else {
    Mem.wipe tarr 16sz;
    Mem.wipe b0 64sz;
    Mem.wipe tn 8sz;
    Mem.wipe subk 32sz;
    false
  }
}

#pop-options

(** {2 Secretbox, combined}

    NaCl's "easy" interface: the tag goes in front of the ciphertext in one
    buffer.  The ciphertext half is handed to the detached code as a window,
    so there is no extra copy of the message; only the sixteen tag bytes are
    moved. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 150"

fn sb_easy (c: A.array S8.t) (m: A.array S8.t) (mlen: SZ.t)
           (nonce: A.array S8.t) (key: A.array S8.t)
           (#vc: erased (Seq.seq S8.t))
           (#pm: perm) (#vm: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to c vc ** A.pts_to m #pm vm **
         A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
         pure (Seq.length vc == 16 + SZ.v mlen /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
ensures exists* (w: Seq.seq S8.t).
  A.pts_to c w ** A.pts_to m #pm vm **
  A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        Seq.length vm <= Spec.max_len /\ Seq.length w == 16 + SZ.v mlen /\
        w == Seq.append (snd (Spec.secretbox vkey vnon vm))
                        (fst (Spec.secretbox vkey vnon vm)))
{
  A.pts_to_len c;
  A.pts_to_len m;
  SZ.fits_lte (16 + SZ.v mlen) (Seq.length vc);
  let clen = SZ.add 16sz mlen;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; 16sz |];
  Mem.track tarr;
  A.pts_to_len tarr;

  let cs = Sub.sub c 16sz clen;
  IO.intro_disjoint cs m;
  sb_detached cs tarr m mlen nonce key;
  IO.elim_disjoint cs m;
  Sub.unsub c 16 (SZ.v clen) cs;
  with tv. assert (A.pts_to tarr tv);
  copy_range c 0sz tarr 0sz 16sz;

  with w. assert (A.pts_to c w);
  Seq.lemma_eq_intro w (Seq.append (snd (Spec.secretbox vkey vnon vm))
                                   (fst (Spec.secretbox vkey vnon vm)));
  Seq.lemma_eq_elim w (Seq.append (snd (Spec.secretbox vkey vnon vm))
                                  (fst (Spec.secretbox vkey vnon vm)));
  Mem.wipe tarr 16sz;
  ()
}

fn sb_open_easy (m: A.array S8.t) (c: A.array S8.t) (clen: SZ.t)
                (nonce: A.array S8.t) (key: A.array S8.t)
                (#vm: erased (Seq.seq S8.t))
                (#pc: perm) (#vc: erased (Seq.seq S8.t))
                (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to m vm ** A.pts_to c #pc vc **
         A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
         pure (Seq.length vc == SZ.v clen /\ SZ.v clen >= 16 /\
               Seq.length vm == SZ.v clen - 16 /\
               Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns ok: bool
ensures exists* (w: Seq.seq S8.t).
  A.pts_to m w ** A.pts_to c #pc vc **
  A.pts_to nonce #pn vnon ** A.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        SZ.v clen >= 16 /\ Seq.length vc == SZ.v clen /\
        Seq.length w == SZ.v clen - 16 /\
        Seq.length (Seq.slice vc 16 (SZ.v clen)) <= Spec.max_len /\
        (ok <==> Spec.secretbox_open_ok vkey vnon
                   (Seq.slice vc 16 (SZ.v clen)) (Seq.slice vc 0 16)) /\
        (ok ==> w == Spec.cipher vkey vnon (Seq.slice vc 16 (SZ.v clen))))
{
  A.pts_to_len m;
  A.pts_to_len c;
  let mlen = SZ.sub clen 16sz;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; 16sz |];
  Mem.track tarr;
  A.pts_to_len tarr;

  let tw = Sub.sub c 0sz 16sz;
  copy_range tarr 0sz tw 0sz 16sz;
  with tv. assert (A.pts_to tarr tv);
  Seq.lemma_eq_intro tv (Seq.slice vc 0 16);
  Seq.lemma_eq_elim tv (Seq.slice vc 0 16);
  Sub.unsub_id c 0 16 tw;

  let cw = Sub.sub c 16sz clen;
  IO.intro_disjoint m cw;
  let ok = sb_open_detached m cw tarr mlen nonce key;
  IO.elim_disjoint m cw;
  Sub.unsub_id c 16 (SZ.v clen) cw;
  Mem.wipe tarr 16sz;
  ok
}

#pop-options

(** {2 Box}

    X25519 and then HSalsa20 with an all-zero nonce.  The agreement fails
    exactly when the shared secret is zero, which is X25519's own contributory
    behaviour check; the derived key is written either way, and the caller is
    expected to look at the return value. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn box_beforenm (k: A.array S8.t) (pk: A.array S8.t) (sk: A.array S8.t)
                (#vk: erased (Seq.seq S8.t))
                (#pp: perm) (#vpk: erased (Seq.lseq S8.t 32))
                (#psk: perm) (#vsk: erased (Seq.lseq S8.t 32))
requires A.pts_to k vk ** A.pts_to pk #pp vpk ** A.pts_to sk #psk vsk **
         pure (Seq.length vk == 32)
returns ok: bool
ensures exists* (w: Seq.seq S8.t).
  A.pts_to k w ** A.pts_to pk #pp vpk ** A.pts_to sk #psk vsk **
  pure (Seq.length w == 32 /\
        w == fst (Spec.beforenm vpk vsk) /\ ok == snd (Spec.beforenm vpk vsk))
{
  A.pts_to_len k;
  let z8 = S8.classify 0uy;
  let mut s = [| z8; 32sz |];
  Mem.track s;
  A.pts_to_len s;
  let mut zn = [| z8; 16sz |];
  Mem.track zn;
  A.pts_to_len zn;
  A.pts_to_len s;

  let ok = Curve.ecdh s sk pk;
  with zv. assert (A.pts_to zn zv);
  Seq.lemma_eq_intro zv Spec.zero_nonce;
  Seq.lemma_eq_elim zv Spec.zero_nonce;
  Salsa.hsalsa20 k s zn;
  Mem.wipe zn 16sz;
  Mem.wipe s 32sz;
  ok
}

#pop-options

(** {2 The C entry points}

    NaCl's return convention, and NaCl's names.  The length arguments are
    [size_t] rather than HACL*'s [uint32_t], because that is what the rest of
    this library uses. *)

let status (b: bool) : U32.t = if b then 0ul else 0xfffffffful

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn crypto_secretbox_detached (c: A.array S8.t) (tag: A.array S8.t)
                             (m: A.array S8.t) (mlen: SZ.t)
                             (n: A.array S8.t) (k: A.array S8.t)
                             (#vc: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
                             (#pm: perm) (#vm: erased (Seq.seq S8.t))
                             (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                             (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires IO.inout c m pm 0 vc vm ** A.pts_to tag vtag **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vc == SZ.v mlen /\ Seq.length vtag == 16 /\
               Seq.length vm == SZ.v mlen /\ Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t) (wt: Seq.seq S8.t).
  IO.inout c m pm (SZ.v mlen) w vm ** A.pts_to tag wt **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        Seq.length vm <= Spec.max_len /\
        Seq.length w == SZ.v mlen /\ Seq.length wt == 16 /\
        res == 0ul /\
        w == fst (Spec.secretbox vkey vnon vm) /\
        wt == snd (Spec.secretbox vkey vnon vm))
{
  sb_detached c tag m mlen n k;
  0ul
}

fn crypto_secretbox_open_detached (m: A.array S8.t) (c: A.array S8.t) (tag: A.array S8.t)
                                  (mlen: SZ.t) (n: A.array S8.t) (k: A.array S8.t)
                                  (#vm: erased (Seq.seq S8.t))
                                  (#pc: perm) (#vc: erased (Seq.seq S8.t))
                                  (#pt: perm) (#vtag: erased (Seq.seq S8.t))
                                  (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                                  (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires IO.inout m c pc 0 vm vc ** A.pts_to tag #pt vtag **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vm == SZ.v mlen /\ Seq.length vc == SZ.v mlen /\
               Seq.length vc <= Spec.max_len /\ Seq.length vtag == 16 /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (pos: nat) (w: Seq.seq S8.t).
  IO.inout m c pc pos w vc ** A.pts_to tag #pt vtag **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\ Seq.length vtag == 16 /\
        Seq.length vc <= Spec.max_len /\ Seq.length w == SZ.v mlen /\
        (res == 0ul <==> Spec.secretbox_open_ok vkey vnon vc vtag) /\
        (res == 0ul ==> w == Spec.cipher vkey vnon vc))
{
  let ok = sb_open_detached m c tag mlen n k;
  status ok
}

fn crypto_secretbox_easy (c: A.array S8.t) (m: A.array S8.t) (mlen: SZ.t)
                         (n: A.array S8.t) (k: A.array S8.t)
                         (#vc: erased (Seq.seq S8.t))
                         (#pm: perm) (#vm: erased (Seq.seq S8.t))
                         (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                         (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to c vc ** A.pts_to m #pm vm **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vc == 16 + SZ.v mlen /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t).
  A.pts_to c w ** A.pts_to m #pm vm **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        Seq.length vm <= Spec.max_len /\ Seq.length w == 16 + SZ.v mlen /\
        res == 0ul /\
        w == Seq.append (snd (Spec.secretbox vkey vnon vm))
                        (fst (Spec.secretbox vkey vnon vm)))
{
  sb_easy c m mlen n k;
  0ul
}

fn crypto_secretbox_open_easy (m: A.array S8.t) (c: A.array S8.t) (clen: SZ.t)
                              (n: A.array S8.t) (k: A.array S8.t)
                              (#vm: erased (Seq.seq S8.t))
                              (#pc: perm) (#vc: erased (Seq.seq S8.t))
                              (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                              (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to m vm ** A.pts_to c #pc vc **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vc == SZ.v clen /\ SZ.v clen >= 16 /\
               Seq.length vm == SZ.v clen - 16 /\ Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t).
  A.pts_to m w ** A.pts_to c #pc vc **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        SZ.v clen >= 16 /\ Seq.length vc == SZ.v clen /\
        Seq.length w == SZ.v clen - 16 /\
        Seq.length (Seq.slice vc 16 (SZ.v clen)) <= Spec.max_len /\
        (res == 0ul <==> Spec.secretbox_open_ok vkey vnon
                           (Seq.slice vc 16 (SZ.v clen)) (Seq.slice vc 0 16)) /\
        (res == 0ul ==> w == Spec.cipher vkey vnon (Seq.slice vc 16 (SZ.v clen))))
{
  let ok = sb_open_easy m c clen n k;
  status ok
}

fn crypto_box_beforenm (k: A.array S8.t) (pk: A.array S8.t) (sk: A.array S8.t)
                       (#vk: erased (Seq.seq S8.t))
                       (#pp: perm) (#vpk: erased (Seq.lseq S8.t 32))
                       (#psk: perm) (#vsk: erased (Seq.lseq S8.t 32))
requires A.pts_to k vk ** A.pts_to pk #pp vpk ** A.pts_to sk #psk vsk **
         pure (Seq.length vk == 32)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t).
  A.pts_to k w ** A.pts_to pk #pp vpk ** A.pts_to sk #psk vsk **
  pure (Seq.length w == 32 /\ w == fst (Spec.beforenm vpk vsk) /\
        (res == 0ul <==> snd (Spec.beforenm vpk vsk)))
{
  let ok = box_beforenm k pk sk;
  status ok
}

#pop-options

(** After [beforenm] there is nothing left of box but secretbox, so the four
    [_afternm] entry points are the four secretbox ones under another name. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

fn crypto_box_detached_afternm (c: A.array S8.t) (tag: A.array S8.t)
                               (m: A.array S8.t) (mlen: SZ.t)
                               (n: A.array S8.t) (k: A.array S8.t)
                               (#vc: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
                               (#pm: perm) (#vm: erased (Seq.seq S8.t))
                               (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                               (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires IO.inout c m pm 0 vc vm ** A.pts_to tag vtag **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vc == SZ.v mlen /\ Seq.length vtag == 16 /\
               Seq.length vm == SZ.v mlen /\ Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t) (wt: Seq.seq S8.t).
  IO.inout c m pm (SZ.v mlen) w vm ** A.pts_to tag wt **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        Seq.length vm <= Spec.max_len /\
        Seq.length w == SZ.v mlen /\ Seq.length wt == 16 /\ res == 0ul /\
        w == fst (Spec.secretbox vkey vnon vm) /\
        wt == snd (Spec.secretbox vkey vnon vm))
{
  sb_detached c tag m mlen n k;
  0ul
}

fn crypto_box_open_detached_afternm (m: A.array S8.t) (c: A.array S8.t)
                                    (tag: A.array S8.t) (mlen: SZ.t)
                                    (n: A.array S8.t) (k: A.array S8.t)
                                    (#vm: erased (Seq.seq S8.t))
                                    (#pc: perm) (#vc: erased (Seq.seq S8.t))
                                    (#pt: perm) (#vtag: erased (Seq.seq S8.t))
                                    (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                                    (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires IO.inout m c pc 0 vm vc ** A.pts_to tag #pt vtag **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vm == SZ.v mlen /\ Seq.length vc == SZ.v mlen /\
               Seq.length vc <= Spec.max_len /\ Seq.length vtag == 16 /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (pos: nat) (w: Seq.seq S8.t).
  IO.inout m c pc pos w vc ** A.pts_to tag #pt vtag **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\ Seq.length vtag == 16 /\
        Seq.length vc <= Spec.max_len /\ Seq.length w == SZ.v mlen /\
        (res == 0ul <==> Spec.secretbox_open_ok vkey vnon vc vtag) /\
        (res == 0ul ==> w == Spec.cipher vkey vnon vc))
{
  let ok = sb_open_detached m c tag mlen n k;
  status ok
}

fn crypto_box_easy_afternm (c: A.array S8.t) (m: A.array S8.t) (mlen: SZ.t)
                           (n: A.array S8.t) (k: A.array S8.t)
                           (#vc: erased (Seq.seq S8.t))
                           (#pm: perm) (#vm: erased (Seq.seq S8.t))
                           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to c vc ** A.pts_to m #pm vm **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vc == 16 + SZ.v mlen /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t).
  A.pts_to c w ** A.pts_to m #pm vm **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        Seq.length vm <= Spec.max_len /\ Seq.length w == 16 + SZ.v mlen /\
        res == 0ul /\
        w == Seq.append (snd (Spec.secretbox vkey vnon vm))
                        (fst (Spec.secretbox vkey vnon vm)))
{
  sb_easy c m mlen n k;
  0ul
}

fn crypto_box_open_easy_afternm (m: A.array S8.t) (c: A.array S8.t) (clen: SZ.t)
                                (n: A.array S8.t) (k: A.array S8.t)
                                (#vm: erased (Seq.seq S8.t))
                                (#pc: perm) (#vc: erased (Seq.seq S8.t))
                                (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                                (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to m vm ** A.pts_to c #pc vc **
         A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
         pure (Seq.length vc == SZ.v clen /\ SZ.v clen >= 16 /\
               Seq.length vm == SZ.v clen - 16 /\ Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24 /\ Seq.length vkey == 32)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t).
  A.pts_to m w ** A.pts_to c #pc vc **
  A.pts_to n #pn vnon ** A.pts_to k #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 24 /\
        SZ.v clen >= 16 /\ Seq.length vc == SZ.v clen /\
        Seq.length w == SZ.v clen - 16 /\
        Seq.length (Seq.slice vc 16 (SZ.v clen)) <= Spec.max_len /\
        (res == 0ul <==> Spec.secretbox_open_ok vkey vnon
                           (Seq.slice vc 16 (SZ.v clen)) (Seq.slice vc 0 16)) /\
        (res == 0ul ==> w == Spec.cipher vkey vnon (Seq.slice vc 16 (SZ.v clen))))
{
  let ok = sb_open_easy m c clen n k;
  status ok
}

#pop-options

(** And the four that do the agreement themselves.  Nothing is written to the
    output when the agreement fails. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn crypto_box_detached (c: A.array S8.t) (tag: A.array S8.t)
                       (m: A.array S8.t) (mlen: SZ.t) (n: A.array S8.t)
                       (pk: A.array S8.t) (sk: A.array S8.t)
                       (#vc: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
                       (#pm: perm) (#vm: erased (Seq.seq S8.t))
                       (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                       (#pp: perm) (#vpk: erased (Seq.lseq S8.t 32))
                       (#ps: perm) (#vsk: erased (Seq.lseq S8.t 32))
requires IO.inout c m pm 0 vc vm ** A.pts_to tag vtag **
         A.pts_to n #pn vnon ** A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
         pure (Seq.length vc == SZ.v mlen /\ Seq.length vtag == 16 /\
               Seq.length vm == SZ.v mlen /\ Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24)
returns res: U32.t
ensures exists* (pos: nat) (w: Seq.seq S8.t) (wt: Seq.seq S8.t).
  IO.inout c m pm pos w vm ** A.pts_to tag wt **
  A.pts_to n #pn vnon ** A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
  pure (Seq.length vnon == 24 /\ Seq.length vm <= Spec.max_len /\
        Seq.length w == SZ.v mlen /\ Seq.length wt == 16 /\
        (res == 0ul <==> snd (Spec.beforenm vpk vsk)) /\
        (res == 0ul ==>
           w == fst (Spec.secretbox (fst (Spec.beforenm vpk vsk)) vnon vm) /\
           wt == snd (Spec.secretbox (fst (Spec.beforenm vpk vsk)) vnon vm)))
{
  A.pts_to_len tag;
  IO.inout_len c m;
  let z8 = S8.classify 0uy;
  let mut kk = [| z8; 32sz |];
  Mem.track kk;
  A.pts_to_len kk;
  let ok = box_beforenm kk pk sk;
  if ok {
    sb_detached c tag m mlen n kk;
    Mem.wipe kk 32sz;
    0ul
  } else {
    Mem.wipe kk 32sz;
    0xfffffffful
  }
}

fn crypto_box_open_detached (m: A.array S8.t) (c: A.array S8.t) (tag: A.array S8.t)
                            (mlen: SZ.t) (n: A.array S8.t)
                            (pk: A.array S8.t) (sk: A.array S8.t)
                            (#vm: erased (Seq.seq S8.t))
                            (#pc: perm) (#vc: erased (Seq.seq S8.t))
                            (#pt: perm) (#vtag: erased (Seq.seq S8.t))
                            (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                            (#pp: perm) (#vpk: erased (Seq.lseq S8.t 32))
                            (#ps: perm) (#vsk: erased (Seq.lseq S8.t 32))
requires IO.inout m c pc 0 vm vc ** A.pts_to tag #pt vtag **
         A.pts_to n #pn vnon ** A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
         pure (Seq.length vm == SZ.v mlen /\ Seq.length vc == SZ.v mlen /\
               Seq.length vc <= Spec.max_len /\ Seq.length vtag == 16 /\
               Seq.length vnon == 24)
returns res: U32.t
ensures exists* (pos: nat) (w: Seq.seq S8.t).
  IO.inout m c pc pos w vc ** A.pts_to tag #pt vtag **
  A.pts_to n #pn vnon ** A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
  pure (Seq.length vnon == 24 /\ Seq.length vtag == 16 /\
        Seq.length vc <= Spec.max_len /\ Seq.length w == SZ.v mlen /\
        (res == 0ul <==>
           (snd (Spec.beforenm vpk vsk) /\
            Spec.secretbox_open_ok (fst (Spec.beforenm vpk vsk)) vnon vc vtag)) /\
        (res == 0ul ==> w == Spec.cipher (fst (Spec.beforenm vpk vsk)) vnon vc))
{
  IO.inout_len m c;
  let z8 = S8.classify 0uy;
  let mut kk = [| z8; 32sz |];
  Mem.track kk;
  A.pts_to_len kk;
  let ok = box_beforenm kk pk sk;
  if ok {
    let ok2 = sb_open_detached m c tag mlen n kk;
    Mem.wipe kk 32sz;
    status ok2
  } else {
    Mem.wipe kk 32sz;
    0xfffffffful
  }
}

fn crypto_box_easy (c: A.array S8.t) (m: A.array S8.t) (mlen: SZ.t) (n: A.array S8.t)
                   (pk: A.array S8.t) (sk: A.array S8.t)
                   (#vc: erased (Seq.seq S8.t))
                   (#pm: perm) (#vm: erased (Seq.seq S8.t))
                   (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                   (#pp: perm) (#vpk: erased (Seq.lseq S8.t 32))
                   (#ps: perm) (#vsk: erased (Seq.lseq S8.t 32))
requires A.pts_to c vc ** A.pts_to m #pm vm ** A.pts_to n #pn vnon **
         A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
         pure (Seq.length vc == 16 + SZ.v mlen /\ Seq.length vm == SZ.v mlen /\
               Seq.length vm <= Spec.max_len /\ Seq.length vnon == 24)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t).
  A.pts_to c w ** A.pts_to m #pm vm ** A.pts_to n #pn vnon **
  A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
  pure (Seq.length vnon == 24 /\ Seq.length vm <= Spec.max_len /\
        Seq.length w == 16 + SZ.v mlen /\
        (res == 0ul <==> snd (Spec.beforenm vpk vsk)) /\
        (res == 0ul ==>
           w == Seq.append (snd (Spec.secretbox (fst (Spec.beforenm vpk vsk)) vnon vm))
                           (fst (Spec.secretbox (fst (Spec.beforenm vpk vsk)) vnon vm))))
{
  A.pts_to_len c;
  let z8 = S8.classify 0uy;
  let mut kk = [| z8; 32sz |];
  Mem.track kk;
  A.pts_to_len kk;
  let ok = box_beforenm kk pk sk;
  if ok {
    sb_easy c m mlen n kk;
    Mem.wipe kk 32sz;
    0ul
  } else {
    Mem.wipe kk 32sz;
    0xfffffffful
  }
}

fn crypto_box_open_easy (m: A.array S8.t) (c: A.array S8.t) (clen: SZ.t)
                        (n: A.array S8.t) (pk: A.array S8.t) (sk: A.array S8.t)
                        (#vm: erased (Seq.seq S8.t))
                        (#pc: perm) (#vc: erased (Seq.seq S8.t))
                        (#pn: perm) (#vnon: erased (Seq.seq S8.t))
                        (#pp: perm) (#vpk: erased (Seq.lseq S8.t 32))
                        (#ps: perm) (#vsk: erased (Seq.lseq S8.t 32))
requires A.pts_to m vm ** A.pts_to c #pc vc ** A.pts_to n #pn vnon **
         A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
         pure (Seq.length vc == SZ.v clen /\ SZ.v clen >= 16 /\
               Seq.length vm == SZ.v clen - 16 /\ Seq.length vm <= Spec.max_len /\
               Seq.length vnon == 24)
returns res: U32.t
ensures exists* (w: Seq.seq S8.t).
  A.pts_to m w ** A.pts_to c #pc vc ** A.pts_to n #pn vnon **
  A.pts_to pk #pp vpk ** A.pts_to sk #ps vsk **
  pure (Seq.length vnon == 24 /\ SZ.v clen >= 16 /\ Seq.length vc == SZ.v clen /\
        Seq.length w == SZ.v clen - 16 /\
        Seq.length (Seq.slice vc 16 (SZ.v clen)) <= Spec.max_len /\
        (res == 0ul <==>
           (snd (Spec.beforenm vpk vsk) /\
            Spec.secretbox_open_ok (fst (Spec.beforenm vpk vsk)) vnon
              (Seq.slice vc 16 (SZ.v clen)) (Seq.slice vc 0 16))) /\
        (res == 0ul ==>
           w == Spec.cipher (fst (Spec.beforenm vpk vsk)) vnon
                            (Seq.slice vc 16 (SZ.v clen))))
{
  A.pts_to_len m;
  A.pts_to_len c;
  let z8 = S8.classify 0uy;
  let mut kk = [| z8; 32sz |];
  Mem.track kk;
  A.pts_to_len kk;
  let ok = box_beforenm kk pk sk;
  if ok {
    let ok2 = sb_open_easy m c clen n kk;
    Mem.wipe kk 32sz;
    status ok2
  } else {
    Mem.wipe kk 32sz;
    0xfffffffful
  }
}

#pop-options
