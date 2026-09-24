import os
HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.join(HERE, '..', '..')
R=SPEC+'/'
s=open(R+'Spec.P256.GroupNR.fst').read()
pk=2**256-2**32-977
c0=(-392)%pk
s=s.replace("module Spec.P256.GroupNR","module Spec.K256.GroupNR").replace("open Spec.P256.GroupSv","open Spec.K256.GroupSv").replace("module P = Spec.P256","module P = Spec.K256")
i=s.index("(** Two polynomials"); j=s.index("*)",i)+2
s=s[:i]+"""(** Two polynomials without roots in the secp256k1 field.

    [f = x^3 + 7]: a root would be a point of order two, and the group has
    odd prime order.  [q = x^6 + 140 x^3 - 392] is what the second
    coordinate of [point_add P (-P)] reduces to on an affine point; it is
    irreducible over the field.  Both are certified by
    {!Spec.Group.Check.nr_check}, with cofactors computed by PARI/GP. *)"""+s[j:]
def repl_def(s, head, new):
    i=s.index(head); j=s.index("\n\n",i); return s[:i]+new+s[j:]
s=repl_def(s,"let qb (c: ctx)",f"""let qb (c: ctx) (x: sv c) : sv c =
  let x3 = smul (smul x x) x in
  sadd (sadd (smul x3 x3) (smul (kc c 140) x3)) (kc c {c0})""")
s=repl_def(s,"let fq (x: P.felem)",f"""let fq (x: P.felem) : P.felem =
  let x3 = P.fmul (P.fmul x x) x in
  P.fadd (P.fadd (P.fmul x3 x3) (P.fmul (cst 140) x3)) (cst {c0})""")
uf="0; 0; 46758632835564736012269203954919337884311706168562511263687580192619680188360"
uq="0; 0; 95759930878925550389862433258728329785182363458630619644079867686454730649882; 0; 0; 111244439360252908099111608111787426390337830471608360441708511948622550931786"
import re
s=re.sub(r"let uf : list nat = \[.*?\]",f"let uf : list nat = [{uf}]",s)
s=re.sub(r"let uq : list nat = \[.*?\]",f"let uq : list nat = [{uq}]",s)
open(R+'Spec.K256.GroupNR.fst','w').write(s)
