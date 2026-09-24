import re
import os
HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.join(HERE, '..', '..')
R=SPEC+'/'
s=open(R+'Spec.P256.GroupSv.fst').read()
spec=open(R+'Spec.K256.fst').read()
def body(name):
    i=spec.index(f"let {name} (")
    j=spec.index("\n\n",i)
    txt=spec[i:j]
    lines=txt.split("\n")[1:]
    out=[]
    for l in lines:
        l=re.sub(r'\bfmul\b','smul',l); l=re.sub(r'\bfadd\b','sadd',l); l=re.sub(r'\bfsub\b','ssub',l)
        l=re.sub(r'\bb3\b','b',l)
        out.append(l)
    return "\n".join(out)
def replace_def(s, header, newbody):
    i=s.index(header); j=s.index("\n\n",i)
    return s[:i]+header+"\n"+newbody+s[j:]
s=s.replace("module Spec.P256.GroupSv","module Spec.K256.GroupSv").replace("module P = Spec.P256","module P = Spec.K256")
s=s.replace("The P-256 formulas","The secp256k1 formulas")
s=s.replace("0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff","0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")
s=s.replace("let bl : nat = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b","let bl : nat = 7")
s=s.replace("let bl_lem () : Lemma (bl < m0 /\\ bl == P.b_coeff) = m0_lem (); assert_norm (bl == P.b_coeff)",
 "let bl_lem () : Lemma (bl < m0 /\\ bl == P.b_coeff) = m0_lem (); assert_norm (bl == P.b_coeff)\n\n(** [3 b], the only curve constant the formulas use. *)\nlet b3l : nat = 21\n\nlet b3_lem () : Lemma (b3l < m0 /\\ b3l == P.b3) = m0_lem (); assert_norm (b3l == P.b3)")
s=s.replace("Spec.Group.Primes.prime_p256 ()","Spec.Group.Primes.prime_k256 ()")
s=replace_def(s,"let point_add_sv (#c: ctx) (b: sv c) (p q: sp c) : sp c =",body("point_add"))
s=replace_def(s,"let point_double_sv (#c: ctx) (b: sv c) (p: sp c) : sp c =",body("point_double"))
s=s.replace("requires ok c /\\ c.o == o /\\ vl b == bl)","requires ok c /\\ c.o == o /\\ vl b == b3l)")
s=s.replace("  = m0_lem (); bl_lem (); o_eqs ();\n    FStar.Pervasives.reveal_opaque (`%P.point_","  = m0_lem (); b3_lem (); o_eqs ();\n    FStar.Pervasives.reveal_opaque (`%P.point_")
s=s.replace("(** [x^3 - 3x + b], the right-hand side","(** [x^3 + 7], the right-hand side")
s=s.replace("  sadd (ssub (smul (smul x x) x) (smul (kc c 3) x)) (kc c bl)","  sadd (smul (smul x x) x) (kc c bl)")
s=s.replace("  P.fadd (P.fsub (P.fmul (P.fmul x x) x) (P.fmul (cst 3) x)) (cst bl)","  P.fadd (P.fmul (P.fmul x x) x) (cst bl)")
s=s.replace("exactly as in [Spec.P256.Group]","exactly as in [Spec.K256.Group]")
s=s.replace("""  P.fadd (P.fsub (P.fmul (P.fmul x x) x)
                 (P.fmul (P.fmul (P.fadd P.fone (P.fadd P.fone P.fone)) x) (P.fmul z z)))
         (P.fmul P.b_coeff (P.fmul (P.fmul z z) z))""","""  P.fadd (P.fmul (P.fmul x x) x) (P.fmul P.b_coeff (P.fmul (P.fmul z z) z))""")
s=s.replace("""  let one = kc c 1 in
  sadd (ssub (smul (smul x x) x) (smul (smul (sadd one (sadd one one)) x) (smul z z)))
       (smul (kc c bl) (smul (smul z z) z))""","""  sadd (smul (smul x x) x) (smul (kc c bl) (smul (smul z z) z))""")
open(R+'Spec.K256.GroupSv.fst','w').write(s)
