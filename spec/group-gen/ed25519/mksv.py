import os
HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.join(HERE, '..', '..')
p=2**255-19
d=37095705934669439343138083508754565189542113879843219016388785533085940283555
d2=(2*d)%p; dinv=pow(d,-1,p)
def envf(n):
    xs=[f"x{i}" for i in range(n)]
    envl="; ".join(f"fromf {x}" for x in xs)
    ens=" /\\ ".join(f"tof (nth0 0 c.env {i}) == x{i}" for i in range(n))
    return f"""let envf{n} (c: ctx) ({' '.join(xs)}: E.elem)
  : Lemma (requires c.m == m0 /\\ c.env == [{envl}]) (ensures {ens}) =
  o_eqs ()"""
ENVF="\n".join(envf(n) for n in range(1,11))
s=open(os.path.join(HERE, 'sv.tmpl')).read().replace('%ENVF%',ENVF).replace('%P%',str(p)).replace('%D%',str(d)).replace('%D2%',str(d2)).replace('%DINV%',str(dinv))
open(os.path.join(SPEC, 'Spec.Ed25519.GroupSv.fst'),'w').write(s)
