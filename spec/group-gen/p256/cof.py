from sympy import *
import sys
x1,y1,x2,y2,b=symbols('x1 y1 x2 y2 b')
p=2**256-2**224+2**192+2**96-1
bl=0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
def tolist(s, vs, bval):
    e=sympify(s).subs(b,bval)
    P=Poly(expand(e),*vs)
    out=[]
    for mon,cf in P.terms():
        cf=Rational(cf)
        v=(int(cf.p)*pow(int(cf.q),-1,p))%p
        out.append((v,list(mon)))
    return out
def fst(ts):
    return "[" + "; ".join(f"({v}, [{'; '.join(map(str,m))}])" for v,m in ts) + "]"
if __name__=="__main__":
    lines=[l for l in open(sys.argv[1]).read().split("\n") if l.strip() and not l.startswith("//") and "sizes" not in l and "G:" not in l]
    for i,l in enumerate(lines[:3]):
        print(f"let cof{i+1} : list (nat & list nat) = {fst(tolist(l,[x1,y1,x2,y2],bl))}")
