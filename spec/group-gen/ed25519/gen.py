import sys
import os
HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.join(HERE, '..', '..')
HEAD = open(os.path.join(HERE, 'hdr.txt')).read()

def hyp_sv(h, cv):
    if h[0]=='aff': return f"aff_hyp {cv} {h[1]} {h[2]}"
    return f"hom_hyp {cv} {h[1]} {h[2]} {h[3]}"

def hyp_ok(h):
    if h[0]=='aff': return f"aff_hyp_ok c0 {h[1]} {h[2]}"
    return f"hom_hyp_ok c0 {h[1]} {h[2]} {h[3]}"

def gen(k):
    global BL
    name=k['name']; n=k['n']; vs=k['vars']; hyps=k.get('hyps',[])
    hl="[" + "; ".join(hyp_sv(h,'c0') for h in hyps) + "]"
    out=[]
    for l in k.get('pre',[]): out.append(l); out.append("")
    out.append(f"(** {k['doc']} *)")
    # chk
    out.append(f"let {name}_chk (o': fops m0) (env: list (elem m0)) : bool =")
    out.append(f"  let c0 = base m0 fl o' {n} env in")
    if hyps:
        out.append(f"  let hs = {hl} in")
        out.append(f"  let c = with_hyps c0 hs in")
    else:
        out.append(f"  let c = c0 in")
    out.append(f"  let b = kc c {BL} in")
    for l in k['lets']: out.append("  "+l+" in")
    conds=(["shapes hs"] if hyps else [])+[f"Nil? (fst (ssub ({a}) ({b})))" for a,b in k['pairs']]
    out.append("  "+" &&\n  ".join(conds))
    out.append("")
    out.append(f"let {name}_ok (o': fops m0) (env: list (elem m0)) : Lemma ({name}_chk o' env == true) =")
    out.append(f"  assert ({name}_chk o' env == true) by (poly_tac ())")
    out.append("")
    out.append(f'#push-options "--fuel 0 --ifuel 1 --z3rlimit {k.get("rl",50)}"')
    envl="[" + "; ".join(f"fromf {v}" for v in vs) + "]"
    vdecl=" ".join(vs)
    req=k.get('req')
    reqs=f"(requires {req})\n          " if req else ""
    if hyps:
        out.append(f"let {name}_ctx ({vdecl}: E.elem)")
        out.append(f"  : Lemma {reqs}(ensures (let env = {envl} in")
        out.append(f"                    let c0 = base m0 fl o {n} env in")
        out.append(f"                    let c = with_hyps c0 {hl} in")
        out.append(f"                    ok c /\\ c.m == m0 /\\ c.o == o /\\ c.nv == {n} /\\ c.env == env))")
        out.append(f"  = o_ok (); o_eqs ();")
        out.append(f"    let env = {envl} in")
        out.append(f"    let c0 = base m0 fl o {n} env in")
        out.append(f"    base_ok m0 fl o {n} env;")
        out.append(f"    envf{n} c0 {vdecl};")
        for h in hyps: out.append(f"    {hyp_ok(h)};")
        hs=[hyp_sv(h,'c0') for h in hyps]
        if len(hs)<=3:
            out.append(f"    holds{len(hs)} " + " ".join(f"({x})" for x in hs) + ";")
        else:
            raise Exception("too many hyps")
        out.append(f"    hyps_ok c0 {hl}")
        out.append("")
    out.append(f"let {name} ({vdecl}: E.elem)")
    out.append(f"  : Lemma {reqs}(ensures {k['ens']})")
    out.append(f"  = let env = {envl} in")
    out.append(f"    {name}_ok o env;")
    out.append(f"    let c0 = base m0 fl o {n} env in")
    if hyps:
        out.append(f"    {name}_ctx {vdecl};")
        out.append(f"    let c = with_hyps c0 {hl} in")
    else:
        out.append(f"    o_ok (); base_ok m0 fl o {n} env;")
        out.append(f"    let c = c0 in")
    out.append(f"    envf{n} c {vdecl};")
    out.append(f"    o_eqs (); m0_lem (); d_lem (); cst_lem ();")
    out.append(f"    let b = kc c {BL} in")
    out.append(f"    assert_norm ({BL} % m0 == {BL});")
    for l in k['lets']: out.append("    "+l+" in")
    for p in k['proof']: out.append("    "+p+";")
    for a,b in k['pairs']:
        out.append(f"    assert (Nil? (fst (ssub ({a}) ({b}))));")
        out.append(f"    sv_eq ({a}) ({b});")
    out.append(f"    ()")
    out.append("#pop-options")
    out.append("")
    return "\n".join(out)

if __name__=="__main__":
    BL="d2l"; CURVE="Ed25519"; CNAME="Ed25519"
    exec(open(sys.argv[1]).read())
    s=HEAD.replace("%MOD%",MOD).replace("%CURVE%",CURVE).replace("%CNAME%",CNAME)+"\n"+"\n".join(gen(k) for k in CHECKS)
    open(sys.argv[2],'w').write(s)
