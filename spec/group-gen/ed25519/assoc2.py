MOD="Spec.Ed25519.GroupAssoc2"
C="1"
AFF3=[('aff',0,1),('aff',2,3),('aff',4,5)]
if C=="0":
  lets=["let a = aff #c 0 1","let bq = aff #c 2 3","let cq = aff #c 4 5","let l = point_add_sv b (point_add_sv b a bq) cq","let r = point_add_sv b a (point_add_sv b bq cq)","let (l0, _, l2, _) = l","let (r0, _, r2, _) = r"]
  pairs=[("smul l0 r2","smul r0 l2")]
  ens="(let l = padd (padd (cpt u1 v1) (cpt u2 v2)) (cpt u3 v3) in let r = padd (cpt u1 v1) (padd (cpt u2 v2) (cpt u3 v3)) in let (l0, _, l2, _) = l in let (r0, _, r2, _) = r in E.fmul l0 r2 == E.fmul r0 l2)"
else:
  lets=["let a = aff #c 0 1","let bq = aff #c 2 3","let cq = aff #c 4 5","let l = point_add_sv b (point_add_sv b a bq) cq","let r = point_add_sv b a (point_add_sv b bq cq)","let (_, l1, l2, _) = l","let (_, r1, r2, _) = r"]
  pairs=[("smul l1 r2","smul r1 l2")]
  ens="(let l = padd (padd (cpt u1 v1) (cpt u2 v2)) (cpt u3 v3) in let r = padd (cpt u1 v1) (padd (cpt u2 v2) (cpt u3 v3)) in let (_, l1, l2, _) = l in let (_, r1, r2, _) = r in E.fmul l1 r2 == E.fmul r1 l2)"
CHECKS=[dict(name="assoc2", doc="Associativity, cross product of coordinate 1.", n=6, vars=["u1","v1","u2","v2","u3","v3"],
  hyps=AFF3, req="on u1 v1 /\\ on u2 v2 /\\ on u3 v3", rl=100, lets=lets, pairs=pairs,
  proof=["aff_val c 0 1","aff_val c 2 3","aff_val c 4 5","point_add_val c b a bq","point_add_val c b (point_add_sv b a bq) cq","point_add_val c b bq cq","point_add_val c b a (point_add_sv b bq cq)"],
  ens=ens)]
