CURVE="P384"
CNAME="P-384"
MOD="Spec.P384.GroupAssoc1"
I=1
pairs=[("smul lx ry","smul rx ly"),("smul lx rz","smul rx lz"),("smul ly rz","smul ry lz")]
enss=["P.fmul lx ry == P.fmul rx ly","P.fmul lx rz == P.fmul rx lz","P.fmul ly rz == P.fmul ry lz"]
CHECKS=[dict(name="assoc1", doc="Associativity on affine points, cross product 1 of 3.", n=6, vars=["x1","y1","x2","y2","x3","y3"],
  hyps=[('aff',0,1),('aff',2,3),('aff',4,5)], req="on x1 y1 /\\ on x2 y2 /\\ on x3 y3", rl=100,
  lets=["let p = aff #c 0 1","let q = aff #c 2 3","let r = aff #c 4 5",
        "let (lx, ly, lz) = point_add_sv b (point_add_sv b p q) r",
        "let (rx, ry, rz) = point_add_sv b p (point_add_sv b q r)"],
  pairs=[pairs[I-1]],
  proof=["aff_val c 0 1","aff_val c 2 3","aff_val c 4 5","point_add_val c b p q","point_add_val c b (point_add_sv b p q) r",
         "point_add_val c b q r","point_add_val c b p (point_add_sv b q r)"],
  ens="(let a = (x1, y1, P.fone) in let b = (x2, y2, P.fone) in let c = (x3, y3, P.fone) in let (lx, ly, lz) = P.point_add (P.point_add a b) c in let (rx, ry, rz) = P.point_add a (P.point_add b c) in "+enss[I-1]+")")]
