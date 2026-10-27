CURVE="P384"
CNAME="P-384"
MOD="Spec.P384.JacChecks"
OPENS="\nopen Spec.P384.JacSv"
V=lambda i: f"(svar c {i})"
J=[('jac',0,1,2)]
CHECKS=[

dict(name="j1", doc="Jacobian doubling preserves the Jacobian equation.", n=3, vars=["x","y","z"],
  hyps=J, req="jeq (x, y, z)",
  lets=["let p = var3 #c 0 1 2","let (rx, ry, rz) = jdouble_sv p"],
  pairs=[("smul ry ry","eqn_rsv (rx, ry, smul rz rz)")],
  proof=["var3_val c 0 1 2","jdouble_val c p","jeq_val c (rx, ry, rz)"],
  ens="jeq (jdouble (x, y, z))"),
dict(name="j2", doc="Jacobian doubling agrees with homogeneous doubling, projectively.", n=3, vars=["x","y","z"],
  hyps=J, req="jeq (x, y, z)",
  lets=["let p = var3 #c 0 1 2","let (ax, ay, az) = to_h_sv (jdouble_sv p)","let (dx, dy, dz) = point_double_sv b (to_h_sv p)"],
  pairs=[("smul ax dy","smul dx ay"),("smul ax dz","smul dx az"),("smul ay dz","smul dy az")],
  proof=["var3_val c 0 1 2","jdouble_val c p","to_h_val c (jdouble_sv p)","to_h_val c p","point_double_val c b (to_h_sv p)"],
  ens="Pj.peq #P.prime (to_h (jdouble (x, y, z))) (P.point_double (to_h (x, y, z)))"),
dict(name="j3", doc="A Jacobian point reads as a solution of the homogeneous equation.", n=3, vars=["x","y","z"],
  hyps=J, req="jeq (x, y, z)",
  lets=["let p = var3 #c 0 1 2","let q = to_h_sv p"],
  pairs=[("eqn_lsv q","eqn_rsv q")],
  proof=["var3_val c 0 1 2","to_h_val c p","eqn_val c q","FStar.Pervasives.reveal_opaque (`%heq) heq"],
  ens="heq (to_h (x, y, z))"),
dict(name="j4", doc="Converting a solution of the homogeneous equation in gives a Jacobian solution.", n=3, vars=["x","y","z"],
  hyps=[('hom',0,1,2)], req="heq (x, y, z)",
  lets=["let p = var3 #c 0 1 2","let (qx, qy, qz) = tj_sv p"],
  pairs=[("smul qy qy","eqn_rsv (qx, qy, smul qz qz)")],
  proof=["var3_val c 0 1 2","tj_val c p","jeq_val c (qx, qy, qz)"],
  ens="jeq (tj (x, y, z))"),
dict(name="j5", doc="Converting in and back out scales by [z^2]: an exact identity.", n=3, vars=["x","y","z"],
  lets=["let p = var3 #c 0 1 2","let (hx, hy, hz) = to_h_sv (tj_sv p)",f"let (sx, sy, sz) = ksc (smul {V(2)} {V(2)}) p"],
  pairs=[("hx","sx"),("hy","sy"),("hz","sz")],
  proof=["var3_val c 0 1 2","tj_val c p","to_h_val c (tj_sv p)",f"ksc_val c (smul {V(2)} {V(2)}) p"],
  ens="to_h (tj (x, y, z)) == Pj.scale #P.prime (P.fmul z z) (x, y, z)"),
dict(name="j6", doc="Mixed addition is the addition law at [Z2 = 1]: an exact identity.", n=5, vars=["x1","y1","z1","x2","y2"],
  lets=["let p = var3 #c 0 1 2",f"let (mx, my, mz) = madd_sv b p {V(3)} {V(4)}",f"let (ax, ay, az) = point_add_sv b p ({V(3)}, {V(4)}, kc c 1)"],
  pairs=[("mx","ax"),("my","ay"),("mz","az")],
  proof=["var3_val c 0 1 2",f"madd_val c b p {V(3)} {V(4)}",f"point_add_val c b p ({V(3)}, {V(4)}, kc c 1)","kc_val c 1"],
  ens="madd (x1, y1, z1) x2 y2 == P.point_add (x1, y1, z1) (x2, y2, P.fone)"),
]
