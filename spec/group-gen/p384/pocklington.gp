default(parisize, 10^9);
nodes = List(); done = Map();
bound = 10^6;
cert(N) = {
  my(f, qs, out, a, e, w, u, q);
  if (mapisdefined(done, N), return);
  if (N < bound, mapput(done, N, 1); listput(nodes, [N, 0]); return);
  f = factor(N-1)[,1];
  out = List();
  for (i=1, #f, q = f[i];
    cert(q);
    a = 2;
    while (1,
      if (Mod(a,N)^(N-1) == 1,
        w = lift(Mod(a,N)^((N-1)/q)) - 1;
        if (gcd(w, N) == 1, u = lift(1/Mod(w,N)); break));
      a++);
    listput(out, [q, a, u]));
  mapput(done, N, 1);
  listput(nodes, [N, Vec(out)]);
}
\\ Factors of n - 1 that PARI does not find quickly; GMP-ECM found the first
\\ (B1 = 10^6), the second is the cofactor.  PARI re-checks both.
addprimes([1124679999981664229965379347, 3055465788140352002733946906144561090641249606160407884365391979704929268480326390471]);
ps = [2^384 - 2^128 - 2^96 + 2^32 - 1, 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973];
for(i=1,#ps, cert(ps[i]));
{
for (i=1, #nodes, my(n = nodes[i]);
  if (n[2] == 0, print("S ", n[1]),
    s = Str("P ", n[1]);
    for (j=1, #n[2], s = Str(s, " ", n[2][j][1], ",", n[2][j][2], ",", n[2][j][3]));
    print(s)));
}
quit;
