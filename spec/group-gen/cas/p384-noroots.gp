\\ P-384: certificates that f = x^3 - 3x + b and the sextic Q of NR.tmpl have
\\ no root in F_p.  Output is p384/nr.txt:  gp -q cas/p384-noroots.gp > p384/nr.txt
p=2^384 - 2^128 - 2^96 + 2^32 - 1; b=0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef;
cert(h, p) = { my(r = lift(Mod(Mod(1,p)*x, h)^p)); my(u = lift(lift(1/Mod(r - x, h)))); Vecrev(u) };
f = Mod(1,p)*(x^3-3*x+b);
Q = Mod(1,p)*(x^6-15*x^4+20*b*x^3-45*x^2+12*b*x-8*b^2+27);
print("uf=", cert(f,p)); print("uq=", cert(Q,p));
quit;
