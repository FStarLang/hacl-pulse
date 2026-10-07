pk=2^256 - 2^32 - 977;
cert(h, p) = { my(r = lift(Mod(Mod(1,p)*x, h)^p)); my(u = lift(lift(1/Mod(r - x, h)))); Vecrev(u) };
fk = Mod(1,pk)*(x^3+7);
Qk = Mod(1,pk)*(x^6+140*x^3-392);
print(polrootsmod(fk,pk)); print(polrootsmod(Qk,pk));
print(cert(fk,pk)); print(cert(Qk,pk));
print(factormod(x^6+140*x^3-392,pk)[,1]~);
quit;
