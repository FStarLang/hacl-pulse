from sympy import *
x,y,b=symbols('x y b')
def add(P,Q,b):
    X1,Y1,Z1=P; X2,Y2,Z2=Q
    t0=X1*X2; t1=Y1*Y2; t2=Z1*Z2; t3=X1+Y1; t4=X2+Y2; t3=t3*t4; t4=t0+t1; t3=t3-t4
    t4=Y1+Z1; X3=Y2+Z2; t4=t4*X3; X3=t1+t2; t4=t4-X3; X3=X1+Z1; Y3=X2+Z2; X3=X3*Y3
    Y3=t0+t2; Y3=X3-Y3; Z3=b*t2; X3=Y3-Z3; Z3=X3+X3; X3=X3+Z3; Z3=t1-X3; X3=t1+X3
    Y3=b*Y3; t1=t2+t2; t2=t1+t2; Y3=Y3-t2; Y3=Y3-t0; t1=Y3+Y3; Y3=t1+Y3; t1=t0+t0
    t0=t1+t0; t0=t0-t2; t1=t4*Y3; t2=t0*Y3; Y3=X3*Z3; Y3=Y3+t2; X3=t3*X3; X3=X3-t1
    Z3=t4*Z3; t1=t3*t0; Z3=Z3+t1
    return X3,Y3,Z3
X3,Y3,Z3=add((x,y,1),(x,-y,1),b)
f=x**3-3*x+b
Y=expand(Y3)
# reduce y^2
Yp=Poly(Y,y)
r=0
for (k,),cf in Yp.terms():
    r+=cf*f**(k//2)*y**(k%2)
r=expand(r)
print(factor(r))
