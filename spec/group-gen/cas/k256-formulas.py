from sympy import *
x,y,z,x1,y1,x2,y2=symbols('x y z x1 y1 x2 y2')
b3=21
def add(P,Q):
    X1,Y1,Z1=P; X2,Y2,Z2=Q
    t0=X1*X2; t1=Y1*Y2; t2=Z1*Z2; t3=X1+Y1; t4=X2+Y2; t3=t3*t4; t4=t0+t1; t3=t3-t4
    t4=Y1+Z1; x3=Y2+Z2; t4=t4*x3; x3=t1+t2; t4=t4-x3; x3=X1+Z1; y3=X2+Z2; x3=x3*y3
    y3=t0+t2; y3=x3-y3; x3=t0+t0; t0=x3+t0; t2=b3*t2; z3=t1+t2; t1=t1-t2; y3=b3*y3
    x3=t4*y3; t2=t3*t1; x3=t2-x3; y3=y3*t0; t1=t1*z3; y3=t1+y3; t0=t0*t3; z3=z3*t4; z3=z3+t0
    return expand(x3),expand(y3),expand(z3)
def dbl(P):
    X,Y,Z=P
    t0=Y*Y; z3=t0+t0; z3=z3+z3; z3=z3+z3; t1=Y*Z; t2=Z*Z; t2=b3*t2; x3=t2*z3; y3=t0+t2
    z3=t1*z3; t1=t2+t2; t2=t1+t2; t0=t0-t2; y3=t0*y3; y3=x3+y3; t1=X*Y; x3=t0*t1; x3=x3+x3
    return expand(x3),expand(y3),expand(z3)
f=lambda t: t**3+7
def red(e, ys):
    e=expand(e)
    for yy,xx in ys:
        P=Poly(e,yy); r=0
        for (k,),cf in P.terms(): r+=cf*f(xx)**(k//2)*yy**(k%2)
        e=expand(r)
    return e
print("add(O,P):", [factor(c) for c in add((0,1,0),(x,y,z))])
print("Z add(A,A):", factor(red(add((x,y,1),(x,y,1))[2],[(y,x)])))
X3,Y3,Z3=add((x,y,1),(x,-y,1))
print("add(A,-A):", [factor(red(c,[(y,x)])) for c in (X3,Y3,Z3)])
print("dbl(0,y,0):", dbl((0,y,0)))
print("dbl Z:", factor(dbl((x,y,z))[2]))
s,t=symbols('s t'); X1,Y1,Z1,X2,Y2,Z2=symbols('X1 Y1 Z1 X2 Y2 Z2')
A=add((s*X1,s*Y1,s*Z1),(t*X2,t*Y2,t*Z2)); B=add((X1,Y1,Z1),(X2,Y2,Z2))
print("homog:", [expand(a - s**2*t**2*b)==0 for a,b in zip(A,B)])
C=add((X2,Y2,Z2),(X1,Y1,Z1))
print("comm:", [expand(a-c)==0 for a,c in zip(B,C)])
