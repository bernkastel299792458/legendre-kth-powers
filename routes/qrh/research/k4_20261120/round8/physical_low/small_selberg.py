"""Absolute finite Selberg lcm mass with a genuine numerator on both large rows."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants
from odd_sieve import denominator
from wheel_small import discrepancy,ordered_count

@lru_cache(None)
def wheel(Q,prec):
    assert ctx.prec==prec
    eta=arb(int(fmpz(Q).euler_phi()))/Q
    D=discrepancy(Q,prec)
    A=65536;H=C=arb(0)
    for n in range(1,A+1):
        if gcd(n,Q)==1:
            H+=1/arb(n)
            C=C.max(H-eta*arb(n).log())
    C=C.max(H-eta*arb(A).log()+D/A)
    Z=(arb(1)/2000).exp()
    Z2=(3*arb(1)/1999).exp()
    for p in range(2,2001):
        if Q%p and fmpz(p).is_prime():
            Z*=1+arb(1)/(p*(p-1))
            Z2*=1+(arb(2)*p-1)/(p*(p-1)**2)
    return eta,D,C,Z,Z2

def shell(Q,t,s):
    z,*_=constants(1732099);G=denominator(z,Q)
    eta,D,C,Z,Z2=wheel(Q,ctx.prec)
    E=D*(1+z.log());Y=t.exp();v0=(t-s).exp()/z;l=(z/v0).log()
    assert 1<v0<z and l>0 and C>=1 and eta<C
    # For v0<=u<=z/g the numerator product is bounded by
    # (C+eta*log((z/g)/u))*(C+eta*log(u/v0)).
    V=eta*(C*C*l+C*eta*l*l+eta**2*l**3/6)+E*C*(C+eta*l)/v0
    J=eta*(C*C*l*l/2+C*eta*l**3/3+eta**2*l**4/24)+E*C*(C*l+eta*l*l/2)/v0
    return Z**4*Z2*(-eta*(-arb(s)).expm1()+E*z/Y)*(C*V+eta*J)/G**2

def count(Q,t,s=4):
    return shell(Q,t,s)+(-arb(s)).exp()*ordered_count(Q,t-s,ctx.prec)

def layers(Q,t,step=arb(1)/2):
    z,*_=constants(1732099);remaining=t;v=arb(0)
    while remaining-step>z.log()+5:
        v+=(remaining-t).exp()*shell(Q,remaining,step)
        remaining-=step
    return v+(remaining-t).exp()*ordered_count(Q,remaining,ctx.prec)

if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--Q",type=int,default=223092870)
    p.add_argument("--logY",default="72");a=p.parse_args();ctx.prec=144
    for s in (3,4,5,6,7,8):
        print(s,count(a.Q,arb(a.logY),s).str(15))
