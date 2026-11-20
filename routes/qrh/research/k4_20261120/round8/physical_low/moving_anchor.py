"""A physical prime-gcd can reverse the sign only above three smaller true factors."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator
from wheel_small import osc

@lru_cache(None)
def triples(Q,p,prec):
    assert ctx.prec==prec
    ps=[r for r in range(2,p) if Q%r and fmpz(r).is_prime()]
    def third(a):
        poly=[arb(1),arb(0),arb(0),arb(0)]
        for r in ps:
            value=arb(r)**a/(r-1)
            for j in (3,2,1):poly[j]+=poly[j-1]*value
        return 8*poly[3]
    return third(0),third(arb(1)/2),third(1)

@lru_cache(None)
def core_data(B,prec):
    Z=arb(1)
    for r in range(2,1001):
        if B%r and fmpz(r).is_prime():Z*=1+arb(1)/(r*(r-1))
    return arb(int(fmpz(B).euler_phi()))/B,arb(osc(B))/B,Z*(arb(1)/1000).exp()

def rare(k,p,Q,width):
    assert p<k and Q%p and fmpz(p).is_prime()
    first=next(i for i in range(2,1000) if Q%i and fmpz(i).is_prime())
    assert k<=first*p
    h,hs,one=triples(Q,p,ctx.prec)
    if h.is_zero():return arb(0)
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp()
    x=arb(116).exp();mass=X*A/H+2*arb(width)*x/H*S
    l0=xl/(k*z);span=(z/(p*l0)).log()
    if span<=0:return arb(0)
    assert span>0
    fac=u*H*(-c).exp()*(arb(p)/(p-1)/denominator(z,Q))**2
    opts=[]
    for B in (210,2310,30030):
        if Q%B:continue
        eta,D,Z=core_data(B,ctx.prec);E=D*(1+z.log())
        slope=eta*mass/(k*p)*(eta*span*h+E/l0*one)
        edge=S*E*(eta*z/p*hs+E*one)
        opts.append(fac*Z**2*(slope+edge))
    return min(opts,key=lambda v:float(v.upper()))
