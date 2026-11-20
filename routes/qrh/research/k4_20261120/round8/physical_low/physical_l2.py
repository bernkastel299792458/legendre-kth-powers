"""All physical frequencies for an actual multiplier by smoothing the two Möbius rows separately."""
from functools import lru_cache
from math import gcd
from pathlib import Path
import sys
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator
from whole_spike import phi,sq
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round7"/"mobius"))
from twisted_rms import bound

@lru_cache(None)
def base_rms(lo,hi,tau,prec):
    assert ctx.prec==prec
    return bound(lo,hi,58,55,6,22,210,True,annulus=True,parts=True,band=(0,arb(H)*arb(tau)))

@lru_cache(None)
def excluded(n,prec):
    v=arb(1);s=arb(58)/100
    for p,_ in fmpz(n).factor():
        p=int(p)
        if 210%p:v/=1-arb(p)/(p-1)*arb(p)**(-s)
    return v

@lru_cache(None)
def units(Q,prec):
    eta=arb(phi(Q))/Q;D=2**len(fmpz(Q).factor())
    Z=(arb(1)/2000).exp();p2=arb(1)/1999
    for p in range(2,2001):
        if Q%p and fmpz(p).is_prime():
            Z*=1+arb(1)/(p*(p-1));p2+=arb(1)/(p-1)**2
    return eta,D,Z,p2

def spectrum(tau,width,exact=False):
    z,c,r,I,A,S,u=constants(1732099);a=(1-arb("1e-12"))*H*(c-116);U=H*r
    m=(2*r).exp()*A+2*arb(width)*(116-c).exp()*S
    err=2*arb(width)*(116-c).exp()*S+r.expm1()*A+4/(U*(1-(a/U)**2))
    assert 0<tau<1 and 0<a<arb.pi()/2
    h0=1-a/arb.pi();h1=-a.sin()/arb.pi();h2=-(2*a).sin()/(2*arb.pi())
    near=arb.pi()/a*abs(h0*(a*(1-tau)).sin()+h1*(a*tau).sin())
    first=I*abs(h1) if exact else I*(abs(h1)+abs(h2))
    tail=near.max(first).max(I*5/(6*arb.pi()))+err
    tv=2*(2*r).exp()*S+m/H
    assert tail<m
    return m,tail,tv

def physical(k,Q=210,tau=".4",mesh=".0003",width=".0002",exact=False):
    assert Q%210==0 and sq(Q) and gcd(k,Q)==1 and k>1
    z,c,r,I,A,S,u=constants(1732099);L=(c-2*r).exp();G=denominator(z,Q)
    assert z*z<L and 0<arb(mesh)<1 and 0<arb(width)<1
    sig=arb(tau);delta=arb(mesh)/H;m,tail,tv=spectrum(sig,width,exact)
    eta,D,Z,p2=units(Q,ctx.prec);E=D*(1+z.log());p1=(arb(11)/10)**2*(1+z.log())
    if exact:
        from wheel_small import discrepancy
        E=discrepancy(Q,ctx.prec)*(1+z.log())
    high=low=transport=gcdcost=arb(0)
    hi=int(z.log().upper().ceil().unique_fmpz())
    def row(ell,conductor):
        lo=int(ell.log().lower().floor().unique_fmpz())
        a0,b0=base_rms(lo,hi,tau,ctx.prec)
        # E/L covers a partially clipped first or last averaging interval as well.
        return Z*(eta+E/(2*delta*ell)),a0*excluded(conductor,ctx.prec)+b0
    for g in range(1,k):
        if not sq(g) or gcd(g,Q)>1:continue
        for b in range(1,(k-1)//g+1):
            if not sq(b) or gcd(b,g*Q)>1:continue
            for t in range(1,min(b,(k-1)//(g*b))+1):
                if not sq(t) or gcd(t,g*Q)>1:continue
                a1=L*t/(k*z);b1=z/(g*b);a2=L*b/(k*z)
                ell=(b1/a1).log()
                if ell<=0:continue
                assert ell>0
                m1,r1=row(a1,g*b*Q);m2,r2=row(a2,g*t*Q)
                energy=(ell+2*delta)*m1*m2
                fac=(1 if b==t else 2)*u*(arb(g)/phi(g))**2/(k*g*G**2*phi(b)*phi(t))
                high+=fac*tail*energy
                low+=fac*(m-tail)*H*sig/arb.pi()*r1*r2
                transport+=fac*4*arb(mesh)*tv*energy
                gcdcost+=fac*Z**2*(m*eta*(eta*ell*p2+E*p1/a1)
                                        +k*g*H*(-c).exp()*S*E*b1*p1)
    return high,low,transport,gcdcost,high+low+transport+gcdcost

if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--k",type=int,default=11)
    p.add_argument("--Q",type=int,default=210);p.add_argument("--tau",default=".4")
    p.add_argument("--mesh",default=".0003");p.add_argument("--upper")
    p.add_argument("--exact-spectrum",action="store_true")
    a=p.parse_args();ctx.prec=144
    v=physical(a.k,a.Q,a.tau,a.mesh,exact=a.exact_spectrum)
    print("outer spectral energy,inner verified energy,transport,coprimality,entire true signed absolute",
          *(x.str(15) for x in v))
    if a.upper:assert v[-1]<arb(a.upper)
