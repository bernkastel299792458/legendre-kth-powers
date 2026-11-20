"""Exact cancellation inside the residual after the complete Ramanujan change of basis."""
from flint import arb,ctx,fmpz
from math import gcd,lcm,prod
from actual_split import constants,H
from whole_spike import gp
from annular_inverse import harmonic_sums,ramanujan_weights

def integer_check():
    ds={n:[j for j in range(1,n+1) if n%j==0] for n in range(1,2501)}
    mu={d:int(fmpz(d).moebius_mu()) for d in range(1,2501)}
    for m in range(1,51):
        if not mu[m]:continue
        for r in range(1,51):
            if not mu[r]:continue
            g=gcd(m,r);l=lcm(m,r);uv=l//g
            ps=[int(p) for p,_ in fmpz(g).factor()]
            for h in range(1,35):
                for a,b in ((0,l),(5,20),(15,200),(60,1200)):
                    raw=sum(mu[d]*mu[e]*gcd(d,e) for d in ds[m] for e in ds[r]
                            if a<lcm(d,e)<=b and h%(l//lcm(d,e))==0)
                    compressed=sum(mu[uv//gcd(uv,s)]*prod(p-2 for p in ps if s%p)
                                   for s in ds[gcd(l,h)] if a<l//s<=b)
                    assert raw==compressed

def removed(Q,m,logY,stop=4000,minimum=1,core=1000):
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp()
    Y=arb(logY).exp()
    p=next(j for j in range(2,1000) if Q%j and fmpz(j).is_prime())
    assert fmpz(Q).moebius_mu() and m>=2 and z*z<X
    B=z/arb(m).sqrt();lo=B/arb(2).sqrt();dx=(B-lo)/p;dy=B-lo
    minl=lo**2;maxl=B**2
    hmin=minimum*Q//m+1;hmax=stop*Q//m
    km=arb(hmax)*X/(Q*minl)
    assert arb(hmin)*X/(Q*maxl)>minimum and maxl<=X/m and minl/hmax>Y and km<arb("2.5e17")
    # u=pw, while w and v are squarefree, mutually coprime units outside Qp.
    P=Q*p;eta=arb(int(fmpz(P).euler_phi()))/P;D=2**len(fmpz(P).factor())
    tail=arb(1)/2000
    for j in range(2,2001):
        if P%j and fmpz(j).is_prime():tail+=1/arb(j)**2
    count=(eta*dx-D)*(eta*dy-D)
    assert eta*dx>D and eta*dy>D
    count-=(dx*tail+(B/p).sqrt())*(eta*dy+D)
    count-=(dy*tail+B.sqrt())*(eta*dx+D)
    count-=dx*dy*tail+(dx+dy)*(1+B.log())+B/p
    assert count>0
    harmonic=count/B**2
    n=harmonic_sums(Q,hmax//p)[0]-harmonic_sums(Q,(hmin-1)//p)[0]
    K=arb(H);a=(1-arb("1e-12"))*H*(c-116);U=K*r
    phase=2*arb.pi()*km*(1-xl/X)
    fac=4*harmonic/(Q*gp(z,Q)**2)
    # Explicit LOWER on the discarded sum of absolute real parts as well.
    j0=(hmin-1)//p;j1=hmax//p
    real_integer=sum(v*max(0,6*(j1//d)-7-16*(j0//d)) for d,v in ramanujan_weights(Q))
    real_weight=arb(real_integer)/16
    B0=arb(core)
    assert a<B0<U
    E=u*(4*arb(".0002")*(116-c).exp()*S+
         r.exp()*(2*arb.pi()*km*(B0/K).expm1()*A+8/(B0*(1-(a/B0)**2))))
    mass0=u*(-2*r).exp()*(A-4/(U*(1-(a/U)**2)))
    mass=mass0-E
    if 0<phase<arb.pi()/2:
        mass=mass.max(mass0*phase.cos())
    value=fac*mass*n
    real=fac*(mass0*real_weight-E*n)
    return p,hmin,hmax,km,harmonic,n,value,real

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--Q",type=int,default=223092870)
    ap.add_argument("--cut",type=int,default=200);ap.add_argument("--logY",default="75")
    ap.add_argument("--minimum",type=int,default=1)
    ap.add_argument("--stop",type=int,default=4000);ap.add_argument("--core",type=int,default=1000)
    ap.add_argument("--integer-check",action="store_true")
    ap.add_argument("--real-lower")
    ap.add_argument("--lower");a=ap.parse_args();ctx.prec=144
    if a.integer_check:integer_check()
    p,h0,h1,km,v,n,L,R=removed(a.Q,a.cut,a.logY,a.stop,a.minimum,a.core)
    print("p,h range,max kappa,unit harmonic,absolute Ramanujan weight,removed raw complex and real absolute mass",p,h0,h1,km.str(13),v.str(13),n,L.str(15),R.str(15))
    if a.lower:assert L>arb(a.lower)
    if a.real_lower:assert R>arb(a.real_lower)
