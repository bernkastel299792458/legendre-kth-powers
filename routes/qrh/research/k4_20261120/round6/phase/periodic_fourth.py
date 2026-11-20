"""Fourth moment of a sieved zeta factor from row-dependent asymmetric cutoffs."""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd,prod
from pathlib import Path
import sys
from flint import arb,arb_poly,ctx

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round5"/"left"))
from off_fourth import reciprocal_gap


def f(x):
    return arb(x.numerator)/x.denominator


def period(q,dual):
    primes=[p for p in [2,3,5,7,11] if q%p==0]
    assert prod(primes)==q
    if not dual:
        return [int(gcd(k,q)==1) for k in range(q)]
    return [prod(p-1 if k%p==0 else -1 for p in primes) for k in range(q)]


@lru_cache(maxsize=None)
def harmonic(values,precision):
    q=len(values)
    rho=arb(sum(values))/q
    const=-sum((v*((arb(i)/q).digamma()+arb(q).log()) for i,v in enumerate(values[1:]+values[:1],1) if v),arb(0))/q
    # The counting remainder is piecewise affine, with extrema at the
    # integers and their left limits. Its absolute bound enters twice.
    counts=0
    discrepancy=Fraction(0)
    mean=Fraction(sum(values),q)
    for i in range(1,q+1):
        discrepancy=max(discrepancy,abs(counts-i*mean))
        counts+=values[i%q]
        discrepancy=max(discrepancy,abs(counts-i*mean))
    return rho,const,2*f(discrepancy)


def envelope(a,b,Z,signed=False):
    q=len(a)
    r,c,k=harmonic(tuple(a),ctx.prec)
    t,d,h=harmonic(tuple(b),ctx.prec)
    z=arb(Z).log()
    va,vb,previous=Fraction(0),Fraction(0),Fraction(0)
    m1=m2=arb(0)
    for n in range(1,Z+1):
        va+=Fraction(a[n%q],n)
        vb+=Fraction(b[n%q],n)
        current=va*vb
        if signed:
            current=max(previous,current)
        mass=f(current-previous)
        if not mass.is_zero():
            u=arb(n).log()
            m1+=mass*u
            m2+=mass*u*u
        previous=current
    av=f(previous)
    if signed:
        assert r.is_zero() and t.is_zero() and a==b
        peak=av.max((abs(c)+k/Z)**2)
        slope=quad=arb(0)
    else:
        error=(k*(t*z+abs(d))+h*(r*z+abs(c))+k*h/Z)/Z
        peak=(r*z+c)*(t*z+d)+error
        slope=2*r*t*z+r*d+t*c
        quad=r*t
        assert slope>0 and peak>=av and z>1
    return peak,m1+(peak-av)*z,m2+(peak-av)*z*z,slope,quad


def product_cumulative(ell,z,first,second):
    m,n,k,A,a=first
    M,N,K,B,b=second
    l=ell-z
    p=ell-2*z
    mixed=B*(m*l-n)+b*(m*l*l-2*n*l+k)+A*(M*l-N)+a*(M*l*l-2*N*l+K)
    continuous=(A*B/2)*p*p+((a*B+A*b)/3)*p**3+(a*b/6)*p**4
    return m*M+mixed+continuous


@lru_cache(maxsize=None)
def diagonal(q,dual,Z,precision):
    vals=period(q,dual)
    divs=[h for h in range(1,q+1) if q%h==0]
    z=arb(Z).log()
    ell=arb_poly([0,1])
    total=arb_poly()
    for h,k in product(divs,repeat=2):
        if gcd(h,k)>1 or (not dual and (h!=1 or k!=1)):
            continue
        a=[int(gcd(n,q)==h) for n in range(q)]
        b=[int(gcd(n,q)==k) for n in range(q)]
        w=[vals[(g*h)%q]*vals[(g*k)%q] for g in range(q)]
        out=envelope(a,b,Z)
        inside=envelope(w,w,Z,signed=not any(w) or sum(w)==0)
        total+=product_cumulative(ell,z,out,inside)
    return total


def weighted_disc(weights):
    q=len(weights)
    rho=Fraction(sum(weights),q)
    s=Fraction(0)
    hi=lo=Fraction(0)
    for k in range(q):
        lo=min(lo,s-k*rho)
        s+=weights[k]
        hi=max(hi,s-k*rho)
    return hi-lo


@lru_cache(maxsize=None)
def near_data(q,dual,precision):
    vals=list(map(abs,period(q,dual)))
    kap=[sum(arb(1)/(r+j*q) for j in range(16))-arb(r+15*q).log()/q for r in range(1,q+1)]
    if q>30:
        from fast_period import fast_near
        return fast_near(vals,kap)
    best=[arb(0)]*3
    for P,Q in product(range(q),repeat=2):
        if gcd(gcd(P,Q),q)!=1:continue
        # For variable h consider the q solutions given by the orbit
        # (b+Qj,d+Pj); use complete period weights for both variables.
        ds=[];rs=[]
        for h in range(1,q+1):
            b,d=next((b,d) for b,d in product(range(q),repeat=2) if (P*b-Q*d-h)%q==0)
            row=[vals[(b+Q*k)%q]*vals[(d+P*k)%q] for k in range(q)]
            ds.append(weighted_disc(row))
            rs.append(Fraction(sum(row),q))
        best[0]=best[0].max(f(sum(ds)/q))
        best[1]=best[1].max(sum(f(x)*v for x,v in zip(ds,kap)))
        best[2]=best[2].max(sum(f(x)*v for x,v in zip(rs,kap)))
    return best


def branch(U,q,dual,scale,Z=96,start=1000,off_estimate=None):
    # The raw cutoff at t is scale*sqrt(t/(2*pi)).
    pi=arb.pi()
    u=arb_poly([0,1])
    ell=(u-(2*pi).log())*(arb(1)/2)+scale.log()
    Y0=scale*(U/2).exp()/(2*pi).sqrt()
    assert Y0>16*q
    v=list(map(abs,period(q,dual)))
    m=arb(sum(v))/q
    disc=f(weighted_disc(v))
    first=m*m*(1+arb(q)/Y0)**2
    second=m*m*(2+(4*q*(1+Y0.log())+4*q*q)/Y0)
    if off_estimate is None:
        D,C,R=near_data(q,dual,ctx.prec)
        small=first*(D*ell+C)+second*(m*m*ell+R)
        far=first*(m*disc+disc**2/Y0)+second*(m*m+m*disc/Y0)*ell
        add=32*reciprocal_gap(ctx.prec)*(m+disc/(2*Y0.sqrt()))**4
        off=(scale**2/(2*pi))*(4*(small+far)+add)
    else:
        off=off_estimate(U,q,dual,scale,ell,Y0,first,second,m,disc)
    normal=q*q if dual else 1
    base=diagonal(q,dual,Z,ctx.prec)(ell)
    cut=2*pi*Z**4/scale**2
    assert cut<U.exp()
    raw=max(v)**4*(1+2*arb(Z).log())**4
    early=(raw+sum(abs(z)*cut.log()**j for j,z in enumerate(base.coeffs())))*cut*(-U).exp()
    anti=base
    derivative=base
    for j in range(1,5):
        derivative=derivative.derivative()
        anti+=(-1)**j*derivative
    # Integrate only from 1000, the asymmetric AFE threshold.
    early+=(-start*anti(arb(start).log())).max(arb(0))*(-U).exp()
    poly=(anti+off+early)*(arb(1)/normal)
    return sum(poly[i].max(arb(0))*U**(i-4) for i in range(5))


def fourth(U,q=6,alpha=arb(1),Z=96):
    root=arb(q).sqrt()
    a,b=root*alpha,root/alpha
    start=max(1000,int((2*arb.pi()*(a.max(b))**2).upper().ceil().unique_fmpz())+1)
    assert q/a*(2*arb.pi()/start).sqrt()<=1 and q/b*(2*arb.pi()/start).sqrt()<=1
    forward=branch(U,q,False,a,Z,start)
    dual=branch(U,q,True,b,Z,start)
    primes=[p for p in [2,3,5,7,11] if q%p==0]
    ef=prod(1+1/arb(p).sqrt() for p in primes)
    assert U>20
    K=16*(2*arb.pi())**(arb(1)/4)*sum((arb(d)/a).sqrt().max((a/d).sqrt())/arb(d).sqrt()
                    for d in range(1,q+1) if q%d==0)
    # The two disjoint small ranges use Euler summation through 200 and
    # symmetric Riemann-Siegel through 1000.
    small=arb(17) if start==1000 else 4*(arb(start)/(2*arb.pi()))**(arb(1)/4)+1
    err=((ef**4*(200*arb(403)**4+(start-200)*small**4)+K**4*U)*(-U).exp())**(arb(1)/4)/U
    return (forward**(arb(1)/4)+dual**(arb(1)/4)+err)**4


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--u",default="40")
    cli.add_argument("--q",type=int,default=6)
    cli.add_argument("--alpha",default="1")
    cli.add_argument("--z",type=int,default=96)
    args=cli.parse_args()
    ctx.prec=160
    print("periodic fourth",fourth(arb(args.u),args.q,arb(args.alpha),args.z).str(18),flush=True)
