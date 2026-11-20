"""Certified finite Selberg remainder for intervals at a specified location and length."""
from fractions import Fraction
from math import sqrt
import numpy as np
from numba import njit
from flint import arb,ctx,fmpz


def upper(x):
    return float(arb(x).upper())*(1+2**-48)


def lower(x):
    return float(arb(x).lower())*(1-2**-48)


def rational(f):
    return arb(f.numerator)/f.denominator


def groups(stop):
    result=[]
    a=1
    while a<=stop:
        b=a if a<32 else min(2*a-1,stop)
        # A decreasing integral after the first term bounds sum 1/n^2.
        mass=Fraction(1,a*a)+Fraction(1,a)-Fraction(1,b)
        result.append((a,b,upper(rational(mass))))
        a=b+1
    return np.array(result,dtype=np.float64)


def lambdas(gmin,max_z,blocks):
    product=1
    rho=Fraction(1)
    for p in range(2,1000):
        if not fmpz(p).is_prime():continue
        product*=p
        if product>max_z:break
        rho*=Fraction(p,p-1)
    assert product>max_z
    result=[]
    for i in range(blocks):
        b=2**(i+1)
        if b<=256:
            v=rational(sum((Fraction(int(fmpz(j).moebius_mu())**2,int(fmpz(j).euler_phi()))
                            for j in range(1,b+1)),Fraction()))
        else:
            v=arb(b).log()+2+arb("2.44")/arb(b).sqrt()
        result.append(upper((rational(rho)*v/gmin).min(arb(1))))
    return np.array(result)


@njit
def bounding_sum(gs,lam,zlo,zhi,tlo,thi,lg,nlo,nhi):
    val=0.
    for ga,gb,gw in gs:
        for ha,hb,hw in gs:
            for i in range(len(lam)):
                for j in range(i+1):
                    dl=zlo/(gb*hb*2.**j)
                    el=zlo/(gb*hb*2.**i)
                    di=min(1.,.5+1/dl)
                    ei=min(1.,.5+1/el)
                    q=2.**(i+j)
                    # The four positive terms of the expanded bilinear bound.
                    rel2=di*ei*(di*(1/el+32*nhi*thi*gb**3*hb**2*q*q/zlo**4*ei)
                          +4*lg*(zhi**2/(tlo*nlo*ga*q)+32*ei/dl))
                    v=min(di*ei,sqrt(rel2))
                    val+=gw*hw*lam[i]*lam[j]*v/q*(1 if i==j else 2)
    return val


def denominator(l,h):
    order=128
    trunc=2**24
    blocks=30
    zlo=(arb(l)/2).exp();zhi=(arb(h)/2).exp()
    Mlo=arb("114.98").exp(); Mhi=arb("115.12").exp()
    assert arb("1.33258")-arb("2.44")/zlo.sqrt()>arb("1.331")
    G=arb(l)/2+arb("1.331")
    gs=groups(trunc)
    lam=lambdas(G,zhi,blocks)
    assert len(gs)**2*blocks*(blocks+1)/2 < 2**22
    K=arb(1)
    for p in range(2,1001):
        if fmpz(p).is_prime():K*=1+arb(2)/(p*(p-1))
    K*=(arb(2)/1000).exp()
    total=(K/G)**2/(order+1)
    tail=(1+arb(2).zeta())/trunc+2*arb(2).zeta()**2/2**blocks
    edges=[1,2,3,4,6,9,13,20,30,45,65,96,129]
    assert edges[0]==1 and edges[-1]==order+1
    for n,j in zip(edges,edges[1:]):
        x=bounding_sum(gs,lam,lower(zlo),upper(zhi),lower(Mlo),upper(Mhi),upper(1+zhi.log()),n,j-1)
        assert 0<x<1
        B=arb(x)*(1+arb("1e-7"))+tail
        fac=sum(2/(arb.pi()*r)+arb(2)/(order+1) for r in range(n,j))
        total+=fac*B
    # 2/(1/A+E)-log N = 2c - 2 E A²/(1+EA), A=.5log N+c.
    eta=2*arb("1.331")-2*total*(arb(h)/2+arb("1.331"))**2
    print(l,h,"error/N",total.str(14),"eta >",eta.str(14),flush=True)
    return eta


if __name__=='__main__':
    ctx.prec=192
    for l in range(83,89):
        assert denominator(l,l+1)>arb("2.10")
