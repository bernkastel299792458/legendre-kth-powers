"""Finite Gram sum for a Riemann--Siegel polynomial filtered at 2 and 3."""
from functools import lru_cache
from math import isqrt, gcd, lcm
import numpy as np


@lru_cache(maxsize=12)
def energy(y,stride=1):
    nmax=6*y//stride
    cut=isqrt(nmax)
    last=nmax//(cut+1)
    ds=((1,1),(2,-1),(3,-1),(6,1))
    ind=np.arange(1,max(cut,last)+1,dtype=np.int64)
    ends={e:(e*y//stride)//ind for e,_ in ds}
    mod={(r,d,e): np.asarray([lcm(d//gcd(d,stride*r),e//gcd(e,stride*j)) for j in range(6)],
                               dtype=np.int64)[ind%6]
         for r in range(6) for d,_ in ds for e,_ in ds}
    # Each signed accumulation uses at most 16*nmax in absolute value.
    # Each reduced row is summed in Python integers after exact int64 dot products.
    assert 16*nmax<2**62 and 2*nmax**2<2**63
    total=0
    for i in ind:
        n=int(i)
        gram=np.zeros(n,dtype=np.int64)
        trunc=np.zeros(n,dtype=np.int64)
        for d,sgn in ds:
            lim=d*y//(n*stride)
            for e,other in ds:
                lims=np.minimum(lim,ends[e][:n])
                periods=mod[(n%6,d,e)][:n]
                gram+=sgn*other*(lims//periods)
                if n<=last:
                    trunc+=sgn*other*(np.minimum(cut,lims)//periods)
        gsum=2*int(gram@gram)-int(gram[-1])**2
        if n<=cut:
            total+=gsum
        if n<=last:
            total+=gsum-(2*int(trunc@trunc)-int(trunc[-1])**2)
    return total


def sieved_energy(y):
    divisors={1:1}
    for p in (2,3,5,7):
        divisors.update({p*n:-sign for n,sign in divisors.copy().items()})
    return sum(sign*energy(y,n) for n,sign in divisors.items())
@lru_cache(maxsize=12)
def harmonic_upper(y):
    """Outward upper bound for the unrestricted harmonic Gram sum, in units of 2^-32."""
    nmax=6*y
    cut=isqrt(nmax)
    last=nmax//(cut+1)
    large,small=2**36,2**16
    ds=((1,1),(2,-1),(3,-1),(6,1))
    maxh=1+nmax.bit_length()
    assert large*maxh<2**63 and 16*large*maxh*small+large<2**63
    H=np.empty(nmax+1,dtype=np.int64)
    H[0]=0
    H[1:]=large//np.arange(1,nmax+1,dtype=np.int64)
    np.cumsum(H,out=H)
    err=((16*(nmax+1))*small+large-1)//large
    norm_max=small*maxh+2*err+3
    assert 2*max(cut,last)*norm_max**2<2**63 and norm_max**2+max(cut,last)**2<2**63
    ind=np.arange(1,max(cut,last)+1,dtype=np.int64)
    ends={e:e*y//ind for e,_ in ds}
    mod={(r,d,e):np.asarray([lcm(d//gcd(d,r),e//gcd(e,j)) for j in range(6)],
                             dtype=np.int64)[ind%6]
         for r in range(6) for d,_ in ds for e,_ in ds}
    total=0
    for ii in ind:
        n=int(ii)
        g=np.zeros(n,dtype=np.int64)
        h=np.zeros(n,dtype=np.int64)
        for d,sgn in ds:
            for e,other in ds:
                lims=np.minimum(d*y//n,ends[e][:n])
                period=mod[(n%6,d,e)][:n]
                g+=sgn*other*(H[lims//period]//period)
                if n<=last:
                    h+=sgn*other*(H[np.minimum(lims,cut)//period]//period)
        den=n*ind[:n]
        gu=(np.abs(g)*small+large-1)//large+err
        top=(gu*gu+den-1)//den
        top_sum=2*int(top.sum())-int(top[-1])
        if n<=cut:
            total+=top_sum
        if n<=last:
            hl=np.maximum(np.abs(h)*small//large-err,0)
            bottom=hl*hl//den
            total+=top_sum-(2*int(bottom.sum())-int(bottom[-1]))
    return total,small**2
if __name__=="__main__":
    from fractions import Fraction
    for y in (2,6,21,44):
        ds=((1,1),(2,-1),(3,-1),(6,1))
        b=[0]+[sum(mu for d,mu in ds if n%d==0 and n<=d*y) for n in range(1,6*y+1)]
        direct=0
        weighted=Fraction(0)
        for i in range(1,len(b)):
            for j in range(1,i+1):
                values=[b[i*k]*b[j*k] for k in range(1,6*y//i+1)]
                copies=1 if i==j else 2
                if gcd(gcd(i,j),210)==1:
                    direct+=copies*sum(values)**2
                inner=sum((Fraction(a,k) for k,a in enumerate(values,1)),Fraction(0))
                weighted+=copies*inner**2/(i*j)
        assert direct==sieved_energy(y) and weighted<=Fraction(*harmonic_upper(y))
    y=691008
    assert sieved_energy(y)==8964635410982 and Fraction(*harmonic_upper(y))<Fraction("202.894")
    print("Direct low-index expansions pass; energy",sieved_energy(y),"harmonic upper < 202.894")
