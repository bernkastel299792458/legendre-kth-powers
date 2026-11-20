"""Exact int64 evaluation of all periodic parameter intervals for modulus <=210."""
import numpy as np
from numba import njit
from math import gcd
from flint import arb


@njit
def _scan(values,other,constants,symmetric):
    q=len(values)
    candidates=np.zeros(3,dtype=np.int64)
    weights=np.zeros(q,dtype=np.int64)
    for P in range(q//2+1):
        for S in range(P if symmetric else 0,q//2+1):
            if gcd(gcd(P,S),q)!=1:
                continue
            # One solution P*x-S*y=1 mod q. Then b=x*v+S*t,d=y*v+P*t.
            found=False
            x=y=0
            for br in range(q):
                for dr in range(q):
                    if (P*br-S*dr-1)%q==0:
                        x,y=br,dr
                        found=True
                        break
                if found:
                    break
            assert found
            totals=np.zeros(3,dtype=np.int64)
            b0=d0=0
            for i in range(q):
                b0=(b0+x)%q
                d0=(d0+y)%q
                b,d=b0,d0
                mass=0
                for j in range(q):
                    w=values[b]*other[d]
                    weights[j]=w
                    mass+=w
                    b+=S
                    d+=P
                    if b>=q:b-=q
                    if d>=q:d-=q
                mn=mx=z=0
                for j in range(q):
                    mn=min(z,mn)
                    z+=q*weights[j]
                    mx=max(z,mx)
                    z-=mass
                disc=mx-mn
                totals[0]+=disc
                totals[1]+=disc*constants[i]
                totals[2]+=mass*constants[i]
            for i in range(3):candidates[i]=max(candidates[i],totals[i])
    return candidates


def fast_near(values,kap,other=None):
    q=len(values)
    symmetric=other is None
    if symmetric:other=values
    assert q%2==0 and q<=210 and max(max(values),max(other))<=48
    power=10**6
    rounded=[int((k*power).upper().ceil().unique_fmpz()) for k in kap]
    # |q D_h| <= 2*q^2*M^2.  Bound every sum of products in the scan.
    assert 2*q**3*max(values)*max(other)*max(map(abs,rounded))<2**63
    n,d,r=map(int,_scan(np.array(values,np.int64),np.array(other,np.int64),
                         np.array(rounded,np.int64),symmetric))
    return arb(n)/q**2,arb(d)/(q*power),arb(r)/(q*power)


@njit
def _line_scan(values,other,constants,projective,lines):
    q=len(values)
    upper=np.zeros((lines,2),np.int64)
    weights=np.empty(q,np.int64)
    for P in range(q//2+1):
        for S in range(q):
            idx=projective[P,S]
            if idx<0:continue
            x=y=0
            found=False
            for br in range(q):
                for dr in range(q):
                    if (P*br-S*dr-1)%q==0:
                        x,y=br,dr
                        found=True
                        break
                if found:break
            b0=d0=0
            summed=means=0
            for i in range(q):
                b0=(b0+x)%q
                d0=(d0+y)%q
                b,d=b0,d0
                mass=0
                for j in range(q):
                    wij=values[b]*other[d]
                    mass+=wij
                    weights[j]=wij
                    b+=S
                    d+=P
                    if b>=q:b-=q
                    if d>=q:d-=q
                lo=hi=z=0
                for j in range(q):
                    lo=min(lo,z)
                    z+=q*weights[j]
                    hi=max(hi,z)
                    z-=mass
                summed+=(hi-lo)*constants[i]
                means+=mass*constants[i]
            upper[idx,0]=max(upper[idx,0],summed)
            upper[idx,1]=max(upper[idx,1],means)
    return upper


def projective_near(values,other,kap,outer1,outer2):
    from itertools import product
    from math import prod
    from fractions import Fraction
    q=len(values)
    primes=[p for p in (2,3,5,7) if q%p==0]
    assert prod(primes)==q
    lines=list(product(*(range(p+1) for p in primes)))
    labels={line:j for j,line in enumerate(lines)}
    mat=np.full((q,q),-1,np.int64)
    groups={}
    for a in range(q):
        for c in range(q):
            tag=tuple((c*pow(a,-1,p))%p if a%p else (p if c%p else -1) for p in primes)
            if -1 not in tag:mat[a,c]=labels[tag]
            v=outer1[a]*outer2[c]
            if v:groups[tag]=groups.get(tag,0)+v
    pw=10**6
    cap=[int((w*pw).upper().ceil().unique_fmpz()) for w in kap]
    assert 2*q**3*max(values)*max(other)*max(map(abs,cap))<2**63
    upper=_line_scan(np.array(values,np.int64),np.array(other,np.int64),np.array(cap,np.int64),mat,len(lines))
    first=Fraction(0)
    second=0
    for tag,weight in groups.items():
        choices=(product(*(range(p+1) if j==-1 else (j,) for j,p in zip(tag,primes))))
        ids=[labels[x] for x in choices]
        divisor=prod(p for p,j in zip(primes,tag) if j==-1)
        first+=Fraction(weight*max(int(upper[i,0]) for i in ids),divisor)
        second+=weight*max(int(upper[i,1]) for i in ids)
    return arb(first.numerator)/(first.denominator*q**3*pw),arb(second)/(q**3*pw)
