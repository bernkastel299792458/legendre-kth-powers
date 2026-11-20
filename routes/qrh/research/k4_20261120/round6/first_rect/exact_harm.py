"""Uniform harmonic Gram bound for a fixed periodic cutoff, with a partial coprimality sieve."""
from functools import lru_cache
from math import gcd,isqrt
from flint import arb,ctx
import numpy as np
from numba import njit
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"phase"))
from periodic_fourth import period,harmonic

MOD=210
UNIT=2**40


def divs(n):
    return [k for k in range(1,n+1) if n%k==0]


def expand(ds,values):
    out=[]
    for j,d in enumerate(ds):
        out.append(values[j]-sum(a for a,e in zip(out,ds[:j]) if d%e==0))
    return out


def fixed_prefix(weights,ds,ns,H):
    assert sum(map(abs,weights))*int(H[-1])+sum(map(abs,weights))*(int(ns.max())+1)<2**60
    val=np.zeros_like(ns)
    for w,d in zip(weights,ds):
        if w:val+=w*(H[ns//d]//d)
    return val


@njit
def row_sum(N,q,cut,H,divis,outer,outer_l1,index,inner,classes):
    total=0.
    for n in range(1,N+1):
        i=index[n%210];m=N//n
        slot=m if m<=cut else cut+n
        for j in range(classes):
            if not outer_l1[i,j]:continue
            pos=outer_l1[i,j]*n
            for h in range(len(divis)):
                if outer[i,j,h]:
                    pos+=outer[i,j,h]*(H[(n-1)//divis[h]]//divis[h])
            upper=2*max(0,pos)/UNIT
            if i==0 and j==0:upper+=1/n
            total+=upper*(inner[i,j,slot]**2)/n
    return total


@lru_cache(maxsize=120)
def uniform_harm(q,dual,N,prec):
    assert q in (6,30) and N>=1 and ctx.prec==prec
    ds,raw=divs(MOD),divs(q);w=period(q,dual);cut=isqrt(N)
    n=np.arange(1,N+1,dtype=np.int64)
    H=np.concatenate((np.zeros(1,dtype=np.int64),np.cumsum(UNIT//n)))
    slots=np.arange(2*cut+1,dtype=np.int64)
    slots[cut+1:]=N//np.arange(1,cut+1,dtype=np.int64)
    outer=np.zeros((len(ds),len(raw),len(ds)),dtype=np.int64)
    l1=np.zeros((len(ds),len(raw)),dtype=np.int64)
    inner=np.zeros((len(ds),len(raw),len(slots)),dtype=np.float64)
    index=np.array([ds.index(gcd(j,MOD)) for j in range(MOD)],np.int64)
    for i,h in enumerate(ds):
        for j,k in enumerate(raw):
            if gcd(h,k)>1:continue
            a=expand(ds,[int(gcd(g,h)==1 and gcd(g,q)==k) for g in ds])
            outer[i,j]=a;l1[i,j]=sum(map(abs,a))
            assert l1[i,j]*(N+int(H[-1])+1)<2**60
            v=[w[(g*h)%q]*w[(g*k)%q] for g in range(q)]
            t=expand(raw,[v[g%q] for g in raw]);err=sum(map(abs,t))
            if all(x>=0 for x in v):
                up=(fixed_prefix(t,raw,slots,H)+err*(slots+1)).astype(np.float64)/UNIT
                inner[i,j]=np.maximum(0,up)
            else:
                assert sum(v)==0
                cap=min(N,1024)
                head=np.arange(cap+1,dtype=np.int64)
                up=(abs(fixed_prefix(t,raw,head,H))+err*(head+1)).astype(np.float64)/UNIT
                peak=np.maximum.accumulate(up)
                result=peak[np.minimum(slots,cap)]
                if N>cap:
                    _,c,e=harmonic(tuple(v),prec)
                    far=float((abs(c)+e/cap).upper())
                    result[slots>cap]=np.maximum(result[slots>cap],far)
                inner[i,j]=result
    val=row_sum(N,q,cut,H,np.array(ds,np.int64),outer,l1,index,inner,len(raw))
    assert (N*len(raw)+100)/2**52<2e-7 and np.isfinite(val)
    return arb(val)*(1+arb("1e-6"))


if __name__=="__main__":
    from fractions import Fraction
    ctx.prec=192
    for q,dual in ((6,False),(6,True),(30,False),(30,True)):
        Y=32;v=period(q,dual)
        upper=uniform_harm(q,dual,Y,ctx.prec)
        for y in range(1,Y+1):
            exact=sum(Fraction(1,i*j)*sum((Fraction(v[(i*k)%q]*v[(j*k)%q],k)
                for k in range(1,y//max(i,j)+1)),Fraction(0))**2
                for i in range(1,y+1) for j in range(1,y+1) if gcd(gcd(i,j),210)==1)
            assert arb(exact.numerator)/exact.denominator<upper
        print(q,dual,upper.str(12),flush=True)
