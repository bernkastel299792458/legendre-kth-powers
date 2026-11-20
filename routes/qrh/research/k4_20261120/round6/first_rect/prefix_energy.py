"""Exact positive product energy on a short integer interval with periodic weights."""
from functools import lru_cache
from math import gcd
import numpy as np
from numba import njit
from flint import arb
from periodic_fourth import period


@lru_cache(maxsize=None)
def tables(q,dual):
    w=list(map(abs,period(q,dual)))
    sm=np.zeros((q,q,q+1),dtype=np.int64)
    sq=np.zeros_like(sm)
    for i in range(q):
        for j in range(q):
            for g in range(1,q+1):
                x=w[i*g%q]*w[j*g%q]
                sm[i,j,g]=sm[i,j,g-1]+x
                sq[i,j,g]=sq[i,j,g-1]+x*x
    return np.array(w,np.int64),sm,sq


@njit
def evaluate(a,b,q,w,sm,sq):
    k=b-a;w2=0;w4=0
    for n in range(a,b+1):
        x=w[n%q]**2
        w2+=x;w4+=x*x
    total=2*w2*w2-w4
    if k*k<a:return total
    for r in range(max(2,(a+k-1)//k),k+1):
        rr=r%q
        if w[rr]==0:continue
        hi=b//r
        for s in range(r-r*k//b,r):
            lo=(a-1)//s
            if hi<=lo+1:continue
            ss=s%q
            if w[ss]==0 or np.gcd(r,s)!=1:continue
            p=sm[rr,ss];z=sq[rr,ss]
            u=(hi//q-lo//q)*p[q]+p[hi%q]-p[lo%q]
            v=(hi//q-lo//q)*z[q]+z[hi%q]-z[lo%q]
            total+=2*(u*u-v)
    return total


@lru_cache(maxsize=None)
def energy(a,b,q,dual):
    if a>b:return 0
    w,sm,sq=tables(q,dual)
    assert 0<a and 2*int(max(w))**4*(b-a+1)**3<2**63
    return int(evaluate(a,b,q,w,sm,sq))


def local_half(a,b,J,q,dual):
    if a>b:return arb(0)
    en=energy(a,b,q,dual)
    span=b*b-a*a
    # Every product of two units is odd, so shifts in that case are even.
    spacing=1 if dual else 2
    shifts=span//spacing
    diag=J/a**2
    if not shifts:return diag*en
    scale=arb(2)*b**2/(a**2*spacing)
    pivot=min(shifts,int((scale/diag).lower().floor().unique_fmpz()))
    if pivot==shifts:off=pivot*diag
    elif pivot:off=pivot*diag+scale*(arb(shifts)/pivot).log()
    else:off=scale*(1+arb(shifts).log())
    return en*(diag+2*off)
