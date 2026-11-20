"""Coefficient floor contributed by mixed semiprimes after a negative prime-block correction."""
from functools import lru_cache
from math import gcd,isqrt
import numpy as np
from gaussian_detector import arb,ctx,THETA,energies,joint_thresholds


@lru_cache(maxsize=6)
def mixed(n_exp,b_exp,ell,precision):
    assert precision==ctx.prec
    assert 2*ell[-1]<ell[0]**2 and ell[-1]**2<2**(n_exp-1)
    top=2**b_exp//ell[0]+1
    sieve=np.ones(top+1,dtype=bool)
    sieve[:2]=False
    for p in range(2,isqrt(top)+1):
        if sieve[p]:sieve[p*p::p]=False
    rows=[]
    for j,x,prime_g in energies(ctx.prec):
        if j<n_exp:continue
        if j>=b_exp:
            rows.append((j,x,prime_g))
            continue
        m=2**j;g=arb(0)
        for ell0 in ell:
            for i in range(16):
                l=m+m*i//16;r=m+m*(i+1)//16
                pc=int(np.count_nonzero(sieve[l//ell0+1:r//ell0+1]))
                g+=arb(pc)*arb(r)**(-2*THETA)
        rows.append((j,x,g*arb(".999")**2))
    return rows


def forced(n,b,ell,av):
    return joint_thresholds(arb(av),(n,),mixed(n,b,ell,ctx.prec))[n]


if __name__=="__main__":
    ctx.prec=144
    for n,b in ((20,25),(20,26),(21,26),(22,26),(20,27)):
        for ell in ((5,7,11),(7,11,13,17,19,23),(11,13,17,19,23,29,31,37,41,43,47,53,59)):
            print(n,b,ell[0],"full-budget lower",forced(n,b,ell,"1").str(9),flush=True)
