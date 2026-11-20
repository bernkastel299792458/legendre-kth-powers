"""All genuine integer ratios d/e>1 in the AFE interference."""
from math import gcd,isqrt,prod

import numpy as np
from flint import arb,ctx
from quarter_diagonal import zq,primes
from quarter_long_row import result as first,periodic,mobius,prefix
from quarter_negative import geometry


def factors(top):
    small=list(range(top+1))
    for p in range(2,isqrt(top)+1):
        if small[p]==p:
            for n in range(p*p,top+1,p):
                if small[n]==n:small[n]=p
    return small


def complete(d0=100000,q=2310):
    out=first(d0,q)
    ctxprec=ctx.prec;U=arb(37);alpha=arb(64);w=arb('.75')
    a=arb(1)/2;u=1+a;Y=(U-3).exp()
    lo,hi,tc,inner,outer,yf=geometry(q,str(U),str(alpha),str(w),ctxprec)
    W=zq(u,q)/zq(2*u,q)
    top=max(d0,100000);small=factors(top)
    mu=mobius(q,d0)
    inv={}
    for k in range(2,top+1):
        if small[k]==k and q%k:inv[k]=1/(1+arb(k)**u)
    # C_r divided by the unrestricted squarefree Euler mass, and rad weights.
    bp=[arb(1)]*(top+1);ah=[arb(1)]*(top+1)
    for n in range(2,top+1):
        p=small[n];j=n//p
        if q%p==0:bp[n]=ah[n]=arb(0)
        elif j%p==0:bp[n]=bp[j];ah[n]=ah[j]
        else:bp[n]=bp[j]*(1-inv[p]);ah[n]=ah[j]*inv[p]
    h=err=arb(0)
    for d in np.flatnonzero(mu[1:])+1:
        d=int(d)
        if d==1:continue
        sign=int(mu[d]);v=arb(d);root=1/v.sqrt()
        mass=W*bp[d]
        taper=(v/Y)**a*(1/a+v/Y)
        h+=(mass if sign>0 else mass-taper)*sign*(1-root)/d
        err+=mass*(tc*root*root.sqrt()+inner*root+outer)
    small_upper=h*(hi if h>0 else lo)+err
    # Supremum of the q-restricted prefix on each scaled half-line.
    s,den=prefix(mobius(q,10**7))
    sup=np.maximum.accumulate(abs(s)[::-1])[::-1]
    universal=(arb(int(sup[0]))+len(s))/den
    assert universal>=out[1]
    tailmass=arb(1);B=10000
    for p,z in inv.items():
        if p<=B:tailmass*=1+z/(p-1)
    tailmass*=(arb(B)**(-u)/(u*(1-1/arb(B)))).exp()
    weighted=used=arb(0)
    for h in range(1,top+1):
        if gcd(h,q)>1:continue
        scale=ah[h]/h
        start=max(1,(d0-1)//h)
        val=out[1].max((arb(int(sup[start-1]))+len(s))/den)
        weighted+=scale*val;used+=scale
    beta=W*(weighted+universal*(tailmass-used))
    time=out[2]*W;lattice=out[3]*W;main=(out[4]+out[5])*beta/out[1]
    nr=arb('20522030')
    return W,beta,small_upper,time,lattice,main,small_upper+time+lattice+main+nr


if __name__=='__main__':
    ctx.prec=144
    out=complete()
    print('all squarefree scales, weighted Mobius sup, true small ratios, time, lattice, two continuous tails, genuine whole integer-ratio upper',
          *(x.str(12) for x in out),flush=True)
