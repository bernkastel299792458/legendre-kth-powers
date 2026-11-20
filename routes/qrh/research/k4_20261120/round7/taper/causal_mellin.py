"""Real-variable Plancherel mass of the one-sided centered Mobius response."""
from functools import lru_cache
from math import gcd
import numpy as np
from numba import njit
from flint import arb,ctx
from taper_profile import research
from fast_short import intlog
from variance import smooth_values


@njit
def _prefix(q,N):
    mu=np.ones(N+1,np.int8)
    prime=np.ones(N+1,np.bool_)
    for p in range(2,N+1):
        if prime[p]:
            mu[p::p]*=-1
            if p*p<=N:mu[p*p::p*p]=0
            prime[2*p::p]=False
            if q%p==0:mu[p::p]=0
    A=np.empty(N+1,np.int64);B=np.empty(N+1,np.int64)
    A[0]=B[0]=0
    K=2**44
    for n in range(1,N+1):
        A[n]=A[n-1];B[n]=B[n-1]
        if mu[n]:
            A[n]+=int(mu[n])*(K//n)
            B[n]+=int(mu[n])*int(K*intlog(n)/n)
    return A,B


@lru_cache(maxsize=2)
def prefix(q,S):
    assert 8<=S<=17
    N=int(arb(S).exp().upper().ceil().unique_fmpz())
    assert (2**44*(S+2)**2)<2**62 and N<2**25
    return _prefix(q,N)


@lru_cache(maxsize=8)
def prefix_grid(q,S,scale,prec):
    assert prec==ctx.prec and scale>=64
    A,B=prefix(q,S)
    K=2**44
    vals=[];ns=[]
    for i in range(S*scale+1):
        t=arb(i)/scale
        n=t.exp().floor().unique_fmpz()
        assert n is not None
        n=int(n)
        # intlog(n) has relative error <150*2^-52 by FAST_SHORT.md.
        common=arb(n)/K
        a=arb(int(A[n]))/K
        b=arb(int(B[n]))/K
        rad=common*(1+t)+160*arb(2)**(-52)*(1+t)**2
        vals.append(arb(t*a-b,rad))
        ns.append(n)
    return vals,ns


@lru_cache(maxsize=48)
def masses(q,S,scale,wi,prec):
    assert prec==ctx.prec and wi>0
    W=arb(wi)/scale
    _,ps=smooth_values(q,1)
    eta=zs=zx=arb(1)
    xi=1-1/(12*arb(10).log())
    for p in ps:
        eta*=1-arb(1)/p
        zs/=1-arb(p)**(-arb(1)/2)
        zx/=1-arb(p)**(-xi)
    g0=arb(3).sqrt()*(arb(2).sqrt()-1)/2 if 2 in ps else arb(1)
    g1=arb('1.4378')*(1-arb(2)**(-xi)) if 2 in ps else arb(1)
    aa=arb('.0336')*g1*zx
    cc=(arb('4.86')*g0+arb('2.93'))*zs
    vals,ns=prefix_grid(q,S,scale,ctx.prec)
    inveta=1/eta
    N=S*scale
    dw=arb(1)/scale
    def exact(i):
        if i<0:return arb(0),arb(0),arb(0)
        r=(ns[i+1]-ns[i])*(-arb(i)/scale).exp()*dw/4
        return vals[i],vals[i+1],r
    upper=[]
    for i in range(N+wi):
        l1,r1,e1=exact(i-wi)
        if i<N:l0,r0,e0=exact(i)
        else:
            t=arb(i)/scale
            l0=r0=inveta
            e0=aa/t+cc*(-t/2).exp()
        l=abs(l0-l1).upper()+e0+e1
        r=abs(r0-r1).upper()+e0+e1
        upper.append((dw*(l*l+l*r+r*r)/(3*W**2)).upper())
    # 4/W² times the integral of (aa/s+cc exp(-s/2))² for s>=S.
    s=arb(S)
    tail=4/W**2*(aa**2/s+4*aa*cc*(-s/2).exp()/s+cc**2*(-s).exp())
    return upper,tail.upper()


def continuous(e,W,q,S=16,scale=512):
    """Upper I_e from weighted positive cell masses. Monotone for all e>=0."""
    wi=(W*scale).unique_fmpz()
    assert wi is not None and (W*scale-int(wi)).is_zero() and e>=0
    vals,tail=masses(q,S,scale,int(wi),ctx.prec)
    ratio=(-e/scale).exp()
    total=tail
    for v in reversed(vals):
        total=v+ratio*total
    return total.upper()


if __name__=="__main__":
    ctx.prec=160
    e=arb(2)/37;w=arb('9.5')
    for s in (14,15,16):
        print(s,continuous(e,w,2310,s),flush=True)
