"""Positive variance in the unsieved-to-sieved Selberg contraction at one exponent."""
from bisect import bisect_left
from functools import lru_cache
from flint import arb
from math import exp
from verify_fine import coarse


@lru_cache(maxsize=8)
def logs_mu(nmax):
    mu=coarse.mobius_up_to(nmax)
    return mu,[arb(0)]+[arb(n).log() for n in range(1,nmax+1)]


@lru_cache(maxsize=8)
def smooth_up_to(nmax):
    vals=[1]
    for p in (2,3,5,7):
        old=vals[:];a=p
        while a<=nmax:
            vals.extend(a*k for k in old if k<=nmax//a)
            a*=p
    return sorted(vals)


def components(e,W,Y,steps=512):
    """Lower bound for Y^e times the variance subtracted from S(1+e)."""
    X=Y*W.exp();smax=W+arb(32).log()
    nmax=int(smax.exp().upper().ceil().unique_fmpz())+2
    mu,logs=logs_mu(nmax)
    a=[arb(0)];b=[arb(0)]
    v=1+e
    for n in range(1,nmax+1):
        weight=mu[n]*(-v*logs[n]).exp() if mu[n] else arb(0)
        a.append(a[-1]+weight);b.append(b[-1]+weight*logs[n])
    def G(t):
        if t<0:return arb(0)
        j=max(0,min(nmax,int(exp(float(t)))))
        # Either neighboring primitive is valid exactly at a breakpoint.
        while j>0 and logs[j]>t:j-=1
        while j<nmax and logs[j+1]<=t:j+=1
        assert j<nmax and t<logs[min(nmax,j+2)]
        ans=a[j]*t-b[j]
        if j>0 and not logs[j]<=t:
            assert j==1 or logs[j-1]<=t
            ans=ans.union(a[j-1]*t-b[j-1])
        if not t<logs[j+1]:ans=ans.union(a[j+1]*t-b[j+1])
        return ans
    allk=smooth_up_to(nmax)
    weights=[(-v*logs[k]).exp() for k in allk]
    wsum=[arb(0)]
    for p in weights:wsum.append(wsum[-1]+p)
    Z=arb(1)
    eta=arb(1)
    for p in (2,3,5,7):
        Z/=1-arb(p)**(-v)
        eta*=1-1/arb(p)
    known=bisect_left(allk,65)
    total=arb(0);low_sum=arb(0);D=1/v.zeta()
    width=smax/steps
    rad=width/2*(1+1/W)
    for j in range(steps):
        lo=smax*j/steps; hi=smax*(j+1)/steps; mid=(lo+hi)/2
        def derivative_range(offset):
            i=max(0,int((lo-offset).exp().lower().floor().unique_fmpz()))
            n=min(nmax,int((hi-offset).exp().upper().ceil().unique_fmpz()))
            assert 0<=i<=n<=nmax
            bot=top=a[i]
            for z in a[i+1:n+1]:
                top=top.max(z);bot=bot.min(z)
            return bot,top
        l1,h1=derivative_range(arb(0));l2,h2=derivative_range(W)
        deriv=abs(h1-l2).max(abs(h2-l1))/W
        peak=abs(D-(G(mid)-G(mid-W))/W)+deriv*width/2
        umass=(width.expm1()+hi.exp()/X)*(-e*(W-hi)).exp()
        low_sum+=umass*peak**2
        cut=max(65,int(hi.exp().upper().ceil().unique_fmpz()))
        tail=Z-wsum[bisect_left(allk,cut)]
        assert tail>0
        ws=wsum[known]+tail
        moments=[(G(mid-logs[k])-G(mid-logs[k]-W))/W for k in allk[:known]]
        first=sum(p*x for p,x in zip(weights[:known],moments))
        second=sum(p*x*x for p,x in zip(weights[:known],moments))
        vrt=(ws*second-first**2).max(arb(0))
        lower=(vrt.sqrt()-ws*rad).max(arb(0))**2
        mass=(eta*(-(-width).expm1())-16*lo.exp()/X).max(arb(0))
        mass*=(-e*(W-lo)).exp()
        total+=mass*lower
    return v.zeta()/Z*total,low_sum
