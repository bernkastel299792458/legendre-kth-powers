"""Recover a finite part of the conditional variance in the exact Jordan identity."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz


@lru_cache(None)
def saving(Wtext,prec,log_y_min=30):
    assert prec==ctx.prec
    w=arb(Wtext);q=2310
    step=32
    ncell=(w*step).unique_fmpz()
    assert ncell is not None
    ncell=int(ncell)
    primes=[p for p in range(13,101) if fmpz(p).is_prime()]
    top=int(w.exp().upper().ceil().unique_fmpz())
    logn=[arb(max(1,n)).log() for n in range(top+1)]
    mu=[int(fmpz(n).moebius_mu()) if n>0 and gcd(n,q)==1 else 0 for n in range(top+1)]
    ans=[]
    for hundredth in range(4,10):
        elo=arb(hundredth)/100;ehi=arb(hundredth+1)/100
        e=elo.union(ehi)
        av=[arb(0)];bv=[arb(0)]
        for lm,sgn in zip(logn[1:],mu[1:]):
            v=sgn*(-(1+e)*lm).exp()
            av.append(av[-1]+v);bv.append(bv[-1]+v*lm)
        def G(r):
            if r<=0:return arb(0)
            ix=int(r.exp().mid().floor().unique_fmpz())
            # Changing the last index only when crossing its true logarithm
            # contributes at most the uncertainty of r at that adjacent node.
            while ix>0 and not logn[ix]<r:ix-=1
            val=r*av[ix]-bv[ix]
            if ix<top and logn[ix+1].overlaps(r):
                val+=arb(0,abs(r-logn[ix+1]).upper())
            return val
        result=arb(0)
        density=arb(480)/2310
        assert fmpz(2310).euler_phi()==480
        for j,p in enumerate(primes):
            lp=arb(p).log()
            dens=density*(1-arb(1)/p)/p
            error=2**(6+j)
            prob=(1-arb(p)**(-1-elo))*arb(p)**(-1-ehi)
            for l in range(ncell):
                a=arb(l)/step;b=arb(l+1)/step;mid=(a+b)/2
                count=dens*(1-(a-b).exp())-error*(a-w-log_y_min).exp()
                val=abs(G(mid)-G(mid-lp))-(1+b)*(b-a)/2
                if val>0 and count>0:
                    result+=prob*(-ehi*(w-a)).exp()*count*(val/w)**2
            density*=1-arb(1)/p
        ans.append(result.lower())
    best=ans[0]
    for v in ans[1:]:best=best.min(v)
    return best


if __name__=="__main__":
    ctx.prec=160
    for w in ("8.5","9","9.5","10"):
        v=saving(w,ctx.prec)
        print("Jordan conditional variance saved, normalized",w,v.str(14),flush=True)
