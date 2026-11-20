"""Positive finite Gram for forward-unit times dual-Ramanujan frozen polynomials."""
from functools import lru_cache
from math import gcd
import numpy as np
from flint import arb,ctx
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"phase"))
from periodic_fourth import period


@lru_cache(maxsize=12)
def gram(q, forward, dual, prec):
    assert ctx.prec == prec and q in (6,30) and 1 <= min(forward, dual)
    Y = max(forward, dual)
    assert (6*Y+100)*2**-52 < 1e-7
    k = np.arange(1, Y+1, dtype=np.int64)
    u = np.asarray(period(q, False), dtype=np.int64)[k%q]
    v = np.asarray(period(q, True), dtype=np.int64)[k%q]**2
    def count(v):
        return np.r_[np.int64(0), np.cumsum(v)]
    def harmonic(v):
        return np.r_[0., np.cumsum(v/k)]
    uf, vd = count(u), count(v)
    hf, hd = harmonic(u), harmonic(v)
    limit = min(forward,dual)
    hmod = 210//q
    maximum = np.r_[np.int64(0), k[:limit]]
    m = maximum[1:]
    energy = 0
    raw = 0.
    cap = 2*int(v.max())*forward*dual*(1+limit.bit_length())
    assert cap < 2**63
    for h in range(1,hmod+1):
        if hmod%h: continue
        # The smaller of the two outer unit indices must be coprime to h.
        allowed = u.copy()
        allowed[np.gcd(k,h)!=1] = 0
        c = count(allowed)
        H = harmonic(allowed)
        n = m[(u[:limit] != 0) & (np.gcd(m,hmod)==h)]
        if len(n)==0: continue
        copies = 2*c[n-1] + (h==1)
        pref = 2*H[n-1] + (1/n if h==1 else 0)
        fi, di = forward//n, dual//n
        energy += int(np.sum(copies*uf[fi]*vd[di]))
        raw += float(np.sum(pref*hf[fi]*hd[di]/n))
    assert 0 <= energy <= cap
    return arb(energy), arb(raw)*(1+arb("1e-6"))


if __name__ == "__main__":
    from fractions import Fraction
    import sys
    ctx.prec=192
    for q in (6,30):
        a,b=17,29
        u,v=period(q,False),period(q,True)
        coeff={}
        for i in range(1,a+1):
            for j in range(1,b+1):
                coeff[i*j]=coeff.get(i*j,0)+u[i%q]*v[j%q]
        e,h=gram(q,a,b,ctx.prec)
        exact=sum((Fraction(x*x,n) for n,x in coeff.items()),Fraction())
        assert e>=sum(x*x for x in coeff.values()) and h>arb(exact.numerator)/exact.denominator
        print(q,e,h.str(12),flush=True)
