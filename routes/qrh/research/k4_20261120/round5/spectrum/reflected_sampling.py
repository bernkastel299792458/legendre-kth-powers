"""Poisson sampling of positive-height zeros using their same-height reflected partners."""
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"left"/"large_values"))
from gaussian_detector import D,H,N,Q,THETA,fraction,short_second,zprime


@lru_cache(maxsize=None)
def edges(j,precision):
    if precision!=ctx.prec:
        raise ValueError("precision changed during sampling")
    d0=arb(j)/1000-arb(1)/2
    out=[]
    for k in range(1080,1361,4):
        c=arb(k)/1000
        C=c-arb(1)/2
        if not (C>D and D>=d0 and d0>0):
            raise ValueError("Poisson pair domain")
        m=(2*C*d0**2/(C**2-d0**2)).min(C**3/(C**2+D**2))
        out.append((m,zprime(k,ctx.prec)))
    return out


def reduction(hi,j):
    s=arb(j)/1000
    c=2*s-arb(1)/2
    base=(hi-(2*arb.pi()).log())/2+arb(".001")
    old=(base+zprime(2*j-500,ctx.prec))/(c-THETA)
    best=old
    for m,delta in edges(j,ctx.prec):
        best=best.min((base+delta)/m)
    return best/old


def replay():
    ctx.prec=192
    worst=[arb(0),arb(0)]
    for tick in range(229,360):
        lo,hi=arb(tick)/8,arb(tick+1)/8
        if hi<arb(H).log():
            continue
        second=short_second(lo,Q,N)
        for j in range(800,875):
            r=reduction(hi,j)
            for i,scale in enumerate((128,512)):
                worst[i]=worst[i].max(fraction(lo,hi,j,scale,second)*r)
    bench=reduction(arb(35),850)*fraction(arb(35),arb(35),850,128,short_second(arb(35),Q,N))
    print("Type II fractions for scales 128 and 512",*[z.str(13) for z in worst])
    print("benchmark fraction",bench.str(13))
    assert worst[0]<arb(".064920") and worst[1]<arb(".025680") and bench<arb(".044315")


if __name__=="__main__":
    replay()
