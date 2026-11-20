"""A global signed-phase test excluding long near-arithmetic populations."""
import math

import numpy as np
from flint import arb

from strip_boundary import PI,THETA,fail,arch_check,coefficient,global_phase


def head(A,P,dmax,m):
    grid=1000
    scale=10**9
    weights=10**7
    size=grid*dmax+1
    events=np.zeros(size+1,dtype=np.int64)
    max_weight=0
    from flint import fmpz
    for p in range(2,P+1):
        if not fmpz(p).is_prime():continue
        lp=arb(p).log()
        w=int((weights*coefficient(lp,1,A)).upper().ceil().unique_fmpz())
        max_weight+=w
        period=2*PI/lp
        lower=int((period*scale).floor().unique_fmpz())
        upper=lower+1
        end=(dmax+1)*scale//lower+3
        assert upper*(m*end+1)<2**63
        k=np.arange(1,end+1,dtype=np.int64)
        den=m*(scale//grid)
        lo=(lower*(m*k-1))//den
        hi=(upper*(m*k+1))//den
        live=(lo<size)
        np.add.at(events,lo[live],w)
        np.add.at(events,np.minimum(hi[live]+1,size),-w)
    # For each prime its rectangles are disjoint even after gridding.
    assert 2*PI/arb(P).log()*(1-arb(2)/m)>arb(4)/grid
    assert max_weight<2**60
    scans=np.cumsum(events)
    assert scans.min()>=0 and scans.max()<=max_weight
    return arb(int(scans[200*grid:size].max()))/weights


def check(ai,P,dmax,m,blocks,V,D):
    eps=arb(1)/m
    A=arb(ai)
    delta_high=2*PI/200
    k=1-THETA
    baseline=blocks*V/(fail*(PI*eps).sin())
    # Integral of v(1-v/A)exp(kv) from 0 to A.
    integ=(k*A).exp()*(1/k**2-2/(A*k**3))+1/k**2+2/(A*k**3)
    smooth=2*eps*(integ+2*delta_high*A*(k*A).exp())
    u=arb(P).log()-2*eps*delta_high
    rounding=(-THETA*u).exp()*(u+dmax/(2*PI)*(u/THETA+1/THETA**2))
    peak=head(A,P,dmax,m)
    print("arithmetic progressions",blocks,"head majorant",peak.str(10),"nonresonant",
          baseline.str(10),"integral and integer endpoint",smooth.str(10),rounding.str(10))
    eps_height=(D-baseline-smooth-rounding-peak)/(A*V)
    disrupted=(D-baseline-smooth-rounding-peak)/(2*V)*fail
    necessary=int(disrupted.lower().ceil().unique_fmpz())
    print("excluded mean absolute displacement below",eps_height.str(12),
          "necessary changed entries for minimum population",necessary)
    assert necessary >= (2520 if blocks==1 else 365)
    return eps_height


def main():
    arch_check()
    _,V,D=global_phase(40)
    assert check(40,9000,5000,8192,1,V,D)>arb(".00030")
    assert check(40,30000,5000,4000,6,V,D)>arb(".00004")


if __name__=="__main__":
    main()
