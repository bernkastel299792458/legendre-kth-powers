"""Geometric and positive-part-moment independence of the 30 finite targets."""

import argparse
from math import isqrt
from pathlib import Path
import sys
from flint import arb, ctx

from grid_target import A, boundary_data, curves, detector

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"low"))
from finite_points import fixed, detector_floor


ABSCISSA=(800,820,837,852,865)
HEIGHT=(1,4,9,17,30,51)
CASES=((".85","8.8","-3.2",210),(".92","9.5","-3.5",210),
       ("1","9","-3.5",210),("1.1","9","-3.5",210),(".92","9","-3.5",2310))


def cold_rows():
    U,delta,left,right,norm,ec,es=boundary_data()
    ratio=left/right
    rows=[]
    for j in range(650,875):
        s=arb(j)/1000
        p=3*(1-s)/(2-s)
        c,k=3*delta/(2-s),3*delta*(2*s-1)/(2-s)**2
        assert c+1+c/U<(U*ratio).log()
        B=detector(j)*norm**(2/(2-s))*right*ratio**p
        B*=(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
        rows.append((s,B,p))
    return rows,ec,es


def target(u,s):
    return 6*u*(u*3*(1-s)/(3*s-1)).exp()


def allowance(beta,u,rows,ec,es):
    minimum=None
    for r,B,p in rows:
        if beta>r:
            count=(B*(p*u).exp()*u**(1+p)+ec+es*u)/(beta-r)
            minimum=count if minimum is None else minimum.min(count)
    return minimum


def poisson_slack():
    a=A(".6")
    d=A(".36500001")
    spacing=arb(1999)
    # Quantile midpoint integration in the count variable and the displacement
    # of one ordinary ordinate by at most 1/4 at each selected pair.
    quantile=(3*arb(3).sqrt()/(2*a*a)/4+A("1e-11"))/8+A("1e-8")
    merged=9/(8*arb(3).sqrt()*a*a)/4+A("1e-8")
    # For all non-nearest selected ordinates, sum both tails at separation
    # (j-1/2)*spacing, using sum_{j>=1} (j-1/2)^(-2) = pi^2/2.
    spread=2*d*d/(a*(a*a-d*d))+3*arb.pi()**2/spacing**2
    primes=[arb(p) for p in range(2,2004) if all(p%i for i in range(2,isqrt(p)+1))]
    def absolute_dirichlet(c):
        return sum(p.log()/(p**c-1) for p in primes)
    euler=absolute_dirichlet(A("1.25"))
    assert quantile+merged+spread<A("2.64") and euler>A("2.87")
    extended=arb(100)
    for j in range(108,136):
        aa=arb(j)/100-arb(1)/2
        quant=(3*arb(3).sqrt()/(2*aa**2)/4+A("1e-11"))/8+A("1e-8")
        move=9/(32*arb(3).sqrt()*aa**2)+A("1e-8")
        # 4a<=3.44 on this enlarged strip for the distant split pairs.
        shift=2*d*d/(aa*(aa**2-d*d))+A("3.44")*arb.pi()**2/spacing**2
        extended=extended.min(absolute_dirichlet(arb(j+1)/100)-quant-move-shift)
    assert extended>A("1.21")
    return quantile+merged+spread,euler,extended


def check(optional=False):
    H=arb(3000175332800)
    heights=[H.log()+arb(j)/4 for j in HEIGHT]
    abscissae=[arb(j)/1000 for j in ABSCISSA]
    rows,ec,es=cold_rows()
    s_far,b_far,ec_far,es_far=curves(heights[-1],False,32768)
    rows_far=[(s,B,p) for s,(B,p) in zip(s_far[:-1],b_far,strict=True)]
    total_allowance=arb(100000)
    remote_allowance=arb(100000)
    other=arb(100000)
    if optional:
        registered=[]
        for u in heights:
            point=[]
            for d,w,lg,q in CASES:
                delta=A(d)
                left,right,*_=fixed(u,delta,w,lg,q,131072)
                point.append((delta,left,right))
            registered.append(point)
    for j,u in enumerate(heights):
        tau=(u-A(".05")).exp()
        assert tau>(H if j==0 else heights[j-1].exp())
        row=[]
        for i,s in enumerate(abscissae):
            beta=s+A("1e-8")
            t=target(u,s)
            count=(A("1.2")*t).floor().unique_fmpz()
            assert count is not None and count>t and tau+2000*count+1<u.exp()
            for h,uu in enumerate(heights[j:],j):
                for m,ss in enumerate(abscissae):
                    if not (h==j and m==i) and beta>ss:
                        other=other.min(target(uu,ss)/t)
                        assert count<=target(uu,ss)
            total_allowance=total_allowance.min(allowance(beta,tau.log(),rows,ec,es)/t)
            remote_allowance=remote_allowance.min(allowance(beta,heights[-1],rows_far,ec_far,es_far)/t)
            if optional:
                cap=None
                for h,uu in enumerate(heights[j:],j):
                    for delta,left,right in registered[h]:
                        v=detector_floor(beta,uu,delta,left,right)[0]/t
                        cap=v if cap is None else cap.min(v)
                assert cap>A("7.45")
                row.append(cap.str(7))
        if optional:
            print("fixed-height radial floors, K =",HEIGHT[j],row,flush=True)
    assert total_allowance>A("25.49") and remote_allowance>A("1.2")
    assert other>A("1.2")
    plus,margin,extended=poisson_slack()
    print("all 30 independent; minimum ratios for the remaining rectangles, cold and remote hinges:",
          *(x.str(13) for x in (other,total_allowance,remote_allowance)))
    print("Poisson excess and available Dirichlet-series allowance",plus.str(13),margin.str(13))
    print("minimum remaining allowance across 1.08 <= c <= 1.36",extended.str(13))


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--fixed",action="store_true",help="also test five global moment choices at every marked ordinate")
    ctx.prec=160
    check(cli.parse_args().fixed)
