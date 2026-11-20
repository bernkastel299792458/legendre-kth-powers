"""Exact cost and logarithmic left-norm threshold when moving the Gabriel line."""
from pathlib import Path
import sys

from flint import arb,ctx

research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round7"/"taper"))
from mellin_bridge import exact,finite_row


def powers(L,R,s):
    theta=(R-s)/(R-L)
    assert 0<theta<1
    return theta,3*theta/(2+theta),4/(2+theta)


def row(U,d=arb("1.1"),W=arb("9.5"),lh=arb(-3)):
    left,right=finite_row(U,U+arb(1)/2,d,W,lh,2**20,128,"1",210,"centered",2310,
                           causal="real",cutoff=100,jordan="rough",prime=True,
                           interference="sweep",adaptive_core=True)
    return left*U.exp()*U**2,right*U


def comparison(U,s,AL,AR,d=arb("1.1")):
    R=1+d/U;L=arb(1)/2
    normal=((1+arb("1e-6"))**2/(1-1/arb(3*10**12))).log()
    theta,p,nu=powers(L,R,s)
    l,r=AL.log(),AR.log()
    base=exact.interpolated_point(nu).log()+nu*normal+p*l+(1-p)*r
    k=int((nu*200).lower().floor().unique_fmpz())
    assert k<200*nu<k+1
    branches=exact.radial_lines(k,k+1,ctx.prec)
    costs=[a+(nu*200-k)*t for a,t in branches]
    live=[t*200 for (a,t),v in zip(branches,costs)
          if not any(c<v for c in costs)]
    slopes=[2/((2+theta)*(R-L))*(l-r-arb(2)/3*(normal+j)) for j in live]
    slope=slopes[0]
    for x in slopes[1:]:slope=slope.union(x)
    def need(h):
        _,ph,nuh=powers(L+h,R,s)
        upper=(base-exact.interpolated_point(nuh).log()-nuh*normal-(1-ph)*r)/ph
        return (upper-l).exp()
    return slope,need


if __name__=="__main__":
    ctx.prec=160
    for i in (35,37,40):
        u=arb(i);l,r=row(u)
        print("height",i,"endpoint integrals",l.str(9),r.str(9),flush=True)
        for s in (".80",".84",".87"):
            sl,h=comparison(u,arb(s),l,r)
            print("hinge",s,"required decay rate",sl.str(9),
                  "required left ratios",*[h(arb(delta)).str(9) for delta in (".005",".01",".02",".04")],flush=True)
