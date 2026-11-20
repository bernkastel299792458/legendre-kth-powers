"""Matched modulus-2310 detector rows for a joint grid, through log height 44."""
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx
from exact_bridge import A,finite_row,interpolated_point
from tables import angular_edge

CANDIDATES=(("1.1","9.5","-3"),("1.28","9.5","-2.75"),("1.34","8.5","-2.75"),
            ("1.16","9","-3"),("1.04","9.5","-3.5"))

@lru_cache(maxsize=64)
def parameters(i,precision,sharp):
    assert precision==ctx.prec
    lo,hi=arb(i)/2,arb(i+1)/2
    out=[]
    for dd,ww,hh in CANDIDATES:
        d,w,h=map(A,(dd,ww,hh))
        l,r=finite_row(lo,hi,d,w,h,1048576,64,"1",210,"centered",2310)
        if sharp:
            sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round7"/"taper"))
            from mellin_bridge import right
            r=r.min(right(lo,hi,d,w,h,64))
        out.append((d,l.log(),r.log(),angular_edge(lo,hi,w,h,q=2310)))
    return out

def improve(u,real,row,sharp=False):
    i=int((u*2).lower().floor().unique_fmpz())
    if not 57<=i<88:return row
    assert arb(i)/2<=u<=arb(i+1)/2
    out=row.copy()
    k=((1+A("1e-6"))**2/(1-1/arb(3*10**12))).log()
    for delta,ll,rr,extra in parameters(i,ctx.prec,sharp):
        L=ll+u+2*u.log()
        R=rr+u.log()
        for j,s in enumerate(real[:-1]):
            den=2-s+3*delta/u
            p=3*(1-s+delta/u)/den
            eta=(2+4*delta/u)/den
            assert 0<p<1
            value=interpolated_point(eta)*(eta*k+p*L+(1-p)*R).exp()/(2*arb.pi())+extra
            out[j]=out[j].min(value)
    return out
