"""Narrow height slabs and multiple complete detectors in the first seven units above H."""
from functools import lru_cache
from pathlib import Path
import sys
from fractions import Fraction
from flint import arb, ctx
from tables import A, H, angular_edge
from exact_bridge import finite_row, point
from finite_anchor import modest_right
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"folds"))
from fold_mean import joint

OPTIONS=((".92","9.5","-3.5"),(".80","8.5","-3"),("1.05","9","-3.5"),("1.16","9","-3"))

@lru_cache(maxsize=2)
def coefficients(precision):
    assert precision==ctx.prec
    out=[]
    for i in range(57,74):
        lo,hi=arb(i)/2,arb(i+1)/2
        params=[]
        for dd,ww,lh in OPTIONS:
            d,w,lg=map(A,(dd,ww,lh))
            left,right=finite_row(lo,hi,d,w,lg,2097152,64,"1.5",210,"disjoint")
            edge=angular_edge(lo,hi,w,lg)
            params.append((d,left.log(),right.log(),edge))
            left=joint(lo,hi,w,lg,q=2310,ncore=1048576,base=210,depth=12,
                       alpha=Fraction(5,4),method="disjoint")[0]
            right=modest_right(lo,hi,d,w,lg,64,q=2310,frequency_cut="100")
            edge=angular_edge(lo,hi,w,lg,q=2310)
            params.append((d,left.log(),right.log(),edge))
        out.append(params)
    return out

def improve(u,real,row):
    i=int((u*2).lower().floor().unique_fmpz())
    if not 57<=i<74:
        return row
    assert u>=arb(i)/2 and u<=arb(i+1)/2
    params=coefficients(ctx.prec)[i-57]
    nuconst=((1+A("1e-6"))**2/(1-1/arb(3*10**12))).log()
    logu=u.log()
    out=row.copy()
    for j,s in enumerate(real[:-1]):
        for delta,ll,rr,edge in params:
            den=2-s+3*delta/u
            nu=(2+4*delta/u)/den
            p=3*(1-s+delta/u)/den
            assert 0<p and p<1
            v=point(nu)*(nu*nuconst+p*(ll+u+2*logu)+(1-p)*(rr+logu)).exp()/(2*arb.pi())+edge
            out[j]=out[j].min(v)
    return out
