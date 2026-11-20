"""Cumulative moving-window hinges from H through several finite heights."""
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx
from tables import A,H,angular_edge
from finite_anchor import modest_right
from exact_bridge import point

research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round6"/"folds"))
from fold_mean import source
from periodic_fourth import fourth

@lru_cache(maxsize=128)
def centered(k,div,prec):
    assert ctx.prec==prec and k>0 and div>0
    T=arb(H)*(arb(k)/div).exp()
    R=(T-H)/2
    C=arb(H)+R
    v,m=A("1.01"),2048
    B=C+v*R
    q=30
    u=R.log()
    p=1+4/B.log()
    assert R>8192 and ((1+2/R)/v)**m<A("1e-6")
    assert 1/(1-(A(".5")+2/R)**m)<1+A("1e-6")
    c4=fourth(B.log(),q,A("1.5"))
    mass=c4*B*B.log()**4*m/(m-p)*(1+(v*R/C)**(m-p))/2
    assert v*R<C
    norm=(1+A("1e-6"))**2/(1-1/arb(H))
    best=[None]*225
    for dd,ww,hh in [(".7","8","-2.5"),(".85","8.5","-3"),("1","9","-3.5")]:
        delta,w,lh=map(A,(dd,ww,hh))
        cm=source(u,w,lh,210,q,12)[0]
        left=(mass**A(".25")*(cm*R*u).sqrt()+(v*m/(m-1)*R)**A(".75"))**A("4/3")
        right=modest_right(u,u,delta,w,lh,32)*u
        edge=angular_edge(u,u,w,lh,T,2)
        for j in range(650,875):
            s=arb(j)/1000
            den=2-s+3*delta/u
            nu=(2+4*delta/u)/den
            e=3*(1-s+delta/u)/den
            z=point(nu)*norm**nu*left**e*right**(1-e)/arb.pi()+edge
            if best[j-650] is None:best[j-650]=z
            else:best[j-650]=best[j-650].min(z)
    return best+[arb(0)]
