"""Control the true upper endpoint of the two sharp fourth-moment sums."""
from functools import lru_cache, partial
from inspect import getsource
from pathlib import Path
import sys

from flint import arb,ctx

from interference import means,mixed_bound,smooth_cut
from dual_projection import improved
from rational_fourth import fourth as rational

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round4"/"hilbert"))
from periodic_hilbert import integer_hilbert


@lru_cache(None)
def norm(q,precision):
    assert precision==ctx.prec
    return integer_hilbert(q)


def simple(q,dual,ell,Y0):
    return norm(1 if dual else q,ctx.prec)*smooth_cut.endpoint_norm(ell,Y0,q,dual,max(2*q,192))


def finite(U,q,alpha,width,Z,slab,limit,boundary):
    source=getsource(smooth_cut.smooth_fourth)
    start=source.index("        g=1 if dual else 2")
    end=source.index("    c=branch",start)
    assert "hilb*endpoint_norm" in source[start:end]
    source=source[:start]+"""        top=bound_endpoint(q,dual,ell,Y0)
        remainder=16*reciprocal_gap(ctx.prec)*(m+disc/(2*Y0.sqrt()))**4
        return scale**2/(2*arb.pi())*(lower+top+remainder)
"""+source[end:]
    old="fourth=s2+v2+2*(var*v2).sqrt()+2*m*v/U**4"
    new="fourth=calculate(U,q,alpha,width,start,s2,v2,m,v,upper)"
    assert source.count(old)==1
    slopes=("1","1.08","1.16","1.25","1.35","1.45","1.6","1.85","2.2")
    context=dict(vars(smooth_cut),bound_endpoint=boundary,calculate=partial(improved,M=-1,
                                              limit=limit,slopes=slopes))
    exec(compile(source.replace(old,new),__file__,"exec"),context)
    return context["smooth_fourth"](U,q,alpha,width,Z,paired=True,disjoint=True,
               projective=True,mixed_bound=partial(mixed_bound,projective=True),
               centering=partial(means,slab=slab))


def fourth(U,q=210,alpha=arb(1),width=arb(".04"),Z=384,limit=65536,boundary=simple):
    if U>64:
        return rational(U,q,alpha,width,Z)
    edge=U
    row=arb(0)
    for length in map(arb,(".125",".25",".625","1","1","1","1","1","1")):
        row=row.max(finite(edge,q,alpha,width,Z,length,limit,boundary))
        edge+=length
        if edge>=U+1:
            tail=rational(edge,q,alpha,width,Z)
            if row>tail:
                return row
    return row.max(tail)


if __name__=="__main__":
    ctx.prec=160
    for u,ceiling in ((35,".001084314"),(37,".000943520"),(40,".000806232")):
        value=fourth(arb(u))
        assert value<arb(ceiling)
        print("integer Hilbert endpoint",u,value.str(15),flush=True)
