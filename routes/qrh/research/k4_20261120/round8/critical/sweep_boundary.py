"""Integrate the exact difference of the two moving endpoint Hilbert forms."""
from functools import partial
from inspect import getsource

from math import factorial

from flint import arb,ctx

from dual_projection import improved
from endpoint_fourth import simple
from interference import mixed_bound,means,smooth_cut
from rational_fourth import fourth as rational
from weighted_boundary import candidate


def finite(U,q,alpha,width,Z,slab,limit):
    source=getsource(smooth_cut.smooth_fourth)
    start=source.index("        g=1 if dual else 2")
    end=source.index("    c=branch",start)
    assert "hilb*endpoint_norm" in source[start:end]
    source=source[:start]+"""        top=average_endpoint(q,dual,ell,Y0,m,disc)
        return scale**2/(2*arb.pi())*(lower+top)
"""+source[end:]
    old="fourth=s2+v2+2*(var*v2).sqrt()+2*m*v/U**4"
    assert source.count(old)==1
    source=source.replace(old,"fourth=calculate(U,q,alpha,width,start,s2,v2,m,v,upper)")
    boundary=(partial(candidate,primes=(2,3,5,7),weight_tuple=("1.625","3.75","10.5","18"),
                      target="117.354") if q==210 else simple)

    def average_endpoint(q,dual,ell,Y0,m,disc):
        eta=(-2*width).exp()
        small=eta*Y0
        h=boundary(q,dual,ell,small)+16*smooth_cut.reciprocal_gap(ctx.prec)*(m+disc/(2*small.sqrt()))**4
        return (1-eta**2)/(4*width)*h

    def sweep(U,q,dual,scale,ell,Y0,first,second,m,disc):
        pi=arb.pi()
        err=smooth_cut.reciprocal_gap(ctx.prec)
        K=max(2*q,192)
        ymin=arb(K*(K+1)+10)
        eta=(-2*width).exp()
        ymax=ymin/eta
        te=2*pi*(ymax/scale)**2
        assert te<U.exp()
        cutcost=boundary(q,dual,ell,ymin)+16*err*(m+disc/(2*ymin.sqrt()))**4
        M=max(map(abs,smooth_cut.period(q,dual)))
        small=M**4*(2*pi*(1+ymax.log())+16*err)*te/U.exp()
        lower=(1+eta**2)/(4*width)*(cutcost+small)
        top=average_endpoint(q,dual,ell,Y0,m,disc)
        return scale**2/(2*pi)*(lower+top)

    old=smooth_cut.branch
    src=getsource(old)
    a="base=diagonal(q,dual,Z,ctx.prec)(ell)"
    b="cut=2*pi*Z**4/scale**2"
    c="raw=max(v)**4*(1+2*arb(Z).log())**4"
    assert all(src.count(z)==1 for z in (a,b,c))

    def averaged(poly,ell):
        value=poly(ell)
        for k in range(1,5):
            poly=poly.derivative()
            value+=poly(ell)*((-2*width)**k/factorial(k+1))
        return value

    src=src.replace(a,"base=averaged(diagonal(q,dual,Z,ctx.prec),ell)")
    src=src.replace(b,b+"*(4*width).exp()").replace(c,"raw=max(v)**4*(1+2*arb(Z).log()+2*width)**4")
    args=dict(old.__globals__,averaged=averaged,width=width)
    exec(compile(src,__file__,"exec"),args)
    original=args["branch"]
    def choose(U,q,dual,scale,Z,start,off):
        direct=original(U,q,dual,scale,Z,start,off)
        averaged=original(U,q,dual,scale,Z,start,sweep)
        return direct.min(averaged)

    slopes=("1","1.08","1.16","1.25","1.35","1.45","1.6","1.85","2.2")
    context=dict(vars(smooth_cut),average_endpoint=average_endpoint,branch=choose,
                 calculate=partial(improved,M=-1,limit=limit,slopes=slopes))
    exec(compile(source,__file__,"exec"),context)
    return context["smooth_fourth"](U,q,alpha,width,Z,paired=True,disjoint=True,
               projective=True,mixed_bound=partial(mixed_bound,projective=True),
               centering=partial(means,slab=slab))


def fourth(U,q=210,alpha=arb(".82"),width=arb(".34"),Z=384,limit=65536):
    if U>64:
        return rational(U,q,arb(1),arb(".04"),Z)
    edge=U
    row=arb(0)
    for length in map(arb,(".125",".25",".625","1","1","1","1","1","1","1","1","1")):
        row=row.max(finite(edge,q,alpha,width,Z,length,limit))
        edge+=length
        if edge>=U+1:
            tail=rational(edge,q,arb(1),arb(".04"),Z)
            if row>tail:
                return row
    return row.max(tail)


if __name__=="__main__":
    ctx.prec=160
    for u,ceiling in ((35,".000839933"),(37,".000743574"),(40,".000659672")):
        value=fourth(arb(u))
        assert value<arb(ceiling)
        print("moving Hilbert endpoints",u,value.str(15),flush=True)
