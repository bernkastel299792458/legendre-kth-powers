"""Center the real interference term on a finite log-height slab."""
from functools import partial
from flint import arb,ctx
from mixed_product import projected_fourth,mixed_bound
from periodic_fourth import period,harmonic
from smooth_cut import smooth_fourth


def means(U,q,alpha,width,start,*,slab):
    # Uniform E[S]>=m, |E[V]|<=v for the two sharp sums above start.
    scales=[arb(q).sqrt()*x/(2*arb.pi()).sqrt() for x in (alpha,1/alpha)]
    m=arb(0)
    for dual,scale in enumerate(scales):
        vals=period(q,dual)
        squares=tuple(a*a for a in vals)
        density,constant,err=harmonic(squares,ctx.prec)
        lo=scale*(U/2-width).exp()
        hi=scale*(U/2+width).exp()
        assert lo>1 and hi>1 and start<U.exp()
        H=density*lo.log()+constant-err/lo
        assert H>0
        # err bounds twice the absolute counting-function discrepancy.
        lower=(1-start*(-U).exp())*H-density/2-err/lo
        lower-=4*max(squares)*hi*(3+hi.log())*(-U).exp()
        m+=lower/(q if dual else 1)
    eps=(-U/4).exp()
    assert eps<arb(".1")
    M=max(map(abs,period(q,True)))
    y=scales[1]*(U/2+width).exp()
    invroot=(width).exp()/alpha
    # Far index ratios cost <=2/eps per oscillatory integral. Near ratios
    # cost <=3 sqrt(T); count one plus the length of the interval in n.
    far=8*M*eps/(2*arb.pi()).sqrt()
    near=3*M*(eps/2).exp()*(3*eps/(2*arb.pi()).sqrt()
                         +invroot*(1+y.log())*(-U/2).exp()/arb(q).sqrt())
    return m.max(arb(0)),2*(far+near),U+slab


def fourth(U,q=210,alpha=arb(1),width=arb(".05"),Z=384,slab=arb("1.5")):
    assert slab>0
    finite=smooth_fourth(U,q,alpha,width,Z,paired=True,disjoint=True,projective=True,
                         mixed_bound=partial(mixed_bound,projective=True),
                         centering=partial(means,slab=slab))
    return finite.max(projected_fourth(U+slab,q,alpha,width,Z))


if __name__=="__main__":
    ctx.prec=160
    for q in [30,210]:
        U=arb(37)
        args=(q,arb(1),arb(".04"),384)
        print(q,"projected",projected_fourth(U,*args).str(14),
              "centered",fourth(U,*args).str(14),flush=True)
