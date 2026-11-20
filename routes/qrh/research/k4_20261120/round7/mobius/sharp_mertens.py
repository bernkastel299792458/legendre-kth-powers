"""A sharp Mertens prefix, uniform in a logarithmic length cell and twist."""
from functools import lru_cache
from flint import arb,acb,ctx
from short_spectrum import estimate as spectrum
from selberg_band import low_line
from finite_inverse import H,right


@lru_cache(None)
def low_integral(i,prec):
    assert ctx.prec==prec
    s=arb(i)/100
    value=arb(0)
    stack=[(j,3) for j in range(800)]
    while stack:
        j,k=stack.pop()
        lo=arb(j)/2**k;hi=arb(j+1)/2**k
        y=arb((hi+lo)/2,(hi-lo)/2)
        mag=abs(acb(s,y).zeta())
        if mag.lower()>0 and mag.upper()<2*mag.lower():
            value+=((hi/s).asinh()-(lo/s).asinh())/mag.lower()
        else:
            assert k<20
            stack.extend(((2*j,k+1),(2*j+1,k+1)))
    return value


def sharp(xmin,xmax,i,k,kap,logwidth,twist=0,local=False,averaged=False):
    s=arb(i)/100
    u,euler,_=right(k,ctx.prec)
    width=(-arb(logwidth)).exp()
    B=24/width
    T=B+arb(twist)
    assert 0<=twist and 100<=T<=H//2
    left=spectrum(i,T,k,kap,160,True).upper().max(low_line(i,ctx.prec))
    # Horizontal segments can use the unpaired, monotone majorant,
    # together with the low-rectangle maximum principle when needed.
    horizontal=spectrum(i,T,k,kap,64).upper().max(low_line(i,ctx.prec)).max(euler)
    a=arb(xmin);b=arb(xmax)
    vertical=left*((s-1)*a+(width*s)**2/2).exp()*(B/s).asinh()/arb.pi()
    if (local or averaged) and twist==0:
        # Each integral uses the actual Gaussian height and its own
        # archimedean errors; the full vertical path stays at the same sigma.
        left=low_integral(i,ctx.prec) if averaged else low_line(i,ctx.prec)*(arb(100)/s).asinh()
        start=arb(100)
        while start<B:
            end=(start*arb("1.3")).min(B)
            localq=spectrum(i,end,k,kap,160,True,t0=start).upper()
            piece=localq*((end/s).asinh()-(start/s).asinh())
            if averaged:
                from prime_mean import mean
                for bwidth in (4,5,6,7):
                    other=mean(i,k,bwidth,start,end)/(s*s+start*start).sqrt()
                    piece=piece.min(other)
            left+=piece*(-(width*start)**2/2).exp()
            start=end
        vertical=left*((s-1)*a+(width*s)**2/2).exp()/arb.pi()
    endpoints=((u-1)*b+width**2*(u*u-B*B)/2).exp()/arb.pi()
    edges=endpoints*(horizontal*(u-s)/B+euler/(width*B)**2)
    discretization=(width**2/2).exp()*(width/arb(2).sqrt()).erf()+2*(-a).exp()
    return vertical+edges+discretization


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--table",action="store_true")
    arg=cli.parse_args()
    ctx.prec=160;ctx.cap=32
    if arg.table:
        limits=("1.460e-5","9.635e-6","6.441e-6","4.512e-6","2.938e-6","1.924e-6",
                "1.272e-6","8.506e-7","5.953e-7","3.877e-7","2.540e-7","1.680e-7",
                "1.125e-7","7.676e-8","5.209e-8","3.414e-8","2.257e-8","1.512e-8",
                "1.033e-8","6.755e-9","4.430e-9","2.932e-9")
        for x,cap in enumerate(limits,38):
            l=14 if x<41 else 16 if x<46 else 18 if x<52 else 20 if x<57 else 22
            val=sharp(x,66,56,75,6,l,averaged=True)
            print("sharp prefix upper",x,66,val.str(13),flush=True)
            assert val<arb(cap)
        raise SystemExit(0)
    for x in (43,48,52,55,58,60,65):
        best=None
        for i in (55,57,59,61,63,65):
            for l in (15,17,19,21,23):
                val=sharp(x,x+1,i,75,6,l)
                if best is None or val<best[0]:best=val,i,l
        print("uniform Mertens over log interval",x,x+1,best[0].str(12),best[1:],flush=True)
