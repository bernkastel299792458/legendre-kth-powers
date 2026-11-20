"""A mean-square sharp Möbius prefix on the verified H/8 to H/4 band."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from prime_mean import norms
from short_spectrum import estimate,prime_cost,VERIFIED
from selberg_band import low_line
from finite_inverse import H,right

PHYSICAL_HEIGHT=3000175332800


@lru_cache(None)
def uniform_totient(i,modulus,precision):
    assert precision==ctx.prec
    s=arb(i)/100
    value=arb(1)
    for p in range(2,1001):
        if modulus%p and fmpz(p).is_prime():
            r=arb(p)**(-s)
            value*=1+r/((p-1)*(1-r))
    R=arb(1000)
    return value*((1+1/R)*R**(-s)/(s*(1-R**(-s)))).exp()


def reciprocal_mean(i,k,kap,lo,hi,length,modulus=1,right_factors=True,totient=False,power=2):
    """Bound an even moment on any contained interval of given length."""
    m0,m1,l1sq=norms(i,k,kap,ctx.prec,power=power,modulus=modulus,right_factors=right_factors,totient=totient)
    common=estimate(i,hi,k,kap,96,False,t0=lo)/prime_cost(i,k,kap,96,ctx.prec).exp()
    choices=[]
    for n in (2,8,32,128,512):
        R=length/n
        raw=(length+R)*m0+16*((length+R)/R).sqrt()*m1+4*l1sq/(R*arb(2).log()**2)
        choices.append(common**power*raw/length)
    result=min(choices)
    if totient:
        n=int(arb(kap).exp().floor().unique_fmpz())
        s=arb(i)/100
        tail=(1+arb(1)/n)*arb(n)**(-s)/(s*(1-arb(n)**(-s)))
        result*=(power*tail).exp()
    return result


@lru_cache(None)
def core_kernel(i,k,kap,log_width,modulus,precision):
    assert precision==ctx.prec and modulus==210
    s=arb(i)/100;top=24*arb(log_width).exp()+1
    euler=uniform_totient(i,modulus,ctx.prec)
    for p,_ in fmpz(modulus).factor():
        euler/=1-arb(int(p))**(-s)
    result=low_line(i,ctx.prec)*euler*(arb(101)/(1-s)).asinh()
    lo=arb(100)
    while lo<top:
        hi=(2*lo).min(top)
        pointwise=euler*estimate(i,hi,k,kap,96,t0=lo)
        rms=reciprocal_mean(i,k,kap,lo,hi,hi-lo,modulus,totient=True).sqrt()
        result+=(hi-lo)/(lo-1)*pointwise.min(rms)
        lo=hi
    return 2*result/arb.pi()


def bound(lo_log,hi_log,i,k,kap,log_width,modulus=1,totient=False,plancherel=True,parts=False,annulus=False,band=None,pointwise_core=False):
    a,b=arb(lo_log),arb(hi_log)
    s=arb(i)/100
    width=(-arb(log_width)).exp();B=24/width
    L,U=(arb(PHYSICAL_HEIGHT)/8,arb(PHYSICAL_HEIGHT)/4) if band is None else map(arb,band)
    length=U-L
    lo=L-B;hi=U+B
    assert 0<=L<U and hi<VERIFIED-2
    span=hi-lo if plancherel else length
    if pointwise_core:
        assert annulus and plancherel and 0<=L<U<=1
        norm=arb(0)
    elif lo>=100:
        norm=reciprocal_mean(i,k,kap,lo,hi,span,modulus,totient=totient).sqrt()
    else:
        assert plancherel and 100<hi and modulus==210 and totient
        def integral(start,stop):
            return (stop-start)*reciprocal_mean(i,k,kap,start,stop,stop-start,
                                                modulus,totient=totient)
        raw=integral(arb(100),hi)
        if lo < -100:raw+=integral(arb(100),-lo)
        unit=arb(1)
        for p,_ in fmpz(modulus).factor():
            unit/=1-arb(int(p))**(-s)
        low=low_line(i,ctx.prec)*unit*uniform_totient(i,modulus,ctx.prec)
        norm=((raw+200*low**2)/span).sqrt()
    scale=((s-1)*a+(width*s)**2/2).exp()
    vertical=norm*scale*((span/length).sqrt() if plancherel else (B/s).asinh()/arb.pi())
    u,euler,_=right(k,ctx.prec)
    horizontal=estimate(i,hi,k,kap,64).max(low_line(i,ctx.prec)).max(euler)
    for p,_ in fmpz(modulus).factor():
        horizontal/=1-arb(int(p))**(-s)
    if totient:
        # Uniformly bound every Euler correction by its positive series.
        # p>=2 gives 1/(p-1)<=2/p.
        major=uniform_totient(i,modulus,ctx.prec)
        horizontal*=major
        euler*=major
    if pointwise_core:
        vertical=scale*core_kernel(i,k,kap,log_width,modulus,ctx.prec)
    edges=((u-1)*b+width**2*(u*u-B*B)/2).exp()/arb.pi()*(horizontal*(u-s)/B+euler/(width*B)**2)
    if annulus:
        assert plancherel and parts and totient
        edges*=2
    if plancherel:
        # Completing the convolution of the truncated ordinate function brings
        # back only the Gaussian tail beyond B on the original interval.
        vertical+=(2 if annulus else 1)*scale*horizontal*(-(width*B)**2/2).exp()/(arb.pi()*(width*B)**2)
    unsmooth=(width**2/2).exp()*(width/arb(2).sqrt()).erf()+2*(-a).exp()
    if totient:
        product=1;maximum=arb(1)
        for p in range(2,2000):
            if modulus%p and fmpz(p).is_prime():
                product*=p
                if product>(2*b).exp():break
                maximum*=arb(p)/(p-1)
        assert product>(2*b).exp()
        unsmooth=maximum*unsmooth+(32*width**2).exp()*((-7*a).exp()+(-5*a).exp()/6)
        if annulus:
            # Each of the two endpoints: use 1/n <= 2/Y on n>Y/2,
            # and a Gaussian deviation of log(2)/width below that boundary.
            unsmooth=4*unsmooth+2*maximum*(1+b)*(-arb(2).log()**2/(2*width**2)).exp()
    rms=vertical+edges+unsmooth
    if parts:return vertical+edges,unsmooth
    return rms,length*rms**2


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--q",type=int,default=1)
    cli.add_argument("--totient",action="store_true")
    cli.add_argument("--fixed",action="store_true",help="use sigma=.58,u=1.55,kappa=6 and width exp(-22)")
    args=cli.parse_args()
    ctx.prec=160
    if args.fixed:
        for x in range(54,59):
            rms,integral=bound(x,60,58,55,6,22,args.q,args.totient)
            print(x,rms.str(15),integral.str(15),flush=True)
        raise SystemExit(0)
    for x in (45,50,54,56,58):
        best=None
        for i in (55,57,59,61,63):
            for kap in (4,5,6,7):
                for w in (19,21,22):
                    v,cost=bound(x,60,i,75,kap,w,args.q,args.totient)
                    if best is None or v<best[0]:
                        best=(v,cost,i,kap,w)
        v,cost,*par=best
        print(x,v.str(13),cost.str(13),par,flush=True)
