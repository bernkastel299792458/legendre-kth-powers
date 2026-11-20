"""Arithmetic mean square of the forward times dual sharp AFE polynomials."""
from functools import lru_cache
from math import gcd
from fractions import Fraction
from flint import arb,arb_poly,ctx
from periodic_fourth import period,envelope,product_cumulative,weighted_disc,f,reciprocal_gap
from smooth_cut import shift_constants,projected_shift,smooth_fourth


@lru_cache(maxsize=None)
def forms(q,Z,K,prec):
    unit=period(q,False)
    c2=[v*v for v in period(q,True)]
    ell=arb_poly([0,1])
    diagonal=product_cumulative(ell,arb(Z).log(),envelope(unit,unit,Z),envelope(unit,c2,Z))
    r=Fraction(sum(unit),q)
    mu=Fraction(sum(c2),q)
    d=D=Fraction(0)
    n=s=0
    for k in range(1,q+1):
        n+=unit[k%q]
        s+=c2[k%q]
        d=max(d,n-r*k)
        D=max(D,s-mu*k)
    n=s=previous=0
    co=[Fraction(0)]*3
    h2=Fraction(0)
    for k in range(1,K+1):
        if unit[k%q]:
            h2+=Fraction(2*n+1,k*k)
            n+=1
        s+=c2[k%q]
        inc=n*s-previous
        if inc:
            co[0]+=inc*r**2/k**2
            co[1]+=inc*2*r*d/k
            co[2]+=inc*d*d
        previous=n*s
    return diagonal,tuple(map(f,co)),f(r),f(d),f(mu),f(D),n,f(h2)


def mixed_bound(U,q,alpha,width,Z,start,projective=False):
    pi=arb.pi()
    scale=arb(q).sqrt()*alpha.max(1/alpha)*width.exp()
    Y0=scale*(U/2).exp()/(2*pi).sqrt()
    ell=(arb_poly([0,1])-(2*pi).log())*(arb(1)/2)+scale.log()
    K=max(2*q,192)
    X0=Y0/(K+1)
    assert X0>K and X0>3
    diag,co,r,d,mu,D,N,h2=forms(q,Z,K,ctx.prec)
    P=diag(ell)
    tcut=2*pi*Z**4/scale**2
    assert start<tcut<U.exp()
    vals=list(map(abs,period(q,True)))
    raw=max(vals)**2*(1+2*arb(Z).log())**4
    early=(raw+sum(abs(v)*tcut.log()**j for j,v in enumerate(P.coeffs())))*tcut*(-U).exp()
    anti=P
    v=P
    for j in range(1,5):
        v=v.derivative()
        anti+=(-1)**j*v
    early+=(-start*anti(arb(start).log())).max(arb(0))*(-U).exp()
    h2+=(r+d/X0)**2-(arb(N)/K)**2+4*r*d/K+(d/K)**2
    h2+=2*r**2*(ell-arb(K*(K+1)).log())
    s=2*r**2/(K+1)+(2*r*d*(1+X0.log())+2*d*d)/Y0
    num=(r/(K+1)+d/Y0)**2
    gram=co[0]+co[1]/Y0+co[2]/Y0**2+r*mu*h2+(r*D+mu*d)*s+d*D*num
    hilb=pi*arb("1.31541")
    tiny=hilb*max(vals)**2*(1+Y0.log())**4*(-U).exp()
    J=q*(2*width).exp()/(2*pi*width)
    Ji=int((J*1024).upper().ceil().unique_fmpz())
    rawmean=arb(sum(vals))/q
    ff=(1+arb(q)/Y0)**2
    ss=2+(4*q*(1+Y0.log())+4*q*q)/Y0
    if projective:
        ds,rs=projected_shift(q,True,Ji,ctx.prec,mixed=True)
        shift=ff*ds+ss*rs
    else:
        ds,rs=shift_constants(q,True,Ji,ctx.prec,mixed=True)
        shift=r*rawmean*(ff*ds+ss*rs)
    ef=f(weighted_disc(period(q,False)))
    ed=f(weighted_disc(vals))
    add=16*reciprocal_gap(ctx.prec)*(r+ef/(2*Y0.sqrt()))**2*(rawmean+ed/(2*Y0.sqrt()))**2
    off=scale**2/(2*pi)*(2*shift+add+hilb*gram)+tiny
    poly=(anti+off+early)*(arb(1)/q)
    return sum(poly[i].max(arb(0))*U**(i-4) for i in range(5))


def fourth(U,q=210,alpha=arb(1),width=arb(".05"),Z=384):
    return smooth_fourth(U,q,alpha,width,Z,paired=True,disjoint=True,mixed_bound=mixed_bound)


def projected_fourth(U,q=210,alpha=arb(1),width=arb(".05"),Z=384):
    from functools import partial
    return smooth_fourth(U,q,alpha,width,Z,paired=True,disjoint=True,
                         mixed_bound=partial(mixed_bound,projective=True),projective=True)


if __name__=="__main__":
    ctx.prec=160
    for q in [6,30,210]:
        for a in ["1","1.1","1.25"]:
            print(q,a,fourth(arb(37),q,arb(a),arb(".04"),384).str(15),flush=True)
