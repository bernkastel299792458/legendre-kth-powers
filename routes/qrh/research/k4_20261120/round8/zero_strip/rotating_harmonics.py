"""Signed circular moments for nonnegative oscillatory Green sources."""
from math import floor
from functools import lru_cache
from flint import arb,ctx
from rotating import circular_constants,wrapped
from rotating_signed import signed_constants


@lru_cache(maxsize=16)
def fourier_constants(J,prec):
    caps=circular_constants(J,prec,'pad')
    rows=[]
    for exp,pad in zip((arb(4)/3,arb(2)),caps,strict=True):
        # Index one cancels identically at radius <=1; beyond it use the
        # stationary point on [1,J] and the monotone outer branch.
        z=((exp+1)/(exp-1)).sqrt().min(J)
        row=[arb(0),(z**(1-exp)-z**(-1-exp))/2+pad]
        for j in range(2,129):
            left=(1+arb(J)**(1-j))/(2*j)
            right=(arb(J)**(-j)+J)/(2*j*arb(J)**exp)
            row.append(left.max(right)+pad)
        assert pad<arb('.1') and max(v.upper() for v in row)<1
        rows.append(row)
    return rows


def attenuation(distance,gap,span,mass):
    x=abs(distance).lower()
    if x<=0:return arb(1)
    return arb(1).min((-gap*x).exp()/(mass*(-2*span*x).expm1()*(-1)))


def series(start,rate,gap,span,mass):
    assert start>0
    return (-gap*start).exp()/(mass*(-2*span*start).expm1()*(-gap*rate).expm1())


def resonant(freq,rate,gap,span,mass,mean,row):
    n=floor(float(freq/rate));lo=max(1,n-3);hi=max(3,n+4)
    assert hi<len(row)
    v=mean*attenuation(freq,gap,span,mass)
    for j in range(lo,hi+1):
        v+=row[j]*attenuation(freq-j*rate,gap,span,mass)
    # The negative-frequency branch and the two tails use |Ahat_j|/r^p<=1.
    v+=series(freq+rate,rate,gap,span,mass)+series((hi+1)*rate-freq,rate,gap,span,mass)
    if lo>1:v+=series(freq-(lo-1)*rate,rate,gap,span,mass)
    return v


def coefficients(V,ell,r,ll,lr,a,omega,modes,J=8,offset=0):
    p=arb(4)/3;q=arb(2);span=r-ell;A=a-ell;B=r-a;t=B/span;pi=arb.pi()
    assert 0<t<1 and V>=25 and arb('.4')<=ell<=arb('.5') and 1<r<arb('1.5')
    cp,cq=signed_constants(J);lp,lq=circular_constants(J,ctx.prec)
    rate=((p*cp/(q*cq)).log()+ll-lr)/(p*A+q*B)+offset
    assert rate>0 and (1+(1+1/(r-1))**2).log()+B*rate<4*V
    dl=wrapped(A,span,t,rate)-1;dr=wrapped(B,span,1-t,rate)-1
    assert dl<1 and dr<1
    facl=t*(ll-p*A*rate).exp()/(2*pi);facr=(1-t)*(lr+q*B*rate).exp()/(2*pi)
    K=(J+1)*(4*V+2)+20;x=(-pi).exp()
    extra=K*span/pi*(1+4*x*(pi+1)/(pi*(1-x))**2)
    ret=[facl*((1-dl)*cp+2*dl*lp)+facr*((1-dr)*cq+2*dr*lq)+extra]
    cl,cr=fourier_constants(J,ctx.prec)
    for m in modes:
        l=resonant(m*omega,rate,A,span,t,cp,cl)
        r0=resonant(m*omega,rate,B,span,1-t,cq,cr)
        ret.append(facl*l+facr*r0+extra)
    return ret


_tables={}


def plan_rows(U,ell,delta,left,right,nodes,omega,modes):
    from rotating_bins import components
    # The actual boundary masses supplied by the caller are simultaneously
    # valid for the fixed taper. The small U box bounds their two normalizers.
    ix=int((U*64).mid().floor().unique_fmpz())
    low=arb(ix)/64;high=arb(ix+1)/64;u=low.union(high)
    if not (low<=U and U<=high):u=u.union(U)
    key=(u.repr(),ell.repr(),delta.repr(),left.repr(),right.repr(),omega.repr(),modes,tuple(a.repr() for a in nodes),ctx.prec)
    if key not in _tables:
        r=1+delta/u;ll=left.log()+u+2*u.log();lr=right.log()+u.log()
        _tables[key]=[components(u.upper(),ell,r,ll,lr,a,omega,modes) for a in nodes]
    return _tables[key]


def plan_price(U,ell,delta,left,right,nodes,omega,modes,means,jumps):
    from rotating_bins import cost
    rows=plan_rows(U,ell,delta,left,right,nodes,omega,modes)
    return sum((cost(row,[b]+[abs(jumps[m][j]) for m in modes]) for j,(row,b) in enumerate(zip(rows,means,strict=True))),arb(0))


if __name__=='__main__':
    from complete_green import weights
    from frozen_green import Book
    from free_green import FreeGreen
    from pathlib import Path
    ctx.prec=150;U=arb(35);omega=arb(137)
    d,l,r,e,ell,f=next(v for v in Book(Path(__file__).with_name('phase_shift_extra.json'),'.012,.016').row(560)
                        if v[5]==5 and v[4].overlaps(arb('.484')))
    ll=(l*U.exp()*U**2).log();lr=(r*U).log();a=arb('.865');modes=(1,2,4,6)
    for off in (-1,0,1):
        cs=coefficients(U,ell,1+d/U,ll,lr,a,omega,modes,offset=off)
        print('offset',off,'per mean',cs[0].str(10),'per harmonic',*(x.str(9) for x in cs[1:]),flush=True)
