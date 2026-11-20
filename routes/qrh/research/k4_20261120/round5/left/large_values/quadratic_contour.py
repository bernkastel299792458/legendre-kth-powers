"""Quadratic signed vertical criterion, using the deterministic triangular height weight."""
from functools import lru_cache
from math import gcd
from pathlib import Path
import sys
from flint import arb,ctx
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"spectrum"))
from signed_contour import mean_square
from reflected_sampling import H,N,Q,D,fraction,reduction,short_second


@lru_cache(maxsize=1)
def pole_coefficients(precision):
    assert precision==ctx.prec
    mob=[1]*(N+1)
    isprime=[True]*(N+1)
    for p in range(2,N+1):
        if isprime[p]:
            for n in range(p,N+1,p):mob[n]=-mob[n]
            for n in range(p*p,N+1,p*p):mob[n]=0
            for n in range(2*p,N+1,p):isprime[n]=False
    c=cp=arb(0)
    for n in range(1,N+1):
        if mob[n] and gcd(n,Q)==1:
            t=arb(mob[n])/n
            c+=t
            cp-=t*arb(n).log()
    E=arb(1)
    ed=arb(0)
    for p in (2,3,5,7):
        E*=1-arb(1)/p
        ed+=arb(p).log()/(p-1)
    return E*c,E*(cp+ed*c)


def pole_bound(y):
    p,pd=pole_coefficients(ctx.prec)
    b2=2*D**2
    # |P(1/2+iv)|<431 and |zeta(1/2+iv)|<=6 sqrt(1+|v|).
    # Replace sqrt(1+|v|) by 1+|v|. Integrate the Gaussian exactly.
    error=6*431*(arb(1)/(8*b2)).exp()/(arb.pi()*y.sqrt())
    error*= (2*arb.pi()*b2).sqrt()+2*b2
    # 1-Phi(b log y) < 1e-30 in every row.
    value=abs(p*(y.log()+arb.const_euler())+pd-1)+error+arb("1e-30")
    return (2*value+value**2)/2,value


def prime_projection(j,k,spread,power):
    """Normalized signed cost of an arbitrary real |b_m|<=Lambda(m), m<=T^power."""
    from short_block import data
    s=arb(j)/1000
    t=arb(H)*(arb(k)/4).exp()
    width=t/100
    y=512*(t+width)
    p=3*(1-s)/(3*s-1)
    target=6*t.log()*t**p
    h=arb(spread)
    absmass=data(Q,N,ctx.prec)[2]
    for l in (2,3,5,7):
        absmass*=1+arb(1)/l
    d=1-s
    mass=absmass*y**d*(d**2/(4*D**2)).exp()/d
    mz=mass*((-d*h).exp()+(d*h).exp())+mass**2
    lm=arb(power)*t.log()
    ln=arb(N).log()
    # psi(x)<=3x, followed by integration of the decreasing test function.
    weight=arb(3)/ln**2
    for i in range(64):
        lo=lm*i/64
        step=lm/64
        weight+=3*(d*lo).exp()*(d*step).expm1()/(d*(ln+lo)**2)
    return mz*weight/(arb.pi()*width*target)


def row(j,k,spread=0):
    s=arb(j)/1000
    t=arb(H)*(arb(k)/4).exp()
    width=t/100
    v=t+width
    y=512*v
    u=v.log()
    p=3*(1-s)/(3*s-1)
    target=6*t.log()*t**p
    S=short_second(u,Q,N)
    r=fraction(u,u,j,512,S)*reduction(u,j)
    b2=2*D**2
    theta=arb(spread)
    assert 0<=theta and theta<=4
    gram_factor=(1+(-b2*theta**2).exp())/2
    critical=(1+arb("1e-12"))*gram_factor*r*(arb(1)/2-arb("1e-40"))**2*7*u*v**p/target
    A=(2*t).log()/2+3
    radius=arb(1)/32
    ys=(y*(-theta).exp(),y*theta.exp())
    sec=[mean_square(s,yy,width) for yy in ys]
    sup=[(1+2*radius/width)*mean_square(s-radius,yy,width+2*radius)/(arb.pi()*radius*arb(N).log()) for yy in ys]
    regular=3+(2*(2-s)+arb("2.5"))*A
    nearby=(arb("2.5")*(width+4)/(arb(".9")*width)*8*
            (arb(4).log()**2+2*arb(4).log()+2)).sqrt()*A
    linear=regular*sum(x.sqrt() for x in sec)/arb(N).log()+nearby*sum(x.sqrt() for x in sup)
    # For |t-gamma|<=1+radius the kernel at 2 is at least 1/2.55.
    near_mass=(2+(1+radius)**2/2).max(1+(1+radius)**2)
    assert near_mass<arb("2.55")
    quadratic=regular*(sec[0]*sec[1]).sqrt()/(2*arb(N).log())+2*near_mass*A*((4/radius).log()+1)*(sup[0]*sup[1]).sqrt()
    horizontal=(linear+quadratic)/(2*arb.pi())
    d1,d2=(pole_bound(yy)[1] for yy in ys)
    pole=(d1+d2+d1*d2)/2
    right=10/(2*arb.pi()*arb(N).log())
    edges=(horizontal+pole+right)/target
    return 1-arb("1e-28")-critical-edges,critical,edges,d1.max(d2)


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser()
    cli.add_argument("--spread",default="0")
    cli.add_argument("--prime-power",type=int,default=0)
    args=cli.parse_args()
    spread=args.spread
    ctx.prec=160
    worst=arb(1);ce=ee=dd=pcost=arb(0)
    print("P(1),P'(1)",*[v.str(14) for v in pole_coefficients(ctx.prec)],flush=True)
    for k in (1,4,9,17,30,51):
        line=[]
        for j in (800,820,837,852,865):
            val,c,e,d=row(j,k,spread)
            if args.prime_power:
                proj=prime_projection(j,k,spread,args.prime_power)
                val-=proj
                pcost=pcost.max(proj)
            worst=worst.min(val);ce=ce.max(c);ee=ee.max(e);dd=dd.max(d)
            line.append(val.str(9))
        print("k",k,"fraction",*line,flush=True)
    print("minimum",worst.str(14),"critical",ce.str(14),"edges",ee.str(14),"D(1)",dd.str(14),
          "prime projection",pcost.str(14))
    if not args.prime_power:
        assert worst>arb(".98")
