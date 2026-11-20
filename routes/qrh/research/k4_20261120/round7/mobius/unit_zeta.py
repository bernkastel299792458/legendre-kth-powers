"""Finite-height Poisson minorant for the unit zeta factor on the 1-line."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from short_spectrum import VERIFIED,remote_cost


@lru_cache(None)
def arithmetic(modulus,k,kap,precision,panels=384):
    assert ctx.prec==precision
    a=arb(1)/2;u=1+arb(k)/100;b=u-a
    points=[a+(b-a)*j/panels for j in range(panels+1)]
    scales=[(1+(-kap*x).exp())**(-2) for x in points]
    result=u.zeta().log()
    for p,_ in fmpz(modulus).factor():
        result+=(-arb(int(p))**(-u)).log1p()
    top=int(arb(kap).exp().floor().unique_fmpz())
    for p in range(2,top+1):
        if not fmpz(p).is_prime():continue
        n=p;j=1;lp=arb(p).log()
        while n<=top:
            xi=arb(n).log()
            gap=2*(kap-xi)
            down=[(-xi*x).exp() for x in points]
            up=[-(-gap*x).expm1()*w for x,w in zip(points,scales)]
            lo=sum(down[h+1]*up[h] for h in range(panels))
            hi=sum(down[h]*up[h+1] for h in range(panels))
            coeff=lp/arb(n).sqrt()*(b-a)/panels*lo.union(hi)
            if modulus%p==0:
                coeff-=(arb(1)/n-arb(n)**(-u))/j
            result+=abs(coeff).upper()
            n*=p;j+=1
        if modulus%p==0:result+=arb(1)/(n*j*(1-arb(1)/p))
    assert all(p<=top for p,_ in fmpz(modulus).factor())
    return result


def upper(t0,t1,k=65,kap=6,modulus=210):
    t,T=arb(t0),arb(t1)
    assert 100<=t<=T<VERIFIED-2 and 1<=kap<=12 and 1<=k<=400
    a=arb(1)/2;b=a+arb(k)/100;h=b-a;P=(b/a).log()
    slack=2*((1+(-kap*a).exp())/(1+(-kap*b).exp())).log()/kap
    area=h-slack
    C=(b*b-a*a)/2+4*P/kap**2
    Cz=(b*b-a*a)/2+2*(1+(arb(kap)/2).cosh())*P/kap**2
    pi=arb.pi()
    # Lower archimedean integral relative to its log(t/2pi) mass.
    arch=area/2*((2+pi)/t+4/t**2)
    arch+=(2*(P+2*C*(t/2).log())+4*C*((t/2).log()+5))/(2*pi*t)
    edge=2*Cz/(t*t-arb(1)/4)
    remote=remote_cost(h,Cz,T)
    gamma=(20/t**2+(1+pi/2)/(2*t)).min(arb(".04"))
    return (arithmetic(modulus,k,kap,ctx.prec)+slack*(T/(2*pi)).log()/2
            +arch+edge+remote+h*gamma).exp()


if __name__=="__main__":
    ctx.prec=160
    for t,T in ((3*10**12//8,3000175332800//4),(100,2880000000000)):
        for k,kap in ((45,5),(65,6),(85,7),(70,8)):
            print(t,T,k,kap,upper(t,T,k,kap).str(12),flush=True)
