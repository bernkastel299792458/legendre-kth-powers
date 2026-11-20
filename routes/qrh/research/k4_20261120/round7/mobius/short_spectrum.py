"""Integrated bandlimited Poisson majorant using only finite-height RH."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from finite_inverse import H,right

VERIFIED=3000175332800


def remote_cost(h,cz,t):
    old=(24*h+5*cz)*4*(arb(H).log()+1)/H
    if t<=H//2:return old
    top=arb(VERIFIED);gap=top-t
    assert gap>2
    unit=12+2*(2*top+4).log()
    near=2*unit*(1/gap**2+1/gap)
    far=16*(1+(2*top).log())/(2*top)
    return ((6*h+2*cz)*(near+far)).min(old/(1-arb(t)/top)**2)


@lru_cache(None)
def prime_cost(i,k,kappa,panels,prec,paired=False):
    assert prec==ctx.prec
    a=arb(i)/100-arb(1)/2
    b=arb(1)/2+arb(k)/100
    # Positive left Riemann sum, with a quadratic mesh near the singular end.
    vs=[a+(b-a)*j*j/panels**2 for j in range(panels+1)]
    base=[(y-v)/(1-(-kappa*v).exp())**2 for v,y in zip(vs,vs[1:])]
    rightbase=[(y-v)/(1-(-kappa*y).exp())**2 for v,y in zip(vs,vs[1:])]
    primes=arb(0)
    top=int(arb(kappa).exp().upper().ceil().unique_fmpz())
    for p in range(2,top+1):
        if not fmpz(p).is_prime():continue
        lp=arb(p).log()
        n=p
        coeffs=[]
        while n<=top:
            xi=arb(n).log()
            if xi<kappa:
                coef=sum(weight*((-v*xi).exp()-(-v*(2*kappa-xi)).exp()) for v,weight in zip(vs,base))
                hi=lp*coef/arb(n).sqrt()
                if not paired or p*p>top:
                    primes+=hi
                else:
                    lo=lp/arb(n).sqrt()*sum(weight*((-v*xi).exp()-(-v*(2*kappa-xi)).exp())
                                              for v,weight in zip(vs[1:],rightbase))
                    coeffs.append(lo.union(hi))
            else:assert xi>kappa
            n*=p
        if coeffs:
            # Debit the same prime's worst Euler factor, then reinsert it
            # on the identical phase arc used for its prime powers.
            q=arb(p)**(-(arb(1)+arb(k)/100))
            best=None
            for j in range(128):
                th=arb.pi()*(2*j+1)/256
                th=th+arb(0,arb.pi()/256)
                charge=-sum(v*((m+1)*th).cos() for m,v in enumerate(coeffs))
                charge+=(1+q*q-2*q*th.cos()).log()/2-q.log1p()
                best=charge if best is None else best.max(charge)
            primes+=best
    return primes


def estimate(i,t,k,kappa,panels=64,paired=False,t0=100):
    s=arb(i)/100
    u,euler,_=right(k,ctx.prec)
    assert arb(1)/2<s<1 and 1<u<=6 and 100<=t<VERIFIED-2 and 1<=kappa<=12
    a,b=s-arb(1)/2,u-arb(1)/2
    h=b-a
    log=(b/a).log()
    slack=2*((1-(-kappa*b).exp())/(1-(-kappa*a).exp())).log()/kappa
    area=h+slack
    c=(b*b-a*a)/2+4*log/kappa**2
    cz=(b*b-a*a)/2+2*(1+(arb(kappa)/2).cosh())*log/kappa**2
    t0=arb(t0)
    assert 100<=t0<=t
    # Integrated archimedean errors, uniform down to t0.
    arch=(arb("2.5")+arb.pi())*area/(2*t0)+arb(".4")*4*c/(2*arb.pi()*t0)
    arch+=(log/(2*t0)+c*((1/t0).log1p()+t0.log1p()/t0))/arb.pi()
    pole=2*cz/(t0*t0-arb(1)/4)
    rem=remote_cost(h,cz,t)
    err=(20/t0**2+(1+arb.pi()/2)/(2*t0)).min(arb(".04"))
    out=slack*(t/(2*arb.pi())).log()/2+arch+pole+rem+err*h
    return euler*(out+prime_cost(i,k,kappa,panels,ctx.prec,paired)).exp()


if __name__=="__main__":
    ctx.prec=160;ctx.cap=32
    from poisson_power import estimate as reference
    for i,k,m in ((59,215,12),(61,245,20),(63,245,20)):
        t=arb(27).exp()+3000
        print(i,"previous",reference(arb(i)/100,t,k,m).str(10))
        for kap in (3,4,5,6):
            z=estimate(i,t,125,kap)
            print(i,kap,"bandlimited",z.str(10),flush=True)
