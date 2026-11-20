"""Left-shifted whole detector for the finite Gabriel row."""
from math import prod

from flint import arb,ctx

from shift_fold import shifted_cm
from shift_zeta import shifted_fourth
from sweep_boundary import fourth
from moving_line import comparison,row
from short_block import data,short_second


def short(U,V,h,q,N,tau):
    v=arb("1.01");m=2048;ybar=v*m/(m-1)
    _,_,_,_,l1,*_=data(q,N,ctx.prec)
    j=v**(1+1/U)*m/(m-1-1/U)
    sec=short_second(U,q,N)*j
    z=(1-2*tau).max(arb(0))/U+(1-2*tau).min(arb(0))/V
    central=tau**2*sec+z*ybar+40*tau*(1+l1)*ybar.sqrt()*(-U/2).exp()/U
    assert central>0
    if h.is_zero():return central
    primes=[p for p in (2,3,5,7,11) if q%p==0]
    assert prod(primes)==q
    moment=arb(N)*(N+1)*(2*N+1)/6*prod(1+p*p for p in primes)
    maxindex=q*N
    affine=4*maxindex*(1+arb(maxindex).log())/U.exp()
    mean=(v*(m-3)/(m-4)+affine)*moment
    far=(tau*arb(2).zeta()*((v*V.exp()+1)/(2*arb.pi()))**(arb(3)/2)*
        mean.sqrt()+ybar.sqrt())**2/U
    r=h/(arb(3)/2)
    return (1+arb("1e-9"))/(1-arb("1e-6"))*central**(1-r)*far**r


def left(U,V,h,W,lh,q,N,c4):
    z=shifted_fourth(U,V,h,c4)
    # The low-frequency harmonic is quadratic in the removed short core.
    full=shifted_cm(U,V,h,W,lh,q,210,N)
    residual=shifted_cm(U,V,h,W,lh,q,210,N,arb(1))
    v=arb("1.01");ybar=v*2048/2047
    best=(z**(arb(1)/4)*full.sqrt()+ybar**(arb(3)/4)/U**(arb(3)/2))**(arb(4)/3)
    T=arb(0)
    for i in range(1,101):
        t=arb(i)/100
        m=residual+(1-t)**2*(full-residual)
        c=short(U,V,h,q,N,t)
        val=(z**(arb(1)/4)*m.sqrt()+ybar**(arb(1)/4)*c.sqrt()/U)**(arb(4)/3)
        if val<best:best,T=val,t
    return best,T


if __name__=="__main__":
    ctx.prec=160
    U=arb(37);V=U+arb(1)/2
    c=fourth(U,210,arb(".82"),arb(".34"),384)
    al,ar=row(U)
    for delta in (".0001",".001",".0025",".005",".01"):
        h=arb(delta)
        val,tau=left(U,V,h,arb("9.5"),arb(-3),2310,2**18,c)
        ratio=val*U.exp()*U**2/al
        print(delta,"left ratio",ratio.str(10),"tau",tau.str(4),flush=True)
        for sv in (".80",".84",".87"):
            _,need=comparison(U,arb(sv),al,ar)
            print("  hinge",sv,"ceiling",need(-h).str(10),flush=True)
