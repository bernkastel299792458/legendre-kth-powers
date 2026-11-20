"""A zeta-only analytic detector, its exact radial constant, and the scalar log M floor."""
from flint import arb,ctx
from weighted_green import interpolated_point


def canonical(nu):
    assert 1<nu<2
    def g(r):return (1-nu)*r+r/(r-1)-nu*(r-1).log()
    a,b=arb(2),arb(16)
    assert g(a)>0 and g(b)<0
    for _ in range(90):
        m=(a+b)/2
        if g(m)>0:a=m
        elif g(m)<0:b=m
        else:break
    r=a.union(b)
    return (r+(r-1).log())/r**nu


def log_floor(a,T,Y,X,Q=2310):
    assert arb('.65')<=a<1 and X>=Y>3
    Z=arb(2).zeta();pi=arb.pi()
    N=(2*(Q*X).sqrt()/(2-Z)).log()/(arb(15)/14).log()
    horizontal=2*(2-a)*pi*(N+arb(3)/2)
    right=2*Z/arb(2).log()+2*T/(Y-3)
    return -(horizontal+right)


if __name__=='__main__':
    ctx.prec=160
    u=arb(36);T=u.exp();d=arb('1.1');R=1+d/u
    for s in ('.82','.85','.87'):
        a=arb(s);theta=(R-a)/(R-arb('.488'));nu=4/(2+theta)
        c=canonical(nu);orig=interpolated_point(nu)
        floor=log_floor(a,T,(u-3).exp(),(u+6).exp())
        print('a',s,'nu',nu.str(10),'canonical',c.str(10),'archived radial',orig.str(10),
              'ratio',(c/orig).str(9),'scalar log M lower',floor.lower().str(12),flush=True)
