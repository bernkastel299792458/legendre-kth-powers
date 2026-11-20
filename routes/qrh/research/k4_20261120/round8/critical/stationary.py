"""Twisted mean of the genuine AFE interference, including its rational saddle."""
from math import gcd
from flint import arb, ctx
from twisted import constants, offdiag


def cos_bounds(U,slab,q,alpha,width,start,ri,si):
    assert 0 < si < ri and gcd(ri,si)==gcd(ri*si,q)==1
    r,s,T = arb(ri),arb(si),U.exp()
    pi=arb.pi()
    R=r/s
    w=R.log()
    eps=(-U/4).exp()
    assert eps<arb(".1")
    rho,_,_,_,_,du=constants(q,False,ctx.prec)
    _,_,_,_,scaled_mu,scaled_disc=constants(q,True,ctx.prec)
    mu,disc=scaled_mu*arb(q).sqrt(),scaled_disc*arb(q).sqrt()
    base=arb(q).sqrt()/(2*pi).sqrt()
    X,Y=base*alpha*width.exp()*T.sqrt(),base/alpha*width.exp()*T.sqrt()
    lam_max=(alpha*width.exp())**2
    def raw(dual,x):
        _,_,_,_,m,d=constants(q,dual,ctx.prec)
        return 2*m*x.sqrt()+d
    amplitudes=raw(False,X)*raw(True,Y)/T
    # Expected S*cos from the two actual rational diagonals.
    lower=arb(0)
    for side,y in enumerate((X,Y)):
        den,head,er,maxsq,_,_ = constants(q,side,ctx.prec)
        lo=y* (-(2*width)).exp()/r
        H=den*lo.log()+head-er/lo
        assert H>0
        lower+=((1-start/T)*H-den/2-er/lo)/(r*s).sqrt()
        lower-=maxsq*offdiag(r,s,y,y,T)
    # The t_0 correction for extending W to its natural moving lower cutoffs.
    early=2*start/T*raw(False,X*(start/T).sqrt())*raw(True,Y*(start/T).sqrt())
    # First orientation has positive derivative >= log R.
    ordinary=2*amplitudes/w
    # Off-boundary error of the stationary phase approximation.
    away=(4000+8/eps)*amplitudes
    # Count the two lower-boundary strips. The cap on the j index is essential
    # when the center ratio is lambda*R and R is large.
    near=arb(0)
    for side in (-1,1):
        ratio=R**side
        ymax=Y*(arb(1).min(eps.exp()/ratio))
        # lambda*ycut^2 <= (Q/(2pi))*T*min(1,e^eps/ratio)^2
        trunc=arb(1).min(eps.exp()/ratio)
        sumj=(mu*base**2*T*trunc**2/2+disc*lam_max*ymax)
        near+=2*rho*ratio*eps.sinh()*sumj+du*(mu*ymax+disc)
    # Upper-boundary strip for n*j near C; both n<=X, j<=Y.
    cap=arb(q)*T/(2*pi*R)
    near+=2*rho*cap*eps.sinh()*(mu*(1+Y.log()+slab/2)+disc)+du*(mu*Y+disc)
    near*=9*(2*pi*R).sqrt()/(q*T)
    # Complete stationary main over j in a lattice interval, then over n.
    edge=du*Y+(rho*X+du)*q*s*(mu+1)
    principal=(rho*w/(r*s).sqrt()+2*pi*R.sqrt()*edge/(q*T))
    return lower, ordinary+away+near+principal+early
