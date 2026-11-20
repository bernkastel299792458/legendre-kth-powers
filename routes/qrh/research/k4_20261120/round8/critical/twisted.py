"""Twisted second means of the paired sharp AFE from matched asymmetric cutoffs."""
from functools import lru_cache
from math import gcd
from flint import arb, ctx
from interference import period, weighted_disc, f, means
from periodic_fourth import harmonic


@lru_cache(None)
def constants(q,dual,prec):
    assert prec == ctx.prec
    vals = period(q,dual)
    squares = tuple(v*v for v in vals)
    den = q if dual else 1
    rho, head, error = harmonic(squares,ctx.prec)
    absolute = list(map(abs, vals))
    return (rho/den,head/den,error/den,arb(max(squares))/den,
            arb(sum(absolute))/(q*arb(den).sqrt()),f(weighted_disc(absolute))/arb(den).sqrt())


def afe(q,alpha,width):
    a = arb(q).sqrt()*alpha
    changes = sum((arb(j)/a).sqrt().max((a/j).sqrt())/arb(j).sqrt()
                  for j in range(1,q+1) if q%j==0)
    return 16*(2*arb.pi())**(arb(1)/4)*(width/2).exp()*changes


def offdiag(r,s,X,Y,T):
    # Each n-row has at most one residue representative at each distance and sign.
    return (4*(r*s).sqrt()*X*(1+(1+Y.log())/s)+8*(X*Y).sqrt())/T


def branch_norm(q,dual,Y,upperY,T):
    density,head,er,maxsq,_,_ = constants(q,dual,ctx.prec)
    return (density*upperY.log()+head+er/Y+maxsq*offdiag(arb(1),arb(1),Y,Y,T)).sqrt()


def cos_bounds(U,slab,q,alpha,width,start,ri,si):
    assert gcd(ri,si)==1 and gcd(ri*si,q)==1 and 0<si<ri
    r,s,T = arb(ri),arb(si),U.exp()
    pi=arb.pi()
    R=r/s
    tnew=(2*pi*q*(alpha.max(1/alpha)*width.exp())**2*R).max(start)+1
    assert tnew < T
    scales = [arb(q).sqrt()*a/(2*pi).sqrt() for a in (alpha,1/alpha)]
    Y = [v*width.exp()*T.sqrt() for v in scales]
    minl = [v*(-width).exp() for v in scales]
    maxl = [v*width.exp() for v in scales]
    def absolute(dual,x):
        _,_,_,_,mu,err = constants(q,dual,ctx.prec)
        return 2*mu*x.sqrt()+err
    # Lower mean of S*cos(log R t) and aligned-on-original diagonal difference.
    main = increment = errors = arb(0)
    for side in range(2):
        den,head,er,maxsq,_,_ = constants(q,side,ctx.prec)
        lo = minl[side]*T.sqrt()/r
        # Integrate the sharp harmonic mean using the project baseline lower.
        H = den*lo.log()+head-er/lo
        assert H>0
        main += (1-tnew/T)*H-den/2-er/lo
        # Integrate 1/sqrt(t) up to T; harmonic endpoints above zero.
        assert minl[side]*tnew.sqrt()>r
        increment += den*R.log()/2+4*er*r/(minl[side]*T.sqrt())
        if side==0:
            X1,X2=Y[side]/R.sqrt(),Y[side]*R.sqrt()
        else:
            X1,X2=Y[side]*R.sqrt(),Y[side]/R.sqrt()
        orig = maxsq*offdiag(r,s,Y[side],Y[side],T)
        # Forward n:m=s:r; for dual use the same orientation with n,m swapped.
        aligned = maxsq*offdiag(r,s,X1.min(X2),X1.max(X2),T)
        errors += orig+aligned
        main -= (r*s).sqrt()*orig
    lower = main/(r*s).sqrt()
    # Any part missing before the common start in S and V.
    ef = absolute(False,maxl[0]*tnew.sqrt())
    ed = absolute(True,maxl[1]*tnew.sqrt())
    lower -= tnew/T*(ef**2+ed**2)
    early = 2*tnew/T*ef*ed
    # The two balanced cross integrals. For X'Y' = Qt/(2pi R'),
    # their phase is monotone above its stationary endpoint.
    eps = (-U/4).exp()
    assert eps < arb(".1")
    mixed=arb(0)
    for direction in (-1,1):
        scale=R**(arb(direction)/2)
        fx,dy=Y[0]*scale,Y[1]*scale
        far=2*absolute(False,fx)*absolute(True,dy)/(eps*T)
        loglam_low=2*(alpha.log()-width)
        ratio_low=loglam_low.exp()  # Both lengths have the same scaling here.
        ratio_high=(2*(alpha.log()+width)).exp()
        _,_,_,_,rho,disc=constants(q,False,ctx.prec)
        _,_,_,_,mu,D=constants(q,True,ctx.prec)
        # Harmonic absolute dual sum <= mu(1+log y)+D by partial summation.
        near=3*(eps/2).exp()*(2*rho*eps.sinh()*ratio_high.sqrt()*(mu*dy+D)
                   +disc*(mu*(1+dy.log())+D)/ratio_low.sqrt())/T.sqrt()
        mixed += far+near
    # Comparison of two representations of the same zeta factor.
    factors=(alpha,alpha/R.sqrt(),alpha*R.sqrt())
    K=[afe(q,a,width) for a in factors]
    signed_mean=means(U,q,alpha,width,start,slab=slab)[1]
    norm=(sum(branch_norm(q,side,y,y*(slab/2).exp(),T)**2
              for side,y in enumerate(Y))+signed_mean).sqrt()
    err1=(2/T.sqrt()).sqrt()*(K[0]+K[1])
    err2=(2/T.sqrt()).sqrt()*(K[0]+K[2])
    compare=(err1+err2)*norm+err1*err2
    upper=increment/(r*s).sqrt()+errors+mixed+compare+early
    return lower,upper


def project(U,b,q,alpha,width,start,m,v2,s2,mean0,limit=80,bound_fn=cos_bounds):
    T=U.exp()
    rho=(s2/v2).sqrt()*((U+b)/U)**4
    total=inc=cost=squares=arb(0)
    # All noninteger denominators are retained if they pass the individual test.
    for s in range(1,limit):
        if gcd(s,q)!=1:
            continue
        for r in range(s+1,limit+1):
            if gcd(r,s*q)!=1:
                continue
            w=(arb(r)/s).log()
            delta=arb(".25")+((q*arb(start)/(2*arb.pi())).sqrt()).log()-w
            if not delta>0:
                continue
            l,h=bound_fn(U,b,q,alpha,width,start,r,s)
            l-=m/(T*w)
            # mean0=4 B/(.25 T), so 4B/(delta T) dominates both cos orientations.
            h+=mean0*arb(".25")/delta
            p=(2*(l-rho*h)).max(0)
            if not p>0:
                continue
            total+=p
            squares+=p*p
            inc+=2*p*l
            cost+=p*h
    inc-=squares/2+2*(limit**2+1)*total**2/T
    return inc,cost
