"""The pole-free upward contour for the fourth harmonic of paired real cutoffs."""
from flint import arb
from periodic_fourth import period,weighted_disc,f


def harmonic(U,q,alpha,width,start):
    """Uniform bound for the modulus of the mixed fourth harmonic divided by T."""
    pi=arb.pi()
    v=arb(".48")
    assert U>20 and v*U>arb(start).log() and (1+2*(U/2).exp()).log()<=U
    ns=(arb(q).sqrt()*alpha,arb(q).sqrt()/alpha)
    low=[x*(-width).exp()/(2*pi).sqrt() for x in ns]
    high=[x*width.exp()/(2*pi).sqrt() for x in ns]
    amplitudes=[list(map(abs,period(q,i))) for i in (False,True)]
    mu=[arb(sum(w))/q for w in amplitudes]
    disc=[f(weighted_disc(w)) for w in amplitudes]
    # t_e=T^v. At t>=t_e, the monotone-power bound for S_k(x) is
    # sqrt(x) M_j [(k+1/2)^-1 + c/sqrt(t)], x=scale*sqrt(t).
    m=[u+D/lo.sqrt()*(-v*U/4).exp() for u,D,lo in zip(mu,disc,low)]
    # Use the true mu in this denominator so this c is sufficient uniformly.
    c=max((D/(u*lo)).upper() for D,u,lo in zip(disc,mu,low))
    de=c*(-v*U/2).exp()
    assert v>arb(1)/3 and v*U>1
    I3=2+6*de+3*de**2*U+c**3*((1-3*v)*U/2).exp()
    I4=arb(8)/3+8*de+12*de**2+4*de**3*U+c**4*((1-4*v)*U/2).exp()
    mf,md=m
    common=mf**2*md**2/(2*pi)
    endpoints=common*(1+((v-1)*U).exp())*I4
    top=common*(1+c)**4*U*(-U).exp()
    jumps=arb(0)
    for i in range(2):
        j=1-i
        # Sum tau(n)*n <= mu Y^2/2 + D Y.
        jumps+=(mu[i]+2*disc[i]/low[i]*(-U/2).exp())*m[i]*m[j]**2
    jumps*=I3/(2*pi)
    # Before t_e use t_e times a trivial pointwise bound at t_e.
    initial=arb(1)
    for u,D,hi in zip(mu,disc,high):
        initial*=(2*u*hi.sqrt()+D*(-v*U/4).exp())**2
    initial*=((2*v-1)*U).exp()/q
    return initial+endpoints+top+jumps


def fourth(U,q=30,alpha=arb("1.25"),width=arb(".06"),Z=192):
    from smooth_cut import smooth_fourth
    return smooth_fourth(U,q,alpha,width,Z,paired=True)


def disjoint_fourth(U,q=30,alpha=arb("1.25"),width=arb(".06"),Z=192):
    from smooth_cut import smooth_fourth
    return smooth_fourth(U,q,alpha,width,Z,paired=True,disjoint=True)


if __name__=="__main__":
    from flint import ctx
    ctx.prec=160
    for q in (6,30,210):
        print("paired",q,fourth(arb(40),q,arb("1.25"),arb(".06"),384).str(16),flush=True)
        print("disjoint",q,disjoint_fourth(arb(40),q,arb("1.25"),arb(".06"),384).str(16),flush=True)
