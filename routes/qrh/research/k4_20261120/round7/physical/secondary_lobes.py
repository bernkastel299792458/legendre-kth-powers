"""Bound the aggregate of 64 exterior lobe pairs by their direct Selberg square."""
from fractions import Fraction
from flint import arb,fmpz
from weighted_lobe import H,rational,sieve_remainder


def charge(lo,hi,size,ratio,order,cell_bounds,energy,location_hi="115.4",poisson=False,modulus=1,remainder_override=None,sharp_variation=False,lobes=64,physical_terms=False):
    l,h=arb(lo),arb(hi)
    K=arb(H+size);r=arb("1e-6");pi=arb.pi()
    cmax=h+(4*(-l/4).exp()).log1p()/2
    a=(1-arb("1e-12"))*K*(4*(-h/4).exp()).log1p()/2
    b=2*(pi-a);mass=pi*a.sin()/a
    assert 0<a and a<pi and 1<=lobes and (physical_terms or lobes<=64) and 2*pi*(lobes+2)<K*r
    assert l-r>arb("114.98") and cmax+r<arb(location_hi)
    z=rational(Fraction(ratio))*((l-K.log())/2).exp()
    G=z.log()+arb("1.331")
    remainder_fn=sieve_remainder
    if modulus>1:
        from odd_sieve import denominator
        from grouped_lobes import remainder
        from functools import partial
        G=denominator(z,modulus)
        remainder_fn=partial(remainder,modulus=modulus)
    if remainder_override is not None:remainder_fn=remainder_override
    assert z<(l-r).exp() and arb("1.33258")-arb("2.44")/z.sqrt()>arb("1.331")
    numerator=1+a.cos()
    P=arb(0);C=arb(0);A=arb(0)
    N=1024
    numer=[a.cos()-(a+b*k/N).cos() for k in range(1,N)]
    for j in range(1,lobes+1):
        left=2*pi*j+a;right=left+b
        den=left**2-a**2
        peak=numerator/den
        sup2=1/den+4*right/den**2+numerator*(2/den**2+8*right**2/den**3)
        A+=b/N*sum(numer[k-1]/((left+b*k/N)**2-a**2) for k in range(1,N))+arb(0,b**3*sup2/(12*N**2))
        variation=b*sup2
        if sharp_variation:
            from lobe_variation import secondary
            variation=variation.min(secondary(a,left,b))
        C+=a.sin()*(1/den+1/(right**2-a**2))+variation+2*peak/K
        P+=peak
    # The constant term from both signs of dF equals its total variation, 2P.
    err,_=remainder_fn(l,cmax,K,z,G,order,P,C/2,A,True,energy,poisson=poisson)
    base=2*(cmax+r)*(r/2).exp()/mass
    if physical_terms:
        new_slope=base*r.exp()*int(fmpz(modulus).euler_phi())/(modulus*G)
        error=base*K*(-l).exp()*P*z**2*err
        return A,new_slope,error
    # Every old per-level line is at least min_s(C1(s)+C2(s)/b) times
    # its true width. In comparing exact areas the interval is used only once.
    eta=max(tuple(cell_bounds)+("1.16613",),key=Fraction)
    scales=[arb("1.55")]+[b*i/40 for i in range(1,40)]
    lines=[]
    for s in scales:
        v=l-K.log()+arb(eta)+s.log()
        assert v>4
        k=2*(l+r)*(r/2).exp()/(mass*v**2)
        lines.append(k*(r.exp()*(v-1)+s/b))
    m=lines[0]
    for v in lines[1:]:m=m.min(v)
    return (2*m-base*r.exp()*int(fmpz(modulus).euler_phi())/(modulus*G))*A-base*K*(-l).exp()*P*z**2*err
