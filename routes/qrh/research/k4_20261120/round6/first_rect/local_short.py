"""Local second and signed first mean for a short mollifier inside a centered rectangle."""
from functools import lru_cache
from flint import arb,ctx
from short_block import data,short_second


@lru_cache(maxsize=None)
def stats(size,q,n,steps):
    H=arb(3000175332800);R=arb(size)/2;C=H+R
    M=2048;v=arb("1.01");ybar=v*M/(M-1)
    J=v*arb("1.02")*R;B=C+J;y=(B/(2*arb.pi())).sqrt();yl=((C-J)/(2*arb.pi())).sqrt()
    a,b,h,G,roots,K,L,h2,err,gmax,dsum=data(q,n,ctx.prec,steps)
    assert C-J>200 and y>1
    diag=J*(a*(y.log()+arb.const_euler())+b+G/yl)
    # Each pair is active on an interval. Off-diagonal half of the bound in SHORT.md.
    off=2*(1+arb(L).log()+B.log()/2)*(arb(K)**2+gmax*y)
    off+=8*roots**2*y
    # EG is an upper bound for (1/2)int |zeta P|² inside the near segment.
    rs=2*roots*(C-J)**(-arb(1)/4)*J.sqrt()
    main=(2*(diag+off).sqrt()+rs)**2
    # The remote height mixture uses the unconditional cumulative mixed second moment.
    B0=C+v*R;p=1+1/B0.log()
    z=short_second(B0.log(),q,n,steps)*B0*B0.log()
    total=main+z*M/(M-p)*arb("1.02")**(p-M)
    # The power correction follows the cumulative signed first mean on either side.
    first_error=20*(1+roots)*(C+ybar*R+200).sqrt()+82000*(1+roots)
    # The analytic factor (s-1)zeta(s)/((s+1)(s+2)^(1/4)) is bounded by
    # 48 in the whole strip by the maximum principle on its two sides.
    first_error=first_error.min(160*(1+roots)*(C+ybar*R+4)**(arb(1)/4))
    return h,h2,total,first_error


def left_split(size,q,cm,m4,u,w,h,qbase,short_sizes):
    R=arb(size)/2;ybar=arb("1.01")*2048/2047;v=arb("1.01")
    main=m4**(arb(1)/4)*(cm*R*u).sqrt()
    best=(main+(ybar*R)**(arb(3)/4))**(arb(4)/3)
    eu=arb(1)
    for p in (2,3,5,7,11):
        if q%p==0 and qbase%p: eu*=1+1/arb(p)
    # For CM's definition here retain its convolution baseline on all
    # harmonic coefficients after subtraction. Caller supplies this version.
    for n,s in short_sizes:
        S,S2,short,err=stats(size,q,n,s)
        from projected_short import best_projected
        projected=best_projected(size,q,n,s)
        if projected is not None:short=short.min(projected)
        assert n<R*h.exp() and (q//qbase)*n<6*v*arb("1.03")*R/arb.pi()
        for k in range(1,26):
            theta=arb(k)/25
            # Dropping the factor of the convolution loss keeps the harmonic deduction valid.
            shrink=(2*theta*S-theta**2*S2)*eu*R*v*(1-arb("1.03")**(1-2048))
            remainder=cm*R*u-shrink
            assert remainder>0
            small=theta**2*short+(1-2*theta)*ybar*R+2*theta*err
            assert small>0
            root=m4**(arb(1)/4)*remainder.sqrt()+(ybar*R)**(arb(1)/4)*small.sqrt()
            best=best.min(root**(arb(4)/3))
    return best
