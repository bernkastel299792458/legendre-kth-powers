"""Upper signed circular constants with exact Jensen means away from root radii."""
from functools import lru_cache
from math import comb
from flint import arb,ctx


@lru_cache(maxsize=4)
def constants(J,precision):
    assert J==8 and precision==ctx.prec
    eps=arb('2e-6');step=arb(2).log()/64;pp=(arb(4)/3,arb(2))
    cap=[arb(0),arb(0)]
    a=[arb(comb(J,k))*(-arb(1)/J)**k for k in range(J+1)]
    coef=[u+v for u,v in zip(a+[arb(0)],[arb(0)]+a,strict=True)]
    padcoeff=[abs(z)*((1+eps)**k-1) for k,z in enumerate(coef)]
    nang=384
    cos=[(arb.pi()*j/nang).cos() for j in range(nang+1)]
    for k in range(-256,257):
        r=(k*step).exp();s=r/J;pad=sum(v*r**j for j,v in enumerate(padcoeff))
        minimum=abs(r-1)*abs(1-s)**J
        unpadded=r.log().max(0)+J*s.log().max(0)
        if minimum>0:
            direct=unpadded+(pad/minimum).log1p()
        else:direct=None
        if direct is None or any(direct>v*r**p for v,p in zip(cap,pp,strict=True)):
            peak=-(1-arb(1)/J)*r/2
            avg=arb(0)
            for hi,lo in zip(cos,cos[1:]):
                z=peak.max(lo).min(hi)
                mag=((1+2*r*z+r*r)*(1-2*s*z+s*s)**J).max(0).sqrt()
                avg+=(mag+pad).log()
            avg/=nang
            direct=avg if direct is None else direct.min(avg)
        for i,p in enumerate(pp):cap[i]=cap[i].max(direct/r**p)
    r=arb(1)/16
    small=sum(v*r**(j-2) for j,v in enumerate(padcoeff[2:],2))/(1-r)**2
    r=arb(16)
    # Both quotients decrease beyond 16. The independent root factors give
    # a uniform upper bound on the relative perturbation across the full tail.
    ratio=(1+r)/(r-1)*((r+J)/(r-J))**J
    correction=(ratio*((1+eps)**(J+1)-1)).log1p()
    tail=r.log()+J*(r/J).log()+correction
    for i,p in enumerate(pp):
        assert p*tail>J+1
        cap[i]=(cap[i]*(1+(p*step)**2*(p*step).exp()/8)).max(small*(arb(1)/16)**(2-p)).max(tail/r**p)
    return tuple(cap)


if __name__=='__main__':
    ctx.prec=160
    print('signed circular Jensen caps',*(v.upper().str(17) for v in constants(8,ctx.prec)),flush=True)
