"""Finite Riesz cutoff, using the original one-zero Poisson sampling bound."""
from gaussian_detector import H,N,Q,D,THETA,zprime,short_second,arb,ctx


def compact_fraction(lo,hi,j,scale,S,threshold,paired=False):
    s=arb(j)/1000
    c=2*s-arb(1)/2
    lam=2*D
    F=(hi-(2*arb.pi()).log())/2+zprime(2*j-500,ctx.prec)+arb(".004")
    d=s-arb(1)/2
    density_factor=1/(c-THETA)
    if paired:
        # Paired Poisson kernels for beta and 1-beta.
        density_factor=3/(2*(c-arb(1)/2))
    J=lam**2*density_factor/(4*arb.pi()*(lam-D))
    p=3*(1-s)/(3*s-1)
    slope=1-2*d-p
    return (J*F*S*arb("1.0053")*(lo*slope).max(hi*slope).exp()*
            arb(scale)**(-2*d)/(7*(threshold-arb("1e-4"))**2))


def full(jstar=None):
    rows={}
    for lo8 in range(229,360):
        lo,hi=arb(lo8)/8,arb(lo8+1)/8
        S=short_second(lo,Q,N)
        for j in (range(800,875) if jstar is None else [jstar]):
            for scale in (32,128,512):
                for paired in (False,True):
                    key=(scale,paired)
                    rows[key]=rows.get(key,arb(0)).max(
                        compact_fraction(lo,hi,j,scale,S,arb(1)/2,paired))
    return rows


if __name__=="__main__":
    ctx.prec=160
    U=arb(35)
    from short_block import data
    R=data(Q,N,ctx.prec)[4]
    low,high=arb(H),arb(45).exp()
    head=arb("1.001")*(high**arb(".2")/(arb(".9")*low)+200*low**arb("-.8"))
    tail=2*low**arb("-.3")*(1/(arb(".9")*low).sqrt()+(200/low).sqrt())
    err=6*(2*D)*R*arb(32)**arb("-.3")/arb.pi()*(head+tail)
    assert err<arb("1e-4")
    assert arb("1.005")*(1+arb("1.005").log()/low.log())<arb("1.0053")
    for (scale,pair),val in full().items():
        f=compact_fraction(U,U,850,scale,short_second(U,Q,N),arb(1)/2,pair)
        print(scale,pair,"full",val.str(9),"benchmark",f.str(9),flush=True)
