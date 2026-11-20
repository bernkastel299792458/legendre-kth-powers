"""Bounds for 1/zeta and a Gaussian Mobius polynomial in the verified-height strip."""
from functools import lru_cache
from flint import acb_series,arb,ctx

H=3*10**12


@lru_cache(maxsize=64)
def right(k,prec):
    assert prec==ctx.prec
    u=arb(1)+arb(k)/100
    pair=acb_series([u,1],2).zeta()
    return u,pair[0].real/(2*u).zeta(),(-pair[1]/pair[0]).real


def inverse(s,t,k):
    u,euler,deriv=right(k,ctx.prec)
    a,b=s-arb(1)/2,u-arb(1)/2
    assert arb(1)/2<s<u and 100<=t<=H//2 and 1<u<2
    h=u-s
    lam=b*(b/a).log()
    assert lam>h
    # Uniform in 100 <= |Im s| <= t. The explicit signed gamma term is
    # within .04 of log(|Im s|/(2*pi))/2 on 1/2 <= Re s <= 2.
    assert 4*(1/(arb(100)**2))+arb(1)/100+arb.pi()/400+arb(1)/100<arb(".04")
    remote=32*(arb(H).log()+1)/H
    return euler*((lam-h)*(t/(2*arb.pi())).log()/2+lam*deriv+
                  arb(".04")*(lam+h)+h*remote).exp()


def experiment(logx,logt):
    X,T=arb(logx).exp(),arb(logt).exp()
    width=arb(".1")
    B=arb(1000)
    assert T-B>=100 and T+B<=H//2
    best=None
    for m in range(56,96):
        s=arb(m)/100
        for k in range(5,61,2):
            u,euler,_=right(k,ctx.prec)
            bound=inverse(s,T+B,k)
            mass=bound*X**s*((width*s)**2/2).exp()
            edge=2*width*(u-s)*bound*X**u*(width**2*(u*u-B*B)/2).exp()
            tail=euler*X**u*((width*u)**2/2).exp()*(width*B/arb(2).sqrt()).erfc()
            val=(mass+edge+tail)/X
            if best is None or val<best[0]:best=val,m,k
    print("log X",logx,"log |tau|",logt,"bound divided by X",best[0].str(13),
          "sigma hundredths",best[1],"sigma0 increment hundredths",best[2],flush=True)
    return best


if __name__=="__main__":
    ctx.prec=160
    for x,t in ((43,26),(50,15),(55,15),(60,10),(60,25),(70,25)):
        experiment(x,t)
