"""Necessary sieve levels for a positive Selberg majorant with the current band."""
from flint import arb,ctx


def floor_ratio(L,S,C):
    l=arb(L);k=arb(3000175332800+S)
    r=arb("1e-6");Q=arb(10000);pi=arb.pi()
    d=(4*(-l/4).exp()).log1p()/2;c=l+d
    a=(1-arb("1e-12"))*k*d
    I=pi*a.sin()/a
    assert 0<a and a<pi and k*r>a
    outside=1-a/pi-2*(k*d-a)*(1-a.cos())/(a**2*I)-4/(I*k*r*(1-(a/(k*r))**2))
    target=(c-r)*(-r/2-(Q*r)**2).exp()*outside
    z=arb(C)*((l-k.log())/2).exp()
    # The general published upper for G from the original sieve proof.
    max_G=z.log()+2+arb("2.44")/z.sqrt()
    assert z>1 and outside>0
    return target/max_G,k/arb(C)**2

if __name__=="__main__":
    ctx.prec=160
    for l,c0,c1 in [("115.4",130,90),("115.5",660,470),
                    ("116",1160000,860000),("117",340000000000,265000000000)]:
        for size,C in [(0,c0),(16000000000,c1)]:
            cost,f=floor_ratio(l,size,C)
            print(l,size,C,"main cost at least",cost.str(16),"n=1 top phase",f.str(12))
            assert cost>1
