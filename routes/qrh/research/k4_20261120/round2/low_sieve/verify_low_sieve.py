"""Replay the signed finite-height kernel with a sharper exterior-lobe bound."""
from fractions import Fraction
from flint import arb, ctx


def exact(value):
    x=Fraction(value)
    return arb(x.numerator)/x.denominator


def verify(high, lobe, addition):
    low=exact("114.96")
    H, Q, r = arb(3*10**12), arb(10**6), exact(".00004")
    K=H-128*Q
    d=(4*(-high/4).exp()).log1p()/2
    cmax=high+(4*(-low/4).exp()).log1p()/2
    pi=arb.pi()
    assert K*d>lobe and 0<lobe and lobe<pi and r>lobe/K
    mass=pi*lobe.sin()/lobe
    maxg=(1-lobe.cos())/lobe**2
    D=(low/2).exp()*mass/K
    # For each outer lobe with index j>=1, numerator <= 1+cos(a).
    peaks=lobe.sin()/lobe+(1+lobe.cos())/12
    v=low-K.log()+addition
    assert K.log()-addition+r>2 and v>4
    assert 2*(v-addition).exp()/v**2>10
    bt=2*(low+r)*(3*r/2).exp()*(v-1)*(1-lobe/pi)/v**2
    intercept=2*(low+r)*(r/2).exp()*peaks/(v**2*mass)
    powers=maxg*r.exp()*(cmax+r)**2/(2*arb(2).log()*D)
    far=4*maxg*(3*cmax/2+9/(8*Q**2)-(Q*r)**2/2).exp()/D
    pole=16*pi.sqrt()*Q/(K*mass)
    small=2*H*H.log()*pi/(lobe*K*D)
    arch=maxg*(7+(1+K+2*Q/pi.sqrt()).log())/D
    large=2*K/mass*(2*pi*maxg)/(2*pi.sqrt()*Q)*(1/(16*Q**2)).exp()
    large*=H**2*(1+4*Q**2/(H-K)**2)*(-((H-K)/(2*Q))**2).exp()
    total=bt+intercept+powers+far+pole+small+arch+large
    n=int((high/4).exp().floor().unique_fmpz())
    assert 4*arb(n).log()<high and high<4*arb(n+1).log() and total<1
    print("L",high.str(12),"BT addition",addition.str(8),"exterior",(bt+intercept).str(16),
          "total",total.str(18),"integer endpoint",n)


if __name__=="__main__":
    ctx.prec=256
    verify(exact("114.992"),exact("1.9634"),arb(0))
    verify(exact("115.017"),exact("1.9512"),exact(".8601"))
