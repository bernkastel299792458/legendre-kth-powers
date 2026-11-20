"""Infinite harmonic tail on every remaining unit-sieve modulus after tapering."""
from flint import arb,ctx,fmpz
from actual_split import constants,H
from extras.weight_energy import zero_frequency

def run(C,Q,cut,width,J):
    z,c,r,I,mass,peaks,u=constants(C);h=arb(H);eta=arb(int(fmpz(Q).euler_phi()))/Q
    G=eta*(z.log()+arb("1.331"));xh=(c+2*r).exp()
    a=(1-arb("1e-12"))*h*(c-116);w=arb(width);U=h*r;assert 0<w<a and U>4
    assert a>arb("1.5") and a<arb.pi()/2 and 2*arb.pi()-2*a>3
    # Total variation of the first derivative of the piecewise smooth physical shape.
    variation=2/w+7+12/U+6/h
    peakslope=h*(2*r-c).exp()*variation
    pref=u*h*(-c).exp()
    lmass=z*zero_frequency(z,z)/G
    mean=2**len(fmpz(Q).factor())*eta
    tail=mean*(arb(1)/J+arb(Q)/arb(J)**2)
    high=pref*arb(Q)/(2*arb.pi()**2)*peakslope*(xh/cut)*lmass**2*tail
    addedmass=w*a.sin()/(2*a)
    extra=u*(2*r).exp()*eta/G*addedmass
    return high,addedmass/mass,extra

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=1732099)
    ap.add_argument("--Q",type=int,default=210);ap.add_argument("--cut",type=int,default=23)
    ap.add_argument("--w",default=".001");ap.add_argument("--J",type=int,default=10**31);ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=144
    out=run(a.C,a.Q,a.cut,a.w,a.J)
    print("full low-q high modes, relative slope increase, ordinary increase",*(x.str(16) for x in out))
    if a.upper:assert out[0]<arb(a.upper)
