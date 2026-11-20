"""Actual ordinary Mellin I for *all* semiprimes in a hyperbolic modulus annulus."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from prime_twist import run as prime
from row_calibration import run as calibration
from odd_sieve import denominator

def run(m):
    Q=210;C=1732099;K=arb(H);z,c,r,I,A,S,u=constants(C);x=arb(116).exp();X=(c+2*r).exp()
    Pmin=X/(m*z);t0=K/8;t1=K/4;vcut=K/16
    assert m>=24 and m<=10000 and z<arb("2.169e25") and Pmin>10000
    assert 1-arb(4)*m*r>arb(".9") and X/m>z
    w=arb("5.5e-11");delta=arb(".0002")*x/K;area=X/K*A+2*delta*S;pref=u*K*(-c).exp()
    assert (c+r).exp()+2*delta<(c+r*arb("1.01")).exp() and (c-r).exp()-2*delta>(c-r*arb("1.01")).exp()
    G=denominator(z,Q);rho=Pmin/(Pmin-1)
    gp=sum((arb(int(fmpz(b).moebius_mu())**2)/int(fmpz(b).euler_phi()) for b in range(1,m+1) if gcd(b,Q)==1),arb(0))
    assert z/Pmin<m and Pmin>m
    E=z.sqrt()*z.log()**2/(8*arb.pi())
    harm=((z/Pmin).log()+2*E/Pmin)/Pmin.log()
    # Monotone partial summation of the genuine prime coefficient over each dyadic.
    row=arb(0);l=Pmin
    while l<z:
        b=l.min(z);row+=prime(b.log(),t0-vcut,t1+vcut)[0];l*=2
    cal=calibration()[1]
    # Fourier transform of the log cut: density / 2pi, length log(m/23).
    logwidth=(arb(m)/23).log()
    l1=(logwidth+2*((1/w).log()+1))/arb.pi()
    high=(2/arb.pi())*(-(w*vcut)**2/2).exp()/(w*vcut)**2
    smooth=cal*(gp*rho)**2*((t1-t0)*(row**2*l1+harm**2*high)+
                            (t1-t0)/ (Pmin-1))
    # For the sharp-minus-smooth difference keep its physical t oscillation.
    # N truncation in the unit zeta costs < 1 after integrating I.
    N=K**3;eta=arb(48)/210
    assert (t1-t0)*(eta/t0+4*(1+(1+t1**2).sqrt())/N)<1
    resonance=4/(23*r)+4*arb(m)*(1+(2*arb(m)).log())/arb(".9")+2*(1+N.log())/arb(2).log()+1
    near=2*harm*(r/4).exp()*(w*(w**2/2).exp()+2/Pmin)
    far=2*harm**2*(-(r/w)**2/32).exp()
    glob=calibration()[0]
    edge=pref*area/(arb.pi()*G**2)*(gp*rho)**2*(near*resonance+far*(t1-t0)*glob)
    return row,smooth,edge,smooth+edge

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--end",type=int,default=400);ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=160;v=run(a.end)
    print("prime row norm sup, smoothed Mellin cost, sharp cutoff error, whole actual I",*(y.str(13) for y in v))
    if a.upper:assert v[-1]<arb(a.upper)
