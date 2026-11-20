"""Uniform all-modulus high-frequency tail via physical-variable B-spline majorization."""
from flint import arb,ctx,fmpz
from actual_split import H,constants
from extras.weight_energy import zero_frequency

def run(C,Q,cut,w0,J,m,tiny=None):
    z,c,r,I,A,S,u=constants(C);h=arb(H);eta=arb(int(fmpz(Q).euler_phi()))/Q
    g=eta*(z.log()+arb("1.331"));x=arb(116).exp();w=arb(w0);delta=w*x/h
    assert 0<w<1 and m>=2 and J>Q
    assert (c-2*r).exp()<(c-r).exp()-2*delta and (c+r).exp()+2*delta<(c+2*r).exp()
    # The original mass, in the physical t variable, and the added length from dilation.
    base=(c+2*r).exp()/h*A
    added=2*delta*S
    integral=base+added;qh=(c+2*r).exp()/cut
    pref=u*h*(-c).exp()
    sumlam=z*zero_frequency(z,z)/g
    avg=2**len(fmpz(Q).factor())*eta
    order=arb(J)
    moment=avg*(order/(m-1)+Q)
    high=2*pref/Q*integral/qh*sumlam**2*moment*(m*Q*qh/(2*arb.pi()*delta*order))**m
    # Since the Ramanujan tail is periodic, its integral bound holds for every real cutoff.
    scale=order/qh
    harmonic=(1+qh.log())**3
    wedge=2*pref/Q*integral*avg*(m*Q/(2*arb.pi()*delta*scale))**m*(scale*sumlam**2/(m-1)+Q*harmonic)
    out=(high,added/base,pref*added*eta/g,wedge)
    if tiny is not None:
        ty=arb(tiny);y=ty.exp()
        d3=(1+ty)**2
        small=2*pref/Q*integral*int(fmpz(Q).euler_phi())*arb(m).zeta()*d3*(m*Q*y/(2*arb.pi()*delta))**m
        out+=small,
    return out

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=1732099)
    ap.add_argument("--Q",type=int,default=210);ap.add_argument("--cut",type=int,default=23)
    ap.add_argument("--w",default=".0002");ap.add_argument("--J",type=int,default=4*10**18)
    ap.add_argument("--degree",type=int,default=64);ap.add_argument("--upper")
    ap.add_argument("--tiny");a=ap.parse_args();ctx.prec=144
    out=run(a.C,a.Q,a.cut,a.w,a.J,a.degree,a.tiny)
    print("all q low, high frequencies; relative area increase; upper ordinary extra",*(x.str(15) for x in out))
    if a.upper:assert out[0]<arb(a.upper)
