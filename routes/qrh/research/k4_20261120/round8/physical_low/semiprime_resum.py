"""Recombine every middle mode of the concrete semiprime family in phase_floor.py."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from compact_spline import run as spline

def run():
    C=1732099;Q=210
    z,c,r,I,A,S,u=constants(C);x=arb(116).exp();h=arb(H)
    lo=(c-2*r).exp();hi=(c+2*r).exp();d=arb(int((z/11).floor().unique_fmpz()))
    assert 11*(d+1)>z and z/2>d and d**2>arb("70.7").exp()
    assert 4*d*d<hi/23 and d>z**2/d**2 and d>Q
    G=arb(48)/Q*(z.log()+arb("1.331"));lweight=((d/(d-1))/G)**2
    ell=d.log();outer=d**(arb(".92"));inner=arb(22).exp()
    hsum=2*arb(2).log()/outer.log()+(outer+1)/d
    count=2*d/ell
    low=int((lo/(4*d*d)).floor().unique_fmpz())+1
    top=int((hi/(d*d)).floor().unique_fmpz())
    active=[k for k in range(low,top+1) if gcd(k,Q)==1]
    # Use the actual k-dependent outer d-row support when estimating the harmonic mass.
    sc=ec=arb(0)
    for k in active:
        p0=d.max(lo/(2*k*d));p1=(2*d).min(hi/(k*d))
        assert p1>p0
        hr=(2*(p1/p0).log()/outer.log()+(outer+1)/p0).min(hsum)
        pc=(2*(p1-p0)/outer.log()+outer+1).min(count)
        sc+=2*hr/(inner.log()*k)
        ec+=pc*(inner+1)
    w=arb(".0002");dil=w*x/h;allarea=hi/h*A+2*dil*S;pref=u*h*(-c).exp()
    actual=pref*lweight*(sc*allarea+ec*S)
    cap=int((4*Q*d*d/hi).floor().unique_fmpz())
    amps=sum(int(fmpz(gcd(n,Q)).euler_phi()) for n in range(1,cap+1))
    lowcharge=2*pref/Q*allarea*amps*lweight*hsum**2
    hiw=spline(C,Q,23,".0002",4*10**18,64)[3]
    return top,len(active),actual,lowcharge,actual+lowcharge+hiw

if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser(description=__doc__);cli.add_argument("--upper");a=cli.parse_args();ctx.prec=160
    top,n,*v=run()
    print("k max",top,"admissible k",n,"all summed, low correction, same middle band",*(t.str(14) for t in v))
    if a.upper:assert v[-1]<arb(a.upper)
