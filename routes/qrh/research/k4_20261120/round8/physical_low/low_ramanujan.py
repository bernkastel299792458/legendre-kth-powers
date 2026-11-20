"""Signed Ramanujan modes on curved low-modulus slices by one-dimensional Abel summation."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants
from empty_lcm import region,MEAN

def run(C,Q,cuts,frequencies):
    z,c,r,I,mass,peaks,u=constants(C);xh=(c+2*r).exp()
    eta=arb(int(fmpz(Q).euler_phi()))/Q;assert fmpz(Q).moebius_mu()
    assert all(b>a for a,b in zip(cuts,cuts[1:])) and min(cuts)>=1
    totals=[]
    prev=cuts[0]
    left=region("116",C,MEAN,True,threshold=xh/prev,sieve_mod=Q)[1]/eta
    integral=arb(0)
    for right in cuts[1:]:
        end=region("116",C,MEAN,True,threshold=xh/right,sieve_mod=Q)[1]/eta
        uni=region("116",C,MEAN,True,threshold=xh/right,sieve_mod=Q,uniform=True)[1]/eta
        integral+=(right-prev)*uni
        def bound(J):
            value=arb(0)
            for n in range(1,J+1):
                g=gcd(n,Q);amp=abs(int(fmpz(Q//g).moebius_mu()))*int(fmpz(g).euler_phi())
                value+=(end+left+2*arb.pi()*n/Q*integral)*2*amp/Q
            return u*(2*r).exp()*mass*value
        vals=[bound(j) for j in frequencies]
        print("q range X /",right,"to X /",cuts[0],"prefix inverse upper",end.str(10),"modes",*[s.str(12) for s in vals],flush=True)
        totals.append(vals);prev=right
    return totals

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--Q",type=int,default=210)
    ap.add_argument("--C",type=int,default=1732099);ap.add_argument("--cuts",type=int,nargs="+",default=[23,29,41,64,96,128])
    ap.add_argument("--modes",type=int,nargs="+",default=[1,4,8,16,32]);ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=144
    rows=run(a.C,a.Q,a.cuts,a.modes)
    if a.upper:assert rows[-1][-1]<arb(a.upper)
