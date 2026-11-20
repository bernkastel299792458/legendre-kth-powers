"""Certified presieved high-modulus part with no admissible integer multiple."""
import argparse
from flint import arb,ctx,fmpz
from empty_lcm import region,MEAN

def run(L,C,Q,mean):
    h=arb(3000175332800);l=arb(L);d=(4*(-l/4).exp()).log1p()/2;c=l+d
    r=arb("1e-6");z=arb(C)*((l-h.log())/2).exp()
    assert z*z<(c-r).exp() and z*z<(c+r).exp()
    k=2
    while fmpz(k).gcd(Q)>1:k+=1
    threshold=(c+r).exp()/k
    b,u,full=region(L,C,MEAN if mean else (),True,threshold=threshold,sieve_mod=Q)
    return k,b,u,full

if __name__=="__main__":
    ctx.prec=160
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--L",default="116")
    ap.add_argument("--C",type=int,default=1732099);ap.add_argument("--Q",type=int,nargs="+",default=[2,6,30,210])
    ap.add_argument("--mean",action="store_true");ap.add_argument("--upper")
    a=ap.parse_args()
    for Q in a.Q:
        k,n,v,f=run(a.L,a.C,Q,a.mean)
        print("Q",Q,"first k",k,"cells",n,"signed inverse moment",v.str(15),"all near charge",f.str(15))
        if a.upper:assert f<arb(a.upper)
