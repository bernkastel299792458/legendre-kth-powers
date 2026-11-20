"""Signed complete low phase region in n*x/(Q*q), for the same spline proof."""
from functools import lru_cache
from fractions import Fraction
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants
from empty_lcm import region,MEAN

def run(C,Q,M,kap):
    z,c,r,I,mass,peaks,u=constants(C);xh=(c+2*r).exp();eta=arb(int(fmpz(Q).euler_phi()))/Q
    @lru_cache(None)
    def prefix(v,uniform):
        t=arb(v.numerator)/v.denominator
        ray=z*z*t/xh;integer=ray.floor().unique_fmpz()
        assert integer is not None and int(integer)<ray<int(integer)+1
        return region("116",C,MEAN,True,threshold=xh/t,sieve_mod=Q,uniform=uniform)[1]/eta
    start=Fraction(M);edge=prefix(start,False);total=arb(0)
    for n in range(1,int(kap*Q/M)+1):
        top=kap*Q/n
        if top<=start:continue
        points=[start]
        while points[-1]*Fraction(23,20)<top:points.append(points[-1]*Fraction(23,20))
        points.append(top);integral=arb(0)
        for v,w in zip(points,points[1:]):
            d=w-v
            integral+=arb(d.numerator)/d.denominator*prefix(w,True)
        g=gcd(n,Q);amp=int(fmpz(g).euler_phi())
        total+=2*arb(amp)/Q*(edge+prefix(top,False)+2*arb.pi()*n/Q*integral)
    return u*(2*r).exp()*mass*total

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=1732099)
    ap.add_argument("--Q",type=int,default=210);ap.add_argument("--cut",type=int,default=23)
    ap.add_argument("--phase",default="1");ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=144
    v=run(a.C,a.Q,a.cut,Fraction(a.phase))
    print("all signed low modes with n X/(Qq) <=",a.phase,"charge",v.str(16))
    if a.upper:assert v<arb(a.upper)
