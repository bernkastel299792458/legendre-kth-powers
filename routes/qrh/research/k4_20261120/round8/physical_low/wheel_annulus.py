"""All real multiples and all middle phases in one full large-wheel modulus band."""
import argparse
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants
from annular_inverse import cost
from compact_spline import run as spline
from wheel_prefix import physical

def annulus(Q,cut,start,end,limit,logy="70.7",width=".0002",anchored=False,conditional=False,physical_spectrum=False):
    assert 23<=cut<=start<end<=limit and Q%210==0 and fmpz(Q).moebius_mu()
    z,c,r,*_=constants(1732099)
    xl=(c-2*r).exp();X=(c+2*r).exp()
    assert z*z<xl and xl*start>X*(start-1) and xl*end>X*(end-1)
    assert 1<arb(logy).exp()<X/limit and 0<arb(width)<1
    ks=[k for k in range(start,end) if gcd(k,Q)==1]
    assert not conditional or anchored
    if physical_spectrum:
        from physical_l2 import physical as signed
        whole=sum((signed(k,Q,width=width)[-1] for k in ks),arb(0))
    else:
        whole=sum((physical(k,Q,ctx.prec,width,anchored,conditional)[0] for k in ks),arb(0))
    joint=cost(start,end,mod=Q,harmonic_limit=limit,width=width)[1]
    high=spline(1732099,Q,cut,width,4*10**18*(Q//210),64)[3]
    return ks,whole,joint,high,whole+joint+high

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ("Q","cut","start","end"):p.add_argument("--"+arg,required=True,type=int)
    p.add_argument("--limit",type=int);p.add_argument("--upper");p.add_argument("--anchored",action="store_true")
    p.add_argument("--conditional",action="store_true")
    p.add_argument("--physical-spectrum",action="store_true")
    a=p.parse_args();ctx.prec=144
    ks,*v=annulus(a.Q,a.cut,a.start,a.end,a.limit or a.Q,anchored=a.anchored,conditional=a.conditional,physical_spectrum=a.physical_spectrum)
    print("Q,actual integers",a.Q,ks,"actual,joint,high,complete",*(x.str(14) for x in v))
    if a.upper:assert v[-1]<arb(a.upper)
