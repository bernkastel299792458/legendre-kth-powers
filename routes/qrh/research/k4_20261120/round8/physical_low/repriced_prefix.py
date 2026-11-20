"""Reprice all actual large moduli, and the entire low phase, at L=116."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants
from whole_spike import upper,shared_lower,Q
from annular_inverse import cost
from unit_budget import budget
from compact_spline import run as spline

def run(cut):
    assert cut in (23,29,31,37,41,43,47)
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp()
    assert z*z<xl and 19<z*z*23/X<23 and all(gcd(k,Q)!=1 or xl/k>X/cut for k in range(2,cut))
    actual=arb(0)
    for k in range(11,cut):
        if gcd(k,Q)>1:continue
        s,e=upper(k,37);actual+=s+e
        actual-=sum((shared_lower(k,g,23) for g in (11,13,17,19,23) if g<k),arb(0))
    # No false physical sign at k<=19. For all remaining k<50 use one common defect.
    if cut>23:actual+=2*arb(".00000009043441")
    inverse=cost(1,cut,mean_only=True)[1]
    pts=[cut]+[i for i in (29,36,46,59,75,94,119,150,185,210) if i>cut]
    low=sum((cost(a,b,low_only=True)[1] for a,b in zip(pts,pts[1:])),arb(0))
    _,main,other,_,_=budget(Q,1732099)
    _,_,ordinary,high,tiny=spline(1732099,Q,cut,".0002",4*10**18,64,"70.7")
    rem=1-main-other-ordinary-high-tiny-actual-inverse-low
    return actual,inverse,low,rem

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--cut",type=int,default=23);ap.add_argument("--lower")
    a=ap.parse_args();ctx.prec=144;v=run(a.cut);print("cut, all true multiples, signed bulk inverse, low modes, open allowance",a.cut,*(t.str(15) for t in v))
    if a.lower:assert v[-1]>arb(a.lower)
