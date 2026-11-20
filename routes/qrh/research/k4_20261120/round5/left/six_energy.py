"""Fourth moment of zeta*(1-2^-s)*(1-3^-s) by separating the gcd parameters."""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd
from pathlib import Path
import sys
from flint import arb, arb_poly, ctx

research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round4"/"density"))
from sieved_fourth import _constant

R={h:[i for i in range(1,7) if gcd(i,6)==h] for h in (1,2,3,6)}

def frac(x):
    return arb(x.numerator)/x.denominator


@lru_cache(maxsize=4)
def tails(precision):
    assert precision==ctx.prec
    at=48
    widths={1:[],2:[(1,2,-1)],3:[(1,3,-1)],6:[(1,2,-1),(3,6,1)]}
    close={}
    far={}
    far_large={}
    for h in R:
        for restricted in (False,True):
            ranges=[(a,b,sign if restricted else 1,residue)
                    for residue in range(1,7) if not restricted or gcd(residue,6)==1
                    for a,b,sign in widths[gcd(h*residue,6)]]
            center=sum((arb(sign)/6*(arb(b)/a).log() for a,b,sign,_ in ranges),arb(0))
            error=sum((arb(1)/(at*a) for a,b,_,_ in ranges),arb(0))
            beyond=abs(center)+error
            events={}
            for a,b,sign,r in ranges:
                for n in range(r,6*at+1,6):
                    for t,delta in ((Fraction(n,b),Fraction(sign,n)),
                                    (Fraction(n,a),Fraction(-sign,n))):
                        if t<=at:
                            events[t]=events.get(t,Fraction(0))+delta
            current=Fraction(0)
            highest=Fraction(0)
            for t,delta in sorted(events.items()):
                current+=delta
                highest=max(highest,abs(current))
            whole=frac(highest).max(beyond)
            if restricted:
                far[h]=whole
                far_large[h]=beyond
            else:
                close[h]=whole
    # Excess of the close-ratio inner harmonic sum above its average.
    # For s>N its excess is bounded by 6 times the number of residues /s.
    N=384
    exc={}
    for allowed in (False,True):
        rr=R[1] if allowed else range(1,7)
        # In the all-integers case the discrepancy is 1.
        disc=2 if allowed else 1
        rho=arb(1)/3 if allowed else arb(1)
        hs=[Fraction(0)]
        for s in range(1,N+1):
            hs.append(hs[-1]+(Fraction(1,s) if (s-1)%6+1 in rr else 0))
        for h in R:
            val=arb(0)
            for s in range(1,N+1):
                if gcd(s,6)==h:
                    val+=(frac(hs[s]-hs[s//6])-rho*arb(6).log()).max(arb(0))/s
            exc[allowed,h]=val+arb(6*disc)/N
    return close,far,far_large,exc


def fourth(U, *, off_bound=None, bulk_bound=None, ratio_bound=None):
    if not U>=20:
        raise ValueError("minimum height")
    z=arb_poly([0,1])
    pi=arb.pi()
    ell=(z-(2*pi).log())*(arb(1)/2)
    a6=arb(6).log()
    d=arb(1)/3
    extra=ell+a6
    c=(arb.const_euler()+arb(2).log()+arb(3).log()/2)/3
    k=arb(4)/3
    # H_A(x) differs from d log x+c by at most k/x.
    bulk=c**2*(d*ell+c)**2
    bulk+=2*d*(d**2*(c*ell**3*(arb(1)/3)+d*ell**4*(arb(1)/12))
               +2*d*c*(c*ell**2*(arb(1)/2)+d*ell**3*(arb(1)/6))
               +c**2*(c*ell+d*ell**2*(arb(1)/2)))
    # Errors from the inner harmonic approximation and the cumulative pair weight.
    bulk+=2*k*(1+d*ell)*(2*d+2*c+k)
    bulk+=c**2*k*(2*d*ell+2*c+k)
    bulk+=2*d*k*(c+d*ell)*(2*d+2*c+k)
    early_cost=arb(0)
    if bulk_bound is not None:
        bulk,early_cost=bulk_bound(U,ell,bulk)

    close,far,fl,exc=tails(ctx.prec)
    near=arb_poly()
    away=arb_poly()
    for h,rs in R.items():
        offset=sum(arb(1)/a for a in rs)
        rho=arb(len(rs))/6
        hsum=offset+rho*extra
        near+=2*close[h]**2*(a6*hsum+exc[False,h])
        if h!=1:
            far_mass=offset+rho*(6*arb(48)).log()
            away+=2*(1+d*extra)*(fl[h]**2*hsum+far[h]**2*far_mass)
    # Both parameters are units in the mixed bulk-tail term.
    prod_harm=(1+d*ell)+d*(ell+d*ell**2*(arb(1)/2))
    near+=4*close[1]*(d*a6*prod_harm+(1+d*ell)*exc[True,1])
    if ratio_bound is not None:
        near,away,early=ratio_bound(U,ell,near,away)
        early_cost+=early
    diagonal=bulk+near+away

    if off_bound is not None:
        ef=(1+1/arb(2).sqrt())*(1+1/arb(3).sqrt())
        return _constant(U,diagonal,off_bound(U)+early_cost,ef,[])

    # The same frequency-shift calculation as in round4, with the optimal
    # choice of the fixed variable in each of the two index pairs.
    y0=(U/2).exp()/(2*pi).sqrt()
    den={1:d,2:arb(1),3:arb(1)/2,6:arb(1)}
    total=arb(0)
    for i,j,k1,l in product(den,repeat=4):
        a,b=i*j,k1*l
        r=den[i].min(den[j])
        s=den[k1].min(den[l])
        total+=(r+1/y0)*(s+1/y0)/gcd(a,b)
        total+=r*s*(2+abs((arb(a)/b).log()))/max(a,b)
        total+=((r/a+s/b)*(1+(36*y0).log())+arb(1)/max(a,b))/y0
    ef=(1+1/arb(2).sqrt())*(1+1/arb(3).sqrt())
    off=(4*total*(1+2*extra)+16*ef**4)*(1/(2*pi))
    return _constant(U,diagonal,off+early_cost,ef,[])

if __name__=="__main__":
    ctx.prec=160
    for u in [30,40,43,49,54]:
        print(u,fourth(arb(u)).str(16))
