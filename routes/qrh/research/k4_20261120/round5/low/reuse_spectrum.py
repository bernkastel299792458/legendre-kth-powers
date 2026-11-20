"""Fast physical-side reevaluation using an already certified monotone high-zero cap."""
import argparse
from fractions import Fraction
from flint import arb,ctx
from physical_tail import refine
from check_edge import budget


# Each row uses the entire arithmetic-independent high-zero charge returned by
# narrow_cover.py for that verified rectangle, rounded towards +infinity.
ROWS={
    "64": ("115.035950","115.036100",4100000000,"0.001598181923"),
    "44": ("115.035950","115.036030",4050000000,"0.001576673556"),
    "48": ("115.034900","115.035050",4100000000,"0.001628802195"),
    "40": ("115.034900","115.035000",3800000000,"0.001479724675"),
    "32": ("115.034000","115.034900",3200000000,"0.001197347386"),
    "24": ("115.034000","115.034800",3400000000,"0.001298580567"),
}


def transfer(lo,hi,addition,row="32"):
    base_lo,base_hi,shift,cost=ROWS[row]
    H=arb(3000175332800);Q=arb(10000);K=H+shift
    low,high=arb(lo),arb(hi)
    def a(u):
        return (1-arb("1e-12"))*K*(4*(-arb(u)/4).exp()).log1p()/2
    assert low<high
    # Arb equality of identical source expressions need not compare non-strictly;
    # monotonicity in h establishes ordering, and only range checks are needed.
    alpha=a(hi);old=a(base_hi)
    assert arb.pi()/2<alpha and alpha<arb.pi() and arb.pi()/2<old and old<arb.pi()
    arith=refine(lo,hi,shift,addition=addition)[0]-budget(low,high,arb(addition),shift)[1]
    mass=arb.pi()*alpha.sin()/alpha
    g0=(1-alpha.cos())/alpha**2
    top=K+128*Q
    tail=2*K/mass*(2*arb.pi()*g0)/(2*arb.pi().sqrt()*Q)*(1/(16*Q**2)).exp()
    tail*=top**2*(1+arb(4)/128**2)*(-arb(128)**2/4).exp()
    assert tail<arb("1e-1700")
    # When l decreases, each zero weight increases by at most exp(base_lo-l),
    # since every nontrivial zero satisfies 0 < beta < 1.
    factor=(arb(base_lo)-low).max(arb(0)).exp()
    if Fraction(lo)<Fraction(base_lo):
        split=arb(".64")
        D=arb(shift+1280000)
        number=arb(".3")*H.log()+6+((H/(2*arb.pi())).log()/(2*arb.pi())+arb(".15")/H)*D
        number+=D**2/(4*arb.pi()*H)
        eps=1/(16*Q**2)
        cap0=((old*(1-H/K)).max(arb(0)).min(arb.pi()/2).sin()+2*Q*old/(arb.pi().sqrt()*K)).min(arb(1))/old.sin()
        extra=2*eps.exp()*cap0*number*((split-1)*low).exp()
        improved=((1-split)*(arb(base_lo)-low)).exp()*arb(cost)+extra
        charge=(factor*arb(cost)).min(improved)
    else:
        charge=factor*arb(cost)
    if Fraction(hi)<Fraction(base_hi):
        charge*=alpha/old*old.sin()/alpha.sin()
    return arith+charge+tail


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lo",default="115.034000")
    parser.add_argument("--hi",default="115.034900")
    parser.add_argument("--eta",default="1.1328")
    parser.add_argument("--row",choices=ROWS,default="32")
    parser.add_argument("--check",action="store_true")
    q=parser.parse_args()
    ctx.prec=192
    val=transfer(q.lo,q.hi,q.eta,q.row)
    print(q.lo,q.hi,"conditional on sieve addition",q.eta,"total",val.str(18),flush=True)
    if q.check: assert val<1
