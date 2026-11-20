"""Explicit Mellin envelope for a log trapezoid, combined with the BV moments."""
import argparse
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb, ctx

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"right"))
from verify_bv import A, check, endpoints
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"detector"))
from adaptive import coefficient


@lru_cache(maxsize=16)
def flat_constants(u0, shift, transition, cutoff, window, precision):
    from flat_window import moments
    check(ctx.prec==precision,"cached constants use the current precision")
    return moments(A(u0),A(shift),A(transition),A(cutoff),window!="flat",
                   window in ("flat-signed","flat-both"),window=="flat-both")


def envelope(d, a, step, R):
    b = 1-a
    unit = 10**9
    tail = int((4*unit/(a*b*R**2)).upper().ceil().unique_fmpz())
    check(0 < tail < unit, "tail domain")
    last = tail
    jumps = []
    for i in range(R*step-1,step//2-1,-1):
        lo, hi = arb(i)/step, arb(i+1)/step
        mid = (lo+hi)/2
        cap = arb(1)
        for width in (a,b):
            sine = abs((width*mid/2).sin())+width*(hi-lo)/4
            oscillatory = 2*sine/(width*lo)+d*width/2
            cap *= arb(1).min(2/(width*lo)).min(oscillatory)
        level = min(unit,int((cap*unit).upper().ceil().unique_fmpz()))
        if level > last:
            jumps.append((hi,arb(level-last)/unit))
            last = level
    if last < unit:
        jumps.append((arb(step//2)/step,arb(unit-last)/unit))
    check(sum(w for _,w in jumps)+arb(tail)/unit == 1 or
          (sum(w for _,w in jumps)+arb(tail)/unit-1).contains(0), "mass identity")
    return jumps, arb(tail)/unit


def height_integrator(L, d, a, step, R, U, ymin, through=None):
    jumps, tail = envelope(d,a,step,R)
    if through is not None:
        H=arb(3*10**12)
        check(through>=L and U<H.log(),"finite RH cell")
        drop=H*(4*(-through/4).exp()).log1p()
        check(drop<R and H*d<R,"unchanged continuous tail")
        jumps=[(y,w) for y,w in jumps if not y<=drop]
        ymin=ymin.max(d*(H+1))
    check(0<=ymin and ymin<R,"height floor below the continuous tail")
    jumps=[(y.max(ymin),weight) for y,weight in jumps]
    umin = (min(y for y,w in jumps)/d).log()
    check(umin>U and (arb(R)/d).log()>U and umin>arb(3*10**12).log(),
          "all heights above moment threshold and verified RH height")
    pivot = arb(4)
    u = (pivot/d).log()
    logs = [((y/pivot).log(),weight) for y,weight in jumps]
    last = (arb(R)/pivot).log()
    def moment(p,r):
        v = p+r/u
        check(v<2, "tail exponent")
        # Tangent to log(u+z), valid for z of either sign.
        total = sum(w*(v*z).exp() for z,w in logs)
        total += tail*(v*last).exp()*2/(2-v)
        return (p*u+r*u.log()).exp()*total
    return moment, umin, len(jumps)


def verify(anchor, width, step=16, R=96, window="gaussian", u0="64",
           transition="9.25", cutoff="-2.45", shift=".65", min_y="0", theta="7/8",
           through=None,last_gap=".0049"):
    L, a, U = A(anchor), A(width), A(u0)
    check(0<a and a<=A(".5") and step>=2 and step%2==0,"mesh parameters")
    b=1-a
    delta, kap, W, logh = A(shift), A(".105"), A(transition), A(cutoff)
    if window=="gaussian":
        k1,k2,k3,l0,*_ = endpoints(U,delta,kap,W,logh)
    else:
        k1,k2,k3,l0 = flat_constants(u0,shift,transition,cutoff,window,ctx.prec)
    print("boundary constants",k1.str(12),k2.str(12),k3.str(12),l0.str(12))
    upper=A(theta)
    check(A(".66")<=upper and upper<=A("7/8"),"zero real-part assumption")
    gap=A(last_gap)
    check(0<gap and gap<upper-A(".65"),"terminal chord length")
    knots=[arb(i)/1000 for i in range(650,875) if arb(i)/1000<=upper-gap]
    knots.append(upper)
    eps = 4*(-L/4).exp()
    d = eps.log1p()
    moment,umin,count = height_integrator(L,d,a,step,R,U,A(min_y),A(through) if through else None)
    ratio = (k1+k2/U**2)/k3
    base = 2*((knots[0]-1)*L).exp()*moment(arb(1),arb(1))
    if through:
        H=arb(3*10**12)
        base+=2*H*H.log()*(-L/2).exp()
    check(knots[0]-1+A(".25")+1/(4*umin)<0,"base decay")
    jlog=A("15/14").log()
    outer=(11*((logh+W)/2).exp()).log()
    edge=162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+9*outer)/jlog)
    edge+=27/jlog*moment(arb(0),arb(1))
    previous=zm=ze=arb(0)
    for s,t in zip(knots,knots[1:]):
        p=3*(1-s)/(2-s)
        lo=(2+4*delta/U)/(2-s+3*delta/U)
        hi=2/(2-s)
        check(A("1.4")<=lo and hi<=A("16/9"),"detector domain")
        cd=coefficient(lo,hi)
        k=3*delta*(2*s-1)/(2-s)**2
        if window=="gaussian":
            corr=(ratio**(k/U)).max(arb(1))*(k*(1+U.log()/U)).exp()
        else:
            c=3*delta/(2-s)
            check(c+1+c/U<U.log()+ratio.log(),"height correction decreases")
            corr=(k*(U+(U*ratio).log())/(U+c)).exp()
        B=cd*l0**hi*k3*ratio**p*corr/(2*arb.pi())
        slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        jump=slope-previous
        check(jump>0,"positive chord")
        previous=slope
        zm+=2*jump*B*moment(p,1+p)
        ze+=2*jump*edge
        check(t-1+2/L+p/4+(1+p)/(4*umin)<0,"moment decay")
        check(t-1+2/L+1/(4*umin)<0,"edge decay")
    powers=(1+eps)**A("1.5")*(L+d)**2*(-L/4).exp()/(8*b*arb(2).log())
    trivial=(-3*L).exp()/(1-(-2*L).exp())
    check(2/L<A(".25"),"prime powers decay")
    print("atom count",count,"minimum log height",umin.str(12))
    for name,val in (("base",base),("moment",zm),("edges",ze),("powers",powers),("trivial",trivial)):
        print(name,val.str(16))
    return base+zm+ze+powers+trivial


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anchor",default="229")
    parser.add_argument("--width",default="1/5")
    parser.add_argument("--step",type=int,default=128)
    parser.add_argument("--tail",type=int,default=96)
    parser.add_argument("--window",choices=["gaussian","flat","flat-fine","flat-signed","flat-both"],default="flat-both")
    parser.add_argument("--u0",default="55.5")
    parser.add_argument("--transition",default="10.75")
    parser.add_argument("--cutoff",default="-5")
    parser.add_argument("--shift",default=".8")
    parser.add_argument("--min-y",default="1")
    parser.add_argument("--theta",default="7/8",help="assumed upper bound on zero real parts")
    parser.add_argument("--through",help="upper endpoint for the optional finite-height RH cell")
    parser.add_argument("--last-gap",default=".0049",help="lower limit on length of last chord")
    args=parser.parse_args()
    ctx.prec=192
    value=verify(args.anchor,args.width,args.step,args.tail,args.window,args.u0,
                 args.transition,args.cutoff,args.shift,args.min_y,args.theta,args.through,args.last_gap)
    print("total",value.str(18))
    check(value<1,"point budget")
