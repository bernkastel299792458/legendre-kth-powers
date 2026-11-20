"""Sufficient finite-height zero counts, with Huxley and Ingham exponents."""
from pathlib import Path
import sys
from flint import arb, ctx

from verify import A, check, moments
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"kernel"))
from polygon import envelope, height_groups
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"low"))
from short_box import boundary_data, detector


def analytic_tail(end, ustar, eps, amplitude):
    """Bound the contribution of actual zeros above exp(ustar)."""
    delta,W,logh=map(A,(".92","9.5","-3.5"))
    left,right=moments(ustar,delta,W,logh,210,"100")
    _,_,_,_,norm,_,es=boundary_data()
    jlog=A("15/14").log()
    ec=162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+
       9*(11*arb(210).sqrt()*((W+logh)/2).exp()).log())/jlog)
    check(ustar>29 and 9/((ustar+logh)/2).exp()<A("1/4"),"tail rectangular domain")
    def integral(p,r):
        den=2-p-r/ustar
        check(den>0,"integrable remote curve")
        return ((p-2)*ustar).exp()*ustar**r/den
    total=(-A(".35")*end).exp()*integral(1,1)
    ratio=left/right
    from verify_euler import coefficient,quintic_bound
    nodes=[arb(i)/1000 for i in range(650,869)]+[A("7/8")]
    last=arb(0)
    for s,t in zip(nodes,nodes[1:]):
        p=3*(1-s)/(2-s)
        c,k=3*delta/(2-s),3*delta*(2*s-1)/(2-s)**2
        check(c+1+c/ustar<(ustar*ratio).log(),"tail height correction")
        lo,hi=(2+4*delta/ustar)/(2-s+3*delta/ustar),2/(2-s)
        check(A("1.4")<=lo and hi<=A("16/9"),"tail detector domain")
        cd=coefficient(lo,hi)
        other=quintic_bound(lo,hi)
        if other is not None:
            cd=cd.min(other)
        B=cd*norm**hi*right*ratio**p*(k*(ustar+(ustar*ratio).log())/(ustar+c)).exp()/(2*arb.pi())
        slope=((s-1)*end).exp()*((t-s)*end).expm1()/(t-s)
        check(slope>last,"positive tail jump")
        total+=(slope-last)*B*integral(p,1+p)
        last=slope
    total+=last*(ec*integral(0,0)+es*integral(0,1))
    return amplitude*(1+eps)**2*(end/2).exp()*total/4


def targets(anchor="115.033663", last="168.5", upper_log="45", first=800):
    L, end, ustar = map(A,(anchor,last,upper_log))
    H = arb(3000175332800)
    theta = A("7/8")
    eps = 4*(-L/4).exp()
    d = eps.log1p()
    floor = (H*d).max(A("1.45"))
    umin = (floor/d).log()
    check(floor<64 and end>L and ustar>H.log(),"height floor and finite box")
    spectral = height_groups(d,A("1/4"),floor,256,192)
    _, residual = envelope(d,256,192)
    amplitude = 192**2*residual
    # For L in the specified finite band, e^{(theta-1)L}/d(L)^2 <= the next upper bound.
    trivial_far = amplitude*(1+eps)**2*((theta-A("1/2"))*end-ustar).exp()*(ustar+1)/4
    far = trivial_far.min(analytic_tail(end,ustar,eps,amplitude))
    base = 2*(-A(".35")*L).exp()*sum(spectral(arb(1),arb(1)))
    check(-A(".35")+A("1/4")+1/(4*umin)<0 and 2/L<A("1/4"),"base and power decay")
    powers = (1+eps)**A("1.5")*(L+d)**2*(-L/4).exp()/(6*arb(2).log())
    trivial = (-3*L).exp()/(1-(-2*L).exp())
    fixed = base+powers+trivial+far
    if first>650:
        # For beta <= first/1000 use the previously proved hinge bounds.
        U,delta,left,right,norm,ec,es=boundary_data()
        check(umin>U,"low-real-part hinge height")
        ratio=left/right
        last_slope=arb(0)
        for i in range(650,first):
            s,t=arb(i)/1000,arb(i+1)/1000
            p=3*(1-s)/(2-s)
            c,k=3*delta/(2-s),3*delta*(2*s-1)/(2-s)**2
            check(c+1+c/U<(U*ratio).log() and t-1+2/L+p/4+(1+p)/(4*umin)<0,
                  "hinge correction and decay")
            pref=detector(i)*norm**(2/(2-s))*right*ratio**p
            pref*=(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
            slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
            check(slope>last_slope and t-1+2/L+1/(4*umin)<0,"edge decay")
            fixed+=2*(slope-last_slope)*pref*sum(spectral(p,1+p))
            last_slope=slope
        fixed+=2*last_slope*(ec+es*sum(spectral(arb(0),arb(1))))
    print("first",first,"finite box log height",upper_log,"fixed",fixed.str(12),"remote tail",far.str(12),flush=True)
    costs = [arb(0) for _ in range(3)]
    for j in range(first,875):
        s,t = arb(j)/1000,arb(j+1)/1000
        p = (3*(1-s)/(2-s)).min(3*(1-s)/(3*s-1))
        jump = 2*((s-1)*L).exp()*((t-s)*L).expm1()
        if j==first and first>650:
            jump += 2*((s-1)*L).exp()
        for r in range(3):
            check(t-1+1/L+p/4+arb(r)/(4*umin)<0,"finite-band decay for count term")
            costs[r] += jump*sum(spectral(p,arb(r)))
    for r,cost in enumerate(costs):
        check(cost>0,"positive count coefficient")
        print("log power",r,"maximum budget coefficient",((1-fixed)/cost).str(15),flush=True)
    if first==800 and end==A("168.5") and ustar==45:
        check(fixed+7*costs[1]<1,"explicit sufficient finite-density target")
        count=int((4*(ustar-H.log())).ceil().unique_fmpz())
        grid_loss=(1+1/(4*H.log()))*(arb(3)/28).exp()
        check(count==66 and 6*grid_loss<7,"finite grid of 4950 cumulative counts")
    return [(1-fixed)/c for c in costs]


if __name__=="__main__":
    ctx.prec=192
    import argparse
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--first",type=int,choices=range(650,875),default=800)
    cli.add_argument("--upper-log",default="45")
    cli.add_argument("--last",default="168.5")
    args=cli.parse_args()
    targets(first=args.first,upper_log=args.upper_log,last=args.last)
