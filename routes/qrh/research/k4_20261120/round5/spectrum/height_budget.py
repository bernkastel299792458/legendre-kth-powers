"""Full half-line certificate using a separate minimum height in each spectral band."""
import argparse
from flint import arb, ctx

from verify import A, check, moments
from verify_euler import coefficient, quintic_bound, height_groups


def select_knots(rows):
    """A finite subsequence of real-part knots for one group of spectral jumps."""
    keep=[]
    for item in rows:
        while len(keep)>=2:
            a,b=keep[-2],keep[-1]
            if not (b[1]-a[1])*(item[0]-b[0]) > (item[1]-b[1])*(b[0]-a[0]):
                break
            keep.pop()
        keep.append(item)
    return keep


def verify_height(anchor, shift, transition, cutoff, q=210, frequency_cut="100",
                  width="1/4", last_node=868, polygon=False, short_core=0, short_steps=1,
                  mix_width=None, mix_weight=".3", convex=False,tight=False, sensitivity=False,
                  unit_fourth=False):
    L, delta, W, logh, a = map(A,(anchor,shift,transition,cutoff,width))
    check(0<a and a<=A("1/2"),"trapezoid widths")
    floor = A("1.45")
    epsilon = 4*(-L/4).exp()
    d = epsilon.log1p()
    splits = [floor,arb(2),arb(4),arb(8),arb(16),arb(64)]
    if polygon:
        from pathlib import Path
        import sys
        sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"kernel"))
        from polygon import height_groups as polygon_groups
        groups = polygon_groups(d,a,floor,256,192)
    else:
        groups = height_groups(d,a,floor,256,192)
    umin = (floor/d).log()
    thresholds = [(y/d).log()-A(".000001") for y in splits]
    mix=None if mix_width is None else (A(mix_width),A(mix_weight))
    short = None
    if unit_fourth and not short_core:
        raise ValueError("the unit fourth-moment option uses the short-core splitting")
    if short_core:
        from short_block import split_endpoint, cm_local
        fourth_fn=None
        if unit_fourth:
            from unit_diagonal import fourth as fourth_fn
        cm_source=cm_local
        if mix is not None:
            from critical_mean import critical_mean
            def cm_source(U,W,logh,q):
                near=A("1.01")*2048/2047*(1-A("1.03")**(-2047))
                return critical_mean(U,W,logh,q=q,mix=mix),near
        def short(U,W,logh,q):
            return split_endpoint(U,W,logh,q,short_core,cm_source,steps=short_steps,
                                  fourth_fn=fourth_fn)[0]
    cm = [moments(U,delta,W,logh,q,frequency_cut,short=short,mix=mix,tight=tight) for U in thresholds]
    knots = ([arb(i)/2000 for i in range(1300,1750)] if convex else
             [arb(i)/1000 for i in range(650,last_node+1)])+[A("7/8")]
    norm = (1+A(".000001"))**2/(1-1/arb(3*10**12))
    check(umin>arb(3*10**12).log() and thresholds[0].exp()>10**10,"all moment heights")
    T0 = thresholds[0].exp()
    check(((1+2/T0)/A("1.01"))**2048<A(".000001") and 4*2048/T0<1 and
          1/(1-(A(".5")+2/T0)**2048)<1+A(".000001"),"flat analytic window")
    base = 2*((knots[0]-1)*L).exp()*sum(groups(arb(1),arb(1)))
    check(knots[0]-1+A("1/4")+1/(4*umin)<0,"base decreases")
    jlog = A("15/14").log()
    max_width=W if mix is None else mix[0]
    check(q*(logh+max_width).exp()>=1 and 9/((thresholds[0]+logh)/2).exp()<A("1/4"),
          "Jensen disk and right edge")
    outer = (11*arb(q).sqrt()*((logh+max_width)/2).exp()).log()
    ec = 162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+9*outer)/jlog)
    edges=[ec*w+27*z/jlog for w,z in zip(groups(arb(0),arb(0)),groups(arb(0),arb(1)),strict=True)]
    bounds=[[] for _ in thresholds]
    for s in knots[:-1]:
        p = 3*(1-s)/(2-s)
        k,c = 3*delta*(2*s-1)/(2-s)**2,3*delta/(2-s)
        hi = 2/(2-s)
        for j,(U,(left,right),weight) in enumerate(zip(thresholds,cm,groups(p,1+p),strict=True)):
            ratio = left/right
            lo = (2+4*delta/U)/(2-s+3*delta/U)
            check(A("1.4")<=lo and hi<=A("16/9"),"detector domain")
            cd = coefficient(lo,hi)
            quin = quintic_bound(lo,hi)
            if quin is not None:
                cd = cd.min(quin)
            check(c+1+c/U<(U*ratio).log(),"height correction decreases")
            B = cd*norm**hi*right*ratio**p*(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
            exponent=1-p-k/(U+c)
            check(exponent>0,"right moment sensitivity")
            bounds[j].append((s,B*weight+edges[j],exponent))
    cost=rectangles=arb(0)
    scaled=[]
    for j,rows in enumerate(bounds):
        rows.append((knots[-1],arb(0),arb(0)))
        selected=select_knots(rows) if convex else rows
        last=arb(0)
        for (s,hinge,exponent),(t,_,_) in zip(selected,selected[1:]):
            p=3*(1-s)/(2-s)
            slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
            check(slope>last and t-1+2/L+p/4+(1+p)/(4*umin)<0
                  and t-1+2/L+1/(4*umin)<0, "positive jumps and half-line decay")
            term=2*(slope-last)*(hinge-edges[j])
            cost+=term
            if sensitivity:
                scaled.append((term,exponent))
            last=slope
        rectangles+=2*last*edges[j]
    check(2/L<A("1/4"),"prime powers decrease")
    peak = 1/(1-a)
    powers = peak*(1+epsilon)**A("1.5")*(L+d)**2*(-L/4).exp()/(8*arb(2).log())
    trivial = (-3*L).exp()/(1-(-2*L).exp())
    fixed = base+rectangles+powers+trivial
    print("L",anchor,"grouped total",(fixed+cost).str(20),"fixed",fixed.str(12),flush=True)
    if sensitivity and fixed<1 and fixed+cost>1:
        lo,hi=arb(0),arb(1)
        for _ in range(30):
            mid=(lo+hi)/2
            if fixed+sum(term*mid**p for term,p in scaled)<1:
                lo=mid
            else:
                hi=mid
        print("sufficient common right-moment multiplier",lo.str(13),flush=True)
    return fixed+cost


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",default="170")
    cli.add_argument("--shift",default=".92")
    cli.add_argument("--transition",default="9.5")
    cli.add_argument("--cutoff",default="-3.5")
    cli.add_argument("--q",type=int,choices=(210,2310),default=210)
    cli.add_argument("--frequency-cut",default="100")
    cli.add_argument("--width",default="1/4")
    cli.add_argument("--last-node",type=int,choices=range(850,875),default=868)
    cli.add_argument("--short-core",type=int,default=0)
    cli.add_argument("--short-steps",type=int,default=1)
    cli.add_argument("--unit-fourth",action="store_true")
    cli.add_argument("--mix-width")
    cli.add_argument("--mix-weight",default=".3")
    cli.add_argument("--polygon",action="store_true")
    cli.add_argument("--convex",action="store_true")
    cli.add_argument("--tight",action="store_true")
    cli.add_argument("--sensitivity",action="store_true")
    cli.add_argument("--diagnose",action="store_true")
    args=vars(cli.parse_args())
    diagnose=args.pop("diagnose")
    ctx.prec=192
    result=verify_height(**args)
    if not diagnose:
        check(result<1,"full half-line")
        L=A(args["anchor"])
        first=(L/4).exp().ceil().unique_fmpz()
        check(first is not None and 4*arb(first-1).log()<L and L<4*arb(first).log(),
              "first integer on the certified half-line")
        print("first integer",first)
