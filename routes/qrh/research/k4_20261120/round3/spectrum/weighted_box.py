"""Test the first finite-rectangle condition with the new boundary moments."""
from flint import arb, ctx
from verify_height import A, boundary_constants, check, coefficient, quintic_bound


def main():
    ctx.prec = 192
    U, delta, W, logh = map(A, ("28.7",".88","8.5","-4.25"))
    left, right, normalization = boundary_constants(U, delta, W, logh, True)
    ratio = left/right
    anchor, end, theta = A("114.992"), arb(123), A("7/8")
    d = (4*(-end/4).exp()).log1p()
    tau = (2/(d*A("3/16").sqrt())).log()
    cutoffs = [arb(30), arb(31), arb(33), arb(37)]
    thresholds = [51326, 183930, 611919, 611919]
    check(U<cutoffs[0] and cutoffs[0]<tau and tau<cutoffs[1], "valid height range")
    jlog = A("15/14").log()
    outer = (11*((logh+W)/2).exp()).log()
    const = 162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+9*outer)/jlog)

    def power(p,r,cut):
        if cut<tau:
            return (p*cut+r*cut.log()).exp()
        decay = 2-p-r/tau
        check(decay>0, "height-tail tangent")
        duration = cut-tau
        mass = (-decay*duration).exp()-2*(-decay*duration).expm1()/decay
        return (p*tau+r*tau.log()).exp()*mass

    def hinge(s,cut):
        p = 3*(1-s)/(2-s)
        k, c = 3*delta*(2*s-1)/(2-s)**2, 3*delta/(2-s)
        check(c+1+c/U < (U*ratio).log(), "uniform correction")
        lo, hi = (2+4*delta/U)/(2-s+3*delta/U), 2/(2-s)
        cd = coefficient(lo,hi)
        quintic = quintic_bound(lo,hi)
        if quintic is not None:
            cd = cd.min(quintic)
        B = cd*normalization**hi*right*ratio**p*(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
        return B*power(p,1+p,cut)+const+27*power(arb(0),arb(1),cut)/jlog

    knots = [arb(i)/1000 for i in range(800,862)]+[theta]
    sums = []
    for cut in cutoffs:
        total = ((knots[0]-theta)*anchor).exp()*hinge(A(".78"),cut)/(knots[0]-A(".78"))
        last = arb(0)
        for s,t in zip(knots,knots[1:]):
            slope = ((s-theta)*anchor).exp()*((t-s)*anchor).expm1()/(t-s)
            check(slope>last, "positive hinge coefficient")
            total += (slope-last)*hinge(s,cut)
            last = slope
        sums.append(total)
    inv = [arb(1)/n for n in thresholds]+[arb(0)]
    bound = sum(v*(a-b) for v,a,b in zip(sums,inv,inv[1:]))
    print("nested weighted bounds", *(v.str(12) for v in sums))
    print("upper bound for the four-band criterion (target 1)", bound.str(16))


if __name__ == "__main__":
    main()
