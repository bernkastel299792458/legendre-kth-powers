"""Fourth powers with a frequency-localized mean value estimate and height budgets."""
import argparse
from pathlib import Path
import sys

from flint import arb, ctx

research = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(research / "round2" / "spectrum"))
sys.path.insert(0, str(research / "round3" / "critical"))
from verify_spectrum import A, check, coefficient, envelope
from pole_norm import sharp_right
from rs_fourth import fourth_constant
from quintic import bound as quintic_bound


def boundary_constants(U, delta, W, logh, refined):
    T = U.exp()
    width, padding = A(".001"), arb(10**9)
    mass = 1 - 4/(arb.pi()*width*padding)
    check(mass > 0, "positive mass in the time window")
    hilbert = arb.pi()*width.exp()/mass
    m, v = 2048, A("1.01")
    ybar = v*m/(m-1)
    diagonal = (ybar+padding/T)/mass
    old_hilbert = arb.pi()*(1+A("2/3")*A("6/5").sqrt()).sqrt()
    scale = hilbert/old_hilbert
    # In sharp_right, kappa occurs only in the scalar weight of T*S(2+e).
    kappa = arb.pi()*scale**2/(8*diagonal**2)
    right = scale*sharp_right(U, delta, kappa, W, logh)

    divisors = {1: 1}
    for prime in (2, 3, 5, 7, 11):
        divisors.update({prime*d: -sign for d, sign in divisors.copy().items()})
    density = sum(arb(sign)/d**2 for d, sign in divisors.items())
    offset = sum((max(sign, 0)-2*sign*arb(d).log())/d**2 for d, sign in divisors.items())
    harmonic_offset = density*(W/3+logh)+offset
    check(harmonic_offset>0 and T*logh.exp()>2310**2, "squarefree harmonic range")
    harmonic = density+harmonic_offset/U
    taper = 2*(W+logh).exp()*(1-(1+W)*(-W).exp())/W**2
    cm = diagonal*harmonic + hilbert*(density*taper+16/T)/U
    fourth = fourth_constant(U, phased=refined, averaged=refined, shifted=refined)
    c4 = fourth*v**(1+4/U)*m/(m-1-4/U)
    left = (c4**A("1/4")*cm.sqrt()+ybar**A("3/4")/U**A("3/2"))**A("4/3")
    eps = A(".000001")
    check(T>10**10 and ((1+2/T)/v)**m<eps and 4*m/T<1
          and 1/(1-(A(".5")+2/T)**m)<1+eps, "analytic flat window")
    normalization = (1+eps)**2/(1-1/arb(3*10**12))
    return left, right, normalization


def height_groups(d, a, floor, step, tail):
    jumps, residual = envelope(d, a, step, tail)
    cuts = [2, 4, 8, 16, 64]
    groups = [[] for _ in range(len(cuts)+1)]
    for y, weight in jumps:
        y = y.max(floor)
        index = next((i for i, cut in enumerate(cuts) if y<=cut), len(cuts))
        groups[index].append(((y/4).log(), weight))
    u = (4/d).log()
    end = (arb(tail)/4).log()
    def moments(p, r):
        power = p+r/u
        check(power<2, "integrable continuous tail")
        multiplier = (p*u+r*u.log()).exp()
        parts = [sum((weight*(power*z).exp() for z,weight in group), arb(0))
                 for group in groups]
        parts[-1] += residual*(power*end).exp()*2/(2-power)
        return [multiplier*part for part in parts]
    return moments


def verify(anchor, u0=None, shift=".9", transition="10.7", cutoff="-4.85",
           refined=False, diagnose=False):
    L = A(anchor)
    U = A(u0) if u0 is not None else L/4-A("1.02")
    delta, W, logh = map(A, (shift, transition, cutoff))
    a, floor, tail = A("1/4"), A("1.45"), 192
    epsilon = 4*(-L/4).exp()
    d = epsilon.log1p()
    umin = (floor/d).log()
    check(umin>U and umin>arb(3*10**12).log(), "minimum moment height")
    k1, k3, normalization = boundary_constants(U, delta, W, logh, refined)
    print("K1, K3", k1.str(14), k3.str(14), flush=True)
    ratio = k1/k3
    moments = height_groups(d, a, floor, 256, tail)
    knots = [arb(i)/1000 for i in range(650,869)] + [A("7/8")]
    base = 2*((knots[0]-1)*L).exp()*sum(moments(arb(1),arb(1)))
    check(knots[0]-1+A("1/4")+1/(4*umin)<0, "base decreases")
    jlog = A("15/14").log()
    outer = (11*((logh+W)/2).exp()).log()
    edge = 162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+9*outer)/jlog)
    edge += 27*sum(moments(arb(0),arb(1)))/jlog
    by_height = [arb(0) for _ in range(6)]
    high_nodes = [arb(0) for _ in range(6)]
    scaled_terms = []
    last = arb(0)
    for s,t in zip(knots,knots[1:]):
        p = 3*(1-s)/(2-s)
        lo, hi = (2+4*delta/U)/(2-s+3*delta/U), 2/(2-s)
        check(A("1.4")<=lo and hi<=A("16/9"), "detector domain")
        k, c = 3*delta*(2*s-1)/(2-s)**2, 3*delta/(2-s)
        check(c+1+c/U<U.log()+ratio.log(), "height correction decreases")
        correction = (k*(U+(U*ratio).log())/(U+c)).exp()
        detector = coefficient(lo,hi)
        if refined:
            quintic = quintic_bound(lo, hi)
            if quintic is not None:
                detector = detector.min(quintic)
        B = detector*normalization**hi*k3*ratio**p*correction/(2*arb.pi())
        slope = ((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        jump = slope-last
        check(jump>0 and t-1+2/L+p/4+(1+p)/(4*umin)<0
              and t-1+2/L+1/(4*umin)<0, "positive jumps and half-line decay")
        last = slope
        parts = moments(p,1+p)
        if diagnose:
            exponent = 1-p-k/(U+c)
            check(exponent>0, "right moment sensitivity")
            scaled_terms.append((2*jump*B*sum(parts), exponent))
        for i, part in enumerate(parts):
            val = 2*jump*B*part
            by_height[i] += val
            if s>A(".8505"):
                high_nodes[i] += val
    powers = (1+epsilon)**A("1.5")*(L+d)**2*(-L/4).exp()/(8*(1-a)*arb(2).log())
    trivial = (-3*L).exp()/(1-(-2*L).exp())
    check(2/L<A(".25"), "prime powers decrease")
    fixed = base+2*last*edge+powers+trivial
    print("scaled height y <= 2, 4, 8, 16, 64, infinity")
    print("all nodes", *(part.str(12) for part in by_height))
    print("nodes above .85", *(part.str(12) for part in high_nodes))
    result = fixed+sum(by_height)
    print("L", L.str(10), "fixed", fixed.str(14), "total", result.str(20), flush=True)
    if diagnose and result>1:
        # This is a target for a future uniform K3 estimate. Scale only that
        # constant, with the same mollifier, K1 and cumulative height bounds.
        lo, hi = arb(0), arb(1)
        check(fixed<1, "fixed costs below one")
        for _ in range(36):
            middle = (lo+hi)/2
            cost = fixed+sum(part*middle**power for part,power in scaled_terms)
            if cost<1:
                lo = middle
            elif cost>1:
                hi = middle
            else:
                break
        print("sufficient K3 multiplier", lo.str(15), "K3 target", (lo*k3).str(15))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anchor", default="220")
    parser.add_argument("--u0")
    parser.add_argument("--shift", default=".9")
    parser.add_argument("--transition", default="10.7")
    parser.add_argument("--cutoff", default="-4.85")
    parser.add_argument("--refined", action="store_true",
                        help="use the phased fourth moment and the additional quintic detector")
    parser.add_argument("--diagnose", action="store_true",
                        help="report the current budget and solve for a sufficient right moment")
    args = parser.parse_args()
    ctx.prec = 192
    result = verify(**vars(args))
    if not args.diagnose:
        check(result < 1, "prime interval at anchor")
