"""Arb verification of the integrated CS moment bound for fourth powers."""
from fractions import Fraction
import argparse
from flint import arb, ctx


def A(value):
    x = Fraction(value)
    return arb(x.numerator) / x.denominator


def check(condition, label):
    if not condition:
        raise ArithmeticError(label)


def constants():
    """CS v2 (35)--(38), h=1. K1 uses the tangent from the 2026-11-06 rebase."""
    U, V = arb(64), arb(58)
    T, Z = U.exp(), V.exp()
    H = arb(3 * 10**12)
    pi, eg = arb.pi(), arb.const_euler()
    delta, kap = A("3/10"), A("3/20")
    m0 = (1 + A("2/3") * A("6/5").sqrt()).sqrt()
    check(T > H and Z > 10**10 and T > 3 * 10**10 and delta < U/20, "CS domains")
    c1 = 6/pi**2 + A("1.048")/U
    c2 = pi*m0*A(".62")/U + 6*m0/(pi*T) + pi*m0*A("1.048")/(T*U)
    c3 = pi*m0*A(".54")/(2*delta)*(2*delta*eg/U).exp()
    c4 = A(".54")/(5*delta*delta.exp()) + A(".605")*(-2*delta).exp()/U
    a1 = Z*(V-arb(2).log())**4/(2*pi**2) + A("34.842")*Z*(V-arb(2).log())**3 + A("1.3897e16")
    a2 = (1-arb(2).log()/V)**4/(2*pi**2) + A("34.842")/V*(1-arb(2).log()/V)**3 + A("9.5079e15")/(Z*V**4)
    a = 3/(4*kap)
    v = 2/(3*U)
    c = v*a/(1+a)
    D = (v*((1+a).log()-a/(1+a))).exp()
    integral = D*((c1*a.sqrt())**A("2/3")*A("3/2").gamma()/(1-c)**A("3/2")
                  + c2**A("2/3")*A("7/6").gamma()/(1-c)**A("7/6"))
    k1 = (2*a2*a.sqrt())**A("1/3")*integral
    k1 += (2*a1/T)**A("1/3")*(c2+Z*c1/T)**A("2/3")/U**A("4/3")
    k2 = A(2)**A("1/3")*(a.sqrt()*pi.sqrt()/2 + (Z/T)**3/a)
    k3 = c3 + c4*(pi.sqrt()/(2*(2*kap).sqrt())+pi*m0/T)
    l0 = (kap*(1+((1+2*delta/U)/(4*T))**2)).exp()/(1-1/H)
    check(l0 > 1, "prefactor")
    return U, delta, k1, k2, k3, l0


def detector_constants():
    # The radial supremum of log |(1+z)(1-z/5)^5| is increasing.
    bands = [("1.45", "1.65", ".66"), ("1.65", "1.71", ".58"), ("1.71", "16/9", ".567")]
    result = []
    for low, high, cap in bands:
        p, q, bound = A(low), A(high), A(cap)
        check(A(".6")*(A(1)/16)**(2-q) < bound and 12/A(64)**(p-A(".5")) < bound, "detector tails")
        for i in range(-4*256, 6*256):
            lo = A(2)**(arb(i)/256)
            hi = A(2)**(arb(i+1)/256)
            if hi < A("2.5"):
                radial = 3*(hi**2/5).log1p()
            else:
                radial = (hi-1).log()+5*(hi/5).log1p()
            check(radial/lo**(q if i < 0 else p) < bound, "detector interior")
        result.append((p, q, bound))
    return result


def height_moment(u1, p, r):
    """Upper bound for the full integral of T^p (log T)^r against -dg."""
    a = p + r/u1
    check(a < 2 and not (a-1).contains(0), "height moment")
    log7 = arb(7).log()
    b = ((a-1)*log7).exp()
    factor = ((a-1)*log7).expm1()/(a-1) + 2*b/(2-a)
    return (p*u1+r*u1.log()).exp()*factor


def verify(anchor, last_gap=5):
    check(1 <= last_gap <= 224, "increasing knot sequence")
    L = arb(anchor)
    H = arb(3*10**12)
    U, delta, k1, k2, k3, l0 = constants()
    bands = detector_constants()
    knots = [arb(i)/1000 for i in range(650, 876-last_gap)] + [A("7/8")]
    R1 = A("16/7")
    u1 = (R1*(1+(L/4).exp()/4)).log()
    check(u1 > U and U > H.log(), "every height in domain")
    ratio = (k1+k2/U**2)/k3
    baseline = 2*((knots[0]-1)*L).exp()*height_moment(u1, arb(1), arb(1))
    check(knots[0]-1+A("1/4")+1/(4*u1) < 0, "baseline decay")
    jensen_log = A("15/14").log()
    edge_constant = 162/(2*arb.pi()) + 2*(2+(arb(2).log()+6*arb(11).log())/jensen_log)
    edge_slope = 18/jensen_log
    edge_integral = edge_constant + edge_slope*height_moment(u1, arb(0), arb(1))
    previous, zmain, zedge = arb(0), arb(0), arb(0)
    for s, t in zip(knots, knots[1:]):
        p = 3*(1-s)/(2-s)
        nu_min = (2+4*delta/U)/(2-s+3*delta/U)
        nu_max = 2/(2-s)
        matches = [cap for lo, hi, cap in bands if lo <= nu_min and nu_max <= hi]
        if matches:
            cd = matches[0]
        else:
            check(bands[0][0] <= nu_min and nu_max <= bands[-1][1], "detector exponent range")
            cd = max(cap for lo, hi, cap in bands if not (hi < nu_min or lo > nu_max))
        k = 3*delta*(2*s-1)/(2-s)**2
        coefficient = cd*l0**(2/(2-s))*k3*ratio**p
        coefficient *= (ratio**(k/U)).max(arb(1))*(k*(1+U.log()/U)).exp()/(2*arb.pi())
        slope = ((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        jump = slope-previous
        check(jump > 0, "positive chord coefficient")
        previous = slope
        zmain += 2*jump*coefficient*height_moment(u1, p, 1+p)
        zedge += 2*jump*edge_integral
        check(t-1+2/L+p/4+(1+p)/(4*u1) < 0, "infinite-range main decay")
        check(t-1+2/L+1/(4*u1) < 0, "infinite-range edge decay")
    eps = 4*(-L/4).exp()
    pp = A("8/7")*(1+eps).sqrt()*(L+eps.log1p())**2*(-L/4).exp()/(8*arb(2).log())
    trivial = (-3*L).exp()/(1-(-2*L).exp())
    check(2/L < A("1/4"), "prime power decay")
    return baseline, zmain, zedge, pp, trivial


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor", type=int, default=305)
    cli.add_argument("--last-gap", type=int, default=5, help="last knot spacing in thousandths")
    args = cli.parse_args()
    ctx.prec = 192
    parts = verify(args.anchor, args.last_gap)
    for name, value in zip(("baseline", "moment", "edges", "prime powers", "trivial"), parts):
        print(name, value.str(28))
    print("total", sum(parts).str(28))
    check(sum(parts) < 1, "point budget does not pass")
