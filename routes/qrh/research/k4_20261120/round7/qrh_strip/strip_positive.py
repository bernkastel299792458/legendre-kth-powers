"""Right-edge Poisson and Fejer tests on the actual sigma=.865 rectangle."""
from math import isqrt

from flint import acb, arb, arb_series, ctx


ctx.prec = 160
H = arb(3000175332800)
T = H * (arb(7) / 4).exp()
THETA = arb(7) / 8
S = arb(865) / 1000
FAIL = 420071
PI = arb.pi()
BACKGROUND = (T / (2 * PI)).log() / 2 + arb(".0001")


def kernel(a, t, bandwidth):
    z = acb(a, t)
    return (1 / z + (-bandwidth * z).expm1() / (bandwidth * z**2)).real


def archimedean():
    # Uniform upper error on H-1 <= t <= T+1 and 8 <= A <= 120.
    d = H / 10000
    near = (1 + (d + 1) / (H-1)).log() + 4 / (H - 1 - d)
    tail = (2 / (PI * d)) * ((T + 3).log() + (1 + d).log() + 3)
    pole = 2 * (1 + (1 + arb(15).exp()) / 8) / (H - 1)**2
    assert near / 2 + tail / 2 + pole < arb(".0001")
    return near / 2 + tail / 2 + pole


def arithmetic_cap(c=None, lam=None):
    # Bound -P_10(t) by minimizing its p and p^2 summands jointly.
    bandwidth = arb(10)
    cap = int(bandwidth.exp().floor().unique_fmpz())
    primes = bytearray([1]) * (cap + 1)
    primes[:2] = b"\x00\x00"
    for p in range(2, isqrt(cap) + 1):
        if primes[p]:
            primes[p*p::p] = bytes((cap - p*p) // p + 1)
    result = arb(0)
    if lam is not None:
        zz = arb_series([c, 1], 2).zeta()
        result = -lam * zz[1] / zz[0]
    for p in range(2, cap + 1):
        if not primes[p]:
            continue
        logp = arb(p).log()
        n = p
        k = 1
        terms = []
        while n <= cap:
            v = k * logp
            terms.append(logp * (-THETA * v).exp() * (1 - v / bandwidth))
            if lam is not None:
                subtract = lam * logp * (-c*v).exp()
                terms[-1] -= subtract
                result -= subtract
            k += 1
            n *= p
        if len(terms) == 1:
            result += abs(terms[0])
            continue
        b, second = terms[:2]
        lower = second - abs(b)
        if second > 0:
            x = (-b / (4 * second)).max(-1).min(1)
            lower = lower.min(b*x + second*(2*x*x - 1))
        result += -lower + sum(map(abs, terms[2:]), arb(0))
    return result


def pair_positivity(A, lam):
    c = arb("1.4")
    mid = THETA - arb(1)/2
    cut = arb(".30")
    gap = c - THETA
    if A*cut < PI:
        assert kernel(mid, cut, A)+kernel(2*mid, cut, A) > lam*(1/gap+1/(gap+mid))
    else:
        # On the short range even the more distant partner alone suffices.
        for i in range(40):
            a = mid * arb(2*i+1,1)/80
            b = 2*mid-a
            for j in range(24):
                y = cut * arb(2*j+1,1)/48
                bnd = lam*((gap+a)/((gap+a)**2+y**2)+(gap+b)/((gap+b)**2+y**2))
                assert (b-2/A)/(b*b+y*y) > bnd

    def y2_kernel(a, r):
        u = (a*r)**2
        k = a/(1+u) + (1-u)/(A*(1+u)**2) - (-A*a).exp()/(A*(1+u))
        return k.max(0)

    def y2_poisson(a, r):
        return a/(1+(a*r)**2)

    def check(al, au, rl, ru, depth):
        a = arb((al+au)/2, (au-al)/2)
        r = arb((rl+ru)/2, (ru-rl)/2)
        b = 2*mid-a
        if y2_kernel(a,r)+y2_kernel(b,r) > lam*(y2_poisson(gap+a,r)+y2_poisson(gap+b,r)):
            return 1
        assert depth < 25
        if (au-al)/mid > (ru-rl)*cut:
            m = (al+au)/2
            return check(al,m,rl,ru,depth+1) + check(m,au,rl,ru,depth+1)
        m = (rl+ru)/2
        return check(al,au,rl,m,depth+1) + check(al,au,m,ru,depth+1)

    return check(arb(0), mid, arb(0), 1/cut, 0)


def paired_subtraction():
    A = 10
    c = arb("1.4")
    lam = arb(".46")
    leaves = pair_positivity(A, lam)
    cap = arithmetic_cap(c,lam)
    h = arb(".075")
    sub = lam*(1/(c-THETA)+1/(c+S-1))
    pair = kernel(THETA-S,h,A)+kernel(2*THETA-1,h,A)-sub
    ratio = ((1-lam)*(T/(2*PI)).log()/2+arb(".00011")+cap)/pair
    assert ratio < 3
    print("subtraction positivity cells", leaves, "prime cap", cap.str(12),
          "width .15 multiplicity ratio", ratio.str(12))


def finite_excursion(A):
    c = arb("1.4")
    lam = arb(".40")
    pair_positivity(A,lam)
    # The decreasing integral test starting at floor(exp A).
    v = A-arb(".000001")
    assert v.exp()+1<A.exp()
    tail = lam*(-(c-1)*v).exp()*(v/(c-1)+1/(c-1)**2)
    budget = (1-lam)*(T/(2*PI)).log()/2+arb(".00011")+tail
    tax = lam*(1/(c-THETA)+1/(c+S-1))
    def score(y):
        return kernel(THETA-S,y,A)+kernel(2*THETA-1,y,A)-tax-budget
    print("finite joint A",A.str(10),"point threshold",score(0).str(12))
    # Use just yA <= 2 to retain simple horizontal and abscissa monotonicity.
    powers = (8,12,16,20)
    totals = [arb(0) for p in powers]
    bns = 256
    for i in range(1, bns+1):
        h = 2*i/(A*bns)
        s = score(h).max(0)
        for j,p in enumerate(powers):
            totals[j] += s**p
    thresholds = [(4*z*FAIL/(A*bns*(T-H+2))).root(p) for z,p in zip(totals,powers)]
    print("finite signed negative moments (8,12,16,20)",*(z.str(8) for z in thresholds))


def high_moments():
    c = THETA + arb(1) / 10000
    a = c - S
    bmax = c + THETA - 1
    bmin = c + S - 1
    end = arb("2.8")
    assert bmin / (bmax*bmax + (a * end)**2) > arb("1.30")
    bins = 1024
    results = {}
    for power in (2, 4, 6, 8, 10, 12, 16, 20, 24):
        total = arb(0)
        for i in range(1, bins + 1):
            z = end * i / bins
            v = 1 / (a * (1 + z*z)) + arb("1.30") - BACKGROUND
            total += v.max(0) ** power
        integral = 2 * a * end * total / bins
        results[power] = (FAIL * integral / (T - H + 2)).root(power)
    for p, target in ((8, "5.19"), (12, "13.01"), (16, "20.66"), (20, "27.32")):
        assert results[p] > arb(target)
    return results


def main():
    print("archimedean and poles margin", archimedean().str(10))
    cap = arithmetic_cap()
    assert cap < arb("6.510345")
    print("uniform upper bound on -P_10(t)", cap.str(12))
    h = arb(".14")
    pair = kernel(THETA-S, h, 10) + kernel(2*THETA-1, h, 10)
    ratio = (BACKGROUND + cap) / pair
    assert 10 * h < PI and ratio < arb("3.98")
    print("width .28 multiplicity ratio", ratio.str(12))
    paired_subtraction()
    for A in (T.log(),arb(45),arb(60),arb(80)):
        finite_excursion(A)
    for A, target in ((T.log(), ".7566"), (arb(60), "11.7846"), (arb(120), "28.7636")):
        force = kernel(THETA-S, 0, A) + kernel(2*THETA-1, 0, A) - BACKGROUND
        assert force > arb(target)
        print("A", A.str(12), "one-zero lower bound on -P_A(t)", force.str(12))
    for p, result in high_moments().items():
        print("p", p, "failure forces Lp normalized positive log-derivative mean >", result.str(11))


if __name__ == "__main__":
    main()
