"""Arb bounds for the proportion of empty fourth-power intervals in log blocks."""
from flint import arb, ctx


def bounds(left, right, *, coefficient_energy=False):
    """Uniform in real L in [left,right]. Each block is [L,L+1]."""
    pi = arb.pi()
    H = arb(3 * 10**12)
    theta = arb(7) / 8
    Mmin = ((left + 1) / 4).exp()
    Mmax = ((right + 1) / 4).exp()
    dmax = 1 / Mmin
    t = 2 * Mmax
    logt = t.log()
    assert t > H

    def height_integral(p, q):
        rate = 4 - p - q / logt
        assert rate > 0
        return 4 * (p * logt + q * logt.log()).exp() / rate

    mass_low = (-left / 2).exp() * height_integral(1, 2)
    def density(s):
        p = 3 * (1 - s) / (2 - s)
        return (arb(2177) / 100 * height_integral(p, 3 + p)
                + arb(829) / 100 * height_integral(0, 3)
                + 147 * height_integral(0, 2))

    grid = 512
    start = 3 * grid // 4
    end = 7 * grid // 8
    step_factor = (2 * left / grid).expm1()
    cs_mass = (-left / 2).exp() * density(arb(3) / 4)
    for j in range(start, end):
        s = arb(j) / grid
        mass = (2 * (s - 1) * left).exp() * step_factor
        cs_mass += mass * density(s)
    # Row sums for |gamma| >= H. All constants are explicit.
    row_ratio = (2 / pi + arb(3) / 10) * (H + 4).log() / H.log() + 6 / H.log()
    assert row_ratio < arb(116) / 100
    schur = pi / (2 * arb(1).sin()**2) * arb(116) / 100
    critical = 2 * H * H.log() * (dmax - left / 2).exp()
    powers = (right + 1 + dmax)**2 * (3 * dmax / 2 - left / 2).exp() * Mmax / (2 * arb(2).log())
    trivial = (-3 * (left - dmax)).exp() / (1 - (-2 * (left - dmax)).exp())
    deficit = 1 - powers - trivial - critical
    assert deficit > arb("0.99999")
    if coefficient_energy:
        return (2*dmax).exp()*(mass_low+cs_mass)/H.log(),deficit,Mmax,dmax

    k5_arg = 5 * (arb(35) / 16 * t).log()
    assert k5_arg > arb("138.218") and k5_arg < 800
    assert 2 * left > k5_arg
    k5_mass = logt * ((k5_arg - 2 * left) / 8).exp() / 2
    inertia = 1 / (2 * (1 - (-arb(1) / 4).exp() - 2 / Mmin))

    def exception_fraction(high):
        # Positive heights carry both signs with identical energies.
        low_norm = (arb(3) / 8).exp() * mass_low.sqrt()
        high_norm = (arb(1) / 16).exp() * high.sqrt()
        energy = 2 * (2 * dmax).exp() * schur * (low_norm + high_norm)**2
        return inertia * energy / deficit**2

    return exception_fraction(cs_mass), exception_fraction(k5_mass)


if __name__ == "__main__":
    ctx.prec = 160
    reported = {
        "114.96": ("0.282", "0.01204"), "116": ("0.244", "0.01102"),
        "120": ("0.140", "0.00782"), "130": ("0.0342", "0.00331"),
        "150": ("0.00195", "0.000583"), "200": ("1.22e-6", "7.11e-6"),
        "250": ("6.25e-10", "8.15e-8"), "304": ("1.52e-13", "6.26e-10"),
    }
    for endpoint, (cs_limit, k5_limit) in reported.items():
        L = arb(endpoint)
        cs, k5 = bounds(L, L)
        assert cs < arb(cs_limit) and k5 < arb(k5_limit)
        print(endpoint, "CS", cs.str(12), "K5", k5.str(12))
    cs_sup, k5_sup = arb(0), arb(0)
    # Prefix and unit cells tile the full L-domain. The outward envelope
    # in bounds() already handles the dependence of the test on L.
    for lo, hi in [(arb("114.96"), arb(115))] + [(arb(n), arb(n + 1)) for n in range(115, 305)]:
        cs, k5 = bounds(lo, hi)
        cs_sup = cs_sup.max(cs)
        k5_sup = k5_sup.max(k5)
    assert cs_sup < arb("0.314") and k5_sup < arb("0.01415")
    print("all 114.96 <= L <= 305", "CS", cs_sup.str(12), "K5", k5_sup.str(12))
    totals = [arb(192), arb(192)]
    for L in [arb("114.96")] + [arb(n) for n in range(115, 305)]:
        cs, k5 = bounds(L, L)
        count_cap = (L / 4).exp() * (arb(1) / 4).expm1() + 1
        totals[0] += count_cap * cs
        totals[1] += count_cap * k5
    assert totals[0] < arb("4.811e20") and totals[1] < arb("1.223e24")
    print("whole middle, possible exceptions", "CS", totals[0].str(12), "K5", totals[1].str(12))
