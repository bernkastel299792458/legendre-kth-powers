"""Arb verification of the first-moment scale bounds in FIRST_MOMENT.md."""

from flint import arb, ctx


def check_scales():
    ctx.prec = 128
    one = arb(1)
    H = arb(3 * 10**12)
    p = arb(7) / 8
    log_h = H.log()
    P, Y = H.sqrt(), H**p
    log_p, log_y = P.log(), Y.log()

    # Integral on the horizontal segment 1 <= c <= 2.
    grid = 20_000
    J = arb(0)
    for i in range(grid):
        u = arb(i) / grid
        Z, M = 3 + log_h, 1 + log_y
        if i:
            trivial = 1 + 1 / u
            Z, M = Z.min(trivial), M.min(trivial)
        J += (1 + Z * M) / grid

    # Extend the integral from c=1 down to 7/10.
    largest = arb(0)
    for i in range(grid - 1, 7 * grid // 10 - 1, -1):
        c = arb(i) / grid
        a = 1 - c
        direct = 1 + (a * log_p).expm1() / a
        M = 1 + (a * log_y).expm1() / a
        Z = direct + (a * log_p).exp() / c + arb("1.205")
        J += (1 + M * Z) / grid
        if i < 7 * grid // 8:
            hi = arb(i + 1) / grid
            largest = largest.max((8 * J + 20) * H ** (p * (2 * hi - 1) - 1))
    assert largest < arb(".162")
    assert 2 / log_h < arb(11) / 64
    assert 2 * (arb(2).zeta()**2 - 1) / arb(2).log() < 5

    D = H / 10
    tail = 4 * 10**14 * (-(D * arb(2).log())**2 / 8).exp()
    pole_gauss = 40 * (2 * arb.pi()).sqrt() * H ** (-arb(25) / 32) * (1 / D**2).exp()
    # Absolute value of the squared sinc continuation <= exp(2/D).
    pole_sinc = 40 * arb(2).sqrt() * H ** (-arb(25) / 32) * (2 / D).exp()
    assert pole_gauss + tail < arb("1.81e-8")
    assert pole_sinc < arb("1.02e-8")
    return largest, pole_gauss + tail, pole_sinc


def check_gaussian_window():
    H = arb(3 * 10**12)
    X_max = arb(10**14)
    pmass = 20 * arb(-100).exp() / arb.pi().sqrt()
    fringe = pmass * arb(".531") * (2 * arb.pi() * X_max / H)**arb(".75")
    low = pmass * (19 * 9)**2 * H**arb(".6") * X_max**arb("1.35")
    assert fringe < arb("2e-41") and low < arb("3e-12")
    base = 2 * arb.pi() * H**(-arb(1) / 8)
    assert base < 1
    full = arb(".531") * base**arb(".4")
    upper = arb(".268") * base**arb(".7")
    assert full < arb(".2633362") and upper < arb(".0785440")
    paid = fringe + low + arb("1.81e-8")
    assert full + paid < arb(".263337") and upper + paid < arb(".078545")
    print("Gaussian joint cost", (full + paid).str(18), (upper + paid).str(18))


if __name__ == "__main__":
    for label, value in zip(("sharp", "Gaussian", "sinc squared"), check_scales()):
        print(label, value.str(18))
    check_gaussian_window()
