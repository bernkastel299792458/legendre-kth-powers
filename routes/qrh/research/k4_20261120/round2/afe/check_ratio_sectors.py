"""Outward-rounded constants for three primitive AFE ratio sectors."""

from flint import arb, ctx


def check_contour():
    # Reciprocal gamma factors and Euler summation are proved in the note.
    pi, r = arb.pi(), arb(3) / 4
    H = arb(3 * 10**12)
    gaussian = arb(".99")
    assert (arb("1.001") / arb(".999"))**2 * (arb(3) / 4)**(-arb(15) / 16) < 2
    assert ((1 + r)**2).exp() / (1 + r) + arb(1).exp() < 16
    assert 16 * (4 * (1 + r)**2 / H**2).exp() < 20 and 4 / H**2 < 1 - gaussian
    # Bound 1+|u| to the fourth power by 8(1+u^4).
    integrated = 2 * 20 * 5 / (2 * pi)
    integrated *= 8 * (pi / gaussian).sqrt() * (1 + 3 / (4 * gaussian**2))
    assert integrated < 801 and (8 / H).exp() - 1 < 9 / H
    return integrated


def check_sectors(cap):
    H = arb(3 * 10**12)
    X, s = arb(cap), arb(7) / 8
    r = 2 * s - 1
    z_direct, z_dual = (1+r).zeta(), abs((1-r).zeta())
    length_sum = 1 + (X**(1-s)-1)/(1-s)
    scale = (2 * arb.pi() * X / H)**r
    low_mass = 20 / arb.pi().sqrt() * arb(-100).exp()
    abs_bracket = 2 * z_direct + length_sum**2 * arb(-225).exp()
    total = arb(0)
    for a, b in ((1, 1), (1, 2), (2, 1)):
        prod, largest = arb(a*b), arb(max(a,b))
        gap = 30 / largest
        constant = X**r * z_direct * prod**-s * length_sum**2
        constant *= (-(gap**2)/4).exp()+low_mass
        shifted = (25-5*gap).exp() + 5/arb.pi().sqrt()*arb(-75).exp() + arb(-400).exp()
        power = scale * z_dual * prod**(s-1) * length_sum**2 * shifted
        quotient_error = scale * z_dual * prod**(s-1) * 9/H * abs_bracket
        contour_error = scale * 802 * prod**s * 2*arb.pi()/H * abs_bracket
        bound = constant + power + quotient_error + contour_error
        print(f"X <= {cap}, sector {a}/{b}", bound.str(18))
        total += bound
    return total


if __name__ == "__main__":
    ctx.prec = 128
    print("central contour", check_contour().str(18))
    small, large = check_sectors(10**10), check_sectors(10**14)
    print("totals", small.str(18), large.str(18))
    assert small < arb("1.8e-9") and large < arb("1.8e-6")
