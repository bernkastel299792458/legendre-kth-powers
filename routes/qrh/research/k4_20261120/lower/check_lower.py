"""Verify all numerical comparisons in the signed-kernel lower segment, using Arb."""

from flint import arb, ctx


def verify():
    ctx.prec = 256
    lo, hi = arb(1131) / 10, arb(2874) / 25
    H = arb(3 * 10**12)
    Q = arb(10**6)
    K = H - 128 * Q
    r, a = arb(1) / 10000, arb(79) / 40
    pi = arb.pi()
    g0 = (1 - a.cos()) / a**2
    I = pi * a.sin() / a
    dmin = (4 * (-hi / 4).exp()).log1p() / 2
    center_max = hi + (4 * (-lo / 4).exp()).log1p() / 2
    unit_min = (lo / 2).exp() * I / K
    pole_loss = 16 * pi.sqrt() * Q / (K * I)
    u = lo - K.log()
    maxima = a.sin() / a + arb(1) / 6
    bt = 2 * (lo + r) * (3 * r / 2).exp() * (u - 1) / u**2
    intercept = 2 * (lo + r) * (r / 2).exp() / u**2
    near_primes = bt * (1 - a / pi) + intercept * maxima / I
    powers = g0 * r.exp() * (center_max + r)**2 / (2 * arb(2).log() * unit_min)
    far_arithmetic = 4 * g0 * (
        3 * center_max / 2 + 9 / (8 * Q**2) - (Q * r)**2 / 2
    ).exp() / unit_min
    low_zeros = 2 * H * H.log() * pi / (a * K * unit_min)
    spectrum_l1 = 2 * pi * g0
    arch = spectrum_l1 / (2 * pi * unit_min) * (
        7 + (1 + K + 2 * Q / pi.sqrt()).log()
    )
    high_zeros = (
        2 * K / I * spectrum_l1 / (2 * pi.sqrt() * Q)
        * (arb(1) / (16 * Q**2)).exp()
        * H**2 * (1 + 4 * Q**2 / (H - K)**2)
        * (-((H - K) / (2 * Q))**2).exp()
    )
    total = pole_loss + near_primes + powers + far_arithmetic + low_zeros + high_zeros + arch
    assert 0 < a and a < pi and 0 < K and H < 3000175332800
    assert K * dmin > a and r < lo and r > a / K
    assert u > 4 and K.log() + r > 2 and 2 * u.exp() / u**2 > 10
    assert 0 < g0 and g0 < 1 and I > 0
    assert Q >= 1 and H.log() > 3 and unit_min > 0
    assert total < arb(999) / 1000
    nlo = int((lo / 4).exp().floor().unique_fmpz()) + 1
    nhi = int((hi / 4).exp().floor().unique_fmpz())
    assert 4 * arb(nlo - 1).log() < lo and lo < 4 * arb(nlo).log()
    assert 4 * arb(nhi).log() < hi and hi < 4 * arb(nhi + 1).log()
    for name, value in (
        ("K*d_min", K * dmin), ("dimensionless mass", I), ("BT coefficient", bt),
        ("pole loss", pole_loss), ("exterior primes", near_primes),
        ("prime powers", powers), ("far arithmetic", far_arithmetic),
        ("low zeros", low_zeros), ("high zeros", high_zeros),
        ("archimedean term", arch), ("total normalized deductions", total),
        ("strict surplus", 1 - total),
    ):
        print(f"{name:28} {value.str(17)}")
    print("inclusive integer interval", nlo, nhi)


if __name__ == "__main__":
    verify()
