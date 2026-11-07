"""
Lemma B-W (rigorous, Arb; NEW, own lemma): Weyl-exponent version of Thorner-Zaman's bound for -J.

Setting (TZ, proof of Prop. 2.11, chi = 1): s = 1 + r + it, 0 < r < 1/2, 3e12 <= |t| <= T,
F(z) = ((z-1)/(z+1)) zeta(z), J(r1) = (1/(pi r1)) int_0^{2pi} cos th log|F(s + r1 e^{i th})| d th.
TZ prove   limsup_{r1 -> (1/2+r)^-} (-J) <= BTZ(r, log T)
           = (log T + 4.709774)/(4+8r) + (4/pi-1) log(1+1/r)/(1+2r) + 2.6908,
using the convexity bound on the arc J3 (cos th < 0). We replace the convexity input by
           |zeta(1/2+iy)| <= A_eta |1+iy|^{1/6+eta}     for all real y,
           A_eta := max(1.461, 0.618/(e*eta))   provided  A_eta * exp(105*(2/984 + eta)) >= 66.7,
which follows from |zeta(1/2+iy)| <= 1.461 (|y|<=3, certified below in Arb), Hiary-Patel-Yang
0.618|y|^{1/6} log|y| (3 <= |y| <= e^105) and Patel-Yang 66.7|y|^{27/164} (|y| >= e^105) [both as quoted in
Bellotti Lemma 2.5], together with log y <= y^eta/(e eta).  Rademacher's Phragmen-Lindelof lemma on the strip
1/2 <= Re z <= 1 + r (Q = 1/2) then gives, with ell := log(sqrt(2) T),

  limsup (-J) <= BTZW(r, log T; eta) := ((1/6 + eta) ell + log A_eta)/(1+2r) + (4/pi-1) log(1+1/r)/(1+2r) + 2.6908.

The choice eta = 1/ell gives (ell/6 + log(0.618 ell))/(1+2r) + ...  (vs TZ: (ell/4 + 1.0908)/(1+2r) + ...).
"""
import math
from flint import arb, acb, ctx

ctx.prec = 100
PI = arb.pi()
_CERT = {}


def certify_zeta_half_small(tmax=3, n=300):
    """rigorous: sup_{|t|<=3} |zeta(1/2+it)| <= 1.461 (conjugate symmetry: t in [0,3] suffices);
    adaptive bisection of ball evaluations."""
    if 'z' in _CERT:
        return _CERT['z']
    stack = [(arb(tmax) * i / n, arb(tmax) * (i + 1) / n) for i in range(n)]
    worst = 0.0; cnt = 0
    while stack:
        a, b = stack.pop(); cnt += 1
        z = acb(arb("0.5"), a.union(b)).zeta()
        ub = float(z.abs_upper())
        if ub <= 1.461:
            worst = max(worst, ub)
            continue
        assert bool(b - a > arb("1e-12")) and cnt < 10 ** 6, "cannot certify"
        m = (a + b) / 2
        stack += [(a, m), (m, b)]
    _CERT['z'] = worst
    return worst


def A_eta(eta):
    eta = arb(eta)
    A = arb(max(1.461, float((arb("0.618") / (arb(1).exp() * eta)).upper())))
    # Patel-Yang range: need A * |y|^{1/6+eta} >= 66.7 |y|^{27/164} for |y| >= e^105
    cond = A * (arb(105) * (arb(2) / 984 + eta)).exp()
    assert bool(cond >= arb("66.7")), "Patel-Yang range condition fails"
    return A


def BTZW(r, l, eta=None):
    """Weyl version of BTZ (arb in/out). l = log T (upper end). eta default 1/log(sqrt2 T)."""
    certify_zeta_half_small()
    ell = l + arb(2).log() / 2
    if eta is None:
        eta = arb(1 / float(ell.lower()))
    A = A_eta(eta)
    return (((arb(1) / 6 + eta) * ell + A.log()) / (1 + 2 * r)
            + (4 / PI - 1) * (1 + 1 / r).log() / (1 + 2 * r) + arb("2.6908"))


if __name__ == "__main__":
    from lemmaB_count import BTZ
    print("sup_{|t|<=3}|zeta(1/2+it)| <=", certify_zeta_half_small())
    for L in (28.73, 35.0, 40.0, 50.0, 80.0, 110.0):
        r = arb("0.05")
        a = BTZ(r, arb(L)); b = BTZW(r, arb(L))
        print(f"log T={L}: BTZ={float(a.upper()):.4f}  BTZ_Weyl={float(b.upper()):.4f}  ratio={float(b.upper())/float(a.upper()):.4f}")
