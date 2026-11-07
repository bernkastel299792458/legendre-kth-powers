# -*- coding: utf-8 -*-
"""
Arb (python-flint 0.9.0) implementation of the constants of Section 5 of
S. Chourasiya & A. Simonic, "An explicit form of Ingham's zero density
estimate", arXiv:2507.15184v2 (Theorem 2 = thm:4thPMExplicitGeneral).

Every formula below is transcribed from the LaTeX source (v2, lines given in
comments).  Equation labels refer to the paper.  All quantities are arb balls;
all integrals are done with acb.integral (rigorous, analytic integrands) plus
explicit tail bounds.  Parameters are converted from decimal strings to exact
rationals before entering Arb.

Switch PAPER_D_CONSTANTS:
  True  -> use the paper's rounded numbers 0.744342, 0.823266, 0.460324,
           1.488684, 9.73, 17.52, 154, 0.12441, 0.364, 0.3, 4.61 exactly as
           printed (this is "recompute from the paper's formulas").
"""
from fractions import Fraction
from flint import arb, acb, ctx

ctx.prec = 128

PI = arb.pi()
GAM = arb.const_euler()
E = arb(1).exp()
M0 = (1 + arb(2) / 3 * (arb(6) / 5).sqrt()).sqrt()   # Preissmann constant, Lemma 3 (l.637)


def Q(x):
    """exact rational -> arb ball (tiny radius)"""
    f = Fraction(str(x))
    return arb(f.numerator) / f.denominator


# paper's rounded constants (Lemma 11, l.1041 and Lemma 12)
c_D2 = Q("0.744342")
c_D3 = Q("0.823266")
c_D4 = Q("0.460324")
c_2D2 = Q("1.488684")
c_K = Q("9.73")

# ---- corrected mode (audit): exact D_k balls, CHT21 error 9.73 x^{3/4} log x + K2 x^{1/2}
CORR = False
K2 = arb(0)          # 0.73 in corrected mode
D6_CONST = arb(154)  # paper's constant in D6
D6_COEF = (Q("0.349436"), Q("1.155975"), Q("1.28359"))


def exact_D():
    """D1..D4 as rigorous balls: residue of zeta(s)^4/zeta(2s) x^s/s at s=1"""
    import math
    from flint import acb_series
    old = ctx.cap
    ctx.cap = 6
    coef = [acb(1)] + [acb((-1) ** n) * acb.stieltjes(n) / math.factorial(n) for n in range(5)]
    h = acb_series(coef) ** 4 / acb_series.zeta(acb_series([2, 2])) / acb_series([1, 1])
    c = h.coeffs()
    ctx.cap = old
    return c[0].real / 6, c[1].real / 2, c[2].real, c[3].real


def set_mode(corrected):
    """corrected=False: paper's printed constants.  corrected=True: audit-corrected constants."""
    global CORR, K2, c_D2, c_D3, c_D4, c_2D2, D6_CONST, D6_COEF
    CORR = bool(corrected)
    if not CORR:
        c_D2, c_D3, c_D4, c_2D2 = Q("0.744342"), Q("0.823266"), Q("0.460324"), Q("1.488684")
        K2 = arb(0)
        D6_CONST = arb(154)
        D6_COEF = (Q("0.349436"), Q("1.155975"), Q("1.28359"))
        return
    d1, d2, d3, d4 = exact_D()
    c_D2, c_D3, c_D4, c_2D2 = d2, d3, d4, 2 * d2
    K2 = Q("0.73")
    L2 = arb(2).log()
    c0 = d4 + Q("0.5") - (d1 * L2 ** 4 / 4 + d2 * L2 ** 3 / 3 + d3 * L2 ** 2 / 2 + d4 * L2)
    I973 = c_K * arb(2) ** (-Q("0.25")) * (4 * L2 + 16)
    I073 = K2 * 2 / arb(2).sqrt()
    D6_CONST = abs(c0) + I973 + I073
    D6_COEF = (d1 + d2 / 3, d2 + d3 / 2, d3 + d4)


def apow(a, z):
    """a^z for a>0 (arb) and z arb/acb"""
    if isinstance(z, acb):
        return (z * acb(a).log()).exp()
    return (z * a.log()).exp()


def is_acb(*xs):
    return any(isinstance(x, acb) for x in xs)


# ---------------------------------------------------------------- Lemma 9 (l.955-970)
def D1(x0, s0):
    """D_1(x0, sigma0), valid for sigma0 <= 0 (|sigma0| = -sigma0)."""
    L = x0.log()
    sq = x0.sqrt()
    abs_s0 = -s0
    return (1 + (2 * GAM - 1 - s0 / (1 - s0)) / L
            + (1 - s0) * (Q("0.5") + abs_s0 - s0) / sq
            + (1 - 2 * GAM * s0) / (sq * L))


def D2(x0, s0):
    """D_2(x0, sigma0), sigma0 > 1 (eq. D2)."""
    L = x0.log()
    sq = x0.sqrt()
    return s0 - 1 + (1 + 2 * GAM * (s0 - 1)) / L + (4 * s0 - 1) / ((2 * s0 - 1) * sq * L)


# ---------------------------------------------------------------- Lemma 10 (l.1006-1009)
def D3(x0):
    L = x0.log()
    return 1 / E + (1 + 2 * GAM) / (E * L) + 5 / (2 * E * x0.sqrt() * L)


# ---------------------------------------------------------------- Lemma 12 (l.1060-1089)
def D41(x0, s):
    L = x0.log()
    p2 = PI ** 2
    t0 = 1 / ((1 - s) * p2)
    t1 = (-3 * s / ((1 - s) ** 2 * p2) + c_D2 / (1 - s)) / L
    t2 = (6 * s / ((1 - s) ** 3 * p2) - c_2D2 * s / (1 - s) ** 2 + c_D3 / (1 - s)) / L ** 2
    t3 = (-6 * s / ((1 - s) ** 4 * p2) + c_2D2 * s / (1 - s) ** 3 - c_D3 * s / (1 - s) ** 2
          + c_D4 / (1 - s)) / L ** 3
    t4 = Q("17.52") / (apow(x0, Q("0.25")) * L ** 2)
    # audit correction: CHT21 extra term K2 x^{1/2}:  K2 (1+|s|/(1/2+|s|)) / (sqrt(x0) L^3)
    t5 = K2 * (1 + (-s) / (Q("0.5") - s)) / (x0.sqrt() * L ** 3)
    return t0 + t1 + t2 + t3 + t4 + t5


def D42(x0, s, sf):
    L = x0.log()
    mn = Q("0.25") if sf <= 0.75 else (1 - s)
    return (1 / PI ** 2 + c_D2 / L + c_D3 / L ** 2 + c_D4 / L ** 3
            + c_K * s * (1 - s) / (apow(x0, mn) * L)
            + c_K * (1 - s) / (apow(x0, Q("0.25")) * L ** 2)
            # audit correction (K2 x^{1/2} term of CHT21)
            + K2 * (1 - s) / (x0.sqrt() * L ** 3)
            + K2 * s * (1 - s) / (apow(x0, Q("0.5") if sf <= 0.5 else (1 - s)) * L ** 2))


def D4(x0, s):
    """D_4(x0, sigma) (eq. D4); s must be an arb with known sign."""
    sf = float(s.mid())
    if s < 0:
        assert sf >= -3 - 1e-12, ("D4 out of range", sf)
        return D41(x0, s)
    assert s >= 0 and s < 1, ("D4 out of range / ambiguous ball", s)
    assert abs(sf - 0.75) > 1e-9
    return D42(x0, s, sf) / (1 - s)


def D5(x0, s):
    """D_5(x0, sigma), sigma > 1 (eq. D5)."""
    assert s > 1
    L = x0.log()
    p2 = PI ** 2
    u = s - 1
    t0 = u ** 3 / p2
    t1 = u ** 2 * (3 * s / p2 + c_D2 * u) / L
    t2 = u * (6 * s / p2 + c_2D2 * s * u + c_D3 * u ** 2) / L ** 2
    t3 = (6 * s / p2 + c_2D2 * s * u + c_D3 * s * u ** 2 + c_D4 * u ** 3) / L ** 3
    w = s - Q("0.75")
    t4 = (1 + s / w * (1 + 1 / (w * L))) * c_K * u ** 4 / (apow(x0, Q("0.25")) * L ** 2)
    t5 = K2 * u ** 4 * (1 + s / (s - Q("0.5"))) / (x0.sqrt() * L ** 3)   # audit correction
    return t0 + t1 + t2 + t3 + t4 + t5


# ---------------------------------------------------------------- Lemma 13, 14
def D6(x0):
    L = x0.log()
    a, b, c = D6_COEF
    return (a + b / L + c / L ** 2 + D6_CONST / L ** 3
            + c_K / (apow(x0, Q("0.25")) * L ** 2) + K2 / (x0.sqrt() * L ** 3))


def D7(x0):
    L = x0.log()
    return (3 / (2 * E * PI) ** 2 + Q("0.12441") / L + Q("0.364") / L ** 2 + Q("0.3") / L ** 3
            + Q("4.61") / (apow(x0, Q("0.25")) * L ** 2)
            + (Q("0.35") if CORR else 0) / (x0.sqrt() * L ** 3))


# ---------------------------------------------------------------- Lemma 16 (l.1262)
def Um(y0):
    return 1 / (1 + (-PI * y0).exp()) * (-1 / (2 * y0 ** 2)).exp()


def Up(y0):
    return 1 / (1 - (-PI * y0).exp()) * (1 / (2 * y0 ** 2)).exp()


def eta(T0):
    return 1 + PI * M0 / T0


# ---------------------------------------------------------------- integral of |Gamma(c+iu)|
_IG_cache = {}


def IG(c):
    """int_{-inf}^{inf} |Gamma(c+iu)| du, c real (not an integer).
    = 2*int_0^U sqrt(Gamma(c+iu)Gamma(c-iu)) du + tail.
    Tail: for |u|>=U=60, |Gamma(c+iu)| <= 100 exp(-pi|u|/2) (very generous; Stirling with
    remainder |R|<=1/(6|z|) in |arg z|<=3pi/4 gives |Gamma|<=sqrt(2pi) e^{2.01} |u|^{c-1/2}
    e^{-pi|u|/2} for |c|<=1), so tail <= 2*100*(2/pi) e^{-30 pi} < 1e-38."""
    key = (c.mid().str(30), c.rad().str(5))
    if key in _IG_cache:
        return _IG_cache[key]
    cc = acb(c)

    def f(u, analytic):
        z = cc + acb(0, 1) * u
        w = cc - acb(0, 1) * u
        return (z.gamma() * w.gamma()).sqrt(analytic=analytic)

    U = 60
    val = 2 * acb.integral(f, 0, U, rel_tol=2.0 ** -100).real
    tail = arb(0, 400 / PI * (-PI * U / 2).exp())
    res = val + tail
    _IG_cache[key] = res
    return res


def integral_real(f, a, b):
    """rigorous integral of an analytic integrand given as a function of acb z"""
    return acb.integral(lambda z, an: f(z), a, b, rel_tol=2.0 ** -90).real


# ================================================================ the J's
def J1(T0):
    """eq. cJ1"""
    return 2 * eta(T0) * D6(T0) + 4 * PI * M0 * D4(T0, arb(0)) + M0 * T0.log() / (2 * PI * T0)


def J21(T0, s1):
    """eq. cJ21"""
    et = eta(T0)
    um = Um(T0)
    p1 = 2 * apow(2 * PI, 1 - 2 * s1) / um ** 2 * (et * D4(T0, 2 * s1) + 2 * PI * M0 * D4(T0, 2 * s1 - 1))
    twopi = acb(2 * PI)
    pi_ = acb(PI)

    def f(u):
        return ((1 - 2 * u) * twopi.log()).exp() / (1 - u) ** 2 + ((1 - 2 * u) * pi_.log()).exp() / (1 - u) ** 2

    I = integral_real(f, s1, Q("0.5"))
    p2 = 2 / T0.log() * (D1(T0, arb(0)) / um) ** 2 * I
    return p1 + p2


def G1(T0, s2, s3):
    """eq. fG1"""
    et = eta(T0)
    um = Um(T0)
    d7 = D7(T0)
    A = (et + 2 * PI * M0).sqrt() * d7.sqrt()
    t1 = (1 / um ** 2 * apow(2 + 1 / T0, s2 - Q("0.5"))
          * (et * D4(T0, 2 - 2 * s2) + 2 * PI * M0 * D4(T0, 1 - 2 * s2)).sqrt()
          * (A + (et * D4(T0, 2 * s2 - 2) + 2 * PI * M0 * D4(T0, 2 * s2 - 3)).sqrt()))
    t2 = (apow(2 * PI, 1 - 2 * s3) / um ** 2
          * (et * D4(T0, 2 * s3) + 2 * PI * M0 * D4(T0, 2 * s3 - 1)).sqrt()
          * (A + (et * D4(T0, 2 * s3 - 2) + 2 * PI * M0 * D4(T0, 2 * s3 - 3)).sqrt()))
    return t1 + t2


def _D1_acb(x0, s0):
    """D1 with acb argument s0 (s0<=0 on the path)"""
    L = acb(x0.log())
    sq = acb(x0.sqrt())
    g = acb(GAM)
    return (1 + (2 * g - 1 - s0 / (1 - s0)) / L + (1 - s0) * (acb(0.5) - 2 * s0) / sq
            + (1 - 2 * g * s0) / (sq * L))


def _D2_acb(x0, s0):
    L = acb(x0.log())
    sq = acb(x0.sqrt())
    g = acb(GAM)
    return s0 - 1 + (1 + 2 * g * (s0 - 1)) / L + (4 * s0 - 1) / ((2 * s0 - 1) * sq * L)


def G2(T0, s2, s3):
    """eq. fG2"""
    um = Um(T0)
    d1 = D1(T0, arb(0))
    d3 = acb(D3(T0))
    lA = acb(1 + 1 / T0).log()
    lB = acb(1 + 1 / (2 * T0)).log()
    l2p = acb(2 * PI).log()
    lp = acb(PI).log()

    def f1(u):
        return (((u - 0.5) * lA).exp() + ((u - 0.5) * lB).exp()) * (_D1_acb(T0, u - 1) / (2 - u) + d3) / u

    def f2(u):
        return (((1 - 2 * u) * l2p).exp() + ((1 - 2 * u) * lp).exp()) * (_D1_acb(T0, u - 1) / (2 - u) + d3) / (1 - u)

    I1 = integral_real(f1, Q("0.5"), s2)
    I2 = integral_real(f2, s3, Q("0.5"))
    return d1 / um ** 2 * I1 + d1 / um ** 2 * I2


def g1f(T0, s4, c1, a1, a2):
    """eq. fg1"""
    ac = -c1
    L0 = T0.log()
    La = a1 * apow(L0, a2)
    et = eta(T0)
    um = Um(T0)
    up = Up(T0 - La)
    ig = IG(c1)
    return (1 / um ** 2 * apow(1 / PI + 1 / (2 * PI * T0), 2 * s4 - 1)
            * apow(1 / PI + (Q("0.5") + La) / (2 * PI * T0), 2 * (1 - 2 * s4) + 4 * ac)
            * up ** 4 * ig ** 2
            * (et * D5(T0, 2 - 2 * s4 + 2 * ac) / ((2 * PI) ** 2 * (1 - 2 * s4 + 2 * ac) ** 4)
               + M0 * D5(T0, 1 - 2 * s4 + 2 * ac) / (2 * PI * (2 * ac - 2 * s4) ** 4)))


def g2f(T0, s4, c2, b1, b2):
    """eq. fg2"""
    L0 = T0.log()
    Lb = b1 * apow(L0, b2)
    et = eta(T0)
    um = Um(T0)
    up = Up(T0 - Lb)
    ig = IG(c2)
    return (1 / um ** 2 * apow(1 / PI + 1 / (2 * PI * T0), 2 * s4 - 1)
            * apow(1 / (2 * PI) - Lb / (2 * PI * T0), 2 * (1 - 2 * (s4 + c2)))
            * up ** 4 * ig ** 2
            * (et * D4(T0, 2 * (1 - s4 - c2)) / (2 * PI) ** 2 + M0 * D4(T0, 1 - 2 * (s4 + c2)) / (2 * PI)))


def G3(T0, s4, c1, c2, a1, a2, b1, b2):
    """eq. fG3"""
    et = eta(T0)
    um = Um(T0)
    return (apow(2 * PI, s4) / um * (et / (2 * PI) * D4(T0, 2 * (1 - s4)) + M0 * D4(T0, 1 - 2 * s4)).sqrt()
            * (g1f(T0, s4, c1, a1, a2).sqrt() + g2f(T0, s4, c2, b1, b2).sqrt()))


def g3f(T0, s5, c1, a1, a2):
    """eq. fg3"""
    ac = -c1
    L0 = T0.log()
    La = a1 * apow(L0, a2)
    et = eta(T0)
    um = Um(T0)
    up = Up(T0 - La)
    ig = IG(c1)
    return (1 / (apow(2 * PI, 1 + 2 * s5) * um ** 2)
            * apow(1 / PI + (1 + La) / (2 * PI * T0), 2 * (1 - 2 * s5) + 4 * ac)
            * up ** 4 * ig ** 2
            * (et * D5(T0, 2 - 2 * s5 + 2 * ac) / (1 - 2 * s5 + 2 * ac) ** 4
               + 2 * PI * M0 * D5(T0, 1 - 2 * s5 + 2 * ac) / (2 * ac - 2 * s5) ** 4))


def g4f(T0, s5, c2, b1, b2):
    """eq. fg4"""
    L0 = T0.log()
    Lb = b1 * apow(L0, b2)
    et = eta(T0)
    um = Um(T0)
    up = Up(T0 - Lb)
    ig = IG(c2)
    return (1 / (apow(2 * PI, 1 + 2 * s5) * um ** 2)
            * apow(1 / (2 * PI) - Lb / (2 * PI * T0), 2 * (1 - 2 * (s5 + c2)))
            * up ** 4 * ig ** 2
            * (et * D4(T0, 2 * (1 - s5 - c2)) + 2 * PI * M0 * D4(T0, 1 - 2 * (s5 + c2))))


def G4(T0, s5, c1, c2, a1, a2, b1, b2):
    """eq. fG4"""
    et = eta(T0)
    um = Um(T0)
    return (apow(2 * PI, Q("0.5") - s5) / um * (et * D4(T0, 2 * s5) + 2 * PI * M0 * D4(T0, 2 * s5 - 1)).sqrt()
            * (g3f(T0, s5, c1, a1, a2).sqrt() + g4f(T0, s5, c2, b1, b2).sqrt()))


def g5f(T0, s4, c1, a1, a2):
    """eq. fg5"""
    ac = acb(-c1)
    L0 = T0.log()
    La = a1 * apow(L0, a2)
    lA = acb(1 + 1 / T0).log()
    lB = acb(1 + 1 / (2 * T0)).log()
    lb1 = acb(1 / (2 * PI) + (Q("0.5") + La) / (2 * PI * T0)).log()
    lb2 = acb(1 / PI + (Q("0.5") + La) / (2 * PI * T0)).log()

    def f(s):
        e = 1 - 2 * (s - ac)
        return ((((s - 0.5) * lA).exp() * (e * lb1).exp() + ((s - 0.5) * lB).exp() * (e * lb2).exp())
                * _D2_acb(T0, 1 - s + ac) / (s * (s - ac) ** 2))

    return integral_real(f, Q("0.5"), s4)


def g6f(T0, s4, c2, b1, b2):
    """eq. fg6"""
    cc = acb(c2)
    L0 = T0.log()
    Lb = b1 * apow(L0, b2)
    lA = acb(1 + 1 / T0).log()
    lB = acb(1 + 1 / (2 * T0)).log()
    lb1 = acb(1 / (2 * PI) - Lb / (2 * PI * T0)).log()
    lb2 = acb(1 / PI - Lb / (2 * PI * T0)).log()

    def f(s):
        e = 1 - 2 * (s + cc)
        return ((((s - 0.5) * lA).exp() * (e * lb1).exp() + ((s - 0.5) * lB).exp() * (e * lb2).exp())
                / (s * (s + cc)))

    return integral_real(f, Q("0.5"), s4)


def G5(T0, s4, c1, c2, a1, a2, b1, b2):
    """eq. fG5"""
    L0 = T0.log()
    La = a1 * apow(L0, a2)
    Lb = b1 * apow(L0, b2)
    um = Um(T0)
    d10 = D1(T0, arb(0))
    return (d10 / (2 * PI) * (Up(T0 - La) / um) ** 2 * g5f(T0, s4, c1, a1, a2) * IG(c1)
            + d10 * D1(T0, Q("-0.5")) / (2 * PI) * (Up(T0 - Lb) / um) ** 2 * g6f(T0, s4, c2, b1, b2) * IG(c2))


def g7f(T0, s5, c1, a1, a2):
    """eq. fg7"""
    ac = acb(-c1)
    L0 = T0.log()
    La = a1 * apow(L0, a2)
    l2p = acb(2 * PI).log()
    lp = acb(PI).log()
    lb1 = acb(1 / (2 * PI) + (1 + La) / (2 * PI * T0)).log()
    lb2 = acb(1 / PI + (1 + La) / (2 * PI * T0)).log()

    def f(s):
        e = 1 - 2 * (s - ac)
        return ((((1 - 2 * s) * l2p).exp() * (e * lb1).exp() + ((1 - 2 * s) * lp).exp() * (e * lb2).exp())
                * _D2_acb(T0, 1 - s + ac) / ((1 - s) * (s - ac) ** 2))

    return integral_real(f, s5, Q("0.5"))


def g8f(T0, s5, c2, b1, b2):
    """eq. fg8"""
    cc = acb(c2)
    L0 = T0.log()
    Lb = b1 * apow(L0, b2)
    l2p = acb(2 * PI).log()
    lp = acb(PI).log()
    lb1 = acb(1 / (2 * PI) - Lb / (2 * PI * T0)).log()
    lb2 = acb(1 / PI - Lb / (2 * PI * T0)).log()

    def f(s):
        e = 1 - 2 * (s + cc)
        return ((((1 - 2 * s) * l2p).exp() * (e * lb1).exp() + ((1 - 2 * s) * lp).exp() * (e * lb2).exp())
                / ((1 - s) * (s + cc)))

    return integral_real(f, s5, Q("0.5"))


def G6(T0, s5, c1, c2, a1, a2, b1, b2):
    """eq. fG6"""
    L0 = T0.log()
    La = a1 * apow(L0, a2)
    Lb = b1 * apow(L0, b2)
    um = Um(T0)
    d10 = D1(T0, arb(0))
    return (d10 / (2 * PI) * (Up(T0 - La) / um) ** 2 * g7f(T0, s5, c1, a1, a2) * IG(c1)
            + 1 / (2 * PI) * (d10 * Up(T0 - Lb) / um) ** 2 * g8f(T0, s5, c2, b1, b2) * IG(c2))


def J01f(T0, c1, a1, a2):
    """eq. cJ01; integral over [4, inf) done on [4, 400] + tail.
    Tail: for u >= 400, (1+u/(2T0))^{2|c1|} <= (1+u)^2, u^{-|c1|-1/2} <= 1, and
    int_400^inf (1+u)^2 e^{-u/2} du < 1e6 * e^{-200}."""
    ac = -c1
    L0 = T0.log()
    La = a1 * apow(L0, a2)
    acc = acb(ac)
    l1 = acb(1 / (2 * T0))

    def f(u):
        return ((2 * acc) * (1 + u * l1).log()).exp() * (-u / 2).exp() / ((acc + 0.5) * u.log()).exp()

    I = integral_real(f, 4, 400) + arb(0, 1e6 * float((-arb(200)).exp().mid()) * 10)
    return (apow(arb(2), 2 * ac) * (2 / PI).sqrt() * (Q("0.4") + 16 / apow(2 * T0 + La, ac)) ** 2
            * (1 / (2 * La ** 2)).exp() * D2(T0, Q("0.5") + ac) / (ac - Q("0.5")) ** 2 * I)


def J02f(T0, c2, b1, b2):
    """eq. cJ02"""
    L0 = T0.log()
    Lb = b1 * apow(L0, b2)
    return (2 / E ** 4 * (2 / PI).sqrt() * (Q("6.31") / (Q("0.5") - c2)) ** 2 * (1 / (2 * Lb ** 2)).exp()
            * apow(Lb, c2 - Q("0.5")) * D1(T0, arb(0)) / (Q("0.5") + c2))


def J0f(T0, c1, c2, a1, a2, b1, b2):
    """eq. cJ0"""
    L0 = T0.log()
    j01 = J01f(T0, c1, a1, a2)
    j02 = J02f(T0, c2, b1, b2)
    eA = 1 - a1 * apow(L0, a2 - 1)
    eB = 2 - b1 * apow(L0, b2 - 1)
    return Q("3.5") * ((1 + Q(3) / 14 * j01) * j01 * apow(T0, eA)
                       + (1 + Q(3) / 14 * j02) * j02 * apow(T0, eB)
                       + Q("12.1") * T0 * (-PI * T0 / 2).exp())


def check_conditions(T0, c1, c2, s1, s2, s3, s4, s5, a1, a2, b1, b2):
    """conditions (1)-(6) of Theorem 2 (l.284-292) + implicit ones; returns list of (name, ok)"""
    L0 = T0.log()
    out = []
    out.append(("(1) T0>=55", T0 >= 55))
    out.append(("(2) c1 in (-1,-1/2)", (c1 > -1) and (c1 < Q("-0.5"))))
    out.append(("(2) c2 in (0,1/2)", (c2 > 0) and (c2 < Q("0.5"))))
    out.append(("(3) s1 in [0,1/2)", (s1 >= 0) and (s1 < Q("0.5"))))
    out.append(("(3) s2 in (1/2,1]", (s2 > Q("0.5")) and (s2 <= 1)))
    out.append(("(3) s3 in [0,1/2)", (s3 >= 0) and (s3 < Q("0.5"))))
    out.append(("(3) s4 in (1/2,|c1|)", (s4 > Q("0.5")) and (s4 < -c1)))
    out.append(("(3) s5 in (1/2-c2,1/2)", (s5 > Q("0.5") - c2) and (s5 < Q("0.5"))))
    out.append(("(4) a1>0,a2>1,b1>0,b2>1", (a1 > 0) and (a2 > 1) and (b1 > 0) and (b2 > 1)))
    La = a1 * apow(L0, a2)
    Lb = b1 * apow(L0, b2)
    out.append(("(5) T0-a1 L0^a2 >= 2", T0 - La >= 2))
    out.append(("(5) (logT)^a2/T decr. on [T0,inf) <=> log T0 >= a2", L0 >= a2))
    out.append(("(5) a1 L0^(a2-1) >= 1", a1 * apow(L0, a2 - 1) >= 1))
    out.append(("(6) T0-b1 L0^b2 >= 2", T0 - Lb >= 2))
    out.append(("(6) (logT)^b2/T decr. <=> log T0 >= b2", L0 >= b2))
    out.append(("(6) b1 L0^(b2-1) >= 2", b1 * apow(L0, b2 - 1) >= 2))
    # implicit: Lemma 16 (chi bound) used with Re = s4+c2 <= 1 (stated only for x in [-1,1])
    out.append(("impl. s4+c2 <= 1 (Lemma chi range)", s4 + c2 <= 1))
    out.append(("impl. a1 L0^a2 >= log T0 >= 4 (used in J01)", (La >= L0) and (L0 >= 4)))
    out.append(("impl. b1 L0^b2 >= 2 log T0 >= 8 (used in J02)", (Lb >= 2 * L0) and (L0 >= 4)))
    out.append(("impl. x0>=e^4 (Lemma 14)", L0 >= 4))
    return out


def all_J(T0, c1, c2, s1, s2, s3, s4, s5, a1, a2, b1, b2):
    d = {}
    d["J0"] = J0f(T0, c1, c2, a1, a2, b1, b2)
    d["J1"] = J1(T0)
    d["J21"] = J21(T0, s1)
    d["G1"] = G1(T0, s2, s3)
    d["G2"] = G2(T0, s2, s3)
    d["G3"] = G3(T0, s4, c1, c2, a1, a2, b1, b2)
    d["G4"] = G4(T0, s5, c1, c2, a1, a2, b1, b2)
    d["G5"] = G5(T0, s4, c1, c2, a1, a2, b1, b2)
    d["G6"] = G6(T0, s5, c1, c2, a1, a2, b1, b2)
    L0 = T0.log()
    d["J22"] = d["G1"] + d["G3"] + d["G4"] + (d["G2"] + d["G5"] + d["G6"]) / L0
    d["J3"] = (eta(T0) + 2 * PI * M0) * D7(T0)
    d["J4"] = eta(T0) * D4(T0, arb(-1)) + 2 * PI * M0 * D4(T0, arb(-2))
    d["J5"] = g1f(T0, Q("0.5"), c1, a1, a2)
    d["J6"] = g2f(T0, Q("0.5"), c2, b1, b2)
    sq = d["J3"].sqrt() + d["J4"].sqrt() + d["J5"].sqrt() + d["J6"].sqrt()
    d["mixed"] = sq ** 2   # = sum J_n + 2 sum_{n<m} sqrt(J_n J_m)
    d["F1"] = d["J0"] + d["J1"] + d["J21"] + 2 * d["J22"] + d["mixed"]
    d["F2"] = d["J0"] + 2 * d["J1"] + d["mixed"]
    return d


def C1f(T0p, d):
    """C_1(T0', c, a, b) (l.369-371)"""
    lg = (T0p / 2).log()
    s = arb(0)
    for k in ("J3", "J4", "J5", "J6"):
        s += (d[k] / PI ** 2 + 2 * d["J1"] * d[k] / lg).sqrt()
    return 2 * s + d["F2"] / lg.sqrt()
