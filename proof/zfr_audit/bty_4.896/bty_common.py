"""Shared definitions for the audit of Bellotti-Trudgian-Yang, arXiv:2603.21490v1.

Everything is computed in Arb ball arithmetic (python-flint).  Exact rationals
use Python's fractions.Fraction.  Notation follows the paper's LaTeX source
(source/Bellotti_Trudgian_Yang_v1.tex).
"""
from fractions import Fraction as Q
from flint import arb, acb, ctx

ctx.prec = 200

# ---------------------------------------------------------------- reporting
RESULTS = []


def check(name, ok, detail="", issue=False):
    """Record one claim.  ok: True / False / None (None = informational).
    issue=True: a statement of the paper that is false as written but whose
    downstream use is verified separately (tag ISSUE, not counted as FAIL)."""
    tag = {True: "OK", False: "FAIL", None: "INFO"}[ok]
    if issue and ok is False:
        tag = "ISSUE"
    RESULTS.append((name, tag, detail))
    print(f"[{tag:4}] {name}" + (f"  --  {detail}" if detail else ""))
    return ok


def summary():
    n_fail = sum(1 for r in RESULTS if r[1] == "FAIL")
    n_ok = sum(1 for r in RESULTS if r[1] == "OK")
    print(f"\nSUMMARY: {n_ok} OK, {n_fail} FAIL, "
          f"{sum(1 for r in RESULTS if r[1] == 'ISSUE')} ISSUE (false as stated, harmless downstream), "
          f"{sum(1 for r in RESULTS if r[1] == 'INFO')} INFO")
    for r in RESULTS:
        if r[1] in ("FAIL", "ISSUE"):
            print(f"   {r[1]}:", r[0], "--", r[2])
    return n_fail


def D(s):
    """Exact decimal string -> arb ball (exact if representable, else tight)."""
    q = Q(s)
    return arb(q.numerator) / arb(q.denominator)


def A(q):
    """Fraction -> arb."""
    q = Q(q)
    return arb(q.numerator) / arb(q.denominator)


def lt(x, y):
    """Certified x < y for balls."""
    return (y - x).lower() > 0


def fmt(x, n=12):
    return x.str(n, radius=False)


# ---------------------------------------------------------------- the weight w
theta = D("1.1338")
tan_t = theta.tan()
sec2 = 1 / theta.cos() ** 2
cot_t = 1 / tan_t
csc_t = 1 / theta.sin()
csc_2t = 1 / (2 * theta).sin()
d_supp = 2 * theta * cot_t          # support of w is [0, 2 theta cot theta]


def w(u):
    """Heath-Brown's weight (Definition 1), valid for 0 <= u <= d_supp.
    Works for arb, acb, arb_series, acb_series arguments."""
    return sec2 * (sec2 * (theta * cot_t - u / 2) * (u * tan_t).cos()
                   + 2 * theta * cot_t - u
                   + (2 * theta - u * tan_t).sin() * csc_2t
                   - 2 * (1 + (theta - u * tan_t).sin() * csc_t))


w0_formula = sec2 * (theta * tan_t + 3 * theta * cot_t - 3)

# Ford's constants (Lemma 4)
_st, _ct = theta.sin(), theta.cos()
fc0_printed = csc_t * sec2          # as printed in BTY Lemma 4 (typo)
fc0 = 1 / (_st * _ct ** 3)          # Ford (arXiv:1910.08205v4, eq. W_0) and MTY: 1/(sin th cos^3 th)
fc1 = (theta - _st * _ct) * tan_t ** 4
fc2 = tan_t ** 3 * _st ** 2
fc3 = (theta - _st * _ct) * tan_t ** 2


def C_ford(nu, r, c0=None):
    """C(nu, r) of BTY Lemma 4, with Ford's correct c0 unless c0 is given."""
    nu, r = arb(nu), arb(r)
    assert lt(tan_t, r), "Lemma 4 needs r > tan(theta)"
    c0 = fc0 if c0 is None else c0
    return c0 * r * (fc2 * (r + 1) ** 2 * ((-2 * nu * theta * cot_t).exp() + 1)
                      + fc1 * r + fc3 * r ** 3) / (r ** 2 - tan_t ** 2) ** 2


def C_ford_printed(nu, r):
    return C_ford(nu, r, fc0_printed)


def W0_closed(z):
    """Ford's closed form of W_0(z) = W(z) - w(0)/z."""
    z = acb(z)
    return fc0 * (fc2 * ((z + 1) ** 2 * (-2 * theta * cot_t * z).exp() + z ** 2 - 1)
                  - fc1 * z - fc3 * z ** 3) / (z ** 2 * (z ** 2 + tan_t ** 2) ** 2)


def W(z, **kw):
    """Laplace transform W(z) = int_0^d e^{-zu} w(u) du, rigorous (acb.integral)."""
    z = acb(z)
    return acb.integral(lambda u, a: (-z * u).exp() * w(u), 0, d_supp, **kw)


# ---------------------------------------------------------------- parameters
KAPPA = [Q(1), Q(-851, 859), Q(780, 859), Q(-525, 859), Q(171, 859),
         Q(28, 859), Q(-29, 859)]
M = 6
KAPPA_SUM = sum(KAPPA)                       # = 433/859
KAPPA_ABS = sum(abs(k) for k in KAPPA)       # = 3243/859

C_TRIG = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389,
          1896, 949, 239]
K = 16
P_NORM = 14912370


def trig_coeffs():
    """a_k of P(x) = |sum c_k e^{ikx}|^2 / 14912370 = sum a_k cos(kx)."""
    a = []
    for j in range(K + 1):
        s = sum(C_TRIG[i] * C_TRIG[i + j] for i in range(K + 1 - j))
        a.append(Q(s if j == 0 else 2 * s, P_NORM))
    return a


AK = trig_coeffs()

H = arb(3) * arb(10) ** 12
T0 = arb(10) ** 10
logH = H.log()


def params(A0):
    eta0 = A0 / logH
    sigma0 = 1 - A0 / (K * H + T0).log()
    return eta0, sigma0


A0 = 1 / D("4.896")
eta0, sigma0 = params(A0)
x0 = sigma0 - arb(1) / 2
mu0 = (1 - sigma0) / eta0 - arb(10) ** -10
