"""Shared definitions for the audit of A. Yang, PhD thesis (UNSW 2025), Chapter 3
(Littlewood zero-free region, constant 19.62).

All quantities are python-flint `arb` balls (default 160 bits).  Notation follows
the thesis: L1 = log t, L2 = log log t.  Page numbers refer to the thesis PDF
page labels (Chapter 3 = pp. 45-78).

Import from a sibling script with
    import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
so that the scripts also run under `python -I`.
"""
from fractions import Fraction
from flint import arb, acb, ctx

ctx.prec = 160

# ---------------------------------------------------------------- parameters
THETA = arb('1.1272')            # (3.10)
A1 = 1 / arb('19.62')            # target constant, p. 50
EPS = arb('1e-100')              # induction step, Prop. 3.1
K = 16                           # degree of P, (3.7)
T0 = arb(10) ** 10               # Definition 3.3
H = 3 * arb(10) ** 12            # Platt-Trudgian height
LOG_H1 = arb('56.5')             # H1 = exp(56.5), (3.5)
LOG_H2 = arb('225.4')            # H2 = exp(225.4)
B = arb('2.248')                 # lambda* = B (loglog t)^2/log t for t >= H2
E3, E4 = arb('24.2'), arb('67.19')
LOG_T4 = arb(216)                # switch n = 3 -> n = 4 inside [H1, H2]
GAMMA = arb.const_euler()
PI = arb.pi()

# ---------------------------------------------------- trigonometric polynomial
# P(x) = |sum c_k e^{ikx}|^2 / 14912370  (Section 2.4 of the thesis, same as BTY)
C_COEF = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
_D = 14912370
A_FRAC = [Fraction(sum(C_COEF[j] * C_COEF[j + k] for j in range(K + 1 - k)) * (1 if k == 0 else 2), _D)
          for k in range(K + 1)]
A_K = [arb(f.numerator) / f.denominator for f in A_FRAC]
A_SUM = sum(A_K[1:], arb(0))      # a = sum_{k>=1} a_k

# ------------------------------------------------------- Heath-Brown weight w
def tan(x): return x.tan()
def cot(x): return 1 / x.tan()
def sec(x): return 1 / x.cos()
def csc(x): return 1 / x.sin()


def w0(theta=THETA):
    """w(0) = sec^2(th) (th tan th + 3 th cot th - 3)."""
    return sec(theta) ** 2 * (theta * tan(theta) + 3 * theta * cot(theta) - 3)


def w(u, theta=THETA):
    """Definition 3.1 (u in [0, 2 th cot th])."""
    t = theta
    return sec(t) ** 2 * (sec(t) ** 2 * (t * cot(t) - u / 2) * (u * tan(t)).cos() + 2 * t * cot(t) - u
                          + (2 * t - u * tan(t)).sin() * csc(2 * t) - 2 * (1 + (t - u * tan(t)).sin() * csc(t)))


def w_acb(u, theta=THETA):
    t = acb(theta)
    tn = t.tan(); ct = 1 / tn; s2 = 1 / t.cos() ** 2
    return s2 * (s2 * (t * ct - u / 2) * (u * tn).cos() + 2 * t * ct - u
                 + (2 * t - u * tn).sin() / (2 * t).sin() - 2 * (1 + (t - u * tn).sin() / t.sin()))


def C_ford(nu, r, theta=THETA, printed=False):
    """Lemma 2.3 (Ford): |W0(z)| <= C(nu, r)|z|^-3 for Re z >= nu, |z| >= r > tan(theta).

    NOTE: thesis Lemma 2.3 (and BTY Lemma 4) print c0 = csc(th) sec^2(th).  Ford
    (arXiv:1910.08205, eq. for W_0 in Sec. 7) has c0 = 1/(sin th cos^3 th) =
    csc(th) sec^3(th), and only that value is consistent with lim |z|^3|W0(z)| =
    |w''(0)| (check_ford_W0.py).  The numbers the thesis actually uses (46, 51, 52,
    2.56, ...) match Ford's c0, so this is a transcription typo.  printed=True
    reproduces the printed (wrong) formula.
    """
    t = theta
    c0 = csc(t) * sec(t) ** (2 if printed else 3)
    c1 = (t - t.sin() * t.cos()) * tan(t) ** 4
    c2 = tan(t) ** 3 * t.sin() ** 2
    c3 = (t - t.sin() * t.cos()) * tan(t) ** 2
    assert r > tan(t)
    return c0 * r * (c2 * (r + 1) ** 2 * ((-2 * nu * t * cot(t)).exp() + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - tan(t) ** 2) ** 2

# ------------------------------------------------------------ Definition 3.3
def logKt(L1):
    """log(K t + T0) for log t = L1."""
    return L1 + (K + T0 * (-L1).exp()).log()


def sigma_star(L1, A=A1):
    LK = logKt(L1)
    return 1 - A * LK.log() / LK


def lam_star(L1):
    L2 = L1.log()
    if L1 < LOG_T4:
        return 1 / (8 - E3 / L2)
    if L1 < LOG_H2:
        return 1 / (16 - E4 / L2)
    return B * L2 ** 2 / L1


def lam3(L1): return 1 / (8 - E3 / L1.log())
def lam4(L1): return 1 / (16 - E4 / L1.log())
def lamH(L1): return B * L1.log() ** 2 / L1


SIGMA1 = sigma_star(LOG_H1)                              # (3.11)
ETA1 = (A1 + EPS) * LOG_H1.log() / LOG_H1
LAMBDA1 = lam3(LOG_H1)
LAMBDA2 = lamH(LOG_H2)

# ------------------------------------------------------- zeta bounds (Lemma 3.6)
def sigma_n(n): return 1 - arb(n) / (2 ** n - 2)
def delta_n(n): return 1 / arb((n - 1) * 2 ** n + 2)


def mu_n(n, sig):
    """exponent of Lemma 3.6 for sigma_n <= sig <= sigma_{n+1}."""
    return ((1 - sig) * 2 ** n - 1) * delta_n(n)


def C3_thesis(sig):
    """C_3 = 0.0728 * 2.50214^(14 sig/3) (Lemma 3.6)."""
    return arb('0.0728') * arb('2.50214') ** (14 * sig / 3)


def logzeta_upper(x):
    """log zeta(1 + x) <= gamma x - log x  (Ramare, (3.12)), x > 0."""
    return GAMMA * x - x.log()


def fmt(x, n=12):
    return x.str(n, radius=False)
