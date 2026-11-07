"""
rza_common.py -- shared constants and helpers for the audit of
O. Ramare, S. Zuniga Alterman, "On a Mobius double sum", arXiv:2603.25961v3, Theorem 1.2.

Everything here is Arb (python-flint).  The *paper* constants are transcribed verbatim from
the Sage block of the v3 LaTeX source (OnADoubleMobiusSum-20.tex, lines 82-546), as exact
decimals/rationals, so that the paper's own computation can be replayed exactly.
"""
import os
from flint import arb, ctx

ctx.prec = 256

ONE = arb(1)
LOG10 = arb(10).log()
EG = arb.const_euler()
PI = arb.pi()
SQ2 = arb(2).sqrt()
M = 10 ** 8                      # precision used by the paper for all Euler products
PI_M = 5761455                   # pi(10^8)
THETA_M_FLOOR = 99987730         # floor(theta(10^8))
# threshold N = 10^LOG10N where RZA Lemma 2.4/2.5 switch from sqrt- to log-bounds (paper: 10^12);
# configurable for the Helfgott-free variant of repair/ (env RZA_LOG10N); default = paper.
LOG10N = int(os.environ.get("RZA_LOG10N", "12"))
LOGN = LOG10N * LOG10
XI = 1 - 1 / LOGN                # xi = 1 - 1/log N  (paper: 1 - 1/log(10^12))
H1_STR = os.environ.get("RZA_H1", "0.010032")   # |m(t)| <= H1/log t, t >= N   (paper: FA-II Cor 1.2)
H2_STR = os.environ.get("RZA_H2", "0.0296")     # |m_2(t)| <= H2/log t, t >= N (paper: Helfgott book)
OUTDIR = os.environ.get("RZA_OUTDIR", os.path.join(os.path.dirname(os.path.abspath(__file__)), "out"))


def q(s):
    """exact decimal string -> arb (exact if representable, else tight ball)"""
    return arb(s)


def rpow(x, y):
    x = arb(x)
    return (arb(y) * x.log()).exp()


def B_kappa(k, Mv=M, piM=PI_M):
    """paper's B_kappa(M), eq. (Bk_def): Dusart pi-bound tail of sum_{p>M} p^-kappa."""
    k = arb(k)
    Mv = arb(Mv)
    L = Mv.log()
    return k / (k - 1) / rpow(Mv, k - 1) / L * (1 + 1 / L + q("2.53816") / L ** 2) - arb(piM) / rpow(Mv, k)


def C_kappa(k, Mv=M, thM=THETA_M_FLOOR):
    """paper's C_kappa(M), eq. (Ck_def): Dusart theta-bound tail of sum_{p>M} log p / p^kappa."""
    k = arb(k)
    Mv = arb(Mv)
    L = Mv.log()
    return k / (k - 1) / rpow(Mv, k - 1) * (1 + q("0.2") / L ** 2) - arb(thM) / rpow(Mv, k)


def A_delta(d):
    """Delta_1^delta = max(gamma, 1/(delta e^{gamma delta + 1}))"""
    d = arb(d)
    return EG.max(1 / (d * (EG * d + 1).exp()))


def up(x, d=4):
    """round the upper end of an arb up to d decimals (paper's Upper())"""
    from fractions import Fraction
    import math
    u = arb(x).upper()
    # exact rational of the upper endpoint
    m, e = u.man_exp()
    fr = Fraction(int(m)) * (Fraction(2) ** int(e)) if int(e) >= 0 else Fraction(int(m), 2 ** (-int(e)))
    v = math.ceil(fr * 10 ** d)
    return Fraction(v, 10 ** d)


def lo(x, d=4):
    from fractions import Fraction
    import math
    l = arb(x).lower()
    m, e = l.man_exp()
    fr = Fraction(int(m)) * (Fraction(2) ** int(e)) if int(e) >= 0 else Fraction(int(m), 2 ** (-int(e)))
    v = math.floor(fr * 10 ** d)
    return Fraction(v, 10 ** d)


def fstr(fr):
    """Fraction with power-of-10 denominator -> decimal string"""
    from fractions import Fraction
    fr = Fraction(fr)
    den = fr.denominator
    d = 0
    while 10 ** d % den:
        d += 1
        if d > 40:
            return str(float(fr))
    n = fr.numerator * (10 ** d // den)
    s = str(abs(n)).rjust(d + 1, "0")
    out = s[:-d] + "." + s[-d:] if d else s
    return ("-" if n < 0 else "") + out


def show(x, n=12):
    return arb(x).str(n, radius=False)
