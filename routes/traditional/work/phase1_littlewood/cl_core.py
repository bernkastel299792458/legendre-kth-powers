"""Core of the height-dependent CLASSICAL zero-free region, by the method of Bellotti-Trudgian-Yang (BTY,
arXiv:2603.21490v1), with the corrections of proof/zfr_audit/bty_4.896 and per-cell certification (REPORT.md §12).

Claim (per band j of a profile Z_j, A_j = 1/Z_j):  zeta(beta + i gamma) != 0 for log gamma in (a_j, b_j] and
beta >= 1 - A_j / log gamma.  Proof: induction on s in [S0, 1] (REPORT §12.2); this module evaluates the final
contradiction inequality (REPORT §12.3, (CL)) rigorously on a v-cell [va, vb] (v = log t):

    Q := L14(eta, mu) - eta w(0) C_UP - 1e-10 eta - 1e-7 - eta^3 (P_ERR + Q_ERR v)  -  KC (1+eps) A  > 0,
    eta = (1+eps) A / v,  mu in [y va (1-eps/S0)/A, y vb / A],

where L14 = a1 F(sigma-1+eta) + a1 F(sigma-eta) - a0 F(sigma-1) is evaluated directly (G(mu) by rigorous
quadrature for the m = 0 part, Ford's bound for the large arguments), KC = a kappa w(0)/2, and y is the window
width (zfr_window).  All arithmetic is python-flint arb; floats only choose parameters.
"""
import json
import math
import os
from fractions import Fraction as Q
from flint import arb, acb, ctx

ctx.prec = 128
HERE = os.path.dirname(os.path.abspath(__file__))

# ----------------------------------------------------------------------------- fixed parameters (BTY)
THETA = arb(11338) / 10000      # BTY's theta = 1.1338 (exact rational ball)
K = 16
H = 3 * arb(10) ** 12           # RH verified for 0 < gamma <= H (Platt-Trudgian 2021)
LOGH = H.log()
T0 = arb(10) ** 10
EPS = arb('1e-100')
S0 = arb('0.5')
PI = arb.pi()
KAPPA = [Q(1), Q(-851, 859), Q(780, 859), Q(-525, 859), Q(171, 859), Q(28, 859), Q(-29, 859)]
M = 6
KAP = [arb(k.numerator) / k.denominator for k in KAPPA]
KAPPA_SUM = sum(KAPPA)                       # 433/859
KAPPA_ABS = sum(abs(k) for k in KAPPA)       # 3243/859
KAPS = arb(KAPPA_SUM.numerator) / KAPPA_SUM.denominator
KAPA = arb(KAPPA_ABS.numerator) / KAPPA_ABS.denominator
C_COEF = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
A_FRAC = [Q(sum(C_COEF[j] * C_COEF[j + k] for j in range(K + 1 - k)) * (1 if k == 0 else 2), 14912370)
          for k in range(K + 1)]
assert A_FRAC[0] == 1 and A_FRAC[1] == Q(865534, 497079) and sum(A_FRAC[1:]) == Q(2919857, 828465)
A_K = [arb(f.numerator) / f.denominator for f in A_FRAC]
A_SUM = sum(A_K[1:], arb(0))
A0, A1 = A_K[0], A_K[1]
Z_MTY = arb('5.558691')         # Mossinghoff-Trudgian-Yang: no zeros with beta >= 1 - 1/(5.558691 log gamma), gamma >= 2

# ----------------------------------------------------------------------------- global bounds of the profile
Z_MIN = arb('4.58')             # every band constant Z_j must be >= Z_MIN (asserted by the drivers)
A_MAX = 1 / Z_MIN
ETA0 = arb(((1 + 2 * EPS) * A_MAX / LOGH).upper())          # eta <= ETA0 always
SIGMA0 = arb((1 - A_MAX / (K * H + T0).log()).lower())      # sigma >= SIGMA0 always
TWO_S0 = 2 * SIGMA0 - 1
U_CUT = 54                      # Lemma 11': f(u) >= kappa eta w(0) for 0 <= u <= U_CUT (check_cl.py)

# ----------------------------------------------------------------------------- the weight w (Heath-Brown, BTY Def. 1)
_tan = THETA.tan()
_sec2 = 1 / THETA.cos() ** 2
_cot = 1 / _tan
D_SUPP = 2 * THETA * _cot


def w(u):
    """w(u) for 0 <= u <= D_SUPP (arb, acb, arb_series or acb_series argument)."""
    return _sec2 * (_sec2 * (THETA * _cot - u / 2) * (u * _tan).cos() + 2 * THETA * _cot - u
                    + (2 * THETA - u * _tan).sin() / (2 * THETA).sin() - 2 * (1 + (THETA - u * _tan).sin() / THETA.sin()))


W0 = _sec2 * (THETA * _tan + 3 * THETA * _cot - 3)       # w(0) = 5.6727875985...
KC = A_SUM * KAPS * W0 / 2                                # a kappa w(0)/2 = 5.0391...


def C_ford(nu, r):
    """|W0(z)| <= C(nu, r)|z|^-3 for Re z >= nu, |z| >= r > tan theta, W0(z) = W(z) - w(0)/z
    (Ford 2002 §7, corrected arXiv:1910.08205v4: c0 = 1/(sin th cos^3 th))."""
    nu, r = arb(nu), arb(r)
    assert r > _tan
    s, c = THETA.sin(), THETA.cos()
    c0 = 1 / (s * c ** 3)
    c1 = (THETA - s * c) * _tan ** 4
    c2 = _tan ** 3 * s ** 2
    c3 = (THETA - s * c) * _tan ** 2
    return c0 * r * (c2 * (r + 1) ** 2 * ((-2 * nu * THETA * _cot).exp() + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - _tan ** 2) ** 2


# ----------------------------------------------------------------------------- W at large real arguments
R_MIN = arb((1 / ETA0 - 3).lower())         # every large argument below is >= R_MIN (REPORT §12.3)
from flint import arb_series as _ser
W2 = 2 * w(_ser([arb(0), 1], prec=3)).coeffs()[2]          # w''(0) = -50.07...


def _w3_max(n=400):
    """Rigorous upper bound for max |w'''| on [0, d] (ball cover)."""
    m = arb(0)
    for i in range(n):
        lo, hi = D_SUPP * i / n, D_SUPP * (i + 1) / n
        b = arb(((lo + hi) / 2).mid(), ((hi - lo) / 2).upper())
        c = abs(6 * w(_ser([b, 1], prec=4)).coeffs()[3]).upper()
        if c > m:
            m = c
    return arb(m)


M3 = _w3_max()


def W_big(z):
    """Ball containing W(z) for real z >= R_MIN (REPORT §12.3; Taylor at u = 0, w'(0) = 0):
    W(z) = w(0)/z + w''(0)/z^3 + O*(max|w'''|/z^4 + 1e-50)   (the e^{-zd} tails are < 1e-55 since z d > 136)."""
    assert z.lower() >= R_MIN.lower()
    return W0 / z + W2 / z ** 3 + arb(0, (M3 / z ** 4).upper() + arb('1e-50'))


# ----------------------------------------------------------------------------- G(mu) = a1 W(1-mu) - a0 W(-mu)
def G_of_mu(mu, deriv=0):
    """int_0^d e^{mu u}(a1 e^{-u} - a0) w(u) du (deriv=1: G'(mu)); mu an arb (ball allowed)."""
    m = acb(mu)
    a0, a1 = acb(A0), acb(A1)

    def f(u, analytic):
        r = (m * u).exp() * (a1 * (-u).exp() - a0) * w(u)
        return r * u if deriv else r
    return acb.integral(f, 0, acb(D_SUPP)).real


class GTable:
    MU_MIN = Q(88, 100)

    def __init__(self):
        self.vals = {}
        self.ok = False

    def check_increasing(self, lo=Q(879, 1000), hi=Q(1), parts=121):
        for j in range(parts):
            a = lo + (hi - lo) * j / parts
            b = lo + (hi - lo) * (j + 1) / parts
            mid = (arb(a.numerator) / a.denominator + arb(b.numerator) / b.denominator) / 2
            m = arb(mid.mid(), float(b - a) / 2 * (1 + 1e-9))
            d = G_of_mu(m, deriv=1)
            if not d.lower() > 0:
                raise RuntimeError(f"G' not certified > 0 on [{a}, {b}]: {d}")
        self.ok = True

    def lower(self, mu_low):
        """Lower bound of G on [mu_low, 1]: G at a grid point j/10^4 <= mu_low (G increasing on [0.879, 1])."""
        assert self.ok
        m = float(mu_low.lower())
        assert m >= float(self.MU_MIN)
        j = math.floor(m * 10000) - 1
        g = arb(j) / 10000
        assert g.upper() <= mu_low.lower()
        if j not in self.vals:
            self.vals[j] = G_of_mu(g)
        return arb(self.vals[j].lower())


GT = GTable()


def L14_rest(eta, mu):
    """a1 F(s-1+eta) + a1 F(s-eta) - a0 F(s-1) minus its m = 0 part G(mu) (a ball), sigma = 1 - mu eta."""
    sig = 1 - mu * eta
    dd = 2 * sig - 1
    tot = A1 * W_big((sig - eta) / eta)
    for m in range(1, M + 1):
        dm = dd * m
        tot += KAP[m] * (A1 * W_big((sig - 1 + eta + dm) / eta) + A1 * W_big((sig - eta + dm) / eta)
                         - A0 * W_big((sig - 1 + dm) / eta))
    return tot


# ----------------------------------------------------------------------------- constants from check_cl.py
_CJ = os.path.join(HERE, 'cl_constants.json')


def _load():
    d = json.load(open(_CJ))
    assert d['Z_MIN'] == Z_MIN.str(20) and d['U_CUT'] == U_CUT, "cl_constants.json is for other parameters"
    return d


if os.path.exists(_CJ):
    _d = _load()
    C_UP = arb(_d['C_UP'])          # upper bound: kappa/2 sum a_k log(k/2pi) + (k=0 digamma) + tiny - 0.1186
    P_ERR = arb(_d['P_ERR'])        # Err <= eta^3 (P_ERR + Q_ERR log t)
    Q_ERR = arb(_d['Q_ERR'])
else:
    C_UP = P_ERR = Q_ERR = None


# ----------------------------------------------------------------------------- profile window
def window_y(profile, vb, V1):
    """Exact arb lower bound y for min over gamma in [H, T] of (zero-free width at gamma), T = 16 t + T0, for all t
    with log t <= vb.  profile: list of (a, b, Zstr) with a_0 <= log H; above V1 (profile top) MTY is used."""
    logT = arb((K * arb(vb).exp() + T0).log().upper())          # upper bound for log T
    cands = []
    for (a, b, Zs) in profile:
        a_lo = arb(repr(float(a))).lower()                      # band edges are the DECIMAL strings of the CSV
        b_up = arb(repr(float(b))).upper()
        if a_lo < logT.upper():                                 # band may meet [log H, log T]: include
            den = b_up if b_up <= logT.lower() else logT.upper()     # an upper bound for min(b, log T)
            cands.append((1 / arb(Zs) / arb(den)).lower())
    if logT.upper() > arb(V1).lower():
        cands.append((1 / Z_MTY / logT).lower())
    m = cands[0]
    for c in cands[1:]:
        if c < m:
            m = c
    return arb(m), logT


def cell_margin(va, vb, Zs, y, detail=False):
    """Rigorous lower bound (arb, exact) for Q on the v-cell [va, vb] of a band with constant Zs (string).
    Returns None if a hypothesis fails (mu > 1 etc.)."""
    va, vb = arb(va), arb(vb)
    if not arb(Zs) >= Z_MIN:
        return None
    A = 1 / arb(Zs)
    cap = arb((A / vb).lower())         # a smaller y (sigma closer to 1) is always allowed; keeps mu <= 1
    if cap < y:
        y = cap
    v = arb(((va + vb) / 2).mid(), ((vb - va) / 2).upper() * (1 + 1e-12))
    eta = (1 + EPS) * A / v
    mu_lo = arb((y * va / A * (1 - EPS / S0)).lower())
    mu_hi = arb((y * vb / A).upper())
    if not mu_hi <= 1 or float(mu_lo.lower()) < float(GTable.MU_MIN):
        return None
    mu = arb(((mu_lo + mu_hi) / 2).mid(), ((mu_hi - mu_lo) / 2).upper() * (1 + 1e-12))
    G = GT.lower(mu_lo)
    rest = L14_rest(eta, mu)
    R = G + rest - eta * W0 * C_UP - arb('1e-10') * eta - arb('1e-7') - eta ** 3 * (P_ERR + Q_ERR * v)
    Qm = arb((R - KC * (1 + EPS) * A).lower())
    if detail:
        return Qm, dict(G=G, rest=rest, main=KC * (1 + EPS) * A, lin=-eta * W0 * C_UP,
                        err=eta ** 3 * (P_ERR + Q_ERR * v), mu_lo=mu_lo, mu_hi=mu_hi, eta=eta)
    return Qm
