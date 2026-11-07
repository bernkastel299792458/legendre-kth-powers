"""
Rigorous (Arb / python-flint) re-implementation of the constants of
C. Bellotti, "An explicit log-free zero density estimate for the Riemann zeta-function",
arXiv:2405.12545v2 = J. Number Theory 269 (2025) 37-77,
with switches for every correction / improvement discussed in REPORT.md.

Two entry points:
  faithful(row)            -- her github code (bellotti_constants.py.txt) evaluated in Arb at t = T0,
                              including its slips; used to reproduce Table 2.
  row_bound(row, opt, N)   -- the corrected / improved bound, generic in the number system N
                              (N = ARB for rigorous enclosures, N = FLT for the float optimiser).
                              With opt = OPT_PAPER it reproduces faithful() exactly (regression test).

A "row" is a dict with keys L0, L1 (strings; 'LOG3E12' allowed for L0), a0, u, x, v, w (decimal strings),
zfr (tuple of zero-free-region names, see nu()), lam (box height / delta, Bellotti: '1').
All rigorous statements are about the *upper endpoints* of the returned arb balls.
"""
import math, functools, os
from flint import arb, acb, ctx

ctx.prec = 128

# ----------------------------------------------------------------------------------------------
# number systems
# ----------------------------------------------------------------------------------------------
class _Arb:
    name = 'arb'
    def c(self, s):            # decimal string / int -> enclosing ball
        return arb(s)
    def exp(self, a): return a.exp()
    def log(self, a): return a.log()
    def sqrt(self, a): return a.sqrt()
    def pi(self): return arb.pi()
    def maxu(self, a, b): return a.max(b)            # enclosure of max
    def minu(self, a, b):                            # a ball whose upper end bounds min(a,b) from above
        return a if a.upper() <= b.upper() else b
    def surely_ge(self, a, b):                       # True only if a >= b is certain
        a, b = arb(a), arb(b)
        return bool(a >= b)
    def up(self, a): return arb(a).upper()
    def lo(self, a): return arb(a).lower()
    def tofloat(self, a): return float(arb(a).mid())
ARB = _Arb()

class _Flt:
    name = 'float'
    def c(self, s): return float(s)
    def exp(self, a): return math.exp(a) if a < 700 else float('inf')
    def log(self, a): return math.log(a)
    def sqrt(self, a): return math.sqrt(a)
    def pi(self): return math.pi
    def maxu(self, a, b): return max(a, b)
    def minu(self, a, b): return min(a, b)
    def surely_ge(self, a, b): return a >= b
    def up(self, a): return a
    def lo(self, a): return a
    def tofloat(self, a): return float(a)
FLT = _Flt()

LOG3E12_ARB = arb(3 * 10**12).log()

def Lof(s, N=ARB):
    if s == 'LOG3E12':
        return LOG3E12_ARB if N is ARB else math.log(3e12)
    return N.c(s)

# ----------------------------------------------------------------------------------------------
# zero-free regions  nu(T) = width:  zeros satisfy 1 - beta >= nu(gamma)
# ----------------------------------------------------------------------------------------------
LOG_1p88E14 = math.log(1.88e14)   # Ford Thm 3 (as read by MTY 2024, Res. Number Theory) needs t >= 1.88e14

_CLLOC = None
CL_LOCAL_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase1_littlewood', 'zfr_classical_local.csv')

def _cl_local_bands():
    """bands (a, b, Z1) of work/phase1_littlewood/zfr_classical_local.csv (our Theorem C, BTY method, refereed inputs):
    zeta(s) != 0 for sigma >= 1 - 1/(Z1 log t) when log t in (a, b]."""
    global _CLLOC
    if _CLLOC is None:
        import csv
        rows = list(csv.DictReader(open(CL_LOCAL_PATH, newline='')))
        assert all(r['status'] == 'proved' for r in rows)
        _CLLOC = [(r['logt_lo'], r['logt_hi'], r['Z1']) for r in rows]
        for i in range(1, len(_CLLOC)):
            assert _CLLOC[i][0] == _CLLOC[i - 1][1], 'gap in local bands'
    return _CLLOC

def _cl_local_nu(L, N):
    """rigorous LOWER bound, valid for every T with log T <= sup(L), of  inf_{3e12 <= gamma <= T} 1/(Z1(gamma) log gamma)
    = min over bands meeting (log 3e12, log T] of 1/(Z_j min(b_j, log T)).  Returned as an exact point (lower bound)."""
    B_ = _cl_local_bands()
    if N is ARB:
        Lhi = arb(arb(L).upper())
        if not bool(Lhi <= arb(B_[-1][1])):
            raise ValueError('cl_local: log T above the last band')
        best = None
        for a, b, Z in B_:
            if bool(arb(a) > Lhi):             # exact decimal edge vs ball: skip only if the band is certainly above log T;
                continue                       # a band with a == log T is kept (extra bands only lower the min; conservative)
            val = 1 / (arb(Z) * arb(b).min(Lhi))
            best = val if best is None else best.min(val)
        return arb(best.lower())
    Lf = float(L)
    if Lf > float(B_[-1][1]):
        raise ValueError('cl_local: log T above the last band')
    return min(1 / (float(Z) * min(float(b), Lf)) for a, b, Z in B_ if float(a) < Lf)

_LWLOC = None
LW_LOCAL_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase1_littlewood', 'zfr_local_v2.csv')

def _lw_local_bands():
    """bands (a, b, Z2) of work/phase1_littlewood/zfr_local_v2.csv (our Theorem Z v2, refereed inputs, reviewed):
    zeta(s) != 0 for sigma >= 1 - log log t/(Z2 log t) when log t in (a, b]."""
    global _LWLOC
    if _LWLOC is None:
        import csv
        rows = list(csv.DictReader(open(LW_LOCAL_PATH, newline='')))
        assert all(r['status'] == 'proved' for r in rows)
        _LWLOC = [(r['logt_lo'], r['logt_hi'], r['Z2']) for r in rows]
        for i in range(1, len(_LWLOC)):
            assert _LWLOC[i][0] == _LWLOC[i - 1][1], 'gap in local Littlewood bands'
    return _LWLOC

def _lw_local_nu(L, N):
    """rigorous LOWER bound, for every T with log T <= sup(L), of inf_{3e12 <= gamma <= T} width(gamma):
    min over bands meeting (log 3e12, log T] of log(m)/(Z2 m), m = min(b, log T)  (log l / l decreases for l > e);
    zeros with log gamma in (log 3e12, 28.73] (below the first band) are covered by MTY: 1/(5.558691*28.73)."""
    B_ = _lw_local_bands()
    if N is ARB:
        Lhi = arb(arb(L).upper())
        if not bool(Lhi <= arb(B_[-1][1])):
            raise ValueError('lw_local: log T above the last band')
        best = 1 / (arb('5.558691') * arb(B_[0][0]).min(Lhi))
        for a, b, Z in B_:
            if bool(arb(a) > Lhi):             # exact edges; a band starting at log T is kept (conservative)
                break
            m = arb(b).min(Lhi)
            best = best.min(m.log() / (arb(Z) * m))
        return arb(best.lower())
    Lf = float(L)
    best = 1 / (5.558691 * min(float(B_[0][0]), Lf))
    for a, b, Z in B_:
        if float(a) >= Lf:
            break
        m = min(float(b), Lf)
        best = min(best, math.log(m) / (float(Z) * m))
    return best

def nu_region(name, L, N):
    """width of one region at height T = e^L (L may be a ball)."""
    if name == 'lw_local':
        return _lw_local_nu(L, N)
    if name == 'cl_local':
        return _cl_local_nu(L, N)
    if name.startswith('cl'):            # classical 1/(Z log t);  'cl5.558691' MTY 2024, 'cl4.896' BTY 2026 preprint
        return 1 / (N.c(name[2:]) * L)
    if name == 'ford':                   # Bellotti (2.2) = Yang JMAA 534 (2024) eq. (1.4), Ford Thm 3 + HPY 0.618
        J = L / 6 + N.log(L) + N.log(N.c('0.618'))
        return (N.c('0.04962') - N.c('0.0196') / (J + N.c('1.15'))) / (J + N.c('0.685') + N.c('0.155') * N.log(L))
    if name.startswith('lw'):            # Littlewood  log log t / (Z log t); 'lw21.233' Yang JMAA 2024
        return N.log(L) / (N.c(name[2:]) * L)
    if name.startswith('kv'):            # Korobov-Vinogradov 1/(Z log^{2/3} t (log log t)^{1/3}); 'kv53.989' Bellotti JMAA 2024
        return 1 / (N.c(name[2:]) * N.exp(N.c(2) / 3 * N.log(L)) * N.exp(N.log(N.log(L)) / 3))
    raise ValueError(name)

def nu(zfr, L, N):
    """max of the admissible regions at T = e^L.  Ford is only used for L >= 33 (> log 1.88e14)."""
    best = None
    for name in zfr:
        if name == 'ford' and not N.surely_ge(L, N.c(33)):
            continue
        val = nu_region(name, L, N)
        best = val if best is None else N.maxu(best, val)
    return best

# ----------------------------------------------------------------------------------------------
# rigorous one-dimensional integrals (arb), cached
# ----------------------------------------------------------------------------------------------
def _int_analytic(f, a, b):
    return acb.integral(f, a, b).real

def _tail_exp(Y, p, c):
    """upper bound of int_Y^inf y^p e^{-c y} dy for p <= 0 (y^p <= Y^p):  Y^p e^{-cY}/c."""
    return Y ** p * (-c * Y).exp() / c

@functools.lru_cache(maxsize=None)
def gamma_abs_int(sig_lo, sig_hi, t0, t1, nt=1000, nsig=None):
    """rigorous upper bound of  sup_{sigma in [sig_lo,sig_hi]} int_{t0}^{t1} |Gamma(sigma+it)| dt   (strings in)."""
    slo, shi = arb(sig_lo), arb(sig_hi)
    if nsig is None:
        nsig = max(1, int(math.ceil(float((shi - slo).mid()) / 0.002)))
    T0, T1 = arb(t0), arb(t1)
    best = arb(0)
    for i in range(nsig):
        sa = slo + (shi - slo) * i / nsig
        sb = slo + (shi - slo) * (i + 1) / nsig
        sball = sa.union(sb)
        tot = arb(0)
        h = (T1 - T0) / nt
        smid = (sa + sb) / 2; srad = (sb - sa) / 2
        for j in range(nt):
            ta = T0 + h * j
            tb = T0 + h * (j + 1)
            zbox = acb(sball, ta.union(tb))
            zm = acb(smid, (ta + tb) / 2)
            # mean-value enclosure: |Gamma(z)| <= |Gamma(zm)| + sup_box |Gamma'(z)| * |z - zm|
            dG = zbox.gamma() * zbox.digamma()
            rad = (srad ** 2 + (h / 2) ** 2).sqrt()
            val = arb(zm.gamma().abs_upper()) + arb(dG.abs_upper()) * rad
            direct = arb(zbox.gamma().abs_upper())
            tot += h * (val if val.upper() < direct.upper() else direct)
        best = best.max(tot)
    return arb(best.upper())

def S_far(y, a0):      # Stirling majorant used for |Delta| >= 1 (her c4 integrand, incl. sqrt(2pi))
    return (2 * arb.pi()).sqrt() * ((arb('1.5') - 2 * a0) * y.log() - arb.pi() * y / 2 + 1 / (6 * y)).exp()

@functools.lru_cache(maxsize=None)
def consts(a0s, L0s):
    """All alpha0-dependent numerical constants, rigorous (upper bounds, as arb balls).
    'paper_*' are the values her code computes (enclosures of her quad integrals / her printed numbers)."""
    a0 = arb(a0s)
    L0 = LOG3E12_ARB if L0s == 'LOG3E12' else arb(L0s)
    pi = arb.pi(); sq = (2 * pi).sqrt()
    k = arb(27) / 164
    out = {}
    # --- her integrals (code), as enclosures ---
    out['paper_G1'] = arb('0.632121') + arb(1).gamma_upper(3 - 2 * a0)                      # 0.632121 + int_1^inf y^{2-2s} e^{-y}
    fIS = lambda y, an: (((arb('1.5') - 2 * a0) * y.log(analytic=an)) - pi * y / 2 + 1 / (6 * y)).exp()
    IS = _int_analytic(fIS, 1, 60) + _tail_exp(arb(60), arb(0), pi / 2) * arb(1).exp()
    out['IS'] = sq * IS                                                                      # sqrt(2pi) int_1^inf S/sqrt(2pi)
    # iJ1 = int_3^inf (2y)^k e^{-pi y/2} y^{1-2s}
    p = k + 1 - 2 * a0
    b = pi / 2
    out['paper_iJ1'] = arb(2) ** k * b ** (-(p + 1)) * (3 * b).gamma_upper(p + 1)
    fJ3 = lambda y, an: (k * (y / 3 + 1).log(analytic=an) - pi * y / 2 + (1 - 2 * a0) * y.log(analytic=an)).exp()
    out['paper_iJ3'] = _int_analytic(fJ3, 1, 60) + _tail_exp(arb(60), arb(0), pi / 2) * arb(21) ** k
    gm = arb('0.447') * L0
    fI = lambda y, an: (k * (1 + y / gm).log(analytic=an) - pi * y / 2 - a0 * y.log(analytic=an)).exp()
    out['paper_integ'] = _int_analytic(fI, 1, 60) + _tail_exp(arb(60), arb(0), pi / 2) * (1 + 60 / gm) ** k
    # --- verified constants (our derivation) ---
    out['S1'] = S_far(arb(1), a0)                                                             # S(1)
    # c1: sup over sigma' = 1/2-beta in [-1/2, 1/2-a0] of int_0^1 |Gamma|   (her 1.808)
    out['G01_c1'] = gamma_abs_int('-0.5', _dec(0.5, a0s, 1), '0', '1')
    # c5: sigma' = 3/2 - b_r - b_s in [-1/2, 3/2 - 2a0]: int_{-1}^{1} (her 3.62642) and int_{-inf}^{inf} (her 4.05206)
    s5hi = _dec(1.5, a0s, 2)
    g01 = gamma_abs_int('-0.5', s5hi, '0', '1')
    out['G11_c5'] = 2 * g01
    g140 = gamma_abs_int('-0.5', s5hi, '1', '40', nt=3900, nsig=4)
    # tail t>=40 via Gamma(z)=Gamma(z+1)/z and Lemma 2.11 (Re(z+1) in (0,1)): <= sqrt(2pi) t^{s-1/2} e^{-pi t/2 + 1/(6t)}
    tail40 = sq * _tail_exp(arb(40), arb(0), pi / 2) * (arb(1) / 240).exp()
    out['Gall_c5'] = 2 * (g01 + g140 + tail40)
    # J-integrals (c5), verified versions
    e18 = (arb(1) / 18).exp(); e6 = (arb(1) / 6).exp()
    q = k + 1 - 2 * a0
    I3 = b ** (-(q + 1)) * (3 * b).gamma_upper(q + 1)                     # int_3^inf t^{k+1-2a0} e^{-pi t/2}
    out['J1v'] = arb('66.7') * sq * e18 * I3                                 # |t+a| <= |t|
    out['J4v'] = arb('66.7') * sq * e18 * arb(2) ** k * I3                   # |t+a| <= 2t
    out['J2v'] = arb('1.461') * out['Gall_c5']
    r1 = 1 - 2 * a0
    out['J31v'] = arb('66.7') * sq * e6 * b ** (-(r1 + 1)) * b.gamma_upper(r1 + 1)          # int_1^inf t^{1-2a0}e^{-pi t/2}
    fJ33 = lambda y, an: (k * (1 + y / 3).log(analytic=an) + (1 - 2 * a0) * y.log(analytic=an) - pi * y / 2 + 1 / (6 * y)).exp()
    out['J33v'] = arb('66.7') * sq * (_int_analytic(fJ33, 1, 60) + _tail_exp(arb(60), arb(0), pi / 2) * arb(21) ** k * e6)
    out['J32v'] = arb('66.7') * (arb(4) / 3) ** k * out['G11_c5']
    # c1 verified: I2 <= gamma^k [66.7 (1+1/gm)^k G01 + 66.7 sqrt(2pi) int_1^inf (1+t/gm)^k t^{-a0} e^{-pi t/2+1/(6t)}]
    fI2 = lambda y, an: (k * (1 + y / gm).log(analytic=an) - a0 * y.log(analytic=an) - pi * y / 2 + 1 / (6 * y)).exp()
    int2 = _int_analytic(fI2, 1, 60) + _tail_exp(arb(60), arb(0), pi / 2) * (1 + 60 / gm) ** k * e6
    out['I2coef_v'] = arb('66.7') * (1 + 1 / gm) ** k * out['G01_c1'] + arb('66.7') * sq * int2
    out['gm'] = gm
    # same with gamma > 3e12 (Platt-Trudgian: every zero with beta > 1/2 has gamma > 3e12)
    g3 = arb(3 * 10**12)
    fI2b = lambda y, an: (k * (1 + y / g3).log(analytic=an) - a0 * y.log(analytic=an) - pi * y / 2 + 1 / (6 * y)).exp()
    int2b = _int_analytic(fI2b, 1, 60) + _tail_exp(arb(60), arb(0), pi / 2) * (1 + 60 / g3) ** k * e6
    out['I2coef_v3'] = arb('66.7') * (1 + 1 / g3) ** k * out['G01_c1'] + arb('66.7') * sq * int2b
    # Hiary-Patel-Yang |zeta(1/2+i tau)| <= 0.618 tau^{1/6} log tau (tau >= 3):  for tau = gamma + t, gamma >= 3e12,
    # tau^{1/6} log tau <= gamma^{1/6} log gamma (1+t/g3)^{1/6} (1 + log(1+t/g3)/log g3)
    lg3 = g3.log()
    fI2h = lambda y, an: ((1 + y / g3).log(analytic=an) / 6 - a0 * y.log(analytic=an) - pi * y / 2 + 1 / (6 * y)).exp() * (1 + (1 + y / g3).log(analytic=an) / lg3)
    int2h = _int_analytic(fI2h, 1, 60) + _tail_exp(arb(60), arb(0), pi / 2) * (1 + 60 / g3) ** (arb(1) / 6) * 2 * e6
    out['I2coef_hpy'] = arb('0.618') * ((1 + 1 / g3) ** (arb(1) / 6) * (1 + (1 + 1 / g3).log() / lg3) * out['G01_c1'] + sq * int2h)
    # P_h = prod_p (1 + (sqrt p - 1)/p^2)
    out['Ph'] = _Ph()
    for kk in list(out):
        out[kk] = arb(out[kk])
    return out

def _dec(c, a0s, m):
    """exact decimal string of c - m*a0 (a0 given as decimal string)."""
    from decimal import Decimal
    return str(Decimal(str(c)) - m * Decimal(a0s))

@functools.lru_cache(maxsize=1)
def _Ph(P=100000):
    sieve = bytearray([1]) * (P + 1); sieve[0] = sieve[1] = 0
    for i in range(2, int(P ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    prod = arb(1)
    for p in range(2, P + 1):
        if sieve[p]:
            ap = arb(p)
            prod *= 1 + (ap.sqrt() - 1) / (ap * ap)
    # tail: prod_{p>P}(1+p^{-3/2}) <= exp(sum_{n>P} n^{-3/2}) <= exp(2/sqrt(P))
    prod *= (2 / arb(P).sqrt()).exp()
    return arb(prod.upper())

# ----------------------------------------------------------------------------------------------
# harmonic numbers (rigorous balls)
# ----------------------------------------------------------------------------------------------
_H = [arb(0)]
_HMAX = 20000
_EULER = arb.const_euler()
def H(n):
    """H_n as a ball for n <= 20000; for larger n an upper bound log n + gamma + 1/(2n) (valid for n >= 1).
    Only used where an upper bound is needed (terms H(J1-1)+H(J1) with J1 large; subtracted H's are small)."""
    if n > _HMAX:
        an = arb(n)
        return arb((an.log() + _EULER + 1 / (2 * an)).upper())
    while len(_H) <= n:
        _H.append(_H[-1] + arb(1) / len(_H))
    return _H[n]
_HF = [0.0]
def HF(n):
    if n > _HMAX:
        return math.log(n) + 0.5772156649015329 + 1 / (2 * n)
    while len(_HF) <= n:
        _HF.append(_HF[-1] + 1.0 / len(_HF))
    return _HF[n]

# ----------------------------------------------------------------------------------------------
# option sets
# ----------------------------------------------------------------------------------------------
OPT_PAPER = dict(count='paper', d4='code', mono=False, g5='paper', d2='code', consts='paper',
                 b12='code', yfac=False, g1=False, rng='T0', gmin='0.447L')
# corrections only (her parameters, her zero-free regions, her gamma > 0.447 log T):
OPT_CORR = dict(count='fixed', d4='rza', mono=True, g5='fixed', d2='fixed', consts='verified',
                b12='code', yfac=False, g1=False, rng='full', gmin='0.447L')
# corrections + improvements (used for re-optimisation); lam (box height) is a row field:
OPT_IMPR = dict(OPT_CORR, b12='exact', yfac=True, g1=True, gmin='3e12')

# ----------------------------------------------------------------------------------------------
# the bound
# ----------------------------------------------------------------------------------------------
def _d1(lY, N):   # Lemma 2.6 / CHT19:  sum_{n<=Y} d^2(n) <= d1(Y) Y log^3 Y, as coded (rounded-up D2..D4)
    return (1 / N.pi() ** 2 + N.c('0.746') / lY + N.c('0.825') / lY ** 2 + N.c('0.462') / lY ** 3
            + N.c('9.73') * N.exp(-lY / 4) / lY ** 2 + N.c('0.73') * N.exp(-lY / 2) / lY ** 3)

def _D2fixed(lY, N):
    """rigorous bound for sum_{n<=Y} d(n)^2/n  (Y = e^{lY} >= 2) by partial summation of Lemma 2.6 (first form)."""
    D1, D2, D3, D4 = 1 / N.pi() ** 2, N.c('0.746'), N.c('0.825'), N.c('0.462')
    FY = D1 * lY ** 3 + D2 * lY ** 2 + D3 * lY + D4 + N.c('9.73') * N.exp(-lY / 4) * lY + N.c('0.73') * N.exp(-lY / 2)
    integ = D1 * lY ** 4 / 4 + D2 * lY ** 3 / 3 + D3 * lY ** 2 / 2 + D4 * lY + N.c('153.62') + N.c('1.0325')
    return FY + N.c('0.5') + integ
    # 153.62 >= 9.73 * 2^{-1/4}(4 log 2 + 16) = 153.588..., 1.0325 >= 0.73*sqrt(2) = 1.03238...

def _RZA(u, v, N):
    tau = v / u
    return N.c('3.09') * (N.c('1.084') * (tau + 1) + N.c('1.301') * (1 + tau ** 2) - N.c('0.116')) / (tau - 1)

def b12(row, opt, N):
    a0 = N.c(row['a0']); lam = N.c(row.get('lam', '1'))
    if opt['b12'] == 'code':       # her code (circle radius sqrt2 (1-sigma), i.e. the square |t-T|<=1-alpha)
        r = N.sqrt(N.c(2)) * (1 - a0)
        b2 = (r * 2 * N.c('4.7908') / 4 + 2 * r * N.log(1 + 1 / r) * (4 / N.pi() - 1) / (1 + 2 * r)
              + 2 * r * N.c('2.6908') + 2 + 64 * r ** 2 / (1 + 2 * r) ** 2)
        t = N.exp(Lof(row['L0'], N))
        lt = N.log(t + r); L0 = Lof(row['L0'], N)
        b1 = (2 * N.sqrt(N.c(2)) * lt / 4 + 32 * r ** 2 / (1 + 2 * r) ** 2 * lt - 16 * r ** 2 / (1 + 2 * r) ** 2) / L0
        if str(row.get('lam', '1')) != '1':
            raise ValueError("b12='code' only for lam=1")
        return b1, b2, r
    # exact: box of height lam*delta inside the circle |s-(1+it_m)| <= rho*delta, rho = sqrt(1+lam^2/4)
    rho = N.sqrt(1 + lam ** 2 / 4)
    r0 = rho * (1 - a0)
    f0 = N.c('0.5'); fr = 1 / (2 * (1 + 2 * r0)) + 32 * r0 ** 2 / (1 + 2 * r0) ** 2
    b1 = rho * N.maxu(f0, fr)
    b2 = (2 * r0 * N.c('4.7908') / (4 + 8 * r0) + 2 * r0 * (4 / N.pi() - 1) * N.log(1 + 1 / r0)
          + N.c('5.3816') * r0 + 16 * r0 ** 2 * (4 - r0) / (1 + 2 * r0) ** 2 + 2)
    return b1, b2, r0

def Hn_fixed(lam, K, J1, g, IS, S1, dmax, N):
    """per-representative sum, units X^{2 delta}/delta (see REPORT.md, sec. 1.4)."""
    half = N.c('0.5')
    def m(d):
        if d == 0:
            return K * half
        return N.minu(K * half, 1 / (lam * d))
    dstar = 2 / (K * lam)
    tot = K * half                      # s = r
    j = 1
    if J1 >= 1 and N.surely_ge(half, N.up(dstar) if N is ARB else dstar):
        # exact sup over theta of m(theta)+m(1-theta) when d* <= 1/2:  K/2 + 1/(lam (1-d*))  (REPORT 1.4)
        tot = tot + K * half + 1 / (lam * (1 - dstar))
        j = 2
    while j <= J1 and not N.surely_ge(N.c(j - 1), N.up(dstar) if N is ARB else dstar):
        tot = tot + m(j - 1) + m(N.c(j) - half)
        j += 1
    if j <= J1:                         # convex region: sum_{i=j}^{J1} (1/(i-1)+1/i)/lam
        if N is ARB:
            tot = tot + ((H(J1 - 1) - H(j - 2)) + (H(J1) - H(j - 1))) / lam
        else:
            tot = tot + ((HF(J1 - 1) - HF(j - 2)) + (HF(J1) - HF(j - 1))) / lam
    return g * tot + 2 * dmax * S1 + 2 / lam * IS

def piece(row, opt, L, N, C):
    """bound on the sub-range L (ball in ARB mode, float in FLT mode).  C = constants (converted to N).
    returns dict with all intermediate quantities; 'C' is the bound for this piece."""
    a0 = N.c(row['a0']); u = N.c(row['u']); x = N.c(row['x']); v = N.c(row['v']); w = N.c(row['w'])
    lam = N.c(row.get('lam', '1'))
    zfr = row['zfr']
    pi = N.pi(); sq2pi = N.sqrt(2 * pi)
    k = N.c(27) / 164
    L0 = Lof(row['L0'], N); L1 = N.c(row['L1'])
    if opt['rng'] == 'T0':
        L = L0
    if opt.get('v2'):
        return piece_v2(row, opt, L, N, C)
    if opt.get('hl'):
        return piece_hl(row, opt, L, N, C)
    out = {}
    # zero-free region at this height and at the top of the row
    nuT = nu(zfr, L, N)
    out['nu'] = nuT
    Z = 1 / (nuT * L)
    out['Z'] = Z
    # --- d4 ---
    tau = v / u
    rza = _RZA(u, v, N)
    if opt['d4'] in ('code', 'paper'):
        if opt['d4'] == 'code':
            d3 = 4 / ((v - u) ** 2 * L ** 2) * (1 + N.c('1.0061') * (u * L + N.c('1.333') + 11 / N.sqrt(u * L * N.exp(u * L)))) / L
        else:   # Lemma 3.2 + (3.6) as printed: sum Psi^2 <= d3 N / log T
            d3 = 4 * N.c('1.0061') * (u * L + N.c('1.333') + 11 / N.sqrt(u * L * N.exp(u * L)) + 1) / ((v - u) ** 2 * L)
        d4 = rza * (u + v) / (v - u) + d3 / (N.exp(N.exp((u + v - x) * L)) * L) + d3 / L * (2 + (x - (u + v)) * L)
        out['d3'] = d3
    else:       # 'rza': sum Psi^2/n e^{-n/X} <= U/X + K (log X - gamma + 1/X), K = rza/log(V/U)  (REPORT 1.6)
        d4 = N.exp((u - x) * L) + rza * x / (v - u)
    out['d4'] = d4
    # --- d5 = |G(1)| log W ---
    wL = w * L
    d5 = N.c('1.0061') * (wL + N.c('1.333') + N.c('3.95') * N.exp(-wL / 2)) / wL
    out['d5'] = d5
    # --- per-representative sum ---
    g = C['paper_G1'] if not opt['g1'] else N.c(1)
    if opt['count'] == 'paper':
        nuT1 = nu(zfr, L1, N) if opt['rng'] != 'T0' else nu(zfr, N.c(row['L1']), N)
        Hn = g / 2 + g * N.c('1.12') * N.log(1 / nuT1) + N.c('2.4') * C['IS']
        K = N.c(1)
    else:
        kappa = 2 * nuT * x * L
        if N.surely_ge(N.lo(kappa), 1):
            K = N.c(1)
        else:
            kl = N.lo(kappa)
            if N is ARB:
                kl = arb(kl)
                if not bool(kl > 0):
                    raise ValueError('kappa <= 0')
            K = N.exp(kl - 1) / kl
        if not opt['mono']:
            K = N.c(1)
        nlo = N.lo(nuT) if opt['rng'] != 'T0' else N.lo(nu(zfr, L1, N))   # T0-mode: harmonic range from nu(T1), as she does
        Jup = 1 / (lam * nlo)
        J1 = int(math.floor(N.tofloat(N.up(Jup)))) + 2
        Hn = Hn_fixed(lam, K, J1, g, C['IS'], C['S1'], 1 - a0, N)
        out['J1'] = J1
    out['K'] = K
    out['Hn'] = Hn
    if opt['yfac']:
        Ycoef = 1 + N.exp(-2 * nuT * ((x - u) * L + 2 * N.log(L)))
    else:
        Ycoef = N.c(2)
    out['Ycoef'] = Ycoef
    A = Ycoef * d4 * d5 / w * Hn
    out['A'] = A
    # --- b1, b2 ---
    b1, b2, r0 = b12(row, opt, N)
    out['b1'], out['b2'], out['r0'] = b1, b2, r0
    # --- c5 ---
    if opt['g5'] == 'paper':
        Ghalf = d5 * N.exp(wL) / wL
    else:
        Ghalf = 16 * C['Ph'] * N.exp(wL) / wL ** 2
    e5 = N.c('1.5') - 2 * a0
    XY = N.exp(x * e5 * L) + N.exp(e5 * (u * L - 2 * N.log(L)))
    if opt['consts'] == 'paper':
        pre = sq2pi * N.exp(1 / (6 * (2 * a0 - N.c('1.5')))) * N.c('66.7')
        J1b = pre * C['paper_iJ1']; J31b = pre * C['paper_iJ3']
        Jsum = 2 * J1b + N.c('1.461') * N.c('4.05206') + (2 * J31b + N.c('66.7') * N.c('1.0486') * N.c('3.62642')) * N.exp(k * L)
    else:
        Jsum = C['J1v'] + C['J4v'] + C['J2v'] + (C['J31v'] + C['J32v'] + C['J33v']) * N.exp(k * L)
    c5 = d4 / (2 * pi) * Ghalf * XY * Jsum
    out['c5'] = c5
    # --- c1 ---
    lVW = (v + w) * L
    if opt['d2'] == 'code':
        D2VW = _d1((w + x) * L, N) * (1 / lVW + N.c('0.25')) * lVW ** 4       # code: argument-order slip
        powS1 = (u + w) ** 4 * L ** 4                                            # code/paper (3.10): (u+w)^4
        D2S1 = _d1((w + x) * L, N) * (1 / lVW + N.c('0.25')) * powS1
    else:
        D2VW = _D2fixed(lVW, N)
        D2S1 = D2VW
    if opt['consts'] == 'paper':
        gm = N.c('0.447') * L
        S1t = D2S1 * sq2pi * N.exp(1 / (6 * L)) * N.exp(x * (1 - a0) * L) / (N.exp(N.c('0.447') * pi * L / 2) * (N.c('0.447') * L) ** (a0 - N.c('0.5')))
        I2I3 = 2 * (N.c('122.092') + N.exp(N.c(1) / 6) * sq2pi * N.c('66.7') * C['paper_integ'])
        SU = D2VW / lVW ** 4 * I2I3 / (2 * pi) * (v + w) ** 4 * N.exp(((v + w) / 2 + x * (N.c('0.5') - a0) + k) * L) * L ** 4
        tail = N.c('1e-30')
    else:
        gm = N.c('0.447') * L if opt.get('gmin', '0.447L') == '0.447L' else N.c(3 * 10**12)
        I2c = C['I2coef_v'] if opt.get('gmin', '0.447L') == '0.447L' else C['I2coef_v3']
        S1t = D2S1 * sq2pi * N.exp(1 / (6 * gm)) * N.exp(x * (1 - a0) * L - pi * gm / 2) * N.exp((N.c('0.5') - a0) * N.log(gm))
        E312 = N.c('66.7') * sq2pi * N.exp(N.c(1) / 6) * N.exp((k - a0) * N.log(3 + gm)) * 2 / pi * N.exp(-pi * (3 + gm) / 2)
        E313 = N.c('1.461') * sq2pi * N.exp(N.c(1) / 6) * 6 * N.exp(-a0 * N.log(gm - 3)) * N.exp(-pi * (gm - 3) / 2)
        Itot = 2 * I2c * N.exp(k * L) + E312 + E313
        SU = D2VW * N.exp(lVW / 2) * N.exp(x * (N.c('0.5') - a0) * L) * Itot / (2 * pi)
        U = N.exp(u * L); cc = L ** 2 / U
        tail = 4 * N.exp(-cc * (U - 1)) * ((U - 1) / cc + 1 / cc ** 2)
    c1 = N.exp(-L ** 2 / N.exp(u * L)) - S1t - SU - tail
    out['c1'] = c1; out['S1t'] = S1t; out['SU'] = SU
    den = c1 ** 2 - c5
    out['den'] = den
    Cv = A * (b1 + b2 * Z) / den
    out['C'] = Cv
    return out

# ----------------------------------------------------------------------------------------------
# high-L evaluation (opt['hl'] = True): the same bound, algebraically identical, but written so that
# ball evaluation over wide L-ranges has little dependency blow-up: every product of exponentials is
# one exponential of a net exponent, d5 = 1.0061(1 + .../(wL)), Z = 1/(nu L) with nu*L computed directly.
# ----------------------------------------------------------------------------------------------
def nuL_region(name, L, N):
    """nu(e^L) * L, written without cancelling L's."""
    if name == 'lw_local':                      # lower bound: nu_lo(L_hi) * L_lo
        if N is ARB:
            return arb((arb(arb(L).lower()) * _lw_local_nu(L, N)).lower())
        return L * _lw_local_nu(L, N)
    if name == 'cl_local':                      # lower bound: nu_lo(L_hi) * L_lo
        if N is ARB:
            return arb((arb(arb(L).lower()) * _cl_local_nu(L, N)).lower())
        return L * _cl_local_nu(L, N)
    if name.startswith('cl'):
        return 1 / N.c(name[2:])
    if name.startswith('lw'):
        return N.log(L) / N.c(name[2:])
    if name.startswith('kv'):
        lL = N.log(L)
        return N.exp(lL / 3 - N.log(lL) / 3) / N.c(name[2:])
    if name == 'ford':
        return nu_region('ford', L, N) * L
    raise ValueError(name)

def nuL(zfr, L, N):
    best = None
    for name in zfr:
        if name == 'ford' and not N.surely_ge(L, N.c(33)):
            continue
        val = nuL_region(name, L, N)
        best = val if best is None else N.maxu(best, val)
    return best


def piece_hl(row, opt, L, N, C):
    assert opt['count'] == 'fixed' and opt['d4'] == 'rza' and opt['g5'] == 'fixed' and opt['d2'] == 'fixed' and opt['consts'] == 'verified'
    a0 = N.c(row['a0']); u = N.c(row['u']); x = N.c(row['x']); v = N.c(row['v']); w = N.c(row['w'])
    lam = N.c(row.get('lam', '1'))
    zfr = row['zfr']
    pi = N.pi(); sq2pi = N.sqrt(2 * pi)
    k = N.c(27) / 164
    out = {}
    nL = nuL(zfr, L, N)                       # nu(T) * log T
    out['nuL'] = nL
    Z = 1 / nL
    out['Z'] = Z
    nlo = N.lo(nL) / N.up(L) if N is ARB else nL / L      # lower bound of nu(T) on the range
    out['nu'] = nlo
    rza = _RZA(u, v, N)
    d4 = N.exp((u - x) * L) + rza * x / (v - u)
    out['d4'] = d4
    wL = w * L
    d5 = N.c('1.0061') * (1 + (N.c('1.333') + N.c('3.95') * N.exp(-wL / 2)) / wL)
    out['d5'] = d5
    g = C['paper_G1'] if not opt['g1'] else N.c(1)
    kappa = 2 * x * nL
    if N.surely_ge(N.lo(kappa), 1) or not opt['mono']:
        K = N.c(1)
    else:
        kl = N.lo(kappa)
        if N is ARB:
            kl = arb(kl)
            if not bool(kl > 0):
                raise ValueError('kappa <= 0')
        K = N.exp(kl - 1) / kl
    Jup = 1 / (lam * nlo)
    J1 = int(math.floor(N.tofloat(N.up(Jup)))) + 2
    Hn = Hn_fixed(lam, K, J1, g, C['IS'], C['S1'], 1 - a0, N)
    out['J1'] = J1; out['K'] = K; out['Hn'] = Hn
    if opt['yfac']:
        Ycoef = 1 + N.exp(-2 * (x - u) * nL - 4 * nL * N.log(L) / L)
    else:
        Ycoef = N.c(2)
    out['Ycoef'] = Ycoef
    A = Ycoef * d4 * d5 / w * Hn
    out['A'] = A
    b1, b2, r0 = b12(row, opt, N)
    out['b1'], out['b2'], out['r0'] = b1, b2, r0
    # c5 = d4/(2pi) * 16 P_h W/log^2 W * (X^{e5} + Y^{e5}) * (Jc + J3 T^k), all exponents combined
    e5 = N.c('1.5') - 2 * a0
    lL = N.log(L); lwL = N.log(wL)
    Jc = C['J1v'] + C['J4v'] + C['J2v']; J3 = C['J31v'] + C['J32v'] + C['J33v']
    s5 = 0
    for cx, extra in ((x * e5, 0), (u * e5, -2 * e5 * lL)):
        for Jv, kk in ((Jc, 0), (J3, k)):
            s5 = s5 + Jv * N.exp((w + cx + kk) * L + extra - 2 * lwL)
    c5 = d4 / (2 * pi) * 16 * C['Ph'] * s5
    out['c5'] = c5
    # c1
    lVW = (v + w) * L
    D2VW = _D2fixed(lVW, N)
    base = (v + w) / 2 + x * (N.c('0.5') - a0)          # exponent of (VW)^{1/2} X^{1/2-a0}
    if opt.get('gmin', '0.447L') == '0.447L':
        cg = N.c('0.447')
        gm = cg * L
        I2c = C['I2coef_v']
        S1t = D2VW * sq2pi * N.exp(1 / (6 * gm) + (x * (1 - a0) - pi * cg / 2) * L + (N.c('0.5') - a0) * N.log(gm))
        lE312 = N.log(N.c('66.7') * sq2pi * 2 / pi) + N.c(1) / 6 + (k - a0) * N.log(3 + gm) - pi * 3 / 2 + (base - pi * cg / 2) * L
        lE313 = N.log(N.c('1.461') * sq2pi * 6) + N.c(1) / 6 - a0 * N.log(gm - 3) + pi * 3 / 2 + (base - pi * cg / 2) * L
    else:
        gm = N.c(3 * 10**12)
        I2c = C['I2coef_v3']
        S1t = D2VW * sq2pi * N.exp(1 / (6 * gm) + x * (1 - a0) * L - pi * gm / 2 + (N.c('0.5') - a0) * N.log(gm))
        lE312 = N.log(N.c('66.7') * sq2pi * 2 / pi) + N.c(1) / 6 + (k - a0) * N.log(3 + gm) - pi * (3 + gm) / 2 + base * L
        lE313 = N.log(N.c('1.461') * sq2pi * 6) + N.c(1) / 6 - a0 * N.log(gm - 3) - pi * (gm - 3) / 2 + base * L
    SU = D2VW / (2 * pi) * (2 * I2c * N.exp((base + k) * L) + N.exp(lE312) + N.exp(lE313))
    tail = 8 * N.exp(-L ** 2 * (1 - N.exp(-u * L)) + 2 * u * L - 2 * lL)
    c1 = N.exp(-L ** 2 * N.exp(-u * L)) - S1t - SU - tail
    out['c1'] = c1; out['S1t'] = S1t; out['SU'] = SU
    den = c1 ** 2 - c5
    out['den'] = den
    out['C'] = A * (b1 + b2 * Z) / den
    return out

OPT_IMPR_H = dict(OPT_IMPR, hl=True)
OPT_CORR_H = dict(OPT_CORR, hl=True)

# ----------------------------------------------------------------------------------------------
# v2: Phase-2 lemmas (work/phase2_lemmas, own lemmas, unreviewed).  Row fields:
#   row['lems'] subset of {'lemA','lemB','lemC'} (comma separated)
#   row['d4A']  rigorous Lemma-A bound of d4 on the row (decimal string)          [lemA]
#   row['cfB']  rigorous Lemma-B bound of sup #Box/(delta log T) on the row      [lemB]
# Lemma C (implemented here): per pair  |Gamma(z)(X^z-Y^z)| <= (X^{2d}-Y^{2d})/(2d)  (all pairs; no K needed)
#   and  <= g (1+eps_Y) X^{2d}/|z|  ;  far pairs (|Delta|>=1): (1+eps_Y) X^{2d} S(|Delta|).
# ----------------------------------------------------------------------------------------------
def Hn_general(a, b, J1, far, N):
    """per-representative sum (units X^{2delta}/delta) with per-pair bound m(d) = min(a, b/d), m(0) = a,
    d = |Delta|/(box height); plus the far part.  Same pairing argument as Hn_fixed (REPORT 1.4)."""
    half = N.c('0.5')
    def m(d):
        if d == 0:
            return a
        return N.minu(a, b / d)
    dstar = b / a
    tot = a
    j = 1
    if J1 >= 1 and N.surely_ge(half, N.up(dstar) if N is ARB else dstar):
        tot = tot + a + b / (1 - dstar)
        j = 2
    while j <= J1 and not N.surely_ge(N.c(j - 1), N.up(dstar) if N is ARB else dstar):
        tot = tot + m(j - 1) + m(N.c(j) - half)
        j += 1
    if j <= J1:
        if N is ARB:
            tot = tot + b * ((H(J1 - 1) - H(j - 2)) + (H(J1) - H(j - 1)))
        else:
            tot = tot + b * ((HF(J1 - 1) - HF(j - 2)) + (HF(J1) - HF(j - 1)))
    return tot + far

def patch_phase2_rounding():
    """Review round 2, item 1: lemmaB_weyl.A_eta rounds float(x.upper()) to nearest, which can be 1 ulp low.
    Replace it at run time (Phase-2 files are not modified) by a version that keeps A_eta as an arb upper bound."""
    import sys as _s
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase2_lemmas')
    if p not in _s.path:
        _s.path.insert(0, p)
    import lemmaB_weyl as W
    if getattr(W, '_phase0_patched', False):
        return
    def A_eta_up(eta):
        eta = arb(eta)
        a = arb((arb('0.618') / (arb(1).exp() * eta)).upper())
        A = a if bool(a >= arb('1.461')) else arb('1.461')
        cond = A * (arb(105) * (arb(2) / 984 + eta)).exp()
        assert bool(cond >= arb('66.7')), 'Patel-Yang range condition fails'
        return A
    W.A_eta = A_eta_up
    W._phase0_patched = True
    ctx.prec = 128

_LD = None
def lemD_constants():
    """Lemma D (work/phase2_lemmas/lemmaD_mollifier.py, own lemma): c = sup Q(y)/sqrt(y), P* = prod_p(1+p^{-3/2}-p^{-2});
    rigorous arb upper bounds; computed once.  Restores 128-bit precision afterwards (the module sets 100)."""
    global _LD
    if _LD is None:
        import sys as _s
        p = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase2_lemmas')
        if p not in _s.path:
            _s.path.insert(0, p)
        import lemmaD_mollifier as LDm
        c = arb(arb(LDm.certify_c()).upper()); P = arb(arb(LDm.certify_Pstar()).upper())
        ctx.prec = 128
        _LD = (c, P)
    return _LD

def piece_v2(row, opt, L, N, C):
    lems = set(x for x in row.get('lems', '').split(',') if x)
    a0 = N.c(row['a0']); u = N.c(row['u']); x = N.c(row['x']); v = N.c(row['v']); w = N.c(row['w'])
    lam = N.c(row.get('lam', '1'))
    zfr = row['zfr']
    pi = N.pi(); sq2pi = N.sqrt(2 * pi)
    k = N.c(27) / 164
    out = {}
    nL = nuL(zfr, L, N)
    out['nuL'] = nL
    Z = 1 / nL
    nlo = N.lo(nL) / N.up(L) if N is ARB else nL / L
    if 'lemA' in lems:
        d4 = N.c(row['d4A'])
    else:
        d4 = N.exp((u - x) * L) + _RZA(u, v, N) * x / (v - u)
    out['d4'] = d4
    wL = w * L
    d5 = N.c('1.0061') * (1 + (N.c('1.333') + N.c('3.95') * N.exp(-wL / 2)) / wL)
    out['d5'] = d5
    g = N.c(1)                                         # Gamma(1+s) <= 1 on [0,1]
    lL = N.log(L)
    epsY = N.exp(-2 * (x - u) * nL - 4 * nL * lL / L)   # (Y/X)^{2 nu(T)}, Y = U/L^2
    J1 = int(math.floor(N.tofloat(N.up(1 / (lam * nlo))))) + 2
    far = (1 + epsY) * (2 * (1 - a0) * C['S1'] + 2 / lam * C['IS'])
    if 'lemC' in lems:
        q = N.exp(-2 * (1 - a0) * ((x - u) * L + 2 * lL))          # (Y/X)^{2(1-alpha0)} <= (Y/X)^{2 delta}
        a = (1 - q) / 2
        Hn = Hn_general(a, g * (1 + epsY) / lam, J1, far, N)
        out['K'] = N.c(1)
    else:
        kappa = 2 * x * nL
        if N.surely_ge(N.lo(kappa), 1):
            K = N.c(1)
        else:
            kl = N.lo(kappa)
            if N is ARB:
                kl = arb(kl)
                if not bool(kl > 0):
                    raise ValueError('kappa <= 0')
            K = N.exp(kl - 1) / kl
        Hn = Hn_general(g * (1 + epsY) * K / 2, g * (1 + epsY) / lam, J1, far, N)
        out['K'] = K
    out['J1'] = J1; out['Hn'] = Hn
    A = d4 * d5 / w * Hn
    out['A'] = A
    if 'lemB' in lems or 'lemBW' in lems:
        cfac = N.c(row['cfB'])
    elif row.get('cnt') == 'joint':
        cfac = joint_count(row, L, nlo, N)
    else:
        b1, b2, r0 = b12(row, dict(opt, b12='exact'), N)
        cfac = b1 + b2 * Z
    out['cf'] = cfac
    # c5 and c1 exactly as in piece_hl
    e5 = N.c('1.5') - 2 * a0
    lwL = N.log(wL)
    Jc = C['J1v'] + C['J4v'] + C['J2v']; J3 = C['J31v'] + C['J32v'] + C['J33v']
    s5 = 0
    for cx, extra in ((x * e5, 0), (u * e5, -2 * e5 * lL)):
        for Jv, kk in ((Jc, 0), (J3, k)):
            s5 = s5 + Jv * N.exp((w + cx + kk) * L + extra - 2 * lwL)
    c5 = d4 / (2 * pi) * 16 * C['Ph'] * s5
    out['c5'] = c5
    lVW = (v + w) * L
    D2VW = _D2fixed(lVW, N)
    base = (v + w) / 2 + x * (N.c('0.5') - a0)
    gm = N.c(3 * 10**12)
    I2c = C['I2coef_v3']
    S1t = D2VW * sq2pi * N.exp(1 / (6 * gm) + x * (1 - a0) * L - pi * gm / 2 + (N.c('0.5') - a0) * N.log(gm))
    lE312 = N.log(N.c('66.7') * sq2pi * 2 / pi) + N.c(1) / 6 + (k - a0) * N.log(3 + gm) - pi * (3 + gm) / 2 + base * L
    lE313 = N.log(N.c('1.461') * sq2pi * 6) + N.c(1) / 6 - a0 * N.log(gm - 3) - pi * (gm - 3) / 2 + base * L
    main = 2 * I2c * N.exp((base + k) * L)                       # Patel-Yang 66.7 t^{27/164}
    if row.get('c1zeta') == 'hpy':                               # min with Hiary-Patel-Yang 0.618 t^{1/6} log t (both valid)
        main = N.minu(main, 2 * C['I2coef_hpy'] * N.exp((base + N.c(1) / 6) * L + lL))
    if 'lemD' in lems:      # Lemma D: |M(1/2+it)| <= K_D (VW)^{1/2}  replaces D2VW (VW)^{1/2}   (S1t keeps D2VW)
        cD, PD = lemD_constants()
        if N is FLT:
            cD, PD = float(cD), float(PD)
        Dl = (v - u) * L
        Mfac = 4 * cD * cD * PD * (1 - N.exp(-Dl / 2)) * (1 - N.exp(-wL / 2)) / (Dl * wL)
    else:
        Mfac = D2VW
    out['Mfac'] = Mfac
    SU = Mfac / (2 * pi) * (main + N.exp(lE312) + N.exp(lE313))
    tail = 8 * N.exp(-L ** 2 * (1 - N.exp(-u * L)) + 2 * u * L - 2 * lL)
    c1 = N.exp(-L ** 2 * N.exp(-u * L)) - S1t - SU - tail
    out['c1'] = c1; out['S1t'] = S1t; out['SU'] = SU
    den = c1 ** 2 - c5
    out['den'] = den
    out['C'] = A * cfac / den
    return out

def joint_count(row, L, nlo, N, ncell=240):
    """sup over delta in [nlo, 1-alpha0] of  n~(delta)/(delta log T),  n~(delta) = 2r[TZ Prop 2.11 RHS] with r = rho*delta,
    rho = sqrt(1+lam^2/4), log T in the ball L (joint in delta, instead of b1 + b2 Z with separate sups).
    ARB: geometric delta-cells, each evaluated as a ball -> rigorous;  FLT: cell endpoints."""
    a0 = N.c(row['a0']); lam = N.c(row.get('lam', '1'))
    rho = N.sqrt(1 + lam ** 2 / 4)
    dlo = nlo; dhi = 1 - a0
    pi = N.pi()
    def f(d):
        r = rho * d
        br = ((L + N.c('4.7908')) / (4 + 8 * r) + (4 / pi - 1) * N.log(1 + 1 / r) / (1 + 2 * r) + N.c('2.6908')
              + 8 * r * (r * (2 * L - 1) + 4) / (1 + 2 * r) ** 2)
        return (2 * r * br + 2) / (d * L)                     # 2r * (1/r) = 2
    if N is ARB:
        dlo = arb(arb(dlo).lower()); dhi = arb(arb(dhi).upper())
        assert bool(rho * dhi < arb('0.5'))
        q = (dhi / dlo).log() / ncell
        best = arb(0)
        for i in range(ncell):
            da = dlo * (q * i).exp(); db = dlo * (q * (i + 1)).exp() if i < ncell - 1 else dhi
            best = best.max(arb(f(da.union(db)).upper()))
        return arb(best.upper())
    dlo = float(dlo); dhi = float(dhi)
    return max(f(dlo * (dhi / dlo) ** (i / ncell)) for i in range(ncell + 1))

OPT_V2 = dict(OPT_IMPR_H, v2=True)

def consts_N(row, N):
    Cc = consts(row['a0'], row['L0'] if row['L0'] == 'LOG3E12' else row['L0'])
    if N is ARB:
        return Cc
    return {k: float(v.upper()) for k, v in Cc.items()}

def row_bound(row, opt, N=ARB, nsub=None, pts=None, tol=2e-4, minw='1e-4', maxpieces=4000):
    """sup over L in [max(L0, log 3e12), L1] of the piecewise bound.
    ARB: rigorous adaptive bisection: start with nsub balls, bisect a sub-range while its upper bound exceeds
         (1+tol) * (largest point value found); every sub-range of the cover contributes its upper bound.
    FLT: evaluate at the given points (fractions in [0,1])."""
    C = consts_N(row, N)
    L0 = Lof(row['L0'], N); L1 = N.c(row['L1'])
    if N is ARB:
        L0 = L0.max(LOG3E12_ARB)
    if opt['rng'] == 'T0':
        return piece(row, opt, L0, N, C)
    if N is FLT:
        if pts is None:
            pts = (0.0, 0.5, 1.0)
        worst = None
        for f in pts:
            p = piece(row, opt, L0 + (L1 - L0) * f, N, C)
            if p['den'] <= 0 or p['c1'] <= 0:
                p['C'] = float('inf'); return p
            if worst is None or p['C'] > worst['C']:
                worst = p
        return worst
    if opt.get('hl'):
        if nsub is None:
            nsub = 16
        tol = max(tol, 1e-3)
        minw = str(max(1e-4, float(L1.mid()) * 1e-7))
    if nsub is None:
        nsub = max(4, int(math.ceil(float((L1 - L0).mid()) / 0.25)))
    # point values (lower estimates of the sup)
    best_pt = arb(0)
    for i in range(nsub + 1):
        q = piece(row, opt, L0 + (L1 - L0) * i / nsub, N, C)
        if bool(q['den'] > 0) and bool(q['c1'] > 0):
            best_pt = best_pt.max(arb(q['C'].mid()))
    target = best_pt * (1 + arb(tol))
    stack = [(L0 + (L1 - L0) * i / nsub, L0 + (L1 - L0) * (i + 1) / nsub) for i in range(nsub)]
    worst = None; npieces = 0; minw = arb(minw)
    while stack:
        a, b = stack.pop()
        npieces += 1
        p = piece(row, opt, a.union(b), N, C)
        ok = bool(p['den'] > 0) and bool(p['c1'] > 0)
        if ok and bool(p['C'] < target):
            if worst is None or p['C'].upper() > worst['C'].upper():
                worst = p
            continue
        if bool(b - a > minw) and npieces < maxpieces:
            m = (a + b) / 2
            stack.append((a, m)); stack.append((m, b))
            continue
        if not ok:
            p['C'] = arb('inf'); p['bad'] = True
            return p
        if worst is None or p['C'].upper() > worst['C'].upper():
            worst = p
    worst['C'] = arb(worst['C'].upper())
    worst['npieces'] = npieces
    return worst

# ----------------------------------------------------------------------------------------------
# her code, literally, in Arb (evaluated at t = T0)
# ----------------------------------------------------------------------------------------------
def faithful(row):
    N = ARB
    p = piece(row, OPT_PAPER, Lof(row['L0']), N, consts_N(row, N))
    return p

# ----------------------------------------------------------------------------------------------
# hypotheses of every lemma used, checked rigorously over the row
# ----------------------------------------------------------------------------------------------
def check_hypotheses(row, opt, nsub=None):
    """returns list of (name, ok, detail).  All checks in Arb over the whole range [max(L0,log 3e12), L1]."""
    N = ARB
    res = []
    a0 = arb(row['a0']); u = arb(row['u']); x = arb(row['x']); v = arb(row['v']); w = arb(row['w'])
    lam = arb(row.get('lam', '1'))
    L0 = Lof(row['L0']).max(LOG3E12_ARB); L1 = arb(row['L1'])
    res.append(('L0 >= log(3e12) and L1 <= 6.7e12 (0.447 log T <= 3e12 split, Sec.1)', bool(L1 <= arb('6.7e12')), ''))
    res.append(('0 < u < v (3.8), tau=v/u>1 (RZA Cor 1.2)', bool(u > 0) and bool(v > u), ''))
    res.append(('w > 0, x > u (X > U/L^2, Lemma 4.1)', bool(w > 0) and bool(x > u), ''))
    res.append(('[paper only] w < u, u+v < x (3.8)', bool(w < u) and bool(u + v < x), 'needed only by d4=code/paper (Lemma 4.2)'))
    res.append(('alpha0 in [0.95,1): 2-2a0<=1 (g=Gamma(1+s)<=1), 3/2-2a0<0 (Re z<0 in c1,c5 integrals)', bool(a0 >= arb('0.95')) and bool(a0 < 1), ''))
    if 'lw_local' in row['zfr']:
        bl = _lw_local_bands()
        res.append(('lw_local bands cover (28.73, log T1] (Theorem Z v2, phase1_littlewood sec.11) + MTY below 28.73',
                    bool(L1 <= arb(bl[-1][1])), ''))
    if 'cl_local' in row['zfr']:
        bands = _cl_local_bands()
        res.append(('cl_local bands cover (log 3e12, log T1] (Theorem C, phase1_littlewood sec.12)',
                    bool(arb(bands[0][0]) <= LOG3E12_ARB) and bool(L1 <= arb(bands[-1][1])), ''))
        res.append(('alpha0 < 1 - nu(T0) (otherwise the row is vacuous)', bool(a0 < 1 - nu(row['zfr'], L0, N)), ''))
    b1, b2, r0 = b12(row, opt, N)
    res.append(('Prop 2.11 radius r0 < 1/2', bool(r0 < arb('0.5')), str(r0.mid())))
    res.append(('U = T^u >= 100 (RZA Cor 1.2: X >= z1 >= 100)', bool((u * L0).exp() >= 100), ''))
    res.append(('Lemma 2.6 range: VW, W^2 >= 2', bool(((v + w) * L0).exp() >= 2) and bool((2 * w * L0).exp() >= 2), ''))
    res.append(('gamma_min = 0.447 L >= 4 (E313 bound needs gm-3 >= 1)', bool(arb('0.447') * L0 >= 4), ''))
    # zero-free region: widths non-increasing in t (cl, lw, kv: analytic; ford: derivative sign in Arb)
    okmono = True
    if 'ford' in row['zfr'] and bool(arb('32.8') < L1):
        okmono = ford_decreasing(arb('32.8'), L1)
    res.append(('zero-free widths non-increasing in t on [3e12, T1] (needed: 1-beta >= nu(T) for gamma <= T)', okmono, str(row['zfr'])))
    if 'ford' in row['zfr']:
        cl = [z for z in row['zfr'] if z.startswith('cl')] or ['cl5.558691']   # MTY 2024 (refereed) as fallback
        ncl = nu_region(cl[0], arb(LOG_1p88E14) + arb('1e-9'), N)
        ok = bool(nu_region('ford', arb(33), N) <= ncl)
        res.append(('Ford used only for t >= e^33; zeros 3e12<gamma<1.88e14 covered by classical width >= nu_Ford(e^33)', ok, ''))
    # positivity c1 > 0 and c1^2 > c5 over the whole row: done in row_bound (returns inf otherwise)
    p = row_bound(row, opt, ARB, nsub=nsub)
    res.append(('c1 > 0 and c1^2 - c5 > 0 on every sub-range', not p.get('bad', False), ''))
    # monotonicity condition of (4.9): x > Z/2 ; with opt['mono'] the factor K handles failure
    kappa_ok = True
    n = max(4, int(math.ceil(float((L1 - L0).mid()) / 0.1)))
    if opt.get('hl') and all(not z.startswith('ford') for z in row['zfr']):
        # nu*L non-decreasing for lw/kv/cl: one ball evaluation on [L0,L1] gives the minimum
        n = 0
        kappa_ok = bool(2 * x * nuL(row['zfr'], L0.union(L1), N) >= 1)
    for i in range(n):
        a = L0 + (L1 - L0) * i / n; b = L0 + (L1 - L0) * (i + 1) / n
        Lb = a.union(b)
        if not bool(2 * nu(row['zfr'], Lb, N) * x * Lb >= 1):
            kappa_ok = False
    res.append(('(4.9) monotonicity 2 nu(T) x log T >= 1 (x > Z/2)', kappa_ok, 'if False: factor K = e^{k-1}/k applied' if opt.get('mono') else 'if False: paper bound unjustified'))
    return res

def ford_decreasing(La, Lb, n=2000):
    """rigorous: d/dL nu_Ford(L) < 0 on [La, Lb] (sub-balls)."""
    for i in range(n):
        a = La + (Lb - La) * i / n; b = La + (Lb - La) * (i + 1) / n
        L = a.union(b)
        J = L / 6 + L.log() + arb('0.618').log()
        Jp = arb(1) / 6 + 1 / L
        Nn = arb('0.04962') - arb('0.0196') / (J + arb('1.15'))
        Np = arb('0.0196') * Jp / (J + arb('1.15')) ** 2
        D = J + arb('0.685') + arb('0.155') * L.log()
        Dp = Jp + arb('0.155') / L
        if not bool(Np * D - Nn * Dp < 0):
            return False
    return True
