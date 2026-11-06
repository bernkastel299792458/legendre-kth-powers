"""Independent re-implementation of delta_H (Prop. H) and delta_S (Prop. S + Lemma 5)
for k = 67, written from the formulas in proof/manuscript.md only (no project code reused).

This is a POINTWISE, NON-RIGOROUS cross-check (mpmath, Simpson quadrature). It is meant to
(1) check that the certified upper bounds in proof/certificates/*.csv are >= the formula values,
(2) measure the true pointwise margin and its sensitivity to the inputs.
It is not a certificate.

Part of: review/Claude_review_k67_proof_2026-11-06.md (Claude, 2026-11-06).
"""
from mpmath import mp, mpf, exp, log, pi, binomial, factorial, sqrt

mp.dps = 60
k = 67
HR = mpf(3000175332800)                      # Platt-Trudgian RH height
B1, B3 = mpf('17.418'), mpf('2.231')         # Johnston-Yang Table 3, sigma in [0.98, 1)
S1 = mpf('0.98')                             # sigma_1
# zero-free region constants (classical Z1, Littlewood Z2, Vinogradov-Korobov Z3)
Z = {'lw': (mpf('4.896'), mpf('19.62'), mpf('54.004')),          # main chain of the manuscript
     'thesis': (mpf('4.862'), mpf('19.62'), mpf('51.34')),       # Yang thesis Thms 1.1-1.3
     'published': (mpf('5.558691'), mpf('21.233'), mpf('53.989')),
     'nothesis': (mpf('4.896'), mpf('21.233'), mpf('53.989'))}   # drop the thesis constant 19.62
# Bellotti, arXiv:2405.12545v2 Table 2: (log T0, log T1, alpha0, C, B)
ROWS = [
    (log(mpf(3) * 10**12), 29, '0.9927', '37341.72', '14.160'), (29, 30, '0.9927', '37564.18', '14.084'),
    (30, 31, '0.9925', '40014.59', '13.588'), (31, 32, '0.9923', '42840.01', '13.108'),
    (32, 33, '0.9921', '46015.02', '12.647'), (33, 34, '0.9919', '49270.71', '12.226'),
    (34, 35, '0.9918', '52249.66', '11.856'), (35, 36, '0.9916', '55524.80', '11.505'),
    (36, 37, '0.9914', '59715.72', '11.134'), (37, 38, '0.9912', '64228.93', '10.782'),
    (38, 39, '0.9910', '68446.65', '10.475'), (39, 40, '0.9909', '71907.32', '10.217'),
    (40, 41, '0.9907', '76267.80', '9.951'), (41, 42, '0.9906', '80004.48', '9.720'),
    (42, 43, '0.9905', '83811.09', '9.501'), (43, 44, '0.9903', '89209.33', '9.259'),
    (44, 45, '0.9901', '95233.68', '9.020'), (45, '46.2', '0.9900', '99227.30', '8.843'),
    ('46.2', 50, '0.9899', '104761.04', '8.634'), (50, 60, '0.9892', '128806.85', '7.936'),
    (60, 70, '0.9876', '194323.75', '6.661'), (70, 80, '0.9860', '278045.07', '5.809'),
    (80, 90, '0.985', '370655.73', '5.216'), (90, 100, '0.985', '425721.47', '4.831'),
    (100, 110, '0.985', '488901.14', '4.513'), (110, 120, '0.985', '545744.21', '4.264'),
    (120, 130, '0.985', '629490.27', '4.032'), (130, 140, '0.985', '694045.43', '3.855'),
    (140, 150, '0.985', '771373.78', '3.696'), (150, 160, '0.985', '825913.07', '3.572'),
    (160, '170.2', '0.985', '909966.07', '3.448'), ('170.2', 500, '0.985', '1.12e6', '3.337'),
    (500, 1000, '0.985', '6.23e6', '2.152'), (1000, 1500, '0.985', '2.12e7', '1.820'),
    (1500, 2000, '0.985', '6.47e7', '1.684'), (2000, 2500, '0.985', '1.73e8', '1.610'),
    (2500, 3000, '0.985', '2.56e8', '1.577'), (3000, 481958, '0.985', '5.76e8', '1.551'),
    (481958, '6.7e12', '0.985', '1.62e11', '1.448')]
ROWS = [(mpf(a), mpf(b), mpf(c), mpf(C), mpf(B)) for a, b, c, C, B in ROWS]
a1, a2 = 1 + mpf('1.93378e-8'), 1 + mpf('1.936e-8')   # BKLNW Cor. 5.1, b = 300


def eta(v, zs):
    """Zero-free width at height t = e^v (max of the three regions)."""
    z1, z2, z3 = Z[zs]
    return max(1 / (z1 * v), log(v) / (z2 * v), 1 / (z3 * v ** (mpf(2) / 3) * log(v) ** (mpf(1) / 3)))


def row_of(v):
    for r in ROWS:
        if r[0] < v <= r[1]:
            return r
    return None


def Epp(L):
    eps = k * exp(-L / k)
    return (a1 * sqrt(1 + eps) - mpf('0.999')) / k * exp(-(mpf(1) / 2 - mpf(1) / k) * L) + \
           (a2 * (1 + eps) ** (mpf(1) / 3) - mpf('0.885')) / k * exp(-(mpf(2) / 3 - mpf(1) / k) * L)


# ---------------------------------------------------------------- Prop. H (manuscript §6)
def deltaH(L, mu, sstar, zs='lw', eta_at=None):
    """delta_H at a single L. eta is taken at height e^{eta_at} (default: 2T = e^{mu L})."""
    L = mpf(L); mu = mpf(mu); sstar = mpf(sstar)
    u = mu * L
    eps = k * exp(-L / k)
    et = eta(u if eta_at is None else eta_at, zs)
    lamK = L * (1 - 8 * mu / 3) - 2 * log(u)
    r = row_of(u)
    assert r is not None and r[2] <= sstar
    C, B = r[3], r[4]
    lamB = L * (1 - B * mu)
    assert lamK >= 1 and lamB >= 1
    Etriv = u / pi * exp(-(1 - S1 - mu) * L)
    EK = 2 * B1 * u ** 3 * (L / lamK) * exp(-(1 - sstar) * lamK) + 2 * B3 * u ** 2 * exp(-(1 - sstar) * L)
    EB = 2 * C * (L / lamB) * exp(-et * lamB)
    Etr = 2 * mpf('1.26') / k * ((1 + eps) * (L + eps) ** mpf('0.8') + L ** mpf('0.8')) * exp(-(mu - mpf(1) / k) * L)
    return Etriv + EK + EB + Etr + Epp(L), dict(triv=Etriv, K=EK, B=EB, tr=Etr)


# ---------------------------------------------------------------- Prop. S (manuscript §7)
def poly_phi(M):
    c = [mpf(0)] * (2 * M + 1)
    for i in range(M + 1):
        c[M + i] = binomial(M, i) * (-1) ** i
    return c  # ascending coefficients of y^M (1-y)^M


def pder(c):
    return [i * c[i] for i in range(1, len(c))]


def pev(c, y):
    r = mpf(0)
    for a in reversed(c):
        r = r * y + a
    return r


def Rj(M):
    """Exact R_j = ||phi^(j)||_1 / int(phi), j = 0..M, and ||phi||_inf / int(phi).
    ||phi^(j)||_1 = sum |phi^(j-1)(r_{i+1}) - phi^(j-1)(r_i)| over the sign changes r_i of phi^(j)."""
    c = poly_phi(M)
    I = factorial(M) ** 2 / factorial(2 * M + 1)
    out = [mpf(1)]
    prev = c
    for j in range(1, M + 1):
        cj = pder(prev)
        rts, Ngrid = [], 4000
        ys = [mpf(i) / Ngrid for i in range(Ngrid + 1)]
        vals = [pev(cj, y) for y in ys]
        for i in range(Ngrid):
            lo, hi, flo = ys[i], ys[i + 1], vals[i]
            if i > 0 and flo == 0:
                rts.append(lo); continue
            if flo * vals[i + 1] < 0:
                for _ in range(200):          # bisection
                    mid = (lo + hi) / 2; fm = pev(cj, mid)
                    if fm * flo <= 0: hi = mid
                    else: lo, flo = mid, fm
                rts.append((lo + hi) / 2)
        pts = [mpf(0)] + sorted(r for r in rts if 0 < r < 1) + [mpf(1)]
        l1 = sum(abs(pev(prev, pts[i + 1]) - pev(prev, pts[i])) for i in range(len(pts) - 1))
        out.append(l1 / I)
        prev = cj
    return out, (mpf(1) / 4 ** M) / I


def Phi(v, L, zs, sstars=None, full_table=True):
    """Lemma 5: min of options (a), (b), (c) at height t = e^v."""
    t_logt = exp(v) * v / (2 * pi)
    best = t_logt                                              # (a)
    triv = t_logt * exp(-(1 - S1) * L)
    et = eta(v, zs)
    lam = L - 8 * v / 3 - 2 * log(v)
    if lam >= 1:
        best = min(best, triv + B1 * v ** 3 * (L / lam) * exp(-et * lam) + B3 * v ** 2 * exp(-et * L))  # (b)
        r = row_of(v)
        if r is not None and (full_table or r[0] >= 80):
            C, B, s0 = r[3], r[4], r[2]
            lamB = L - B * v
            if lamB >= 1:
                cands = sstars or [s0, s0 + mpf('0.001'), s0 + mpf('0.003'), mpf('0.995')]
                for ss in cands:                                # (c), same sigma* candidates as the project code
                    if ss >= s0 and ss <= 1 - et:
                        best = min(best, triv + B1 * v ** 3 * (L / lam) * exp(-(1 - ss) * lam)
                                   + B3 * v ** 2 * exp(-(1 - ss) * L) + C * (L / lamB) * exp(-et * lamB))
    return best


def deltaS(L, M, zs='lw', step=mpf(1) / 256, sstars=None, full_table=True, R=None):
    """delta_S at a single L (Prop. S), with int Phi d(-g) by composite Simpson in v = log t."""
    L = mpf(L)
    R, ratio = R or Rj(M)
    eps = k * exp(-L / k)
    logxh = L / k - log(k)                                    # log(x/h)
    A = [R[j] * (1 + eps) ** j * exp(j * logxh) for j in range(M + 1)]

    def dg(v):  # -g'(v), g(e^v) = min(1, min_j A_j e^{-jv})
        best, bj = mpf(1), 0
        for j in range(1, M + 1):
            val = A[j] * exp(-j * v)
            if val < best:
                best, bj = val, j
        return bj * best if bj else mpf(0)

    v = log(HR)
    V = max(logxh + 40, (log(A[M]) + 80) / (M - 1))
    n = int((V - v) / step) + 1
    n += n % 2
    hstep = (V - v) / n
    tot = mpf(0)
    for i in range(n + 1):
        vi = v + i * hstep
        d = dg(vi)
        f = Phi(vi, L, zs, sstars, full_table) * d if d else mpf(0)
        tot += (1 if i in (0, n) else (4 if i % 2 else 2)) * f
    tot *= hstep / 3
    tail = M * A[M] / (2 * pi) * exp(-(M - 1) * V) * (V / (M - 1) + mpf(1) / (M - 1) ** 2)  # Phi <= t log t/2pi
    zeros = 2 * (tot + tail)
    low = 2 * HR * log(HR) / (2 * pi) * exp(-L / 2)
    pp = ratio * (Epp(L) + 1 / (exp(3 * L) - exp(L)))
    return zeros + low + pp
