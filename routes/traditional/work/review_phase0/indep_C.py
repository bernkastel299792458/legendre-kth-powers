"""
Independent referee re-evaluation (python-flint / Arb) of the corrected + lambda-box Bellotti bound
used for rows_reopt.csv (Phase 0).  Written from the referee's own derivation (REVIEW.md, sec. 2-3);
belarb.py was read only for conventions (parameter meaning, option set IMPR), no code is imported.

Bound evaluated, for T = e^L in the row and delta = 1 - sigma in [nu(T), 1 - a0]:

   N(1-delta, T) <= J * ntilde(delta)
   J <= A(delta) X^{2 delta} / (delta L (c1^2 - c5))
   => N <= X^{2 delta} * C(L, delta),   C(L, delta) = A(delta) * [ntilde(delta)/(delta L)] / (c1^2 - c5)

and the referee's C_row = sup over L-balls and delta-balls of C(L, delta).  Differences to Phase 0:
  * ntilde(delta)/(delta L) is evaluated directly from Thorner-Zaman Prop 2.11 / Bellotti Cor 2.3 with
    r = rho*delta, jointly with A(delta), on a delta-subdivision (Phase 0 decouples b1, b2 and uses r0 = rho(1-a0));
  * all 1-d integrals are monotone upper Riemann sums (+ explicit tails), not acb.integral;
  * Gamma integrals are plain box enclosures (no mean-value refinement).
Hence the referee value should be <= Phase-0 value and close to it.
"""
import math, sys, functools
from flint import arb, acb, ctx

ctx.prec = 160
PI = arb.pi()
SQ2PI = (2 * PI).sqrt()
K27 = arb(27) / 164
LOG3E12 = arb(3 * 10**12).log()
DECOUPLED = False
PIECE = 0.02
NMAX = 400

def up(x):  # upper end as exact arb
    return arb(arb(x).upper())

def lo(x):
    return arb(arb(x).lower())

# ------------------------------------------------------------------ zero-free regions (width nu, 1-beta >= nu)
def nu_cl(L, Z): return 1 / (arb(Z) * L)
def nu_lw(L, Z): return L.log() / (arb(Z) * L)
def nu_ford(L):
    J = L / 6 + L.log() + arb('0.618').log()
    return (arb('0.04962') - arb('0.0196') / (J + arb('1.15'))) / (J + arb('0.685') + arb('0.155') * L.log())

def nu_of(zfr, L):
    vals = []
    for z in zfr:
        if z.startswith('cl'): vals.append(nu_cl(L, z[2:]))
        elif z.startswith('lw'): vals.append(nu_lw(L, z[2:]))
        elif z == 'ford':
            if bool(L >= 33): vals.append(nu_ford(L))
        else: raise ValueError(z)
    best = vals[0]
    for v in vals[1:]:
        best = best.max(v)
    return best

# ------------------------------------------------------------------ monotone upper Riemann sums
def upper_sum_decreasing(f, a, b, n):
    """int_a^b f for f >= 0 non-increasing on [a,b]: sum h f(left endpoint)."""
    a, b = arb(a), arb(b); h = (b - a) / n
    s = arb(0)
    for i in range(n):
        s += f(a + h * i)
    return up(s * h)

def upper_sum_prod(fdec, ginc, a, b, n):
    """int_a^b fdec*ginc with fdec >= 0 non-increasing, ginc >= 0 non-decreasing: sum h fdec(left) ginc(right)."""
    a, b = arb(a), arb(b); h = (b - a) / n
    s = arb(0)
    for i in range(n):
        s += fdec(a + h * i) * ginc(a + h * (i + 1))
    return up(s * h)

# ------------------------------------------------------------------ |Gamma| integrals by box enclosure
@functools.lru_cache(maxsize=None)
def int_abs_gamma(slo, shi, t0, t1, nt, ns):
    """upper bound for sup_{sigma in [slo,shi]} int_{t0}^{t1} |Gamma(sigma+it)| dt  (sum over t-cells of
    h * max over sigma-cells of |Gamma(box)|)."""
    slo, shi, t0, t1 = arb(slo), arb(shi), arb(t0), arb(t1)
    ht = (t1 - t0) / nt; hs = (shi - slo) / ns
    tot = arb(0)
    for j in range(nt):
        ta = t0 + ht * j; tb = ta + ht
        tball = ta.union(tb)
        mx = arb(0)
        for i in range(ns):
            sa = slo + hs * i; sb = sa + hs
            g = acb(sa.union(sb), tball).gamma()
            mx = mx.max(arb(g.abs_upper()))
        tot += ht * mx
    return up(tot)

# ------------------------------------------------------------------ constants depending on a0 only
@functools.lru_cache(maxsize=None)
def constants(a0s):
    a0 = arb(a0s)
    c = {}
    e6 = (arb(1) / 6).exp()
    # IS = sqrt(2 pi) int_1^inf y^{3/2-2a0} e^{-pi y/2 + 1/(6y)} dy   (decreasing integrand)
    p = arb('1.5') - 2 * a0
    f = lambda y: (p * y.log() - PI * y / 2 + 1 / (6 * y)).exp()
    Y = arb(40)
    tail = Y ** p * (-PI * Y / 2).exp() * (1 / (6 * Y)).exp() / (PI / 2)
    c['IS'] = up(SQ2PI * (upper_sum_decreasing(f, 1, 40, 40000) + tail))
    c['S1'] = up(SQ2PI * (-PI / 2 + arb(1) / 6).exp())
    # Gamma integrals
    # c1: sigma' = 1/2 - beta in [-1/2, 1/2 - a0];  c5: sigma' = 3/2 - beta_r - beta_s in [-1/2, 3/2 - 2a0]
    s1hi = str(arb('0.5') - a0).split()[0] if False else None
    from decimal import Decimal
    s1hi = str(Decimal('0.5') - Decimal(a0s)); s5hi = str(Decimal('1.5') - 2 * Decimal(a0s))
    c['G01_c1'] = int_abs_gamma('-0.5', s1hi, '0', '1', 2000, 40)
    g01 = int_abs_gamma('-0.5', s5hi, '0', '1', 2000, 40)
    g1_40 = int_abs_gamma('-0.5', s5hi, '1', '40', 7800, 10)
    # t >= 40: |Gamma(z)| = |Gamma(z+1)|/|z| <= sqrt(2pi) t^{sigma-1/2} e^{-pi t/2 + 1/(6t)} <= sqrt(2pi) e^{-pi t/2} e^{1/240}
    t40 = SQ2PI * (arb(1) / 240).exp() * (-PI * 20).exp() / (PI / 2)
    c['G11'] = up(2 * g01)                         # int_{-1}^{1}
    c['Gall'] = up(2 * (g01 + g1_40 + t40))        # int_{-inf}^{inf}
    # c5 J-integrals (bounds as derived in REVIEW.md 4.c5)
    e18 = (arb(1) / 18).exp()
    q = K27 + 1 - 2 * a0
    fq = lambda y: (q * y.log() - PI * y / 2).exp()
    Y = arb(60)
    I3 = upper_sum_decreasing(fq, 3, 60, 57000) + Y ** q * (-PI * Y / 2).exp() / (PI / 2)
    c['J1'] = up(arb('66.7') * SQ2PI * e18 * I3)
    c['J4'] = up(arb('66.7') * SQ2PI * e18 * arb(2) ** K27 * I3)
    c['J2'] = up(arb('1.461') * c['Gall'])
    r1 = 1 - 2 * a0
    fr = lambda y: (r1 * y.log() - PI * y / 2).exp()
    I1 = upper_sum_decreasing(fr, 1, 60, 59000) + Y ** r1 * (-PI * Y / 2).exp() / (PI / 2)
    c['J31'] = up(arb('66.7') * SQ2PI * e6 * I1)
    fd = lambda y: (r1 * y.log() - PI * y / 2 + 1 / (6 * y)).exp()
    gi = lambda y: (1 + y / 3) ** K27
    I33 = upper_sum_prod(fd, gi, 1, 60, 59000) + (1 + Y / 3) ** K27 * Y ** r1 * (-PI * Y / 2).exp() * (1 / (6 * Y)).exp() / (PI / 2)
    c['J33'] = up(arb('66.7') * SQ2PI * I33)
    c['J32'] = up(arb('66.7') * (arb(4) / 3) ** K27 * c['G11'])
    # c1: I2 <= gamma^k [66.7 (1+1/g)^k G01_c1 + 66.7 sqrt(2pi) int_1^inf (1+t/g)^k t^{-a0} e^{-pi t/2 + 1/(6t)}],  g = 3e12
    g = arb(3 * 10**12)
    fa = lambda y: (-a0 * y.log() - PI * y / 2 + 1 / (6 * y)).exp()
    ga = lambda y: (1 + y / g) ** K27
    I2 = upper_sum_prod(fa, ga, 1, 60, 59000) + (1 + Y / g) ** K27 * Y ** (-a0) * (-PI * Y / 2).exp() * (1 / (6 * Y)).exp() / (PI / 2)
    c['I2coef'] = up(arb('66.7') * (1 + 1 / g) ** K27 * c['G01_c1'] + arb('66.7') * SQ2PI * I2)
    c['Ph'] = Ph()
    return c

@functools.lru_cache(maxsize=1)
def Ph(P=200000):
    sv = bytearray([1]) * (P + 1); sv[0] = sv[1] = 0
    for i in range(2, int(P ** 0.5) + 1):
        if sv[i]: sv[i * i::i] = bytearray(len(sv[i * i::i]))
    pr = arb(1)
    for p in range(2, P + 1):
        if sv[p]:
            ap = arb(p); pr *= 1 + (ap.sqrt() - 1) / (ap * ap)
    # tail prod_{p>P} (1 + p^{-3/2}) <= exp(int_P^inf t^{-3/2} dt) = exp(2/sqrt P)
    return up(pr * (2 / arb(P).sqrt()).exp())

# ------------------------------------------------------------------ arithmetic sums
def D2_bound(l):
    """sum_{n <= e^l} d(n)^2/n  (e^l >= 2) from CHT19 Thm 2 (first form) by partial summation."""
    D1, D2, D3, D4 = 1 / PI ** 2, arb('0.746'), arb('0.825'), arb('0.462')
    AY = D1 * l ** 3 + D2 * l ** 2 + D3 * l + D4 + arb('9.73') * (-l / 4).exp() * l + arb('0.73') * (-l / 2).exp()
    # int_2^Y A(t)/t^2: main part <= D1 l^4/4 + D2 l^3/3 + D3 l^2/2 + D4 l ; errors int_2^inf 9.73 t^{-5/4} log t + 0.73 t^{-3/2}
    e1 = arb('9.73') * arb(2) ** (arb(-1) / 4) * (4 * arb(2).log() + 16)
    e2 = arb('0.73') * 2 / arb(2).sqrt()
    return AY + arb('0.5') + D1 * l ** 4 / 4 + D2 * l ** 3 / 3 + D3 * l ** 2 / 2 + D4 * l + e1 + e2

def RZA(u, v):
    tau = v / u
    return arb('3.09') * (arb('1.084') * (tau + 1) + arb('1.301') * (1 + tau ** 2) - arb('0.116')) / (tau - 1)

# ------------------------------------------------------------------ zeros in a box (TZ Prop 2.11 via Bellotti Cor 2.3)
def ntilde_over_dL(delta, rho, L):
    r = rho * delta
    br = ((L + arb('4.7908')) / (4 + 8 * r) + (4 / PI - 1) * (1 + 1 / r).log() / (1 + 2 * r) + arb('2.6908')
          + 8 * r / (1 + 2 * r) ** 2 * (r * (2 * L - 1) + 4) + 1 / r)
    return 2 * r * br / (delta * L)

def ntilde_over_dL_sup(da, db, rho, L):
    """sup over delta in [da, db] of ntilde(delta)/(delta L), using monotonicity in r = rho*delta:
    decreasing: (L+4.7908)/(4+8r), log(1+1/r)/(1+2r), 2/(delta L);  increasing: r(r(2L-1)+4)/(1+2r)^2 (L > 2.5)."""
    ra = rho * da; rb = rho * db
    dec = (2 * rho / L * ((L + arb('4.7908')) / (4 + 8 * ra) + (4 / PI - 1) * (1 + 1 / ra).log() / (1 + 2 * ra) + arb('2.6908'))
           + 2 / (da * L))
    inc = 2 * rho / L * 8 * rb * (rb * (2 * L - 1) + 4) / (1 + 2 * rb) ** 2
    return dec + inc

# ------------------------------------------------------------------ per-representative sum
def Hn(lam, K, J1, dmax, c):
    """per-representative sum / (X^{2delta}/delta).  m(d) = min(K/2, 1/(lam d)), d in box units.
    j-th neighbours (both sides) are at distances >= j - theta and >= j - 1 + theta (theta = position of r in its box)."""
    def m(d):
        d = arb(d)
        if bool(d == 0): return K / 2
        a = K / 2; b = 1 / (lam * d)
        return a if bool(a.upper() <= b.lower()) else (b if bool(b.upper() <= a.lower()) else a.max(b))
    dstar = 2 / (K * lam)
    tot = K / 2                                      # s = r
    if bool(dstar <= arb('0.5')):
        tot += K / 2 + 1 / (lam * (1 - dstar))       # exact sup_theta m(theta) + m(1-theta)
    else:
        tot += m(0) + m(arb('0.5'))                  # one distance >= 1/2, the other >= 0
    s = arb(0)
    for j in range(2, J1 + 1):
        if bool(arb(j - 1) >= dstar):                # convex on [j-1, j]: max at theta in {0,1}
            s += (arb(1) / (j - 1) + arb(1) / j) / lam
        else:                                        # one distance >= j-1/2, the other >= j-1
            s += m(j - 1) + m(arb(j) - arb('0.5'))
    tot += s
    return tot + 2 * dmax * c['S1'] + 2 / lam * c['IS']   # g = 1;  boxes j > J1 have distance >= 1

# ------------------------------------------------------------------ C on an L-ball and delta-ball
def C_piece(row, Lb, nd=64):
    a0 = arb(row['alpha0']); u = arb(row['u']); x = arb(row['x']); v = arb(row['v']); w = arb(row['w'])
    lam = arb(row['lam']); zfr = row['zfr']
    c = constants(row['alpha0'])
    L = Lb
    nu = nu_of(zfr, L)
    nulo = lo(nu)
    # K
    kap = lo(2 * nulo * x * lo(L))
    K = arb(1) if bool(kap >= 1) else up((kap - 1).exp() / kap)
    # J1 >= 1/(lam nu): boxes beyond J1 are at distance >= J1 lam delta >= 1
    J1 = int(math.floor(float(up(1 / (lam * nulo)).upper()))) + 1
    assert bool(arb(J1) * lam * nulo >= 1)
    dmax = 1 - a0
    H = Hn(lam, K, J1, dmax, c)
    Ycoef = 1 + (2 * nu * ((u - x) * L - 2 * L.log())).exp()
    d4 = ((u - x) * L).exp() + RZA(u, v) * x / (v - u)
    wL = w * L
    d5 = arb('1.0061') * (wL + arb('1.333') + arb('3.95') * (-wL / 2).exp()) / wL
    A = Ycoef * d4 * d5 * H / w
    # c5
    Ghalf = 16 * c['Ph'] * wL.exp() / wL ** 2
    e5 = arb('1.5') - 2 * a0
    XY = (x * e5 * L).exp() + (e5 * (u * L - 2 * L.log())).exp()
    Jsum = c['J1'] + c['J4'] + c['J2'] + (c['J31'] + c['J32'] + c['J33']) * (K27 * L).exp()
    c5 = d4 / (2 * PI) * Ghalf * XY * Jsum
    # c1
    lVW = (v + w) * L
    D2 = D2_bound(lVW)
    g = arb(3 * 10**12)
    S1t = D2 * SQ2PI * (1 / (6 * g)).exp() * (x * (1 - a0) * L - PI * g / 2).exp() * ((arb('0.5') - a0) * g.log()).exp()
    E312 = arb('66.7') * SQ2PI * (arb(1) / 6).exp() * ((K27 - a0) * (3 + g).log()).exp() * 2 / PI * (-PI * (3 + g) / 2).exp()
    E313 = arb('1.461') * SQ2PI * (arb(1) / 6).exp() * 6 * (-a0 * (g - 3).log()).exp() * (-PI * (g - 3) / 2).exp()
    Itot = 2 * c['I2coef'] * (K27 * L).exp() + E312 + E313
    SU = D2 * (lVW / 2).exp() * (x * (arb('0.5') - a0) * L).exp() * Itot / (2 * PI)
    U = (u * L).exp(); cc = L ** 2 / U
    tail = 4 * (-cc * (U - 1)).exp() * ((U - 1) / cc + 1 / cc ** 2)
    c1 = (-L ** 2 / U).exp() - S1t - SU - tail
    den = c1 ** 2 - c5
    ok = bool(c1 > 0) and bool(den > 0)
    # joint sup over delta in [nu_lo, 1-a0]: A depends on delta only via 2 delta S(1) (bounded at dmax above)
    rho = (1 + lam ** 2 / 4).sqrt()
    dl = nulo; dh = dmax
    best = arb(0)
    if DECOUPLED:
        # Phase-0 style: sup_delta ntilde/(delta L) <= b1 + b2 Z, every r-term at its worst r in (0, r0]
        r0 = rho * dmax
        f = lambda r: 1 / (2 * (1 + 2 * r)) + 32 * r ** 2 / (1 + 2 * r) ** 2   # quasi-convex: max at endpoints
        b1 = rho * arb('0.5').max(f(r0))
        b2 = (2 * r0 * arb('4.7908') / (4 + 8 * r0) + 2 * r0 * (4 / PI - 1) * (1 + 1 / r0).log()
              + arb('5.3816') * r0 + 16 * r0 ** 2 * (4 - r0) / (1 + 2 * r0) ** 2 + 2)
        best = up(b1 + b2 / (nulo * lo(L)))
        nd = 0
    for i in range(nd):
        da = dl + (dh - dl) * i / nd; db = dl + (dh - dl) * (i + 1) / nd
        nt = ntilde_over_dL_sup(da, db, rho, L)
        best = best.max(arb(nt.upper()))
    Cv = A * best / den
    return dict(C=Cv, ok=ok, c1=c1, c5=c5, A=A, Hn=H, K=K, J1=J1, d4=d4, d5=d5, nbar=best, nu=nu,
                r0=rho * dmax, Ycoef=Ycoef, den=den)

def C_row(row, n=None, nd=64):
    L0 = arb(row['logT0']); L1 = arb(row['logT1'])
    L0 = L0.max(LOG3E12)
    if n is None:
        n = min(NMAX, max(8, int(math.ceil(float((L1 - L0).mid()) / PIECE))))
    worst = None; allok = True
    for i in range(n):
        a = L0 + (L1 - L0) * i / n; b = L0 + (L1 - L0) * (i + 1) / n
        p = C_piece(row, a.union(b), nd)
        allok = allok and p['ok']
        if worst is None or p['C'].upper() > worst['C'].upper():
            worst = p; worst['Lball'] = a.union(b)
    worst['allok'] = allok
    return worst

def C_point(row, L, nd=64):
    return C_piece(row, arb(L), nd)

def parse(rec):
    nd = {}
    for part in rec['notes'].split(';'):
        if '=' in part:
            k, v = part.split('=', 1); nd[k.strip()] = v.strip()
    return dict(rec, lam=nd.get('lam', '1'), zfr=tuple(rec['zfr_input'].split('+')))

if __name__ == '__main__':
    import csv
    path = sys.argv[1]
    if len(sys.argv) > 3 and sys.argv[3] == 'decoupled':
        DECOUPLED = True
    ids = sys.argv[2].split(',')
    recs = {r['id']: r for r in csv.DictReader(open(path))}
    for i in ids:
        row = parse(recs[i])
        w = C_row(row)
        Ccsv = arb(row['C'])
        print(f"{i} [{row['logT0']},{row['logT1']}] a0={row['alpha0']} lam={row['lam']} zfr={row['zfr']} B={row['B']} 2x={2*float(row['x'])}")
        print(f"    C_csv={row['C']}  C_ref(sup)={float(w['C'].upper()):.8g}  ratio ref/csv={float(w['C'].upper())/float(row['C']):.6f}"
              f"  all c1>0,den>0: {w['allok']}  worst L-ball={w['Lball'].str(5)}")
        print(f"    at worst: Hn={float(w['Hn'].mid()):.6f} K={float(w['K'].mid()):.6f} J1={w['J1']} A={float(w['A'].mid()):.4f} "
              f"nbar={float(w['nbar'].mid()):.4f} c1={float(w['c1'].mid()):.6f} c5={float(w['c5'].mid()):.6f} d4={float(w['d4'].mid()):.4f} "
              f"d5={float(w['d5'].mid()):.5f} r0={float(w['r0'].mid()):.4f}")
        sys.stdout.flush()
