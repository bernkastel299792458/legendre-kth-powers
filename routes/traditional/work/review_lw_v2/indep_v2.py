"""Independent referee re-implementation of the v2 cell inequality (REPORT.md §2-§5, §11), written from the
mathematics (thesis Def. 2.1/3.1, Lemma 2.3 with Ford's corrected c0, REPORT §3-§4), NOT from zl_core.py.

Number systems:
  * mpmath.iv (interval arithmetic, 200 bits) for the cell checks  -> rigorous enclosure of eta*Psi over a cell
  * mpmath.mp (50 digits) for the dense point scan                 -> exploration / cross-check
  * G(mu) by mpmath.quad (50 digits; not an interval, but accurate to far below the margins tested)

The window constant Z_w is recomputed from zfr_local_v2.csv itself (exact high-precision window), with
  below V0 = 28.73: 5.558691 * log(V0)  (MTY);  above V1 = 6006998: min(21.233, Z_VK(V1)), Z_VK(v) = 54.004 (log v)^{4/3} v^{-1/3}.

Usage:
  python -I indep_v2.py cells            -> selected cells, compared with zl_core.cell_terms (needs ../phase1_littlewood)
  python -I indep_v2.py scan [step]      -> dense point scan of all 366 bands, all lines n = 3..18
  python -I indep_v2.py asym             -> local requirement Z(v) of this method far above V1 (lines n <= 30)
"""
import os, sys, csv, math
from fractions import Fraction as Fr
from mpmath import mp, iv, mpf

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.abspath(os.path.join(HERE, '..', 'phase1_littlewood'))
iv.prec = 200
mp.dps = 50

# ---------------------------------------------------------------- polynomial (thesis (2.34), [MT14, Table 5])
CJ = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
KK = 16
AK = [Fr(sum(CJ[j] * CJ[j + k] for j in range(KK + 1 - k)) * (1 if k == 0 else 2), 14912370) for k in range(KK + 1)]
assert AK[0] == 1 and AK[1] == Fr(865534, 497079) and sum(AK[1:]) == Fr(2919857, 828465)
assert all(x > 0 for x in AK)


class Num:
    """Thin wrapper so the same formulas run in iv (rigorous) or mp (points)."""

    def __init__(self, M):
        self.M = M
        c = lambda s: M.mpf(s)
        self.c = c
        self.th = c('1.1272')
        th = self.th
        self.tn, self.sn, self.cs = M.tan(th), M.sin(th), M.cos(th)
        tn, sn, cs = self.tn, self.sn, self.cs
        self.pi = M.pi
        self.gamma = M.euler
        self.w0 = (th * tn + 3 * th / tn - 3) / cs ** 2                    # thesis p. 30 (closed form of w(0))
        self.d = 2 * th / tn
        self.c0 = 1 / (sn * cs ** 3)                                        # Ford's corrected c0 (thesis prints csc sec^2)
        self.c1 = (th - sn * cs) * tn ** 4
        self.c2 = tn ** 3 * sn ** 2
        self.c3 = (th - sn * cs) * tn ** 2
        self.kappa = (M.log(M.pi) - (2 - M.euler - 2 * M.log(2))) / 2       # (log pi - psi(3/2))/2
        self.a = [M.mpf(f.numerator) / f.denominator for f in AK]
        self.logk = [None] + [M.log(k) for k in range(1, KK + 1)]
        self.l2pi = M.log(2 * M.pi)

    def C(self, nu, r):
        M = self.M
        assert self.lo(r) > self.hi(self.tn)
        return self.c0 * r * (self.c2 * (r + 1) ** 2 * (M.exp(-2 * nu * self.th / self.tn) + 1) + self.c1 * r
                              + self.c3 * r ** 3) / (r ** 2 - self.tn ** 2) ** 2

    def lo(self, x):
        """lower endpoint as a plain mpf (exact)"""
        if self.M is iv:
            return mp.make_mpf(iv.mpf(x)._mpi_[0])
        return x

    def hi(self, x):
        if self.M is iv:
            return mp.make_mpf(iv.mpf(x)._mpi_[1])
        return x

    def line(self, n):
        c = self.c
        if n == 3:
            return c(1) / 2, c('0.618'), c(1) / 6
        q = 2 ** n - 2
        return 1 - c(n) / q, c('1.546'), c(1) / q

    def R0(self, lT):
        return self.c('0.137') * lT + self.c('0.443') * self.M.log(lT) + self.c('1.588')

    def cell(self, V, Z, Zw, n, exact351=False):
        """V: iv interval (cell) or mp point.  Z, Zw: decimal strings.  Returns (mu_low, PsiEta) or None."""
        M, c = self.M, self.c
        Zs, Zws = c(Z), c(Zw)
        sig_n, X, Y = self.line(n)
        LK = V + M.log(16 + c(10) ** 10 * M.exp(-V))       # log(16 t + 1e10)
        lK = M.log(LK) / LK
        lt = M.log(V) / V
        y = lK / Zws                                        # s = 1 worst case
        sig = 1 - y
        lam = sig - sig_n
        if not (self.hi(lam) < 0.5 and self.lo(lam - y) > 0 and self.lo(sig) > 0.75):
            return None
        eta = lt / Zs * (1 + c('4e-100'))                   # eta_max >= (s+eps) A l(t)
        sl = 0
        for k in range(1, KK + 1):
            lT = V + self.logk[k]
            sl = sl + self.a[k] * (M.log(X) + Y * lT + M.log(lT))
        x = lam - y                                         # sigma* + lambda = 1 + x
        B = (sl + (self.gamma * x - M.log(x))) / (2 * lam)  # Ramare: log zeta(1+x) <= gamma x - log x
        nu = lam / eta
        r = self.lo(nu)
        if not r > 2 * self.hi(self.tn):
            return None
        Cm1 = self.C(c(-1), M.mpf(r) if M is iv else r)
        J = (lam ** -3 + (2 * sig - 1 - lam) ** -3) / 2
        zs = 0
        for k in range(1, KK + 1):
            lT = V + self.logk[k]
            Mc = (lT - self.l2pi) / self.pi + 2 * self.R0(lT) + c('1e-9')
            Sf = (lT - self.l2pi) / (2 * self.pi) + 4 * self.R0(lT) + c('1e-9')
            zs = zs + self.a[k] * (J * Mc + Sf)
        zero_err = Cm1 * eta ** 3 * zs
        x0 = self.lo(sig - c(1) / 2)
        etau = self.hi(eta)
        x0m, etam = (M.mpf(x0), M.mpf(etau)) if M is iv else (x0, etau)
        CE = self.C(x0m / etam, x0m / etam)
        pre = CE / (2 * self.pi) * eta ** 3
        Es = pre * ((2 / x0m ** 2) * (M.log(4) + c(10) / 3) + 2 / (x0m * 8)) + CE * eta ** 3 / x0m ** 3   # T = 0
        for k in range(1, KK + 1):
            lT = V + self.logk[k]          # log(T/2 + 4) <= log T for T >= 8;  2/(x0 (T+8)) <= 2 e^{-lT}/x0
            Es = Es + self.a[k] * (pre * ((2 / x0m ** 2) * (lT + c(10) / 3) + 2 * M.exp(-lT) / x0m)
                                   + CE * eta ** 3 / x0m ** 3)
        mu = (Zs / Zws) * (lK / lt) * (1 - c('4e-100'))
        mu_low = self.lo(mu)
        u = self.pi * eta * (1 - (M.mpf(mu_low) if M is iv else mu_low)) / (2 * lam)
        assert self.hi(u) < 1
        if exact351:
            loss = self.a[1] * eta * self.w0 * (self.pi / (2 * lam)) * (1 / u - M.cot(u))
        else:
            loss = self.a[1] * eta * self.w0 * (self.pi / (2 * lam)) * c('0.36') * u
        tiny = c('1e-9') * eta
        PE = eta * self.w0 * (B - self.kappa) + zero_err + Es + loss + tiny
        return mu_low, PE, dict(B=B, lam=lam, eta=eta, y=y, zero_err=zero_err, Es=Es, loss=loss, nu=nu, Cm1=Cm1)


# ---------------------------------------------------------------- G(mu) from Def. 2.1 (own implementation)
def w_mp(u, th=None):
    th = th or mpf('1.1272')
    tn = mp.tan(th)
    s2 = 1 / mp.cos(th) ** 2
    return s2 * (s2 * (th / tn - u / 2) * mp.cos(u * tn) + 2 * th / tn - u + mp.sin(2 * th - u * tn) / mp.sin(2 * th)
                 - 2 * (1 + mp.sin(th - u * tn) / mp.sin(th)))


_G = {}


def G_mp(mu):
    key = mp.nstr(mu, 40)
    if key not in _G:
        a0 = mpf(AK[0].numerator) / AK[0].denominator
        a1 = mpf(AK[1].numerator) / AK[1].denominator
        th = mpf('1.1272')
        d = 2 * th / mp.tan(th)
        _G[key] = mp.quad(lambda u: mp.exp(mu * u) * (a1 * mp.exp(-u) - a0) * w_mp(u), mp.linspace(0, d, 9))
    return _G[key]


def G_grid(mu_low):
    """the code's lookup: g = (floor(1e4 mu_low) - 1)/1e4 (any g <= mu_low is valid since G' > 0 on [0.849, 1])."""
    j = math.floor(float(mu_low) * 10000) - 1
    g = mpf(j) / 10000
    assert g <= mu_low
    return G_mp(g), g


# ---------------------------------------------------------------- profile and window (from the CSV)
def load_csv():
    rows = list(csv.DictReader(open(os.path.join(SRC, 'zfr_local_v2.csv'))))
    return [(Fr(r['logt_lo']), Fr(r['logt_hi']), r['Z2']) for r in rows]


PROF = load_csv()
V0, V1 = PROF[0][0], PROF[-1][1]
assert V0 == Fr('28.73') and V1 == 6006998


def z_vk(v):
    v = mpf(v)
    return mpf('54.004') * mp.log(v) ** (mpf(4) / 3) / v ** (mpf(1) / 3)


ZBELOW = mpf('5.558691') * mp.log(mpf('28.73'))
ZABOVE = min(mpf('21.233'), z_vk(6006998))


def zw_exact(va, vb):
    """max of the profile over log u in [log(e^va - 1e10), log(16 e^vb + 1e10)] (+1e-25 pad), as decimal string."""
    va, vb = mpf(va), mpf(vb)
    lo = va + mp.log(1 - mpf(10) ** 10 * mp.exp(-va)) - mpf('1e-25')
    hi = vb + mp.log(16 + mpf(10) ** 10 * mp.exp(-vb)) + mpf('1e-25')
    cands = []
    if lo <= mpf(V0.numerator) / V0.denominator:
        cands.append(ZBELOW)
    if hi > V1:
        cands.append(ZABOVE + mpf('1e-20'))
    for a, b, Zs in PROF:
        if mpf(b.numerator) / b.denominator > lo and mpf(a.numerator) / a.denominator < hi:
            cands.append(mpf(Zs))
    m = max(cands)
    return mp.nstr(m, 45) if m not in [mpf(z) for _, _, z in PROF] else [z for _, _, z in PROF if mpf(z) == m][0]


def band_of(v):
    for i, (a, b, Zs) in enumerate(PROF):
        if a < Fr(v) <= b:
            return i
    return None


# ---------------------------------------------------------------- modes
def point_margin(Nm, v, Z, Zw, lines=range(3, 19)):
    best = None
    for n in lines:
        r = Nm.cell(mpf(v), Z, Zw, n)
        if r is None:
            continue
        mu, PE, _ = r
        if mu < 0.85:
            continue
        G, g = G_grid(mu)
        rel = (G - PE) / G
        if best is None or rel > best[0]:
            best = (rel, n, mu, PE, G)
    return best


def run_scan(step_div=40):
    Nm = Num(mp)
    mp.dps = 30
    worst = []
    out = open(os.path.join(HERE, 'scan_output.txt'), 'w')
    for i, (a, b, Zs) in enumerate(PROF):
        af, bf = float(a), float(b)
        pts = [af + (bf - af) * q / step_div for q in range(step_div + 1)]
        pts[0] = af + 1e-9 * max(1, af / 100)
        res = []
        prev = None
        for x in pts:
            Zw = zw_exact(x, x)
            r = point_margin(Nm, x, Zs, Zw)
            res.append((x, r))
        # refine line switches (local maxima of the requirement) by bisection on the best-line change
        extra = []
        for (x1, r1), (x2, r2) in zip(res[:-1], res[1:]):
            if r1 and r2 and r1[1] != r2[1]:
                lo_, hi_ = x1, x2
                n1, n2 = r1[1], r2[1]
                for _ in range(40):
                    m = (lo_ + hi_) / 2
                    Zw = zw_exact(m, m)
                    m1 = point_margin(Nm, m, Zs, Zw, [n1])
                    m2 = point_margin(Nm, m, Zs, Zw, [n2])
                    if m1 is None or m2 is None:
                        break
                    if m1[0] > m2[0]:
                        lo_ = m
                    else:
                        hi_ = m
                m = (lo_ + hi_) / 2
                Zw = zw_exact(m, m)
                extra.append((m, point_margin(Nm, m, Zs, Zw)))
        allr = res + extra
        mn = min(allr, key=lambda t: t[1][0] if t[1] else -9)
        lines_seen = sorted({t[1][1] for t in allr if t[1]})
        msg = (f"band {i} ({af:g}, {bf:g}] Z={Zs}: min point rel margin {float(mn[1][0]) if mn[1] else -9:.3e} "
               f"at v={mn[0]:.6f} n={mn[1][1] if mn[1] else None}; best lines seen {lines_seen}; switches {len(extra)}")
        print(msg, flush=True)
        out.write(msg + '\n')
        worst.append((float(mn[1][0]) if mn[1] else -9, i, mn[0]))
    worst.sort()
    msg = f"WORST 10: {worst[:10]}\nNEGATIVE: {[w for w in worst if w[0] <= 0]}"
    print(msg)
    out.write(msg + '\n')
    out.close()


def run_cells():
    sys.path.insert(0, SRC)
    import zl_core as ZL
    import cert_profile as CP
    import cert_v2 as C2
    CP.GT.check_increasing()
    zw, above = C2.make_zw(6006998.0)
    import json
    prof_code = [[float(a), float(b), str(Z)] for a, b, Z, ln in json.load(open(os.path.join(SRC, 'profile_v2.json')))['bands']]
    NI = Num(iv)
    cells = [
        (28.73, 28.734, 3), (28.996, 29.0, 3), (30.0, 30.004, 3), (130.5, 130.504, 3), (130.5, 130.504, 4),
        (299.996, 300.0, 4), (300.0, 300.0075, 4), (1000.0, 1000.025, 6),
        (147324.0, 147326.9465, 11), (150000.0, 150002.9, 11),
        (380000.0, 380007.4, 11), (380000.0, 380007.4, 12),
        (960000.0, 960018.8, 12), (960000.0, 960018.8, 13),
        (2377171.0, 2377171.7429, 13), (2440000.0, 2440000.74, 13), (2440000.0, 2440000.74, 14),
        (2377168.5, 2377169.2, 13),       # top of band 346 (window reaches band 347)
        (5000000.0, 5000000.772, 14), (6006997.2, 6006998.0, 14),   # last cell: window crosses V1
    ]
    extra = os.environ.get('EXTRA_CELLS')
    if extra:
        for tok in extra.split(';'):
            va, vb, n = tok.split(',')
            cells.append((float(va), float(vb), int(n)))
    out = open(os.path.join(HERE, 'cells_output.txt'), 'a')
    for va, vb, n in cells:
        i = band_of((va + vb) / 2)
        Zs = PROF[i][2]
        Zw_me = zw_exact(va, vb)
        Zw_code = zw(prof_code, va, vb, float(V0), 6006998.0)
        V = iv.mpf([va, vb])
        r = NI.cell(V, Zs, Zw_me, n)
        rc = ZL.cell_terms(ZL.arb(va), ZL.arb(vb), ZL.arb(Zs), Zw_code if Zw_code > ZL.arb(Zs) else ZL.arb(Zs), n)
        if r is None:
            msg = f"cell [{va}, {vb}] n={n}: indep constraints fail; code {'None' if rc is None else 'ok'}"
        else:
            mu, PE, dd = r
            PEb = NI.hi(PE)
            G, g = G_grid(mu)
            Gex = G_mp(mu)
            line = f"cell [{va}, {vb}] band {i} Z={Zs} Zw(me)={Zw_me} Zw(code)={Zw_code.str(12)} n={n}: "
            line += f"mu_low={mp.nstr(mu, 12)} PsiEta<= {mp.nstr(PEb, 15)} G(g={g})={mp.nstr(G, 15)} "
            line += f"rel.margin(grid)={mp.nstr((G - PEb) / G, 6)} rel.margin(exact G(mu_low))={mp.nstr((Gex - PEb) / Gex, 6)}"
            if rc is not None:
                muc, PEc = rc
                Gc = CP.GT.lower(muc)
                line += f" | code: mu_low={muc.str(12)} PsiEta<= {PEc.upper().str(15)} G={Gc.str(15)} rel={float(((Gc - PEc) / Gc).lower()):.6e}"
                line += f" | diff PsiEta (me - code) = {mp.nstr(PEb - mpf(PEc.upper().str(30, radius=False)), 4)}"
            else:
                line += " | code: None"
            msg = line
        print(msg, flush=True)
        out.write(msg + '\n')
    out.close()


def run_asym():
    """Float-level local requirement of this very method far above V1, if the lines were extended (n <= 30).
    Uses the point inequality with Zw = Z (no window effects)."""
    Nm = Num(mp)
    mp.dps = 30
    out = open(os.path.join(HERE, 'asym_output.txt'), 'w')
    for v in [1e3, 1e4, 1e5, 1e6, 2.4e6, 6e6, 1e7, 1e8, 1e9, 1e10, 1e12, 1e15, 1e20]:
        lo_, hi_ = mpf(3), mpf(25)
        for _ in range(40):
            Z = (lo_ + hi_) / 2
            Zs = mp.nstr(Z, 20)
            r = point_margin(Nm, v, Zs, Zs, range(3, 31))
            if r is not None and r[0] > 0:
                hi_ = Z
            else:
                lo_ = Z
        r = point_margin(Nm, v, mp.nstr(hi_, 20), mp.nstr(hi_, 20), range(3, 31))
        msg = f"v={v:.3g}: local Z requirement {mp.nstr(hi_, 6)} (line n={r[1]}); Bellotti Z_VK={mp.nstr(z_vk(v), 6)}; " \
              f"Ford-57.54 equiv={mp.nstr(z_vk(v) * mpf('57.54') / mpf('54.004'), 6)}"
        print(msg, flush=True)
        out.write(msg + '\n')
    out.close()


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'cells'
    if mode == 'cells':
        run_cells()
    elif mode == 'scan':
        run_scan(int(sys.argv[2]) if len(sys.argv) > 2 else 40)
    elif mode == 'asym':
        run_asym()
