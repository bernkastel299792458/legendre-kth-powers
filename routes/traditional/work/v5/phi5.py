"""v5 zero-sum majorant Φ (generalises Lemma 5 of manuscript v4; rigorous, Arb).

New compared with proof/code/rigorous_smooth.Phi_upper:
  * several alternative density rows may cover the same heights (from CSV files); for each height we use the best one;
  * a height-dependent Littlewood zero-free region (local constants Z2_i on bands of v = log t);
  * Chourasiya-Simonic (CS) Cor. 1 density estimate as an extra option (only if enabled; status: preprint, under audit);
  * optional replacement of the Johnston-Yang KLN constants.
A cell [va, vb] is split at every row / band boundary inside it. For each sub-piece the best of all options is
taken, and then the maximum over the sub-pieces. Each option is a valid upper bound for every v in its sub-piece,
because v enters as an Arb ball and every zero-free width is a lower bound over the whole sub-piece.
"""
import sys
import os
import csv
from fractions import Fraction as F
CODE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'proof', 'code')
sys.path.insert(0, os.path.abspath(CODE))
from flint import arb  # noqa: E402
import rigorous_smooth as RS  # noqa: E402
import rigorous_hyb as RH  # noqa: E402
from rigorous_hyb import A, certainly_le  # noqa: E402

PI = arb.pi()


def af(fr):
    fr = F(fr)
    return arb(fr.numerator) / fr.denominator


# ---------------- configuration ----------------
CFG = dict(Z1=A("4.896"), Z2=A("21.233"), Z3=A("54.004"),
           KLN=(A("17.4193"), A("2.2311")),       # (I3) Johnston-Yang, sigma in [0.98, 1); 17.418 printed, 17.41921 recomputed (Phase 1a)
           # KLN-type forms: (B1, B3, power of v, coefficient of log v in lambda). 'JY': (log T)^{5-2s} -> v^3, -2 log v.
           # 'CSB': Chourasiya-Simonic (119) corrected (Phase 1a): A T^{8(1-s)/3}(log T)^{6-4s} + B log^2 T, s in [0.975,1],
           #        A <= 19.975, B <= 2.474 (rows of the corrected Table 4), T >= 3e12 -> v^2, -4 log v.  Depends on RZA preprint.
           KLNS=None,
           S1=F(49, 50),
           CS=False, CS_CONST=(A("50.58"), A("4.822"), A("85.51")), CS_SIGMA=F(31, 32),   # CS Cor. 1 (A), corrected (Phase 1a)
           ROWS=None,     # list of (T0, T1, s0 Fraction, C, B, tag) with arb T0, T1, C, B; None -> Bellotti original
           BANDS=[],      # list of (lo Fraction, hi Fraction, Z2 arb): no zeros with sigma > 1 - log v/(Z2 v), v in (lo, hi]
           CBANDS=[])     # list of (lo, hi, Z1): no zeros with sigma >= 1 - 1/(Z1 v), v in (lo, hi] (local classical)


def _frac_up(sx):
    """Exact Fraction for a decimal string; for 'LOG3E12' a rational upper bound of log(3e12)."""
    if sx == 'LOG3E12':
        lg = arb(3000000000000).log()
        f = F(int(float(lg.upper()) * 2 ** 20) + 1, 2 ** 20)
        assert certainly_le(lg, af(f))
        return f
    return F(sx)


def original_rows():
    """Bellotti Table 2 (arXiv v2), from the decimal source strings used in proof/code.
    Each row: (T0, T1, s0, C, B, tag, T0_up, T1_lo) with exact rational T0_up >= T0 and T1_lo <= T1."""
    out = []
    for src in RS.LOW_ROWS_SRC:
        out.append((RS._row(src)[0], A(src[1]), F(src[2]), A(src[3]), A(src[4]), 'bellotti', _frac_up(src[0]), F(src[1])))
    for t0, t1, s0, c, b in RH.BELLOTTI:
        out.append((A(t0), A(t1), F(985, 1000), A(c), A(b), 'bellotti', F(t0), F(t1)))
    return out


def load_rows_csv(path, tag=None, statuses=None):
    out = []
    with open(path, newline='', encoding='utf-8') as f:
        for r in csv.DictReader(f):
            if statuses and r.get('status', '') not in statuses:
                continue
            out.append((A(r['logT0']), A(r['logT1']), F(r['alpha0']), A(r['C']), A(r['B']), tag or r.get('status', 'csv'),
                        F(r['logT0']), F(r['logT1'])))
    return out


def load_bands_csv(path, col='Z2'):
    out = []
    with open(path, newline='', encoding='utf-8') as f:
        for r in csv.DictReader(f):
            if r.get('status', 'proved') != 'proved':
                continue
            out.append((F(r['logt_lo']), F(r['logt_hi']), A(r[col])))
    return sorted(out)


_IDX = {}


def rows():
    return CFG['ROWS'] if CFG['ROWS'] is not None else original_rows()


def klns():
    if CFG['KLNS'] is not None:
        return CFG['KLNS']
    B1, B3 = CFG['KLN']
    return [(B1, B3, 3, 2)]


CSB = (A("19.975"), A("2.474"), 2, 4)          # with RZA b4 = 0.5936 -- UNPROVED (RZA Thm 1.2 fails), reference only
CSB5161 = (A("17.384"), A("2.474"), 2, 4)      # with our Theorem R, b4 = 0.5161 (work/audit_rza/repair), sigma in [0.96875,1]

# Chourasiya-Simonic (119), corrected Table 4 rows (Phase 1a, work/phase1_cs/REPORT.md §2.2), T >= 3e12:
# N(s,T) <= A T^{8(1-s)/3} (log T)^{6-4s} + B log^2 T for s in [lo, hi].  Depends on RZA arXiv:2603.25961v3 Thm 1.2.
CSB_ROWS_5161 = [(F(15, 16), F(31, 32), A("15.248"), A("2.749")), (F(31, 32), F(39, 40), A("15.663"), A("2.474")),
                 (F(39, 40), F(157, 160), A("16.085"), A("2.420")), (F(157, 160), F(79, 80), A("16.513"), A("2.366")),
                 (F(79, 80), F(159, 160), A("16.946"), A("2.312")), (F(159, 160), F(1), A("17.384"), A("2.258"))]
CSB_ROWS = [(F(15, 16), F(31, 32), A("17.370"), A("2.750")), (F(31, 32), F(39, 40), A("17.875"), A("2.474")),
            (F(39, 40), F(157, 160), A("18.388"), A("2.420")), (F(157, 160), F(79, 80), A("18.909"), A("2.366")),
            (F(79, 80), F(159, 160), A("19.438"), A("2.312")), (F(159, 160), F(1), A("19.975"), A("2.258"))]


# Piecewise KLN-type rows for low sigma (work/phase1_cs/kln_rows_low_sigma.csv), plus Johnston-Yang Table 3 on [0.98, 1]:
# entries (sig_lo, sig_hi, C1, C2, form): N(s,T) <= C1 T^{8(1-s)/3} (log T)^{p(s)} + C2 log^2 T, T >= 3e12, s in [lo, hi],
# p(s) = 5 - 2s ('JY52') or 6 - 4s ('B119').  C1 is taken at the upper end and C2 at the lower end of each interval.
JY_TOP = [(F(49, 50), F(99, 100), A("16.848"), A("2.2311"), 'JY52'), (F(99, 100), F(1), A("17.4193"), A("2.1503"), 'JY52')]


def load_kln_rows(path, forms):
    out = []
    with open(path, newline='', encoding='utf-8') as f:
        for r in csv.DictReader(f):
            if r['form'] not in forms or F(r['sigma_lo']) == F(r['sigma_hi']):
                continue
            out.append((F(r['sigma_lo']), F(r['sigma_hi']), A(r['C1']), A(r['C2']), r['form']))
    return sorted(out)


_KSEG = {}


def _kseg():
    """Elementary sigma-segments between all KROWS breakpoints, each with the rows covering it."""
    ver = CFG.get('VER', 0)
    if _KSEG.get('ver') != ver:
        rows = CFG.get('KROWS') or []
        bps = sorted({r[0] for r in rows} | {r[1] for r in rows})
        segs = []
        for a, b in zip(bps[:-1], bps[1:]):
            cov = [r for r in rows if r[0] <= a and b <= r[1]]
            segs.append((a, b, cov))
        _KSEG.update(ver=ver, segs=segs, los=[x[0] for x in segs])
    return _KSEG


def kpw_integral(w, L, sa, top, cache=None):
    """Upper bound for int_{sa}^{top} N(s, e^w) x^{s-1} L ds using CFG['KROWS'] piecewise.
    On each elementary segment [a, b] (clipped at top) the best covering row is used, with (log T)^{p(s)} <= w^{p(a)}
    and the s-integral of exp(-(1-s)lam0) bounded by exp(-(1-b)lam0)/lam0. Returns None if [sa, top] is not covered.
    `cache` (dict) may hold full-segment terms for the same (w, L)."""
    lam0 = L - 8 * w / 3
    if not certainly_le(arb(1), lam0):
        return None
    ks = _kseg()
    segs, los = ks['segs'], ks['los']
    if not segs:
        return None
    topf = top if isinstance(top, F) else None
    i = _bisect.bisect_right(los, sa) - 1
    if i < 0 or not (segs[i][0] <= sa < segs[i][1]):
        return None
    tot = arb(0)
    cur = sa
    while i < len(segs):
        a, b, cov = segs[i]
        if not cov or a > cur:
            return None
        if topf is not None:
            if cur >= topf:
                break
            full = b <= topf
            bb = af(b) if full else af(topf)
        else:
            if certainly_le(top, af(cur)):
                break
            full = certainly_le(af(b), top)
            bb = af(b) if full else top
        ckey = (i, cur) if full else None
        if cache is not None and ckey is not None and ckey in cache:
            val = cache[ckey]
        else:
            aa = af(cur)
            val = None
            for lo, hi, C1, C2, form in cov:
                pw = (5 - 2 * aa) if form == 'JY52' else (6 - 4 * aa)
                v_ = (C1 * w ** pw * (L / lam0) * (-(1 - bb) * lam0).exp() + C2 * w ** 2 * (-(1 - bb) * L).exp()).upper()
                val = v_ if val is None or float(v_) < float(val) else val
            if cache is not None and ckey is not None:
                cache[ckey] = val
        tot += val
        if not full:
            break
        cur = b
        i += 1
    else:
        # ran past the last segment without reaching top
        if topf is None or cur < topf:
            return None
    return tot


S1_LIST = [F(9, 10), F(93, 100), F(19, 20), F(24, 25), F(97, 100), F(49, 50)]


def csbp_integral(v, L, sa, top):
    """Upper bound for int_{sa}^{top} N(s, e^v) x^{s-1} L ds using CSB_ROWS piecewise.
    sa: Fraction >= 15/16; top: Fraction or arb (upper end; an upper bound for it is fine)."""
    lam0 = L - 8 * v / 3
    if not certainly_le(arb(1), lam0):
        return None
    tot = arb(0)
    for lo, hi, Ar, Br in (CSB_ROWS_5161 if CFG.get('CSB_B4') == '0.5161' else CSB_ROWS):
        a = max(sa, lo)
        if isinstance(top, F):
            if a >= top:
                continue
            b = af(min(hi, top))
        else:
            if certainly_le(top, af(a)):
                continue
            b = af(hi) if certainly_le(af(hi), top) else top
        if a >= hi:
            continue
        aa = af(a)
        tot += Ar * v ** (6 - 4 * aa) * (L / lam0) * (-(1 - b) * lam0).exp() + Br * v ** 2 * (-(1 - b) * L).exp()
    return tot


def _index():
    """Group rows by their exact interval (T0_up, T1_lo); cached per row list."""
    rs = rows()
    key = id(rs)
    if _IDX.get('key') != key:
        groups = {}
        for r in rs:
            groups.setdefault((r[6], r[7]), []).append(r)
        # Pareto pruning inside each interval: drop a row if another row on the same interval has
        # alpha_0, B and C all <= (it is then never better). Dropping options cannot affect rigour.
        for iv, grp in groups.items():
            keep = []
            for r in grp:
                dom = False
                for o in grp:
                    if o is r:
                        continue
                    if o[2] <= r[2] and float(o[4].mid()) <= float(r[4].mid()) and float(o[3].mid()) <= float(r[3].mid())                             and (o[2] < r[2] or float(o[4].mid()) < float(r[4].mid()) or float(o[3].mid()) < float(r[3].mid())
                                 or id(o) < id(r)):
                        dom = True
                        break
                if not dom:
                    keep.append(r)
            groups[iv] = keep
        bpts = sorted({x for iv in groups for x in iv})
        _IDX.update(key=key, groups=sorted(groups.items()), bpts=bpts,
                    flat=[r for _, g in sorted(groups.items()) for r in g])
    return _IDX


def pruned_rows():
    return _index()['flat']


def containing_rows(p, q):
    out = []
    for (t0, t1), grp in _index()['groups']:
        if t0 <= p and q <= t1:
            out.extend(grp)
    return out


# ---------------- zero-free width ----------------
def eta_base(q):
    """Lower bound for eta at the single height v = q (arb); all three regions are decreasing in v (v > e)."""
    lu = q.log()
    e = [1 / (CFG['Z1'] * q), lu / (CFG['Z2'] * q), 1 / (CFG['Z3'] * q ** (arb(2) / 3) * lu ** (arb(1) / 3))]
    return max((x.lower() for x in e), key=float)


import bisect as _bisect
_BIDX = {}


def _band_index():
    ver = CFG.get('VER', 0)
    if _BIDX.get('ver') != ver:
        bl = sorted(CFG['BANDS'])
        cl = sorted(CFG['CBANDS'])
        _BIDX.update(ver=ver, bl=bl, blo=[b[0] for b in bl], cl=cl, clo=[b[0] for b in cl])
    return _BIDX


def _containing(lst, los, p, q):
    """Bands of a sorted list that contain (p, q]; bands may touch but are scanned around the bisect position."""
    out = []
    i = _bisect.bisect_right(los, p)
    for j in range(max(0, i - 3), min(len(lst), i + 1)):
        lo, hi, z = lst[j]
        if lo <= p and q <= hi:
            out.append(z)
    return out


def eta_piece(p, q):
    """Lower bound for eta(v) for all v in (p, q], where (p, q] lies inside one band or in no band (Fractions)."""
    qa = af(q)
    e = eta_base(qa)
    bi = _band_index()
    for z2 in _containing(bi['bl'], bi['blo'], p, q):
        loc = (qa.log() / (z2 * qa)).lower()
        if float(loc) > float(e):
            e = loc
    for z1 in _containing(bi['cl'], bi['clo'], p, q):
        loc = (1 / (z1 * qa)).lower()
        if float(loc) > float(e):
            e = loc
    return e


_LOGHR_LO = None


def loghr_lo():
    """Exact rational lower bound for log H_R (H_R = 3000175332800, RH verified up to H_R)."""
    global _LOGHR_LO
    if _LOGHR_LO is None:
        lg = RS.LOG_HR
        f = F(int(float(lg.lower()) * 2 ** 30) - 1, 2 ** 30)
        assert certainly_le(af(f), lg)
        _LOGHR_LO = f
    return _LOGHR_LO


_RUNMIN = {}


_RUNIDX = {}


def _run_index():
    """Breakpoints of all bands (>= 28.7296) and prefix minima of eta over the complete pieces between them."""
    ver = CFG.get('VER', 0)
    if _RUNIDX.get('ver') != ver:
        start = F(287296, 10000)
        pts = {start}
        for lo, hi, _ in CFG['BANDS'] + CFG['CBANDS']:
            for t in (lo, hi):
                if t > start:
                    pts.add(t)
        bps = sorted(pts)
        pref = []
        cur = None
        for a, b in zip(bps[:-1], bps[1:]):
            e = eta_piece(a, b)
            cur = e if cur is None or float(e) < float(cur) else cur
            pref.append(cur)
        _RUNIDX.update(ver=ver, bps=bps, pref=pref)
    return _RUNIDX


def eta_running(q):
    """Lower bound for the zero-free width over ALL heights H_R < t <= e^q (running minimum).
    Lemma 5 needs N(s, t) = 0 for s > 1 - eta, i.e. eta below the width at every height up to t, so with
    non-monotone local constants the running minimum (not the width at height t) must be used.
    Complete pieces between band breakpoints use precomputed prefix minima; the last partial piece is evaluated."""
    key = (q, CFG.get('VER', 0))
    if key in _RUNMIN:
        return _RUNMIN[key]
    ri = _run_index()
    bps, pref = ri['bps'], ri['pref']
    m = _bisect.bisect_right(bps, q) - 1          # bps[m] <= q < bps[m+1]
    best = None
    if m >= 1:
        best = pref[m - 1]                        # complete pieces (bps[i], bps[i+1]] with i < m
    if m >= 0 and q > bps[m]:
        e = eta_piece(bps[m], q)
        best = e if best is None or float(e) < float(best) else best
    if best is None:
        best = eta_base(af(q))
    if len(_RUNMIN) > 200000:
        _RUNMIN.clear()
    _RUNMIN[key] = best
    return best


def split_points(p, q):
    pts = {p, q}
    h = loghr_lo()
    if p < h < q:
        pts.add(h)
    import bisect
    b = _index()['bpts']
    i = bisect.bisect_right(b, p)
    while i < len(b) and b[i] < q:
        pts.add(b[i])
        i += 1
    for lo, hi, _ in CFG['BANDS'] + CFG['CBANDS']:
        for t in (lo, hi):
            if p < t < q:
                pts.add(t)
    return sorted(pts)


# ---------------- options ----------------
def opt_options(p_, q_, L, eta):
    """All valid upper bounds for Phi(e^v), v in [pa, qa] (arb balls of exact rationals)."""
    pa, qa = af(p_), af(q_)
    v = pa.union(qa)
    out = [(v.exp() * v / (2 * PI)).upper()]                      # (a) N(t)
    s1 = af(CFG['S1'])
    triv = v.exp() * v / (2 * PI) * (-(1 - s1) * L).exp()
    forms = []
    for B1, B3, pw, lc in klns():
        lam = L - 8 * v / 3 - lc * v.log()
        if certainly_le(arb(1), lam):
            forms.append((B1, B3, pw, lam))
            out.append((triv + B1 * v ** pw * (L / lam) * (-eta * lam).exp() + B3 * v ** 2 * (-eta * L).exp()).upper())  # (b)
    # (c) KLN on [s1, ss] + row on [ss, 1 - eta]; (d) CS variants
    cs_on = CFG['CS']
    if cs_on:
        c1, c2, c3 = CFG['CS_CONST']
        lam_c = L - 3 * v
        cs_ok = certainly_le(arb(1), lam_c)
        cs_variants = []
        if cs_ok:
            for sc in (CFG['CS_SIGMA'], F(49, 50)):
                s = af(sc)
                pexp = (7 - 5 * s) / (2 - s)
                trivc = v.exp() * v / (2 * PI) * (-(1 - s) * L).exp()
                cs_variants.append((sc, s, pexp, trivc))
                out.append((trivc + c1 * v ** pexp * (L / lam_c) * (-eta * lam_c).exp()
                            + (c2 * v ** 2 + c3 * v) * (-eta * L).exp()).upper())                  # (d1)
    top = 1 - eta
    csbp = CFG.get('CSBP', False)
    trivs = {}
    if csbp:
        for s1c in (F(15, 16), F(31, 32), F(39, 40), F(49, 50)):
            tv = v.exp() * v / (2 * PI) * (-(1 - af(s1c)) * L).exp()
            trivs[s1c] = tv
            ci = csbp_integral(v, L, s1c, top)
            if ci is not None:
                out.append((tv + ci).upper())                                                     # (e1)
    gtriv = {}
    kmemo = {}
    kcache = {}
    if CFG.get('KROWS'):
        for s1c in S1_LIST:
            if not certainly_le(af(s1c), top):
                continue
            tv = v.exp() * v / (2 * PI) * (-(1 - af(s1c)) * L).exp()
            gtriv[s1c] = tv
            ki = kpw_integral(v, L, s1c, top, kcache)
            if ki is not None:
                out.append((tv + ki).upper())                                                     # (g1)
    for T0, T1, s0, C, B, tag, T0f, T1f in containing_rows(p_, q_):
        lamB = L - B * v
        if not certainly_le(arb(1), lamB):
            continue
        rowpart = C * (L / lamB) * (-eta * lamB).exp()
        # (f) trivial bound below the row's own alpha_0, row on [alpha_0, 1 - eta]:
        #     sum x^{beta-1} <= N(t) x^{s0-1} + int_{s0}^{1-eta} N(s,t) x^{s-1} L ds
        if certainly_le(af(s0), top):
            trivr = v.exp() * v / (2 * PI) * (-(1 - af(s0)) * L).exp()
            out.append((trivr + rowpart).upper())
        for sf in sorted({s0, s0 + F(1, 1000), s0 + F(3, 1000), F(995, 1000)}):
            if sf < s0:
                continue
            ss = af(sf)
            if not certainly_le(ss, top):
                continue
            if sf >= CFG['S1']:
                for B1, B3, pw, lam in forms:
                    k1 = B1 * v ** pw * (L / lam) * (-(1 - ss) * lam).exp() + B3 * v ** 2 * (-(1 - ss) * L).exp()
                    out.append((triv + k1 + rowpart).upper())                                     # (c)
            for s1c, tv in gtriv.items():
                if sf > s1c:
                    kkey = (s1c, sf)
                    if kkey not in kmemo:
                        ki = kpw_integral(v, L, s1c, sf, kcache)
                        kmemo[kkey] = None if ki is None else (tv + ki)
                    if kmemo[kkey] is not None:
                        out.append((kmemo[kkey] + rowpart).upper())                               # (g2)
            if csbp:
                for s1c, tv in trivs.items():
                    if sf > s1c:
                        ci = csbp_integral(v, L, s1c, sf)
                        if ci is not None:
                            out.append((tv + ci + rowpart).upper())                               # (e2)
            if cs_on and cs_ok:
                for sc, s, pexp, trivc in cs_variants:
                    if sf >= sc:
                        part = c1 * v ** pexp * (L / lam_c) * (-(1 - ss) * lam_c).exp() \
                            + (c2 * v ** 2 + c3 * v) * (-(1 - ss) * L).exp()
                        out.append((trivc + part + rowpart).upper())                               # (d2)
    return out


def Phi_upper(va, vb, L):
    p, q = F(float(va.mid())), F(float(vb.mid()))
    assert va.rad() == 0 and vb.rad() == 0
    pts = split_points(p, q)
    worst = None
    for a_, b_ in zip(pts[:-1], pts[1:]):
        if b_ <= loghr_lo():
            # every t in this piece has t <= H_R: Phi_0(t) = sum over H_R < gamma < t = 0 exactly
            best = arb(0)
            worst = best if worst is None else worst.max(best).upper()
            continue
        eta = eta_running(b_)
        opts = opt_options(a_, b_, L, eta)
        best = min(opts, key=float)
        worst = best if worst is None else worst.max(best).upper()
    return worst


def install():
    """Route proof/code's Prop. S through this Phi."""
    RS.Phi_upper = Phi_upper
