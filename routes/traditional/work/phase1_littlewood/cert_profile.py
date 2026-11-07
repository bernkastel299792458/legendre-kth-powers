"""Rigorous certification of a height-dependent Littlewood zero-free region (REPORT.md §2-§5).

  python -I cert_profile.py design            -> chooses bands/constants (float search, not a proof), writes profile_design.json
  python -I cert_profile.py certify [file]    -> certifies a profile (default profile_design.json) cell by cell in arb,
                                                 writes zfr_local.csv + cert_summary.json + cert_log.txt

Certification of a band (a, b] with constant Z: [a, b] is covered by closed cells [va, vb]; for each cell some
zeta-line n in {3,4,5} gives  PsiEta.upper() < G(mu_low).lower()  (zl_core.cell_terms), where the window constant
Zw is the max of the profile (incl. the classical region below V0 and the published 21.233 above V1) over all
heights log u in [va + log(1 - T0 e^-va), vb + log(16 + T0 e^-va)].
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json, time, math
from fractions import Fraction
from zl_core import *

HERE = os.path.dirname(os.path.abspath(__file__))
Z1_BELOW = arb('5.558691')      # classical region below V0: MTY 2024 (refereed), |t| >= 2
Z2_ABOVE = '21.233'             # Littlewood region above V1: Yang JMAA 2024 (refereed), |t| >= 3
MU_MIN = arb('0.85')
G_STEP = Fraction(1, 10000)


# ------------------------------------------------------------------ G table (lower bounds) + monotonicity
class GTable:
    def __init__(self):
        self.vals = {}
        self.verified_increasing = False

    def check_increasing(self, lo=Fraction(849, 1000), hi=Fraction(1), parts=151):
        """G'(mu) > 0 on [lo, hi]: evaluate G' with mu as a ball on `parts` subintervals."""
        for j in range(parts):
            a = lo + (hi - lo) * j / parts
            b = lo + (hi - lo) * (j + 1) / parts
            m = arb((a.numerator / arb(a.denominator) + b.numerator / arb(b.denominator)) / 2,
                    float(b - a) / 2 * (1 + 1e-9))
            d = G_of_mu(m, deriv=1)
            if not d.lower() > 0:
                raise RuntimeError(f"G' not certified positive on [{a}, {b}]: {d}")
        self.verified_increasing = True

    def lower(self, mu_low):
        """Rigorous lower bound for G(mu) valid for all mu in [mu_low, 1] (G increasing there): G(g) with g a grid
        point g = j/10^4 <= mu_low (checked exactly)."""
        assert self.verified_increasing
        m = float(mu_low.lower())
        if m < float(MU_MIN):
            return arb(-1)
        j = math.floor(m * 10000) - 1
        g = arb(j) / 10000
        assert g.upper() <= mu_low.lower()
        if j not in self.vals:
            self.vals[j] = G_of_mu(g)
        return arb(self.vals[j].lower())


GT = GTable()


# ------------------------------------------------------------------ profile helpers
def zw_window(profile, va, vb, V0, V1):
    """Exact upper bound (arb, exact value) for the max of Z over the window heights for t with log t in [va, vb]:
    heights log u in [va + log(1 - T0 e^-va), vb + log(16 + T0 e^-va)] (enlarged by 1e-9; floats only decide which
    bands meet the window).  Below V0 the classical region (MTY) counts as Z_eff = 5.558691 log V0; above V1 the
    published Littlewood region counts as 21.233.  profile entries: (a, b, Zstr)."""
    lo = va + math.log1p(-1e10 * math.exp(-va)) - 1e-9
    hi = vb + math.log(16 + 1e10 * math.exp(-va)) + 1e-9
    ups = []
    if lo < V0:
        ups.append((Z1_BELOW * arb(V0).log()).upper())
    if hi > V1:
        ups.append((arb(Z2_ABOVE) + arb('1e-20')).upper())   # strictly > 21.233 (Claim W, case log u > V1)
    for (a, b, Zs) in profile:
        if b >= lo and a <= hi:
            ups.append(arb(Zs).upper())
    if not ups:
        return arb(0)
    m = ups[0]
    for u in ups[1:]:
        if u > m:
            m = u
    return arb(m)


def cell_ok(va, vb, Z, Zw, lines=(3, 4, 5)):
    """Try the zeta lines; return (n, relative margin) of the first line that certifies, or (None, best margin).
    Z: band constant (decimal string or float), Zw: window constant (arb or float, an upper bound of the window max;
    max(Zw, Z) is used)."""
    best = (None, -9.0)
    Za = arb(Z) if isinstance(Z, str) else arb(Z)
    Zwa = Zw if isinstance(Zw, arb) else arb(Zw)
    if Zwa < Za:
        Zwa = Za
    for n in lines:
        r = cell_terms(arb(va), arb(vb), Za, Zwa, n)
        if r is None:
            continue
        mu, PE = r
        G = GT.lower(mu)
        marg = (G - PE).lower()
        rel = float(marg / G.lower()) if G.lower() > 0 else -9.0
        if marg > 0:
            return n, rel
        if rel > best[1]:
            best = (None, rel)
    return best


def certify_band(profile, i, V0, V1, h0, hmin):
    a, b, Z = profile[i]
    a, b = float(a), float(b)
    stack = []
    n_cells = 0
    minrel = 1.0
    lines_used = set()
    # split [a, b] into initial cells of width h0 (cell edges are exact decimals)
    m = max(1, math.ceil((b - a) / h0 - 1e-9))
    edges = [a + (b - a) * j / m for j in range(m + 1)]
    edges[0], edges[-1] = a, b
    for j in range(m):
        stack.append((edges[j], edges[j + 1]))
    stack.reverse()
    fails = []
    while stack:
        va, vb = stack.pop()
        Zw = zw_window(profile, va, vb, V0, V1)
        n, rel = cell_ok(va, vb, Z, Zw)
        if n is not None:
            n_cells += 1
            minrel = min(minrel, rel)
            lines_used.add(n)
            continue
        if vb - va <= hmin:
            fails.append((va, vb, rel))
            if len(fails) > 3:
                break
            continue
        mid = (va + vb) / 2
        stack.append((mid, vb))
        stack.append((va, mid))
    return dict(ok=not fails, cells=n_cells, minrel=minrel, lines=sorted(lines_used), fails=fails[:3])


# ------------------------------------------------------------------ local requirement (design only)
def z_local(v, Zw_extra=None, lines=(3, 4, 5)):
    """Smallest Z (to 1e-4) such that a tiny cell at v certifies with Zw = max(Z, Zw_extra)."""
    lo, hi = 17.0, 24.0
    for _ in range(26):
        Z = (lo + hi) / 2
        Zw = Z if Zw_extra is None else max(Z, float(Zw_extra))
        n, _r = cell_ok(v, v + 1e-7, Z, Zw, lines)
        if n is not None:
            hi = Z
        else:
            lo = Z
    return hi


def z_local_cell(va, vb, Zw_other, lines=(3, 4, 5)):
    lo, hi = 17.0, 24.0
    for _ in range(26):
        Z = (lo + hi) / 2
        n, _r = cell_ok(va, vb, Z, max(Z, float(Zw_other)), lines)
        if n is not None:
            hi = Z
        else:
            lo = Z
    return hi


def design(V0=30.0, V1=300.0, passes=3):
    GT.check_increasing()
    edges = []
    v = V0
    while v < V1 - 3 - 1e-9:
        edges.append(v)
        w = 1.0 if v < 140 else (2.0 if v < 200 else 5.0)
        v = min(V1 - 3, v + w)
    edges += [V1 - 3, V1]
    prof = [[edges[j], edges[j + 1], 0.0] for j in range(len(edges) - 1)]
    for p in range(passes):
        new = []
        for (a, b, Zold) in prof:
            pts = [a + (b - a) * q / 8 for q in range(9)] + [a + 1e-9, b - 1e-9]
            pts += [x for x in (b - 2.8, b - 2.0, b - 1.0, b - 0.5) if x > a]
            zl = 0.0
            for x in pts:
                extra = None if p == 0 else zw_window([(q[0], q[1], f"{q[2]:.3f}") for q in prof if q[0] != a],
                                                      x, x + 1e-7, V0, V1)
                zl = max(zl, z_local(x, extra))
            new.append([a, b, math.ceil((zl * (1 + 2e-4)) * 1000) / 1000])
        prof = new
        print("design pass", p, "done", flush=True)
    return prof


def run_design():
    t0 = time.time()
    prof = design()
    json.dump(dict(V0=30.0, V1=300.0, bands=[[a, b, f"{Z:.3f}"] for a, b, Z in prof]),
              open(os.path.join(HERE, 'profile_design.json'), 'w'), indent=1)
    for a, b, Z in prof:
        print(f"{a:8.2f} {b:8.2f} {Z:.3f}")
    print("design time", round(time.time() - t0, 1), "s")


def run_certify(fn, h0=0.004, hmin=1e-5, bump=0.001, max_rounds=8):
    GT.check_increasing()
    d = json.load(open(fn))
    V0, V1 = float(d['V0']), float(d['V1'])
    prof = [[float(a), float(b), str(Z)] for a, b, Z in d['bands']]
    log = open(os.path.join(HERE, 'cert_log.txt'), 'w')
    t0 = time.time()
    results = [None] * len(prof)
    todo = set(range(len(prof)))
    for rnd in range(max_rounds):
        bumped = []
        for i in sorted(todo):
            r = certify_band(prof, i, V0, V1, h0, hmin)
            r['Z'] = str(prof[i][2])
            results[i] = r
            msg = (f"round {rnd} band ({prof[i][0]:.3f}, {prof[i][1]:.3f}] Z={prof[i][2]}: "
                   f"{'OK' if r['ok'] else 'FAIL'} cells={r['cells']} minrel={r['minrel']:.2e} lines={r['lines']} "
                   f"{'fails=' + str(r['fails']) if not r['ok'] else ''}  t={time.time() - t0:.0f}s")
            print(msg, flush=True)
            log.write(msg + chr(10)); log.flush()
            if not r['ok']:
                zreq = 0.0
                for (va, vb, _rel) in r['fails']:
                    zw_other = zw_window([q for k, q in enumerate(prof) if k != i], va, vb, V0, V1)
                    zreq = max(zreq, z_local_cell(va, vb, zw_other))
                newZ = max(Fraction(prof[i][2]) + Fraction(bump).limit_denominator(10 ** 6),
                           Fraction(math.ceil(zreq * (1 + 1e-4) * 1000), 1000))
                prof[i][2] = f"{float(newZ):.3f}"
                assert Fraction(prof[i][2]) == newZ
                bumped.append(i)
        if not bumped:
            break
        # a bump changes the window constant Zw of bands within ~3 in v: re-certify those and the bumped ones
        todo = set()
        for i in bumped:
            for j in range(len(prof)):
                if prof[j][1] >= prof[i][0] - 3.0 and prof[j][0] <= prof[i][1] + 3.0:
                    todo.add(j)
    allok = all(r is not None and r['ok'] for r in results)
    # write interface file
    with open(os.path.join(HERE, 'zfr_local.csv'), 'w', newline='') as f:
        f.write("logt_lo,logt_hi,Z2,status,notes\n")
        for (a, b, Zs), r in zip(prof, results):
            st = "proved" if r['ok'] else "FAILED"
            f.write(f"{a:.6g},{b:.6g},{Zs},{st},own proof (thesis method; refereed inputs only); "
                    f"zeta line(s) n={'/'.join(map(str, r['lines']))}; cells={r['cells']}; min rel. margin={r['minrel']:.1e}\n")
    json.dump(dict(V0=V0, V1=V1, all_ok=allok, seconds=round(time.time() - t0),
                   bands=[dict(lo=a, hi=b, Z2=Zs, **{k: v for k, v in r.items() if k != 'Z'})
                          for (a, b, Zs), r in zip(prof, results)]),
              open(os.path.join(HERE, 'cert_summary.json'), 'w'), indent=1)
    msg = f"ALL BANDS CERTIFIED: {allok}  ({len(prof)} bands, {round(time.time() - t0)} s)"
    print(msg); log.write(msg + "\n"); log.close()


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'design':
        run_design()
    elif len(sys.argv) > 1 and sys.argv[1] == 'certify':
        run_certify(sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, 'profile_design.json'))
    else:
        print(__doc__)
