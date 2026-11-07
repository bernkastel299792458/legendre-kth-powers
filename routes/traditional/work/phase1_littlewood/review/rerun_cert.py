"""Re-run the certification in memory (writes nothing into ../), compare with cert_summary.json, and cross-check
zw_window against an independent window computation.  Also probes robustness:
  (a) every cell of every band re-certified exactly as cert_profile.certify_band does;
  (b) zw_window(...) >= independent max of the profile over the exact window, for every certified cell;
  (c) the per-cell minimum of mu_low (GTable domain [0.85, 1]).
Run:  python -I rerun_cert.py > rerun_cert_output.txt
"""
import os, sys, json, math
HERE = os.path.dirname(os.path.abspath(__file__))
PL = os.path.dirname(HERE)
sys.path.insert(0, PL)
import cert_profile as CP
from zl_core import arb, cell_terms

CP.GT.check_increasing()
d = json.load(open(os.path.join(PL, 'cert_summary.json')))
V0, V1 = d['V0'], d['V1']
prof = [[b['lo'], b['hi'], b['Z2']] for b in d['bands']]


def window_exact(va, vb):
    """independent: heights log u in [log(e^va - 1e10), log(16 e^vb + 1e10)] (mpmath, 50 digits)"""
    import mpmath as mp
    mp.mp.dps = 50
    lo = mp.log(mp.exp(mp.mpf(va)) - mp.mpf(10) ** 10)
    hi = mp.log(16 * mp.exp(mp.mpf(vb)) + mp.mpf(10) ** 10)
    m = mp.mpf(0)
    if lo <= V0:
        m = max(m, mp.mpf('5.558691') * mp.log(V0))
    if hi > V1:
        m = max(m, mp.mpf('21.233'))
    for a, b, Zs in prof:
        if b > lo and a < hi:      # (a, b] meets [lo, hi]
            m = max(m, mp.mpf(Zs))
    return m


tot_cells = 0
bad = []
minmu = 9
worst_w = 0
for i, (a, b, Z) in enumerate(prof):
    r = CP.certify_band(prof, i, V0, V1, 0.004, 1e-5)
    ref = d['bands'][i]
    same = (r['ok'] == ref['ok'] and r['cells'] == ref['cells'] and abs(r['minrel'] - ref['minrel']) < 1e-12)
    tot_cells += r['cells']
    if not (r['ok'] and same):
        bad.append((a, b, Z, r, ref))
    # window cross-check + mu_low range on the cells of this band (initial cells of width 0.004)
    m = max(1, math.ceil((b - a) / 0.004 - 1e-9))
    for j in range(m):
        va = a + (b - a) * j / m
        vb = a + (b - a) * (j + 1) / m
        Zw = CP.zw_window(prof, va, vb, V0, V1)
        Zx = window_exact(va, vb)
        if float(Zw.upper()) < float(Zx):
            bad.append(("window", va, vb, Zw, Zx))
        if j % 25 == 0:
            for n in (3, 4, 5):
                rr = cell_terms(arb(va), arb(vb), arb(Z), Zw if Zw > arb(Z) else arb(Z), n)
                if rr is not None:
                    minmu = min(minmu, float(rr[0].lower()))
    print(f"band ({a}, {b}] Z={Z}: ok={r['ok']} cells={r['cells']} minrel={r['minrel']:.3e} reproduces={same}", flush=True)
print("total cells:", tot_cells, " problems:", len(bad))
for x in bad[:10]:
    print("  PROBLEM:", x)
print("min mu_low over sampled cells:", minmu)
