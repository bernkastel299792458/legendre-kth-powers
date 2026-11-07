"""Referee re-run of selected v2 bands with the CURRENT code of phase1_littlewood (read-only use).
Replicates cert_v2.run_certify / cert_profile.certify_band for chosen band indices, and additionally records the
cell attaining the minimum relative margin.  Usage:  python -I rerun_v2.py i1 i2 ...   (band indices, 0-based)
"""
import os, sys, json, math, time
SRC = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase1_littlewood')
sys.path.insert(0, os.path.abspath(SRC))
from zl_core import *
import cert_profile as CP
import cert_v2 as C2


def certify_band_track(profile, i, V0, V1, h0, hmin, lines):
    a, b, Z = profile[i]
    stack = []
    n_cells = 0
    best = (1.0, None, None, None)
    used = set()
    m = max(1, math.ceil((b - a) / h0 - 1e-9))
    edges = [a + (b - a) * j / m for j in range(m + 1)]
    edges[0], edges[-1] = a, b
    for j in range(m):
        stack.append((edges[j], edges[j + 1]))
    stack.reverse()
    fails = []
    depth_hist = {}
    while stack:
        va, vb = stack.pop()
        Zw = CP.zw_window(profile, va, vb, V0, V1)
        n, rel = CP.cell_ok(va, vb, Z, Zw, lines)
        if n is not None:
            n_cells += 1
            used.add(n)
            w = vb - va
            depth_hist[round(math.log2(h0 / w))] = depth_hist.get(round(math.log2(h0 / w)), 0) + 1
            if rel < best[0]:
                best = (rel, va, vb, n)
            continue
        if vb - va <= hmin:
            fails.append((va, vb, rel))
            if len(fails) > 3:
                break
            continue
        mid = (va + vb) / 2
        stack.append((mid, vb))
        stack.append((va, mid))
    return dict(ok=not fails, cells=n_cells, minrel=best[0], argmin=best[1:], lines=sorted(used), fails=fails[:3],
                depths=depth_hist)


def main(idx):
    CP.GT.check_increasing()
    d = json.load(open(os.path.join(SRC, 'profile_v2.json')))
    summ = json.load(open(os.path.join(SRC, 'cert_v2_summary.json')))
    V0_, V1 = float(d['V0']), float(d['V1'])
    zw, above = C2.make_zw(V1)
    CP.zw_window = zw
    prof = [[float(a), float(b), str(Z)] for a, b, Z, ln in d['bands']]
    lines = [tuple(ln) + tuple(n for n in (3, 4, 5) if n not in ln) for a, b, Z, ln in d['bands']]
    for i in idx:
        a, b = prof[i][0], prof[i][1]
        h0 = 0.004 * max(1.0, a / 100) * (0.5 if a >= 300 else 1.0)
        t0 = time.time()
        r = certify_band_track(prof, i, V0_, V1, h0, 2.5e-7 * max(1.0, a), lines[i])
        s = summ['bands'][i]
        same = (r['cells'] == s['cells'] and abs(r['minrel'] - s['minrel']) <= 1e-12 * max(1, abs(s['minrel']))
                and r['lines'] == s['lines'] and r['ok'] == s['ok'])
        print(f"band {i} ({a}, {b}] Z={prof[i][2]} lines_tried={lines[i]} h0={h0:.4g}: ok={r['ok']} cells={r['cells']} "
              f"minrel={r['minrel']:.6e} argmin={r['argmin']} used={r['lines']} depths={r['depths']} "
              f"| summary cells={s['cells']} minrel={s['minrel']:.6e} lines={s['lines']} -> REPRODUCED={same} "
              f"({time.time() - t0:.0f}s)", flush=True)


if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]])
