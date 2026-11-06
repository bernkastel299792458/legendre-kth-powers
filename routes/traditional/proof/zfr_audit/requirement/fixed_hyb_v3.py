"""Per-piece thresholds of the v3 Prop. H certificate (cert_hyb_v3_k67_lw.csv, L in [7219, 1e8]) with its own
parameters, for Z2 (Littlewood) and Z3 (VK); single process (Prop. H evaluations are ~20 us).
Usage: python -I fixed_hyb_v3.py      (writes out/fixed_hyb_v3.csv)"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
import common as C
import zfr_model as ZM


def thr(piece, fam, lo, hi, rel=1e-7):
    ok = lambda x: C.piece_ok('H', piece, C.family_model(fam, f"{x:.10g}"))[3]
    if ok(hi):
        return ('beyond', hi)
    if not ok(lo):
        return ('fails', lo)
    g, b = lo, hi
    while b - g > rel * g:
        m = (g + b) / 2
        g, b = (m, b) if ok(m) else (g, m)
    return ('thr', g)


if __name__ == '__main__':
    H = C.load_hyb()
    print('base H certificate:', C.USED['H'], len(H), 'pieces')
    rows = []
    for p in H:
        r2 = thr(p, 'Z2', 19.62, 200.0)
        r3 = thr(p, 'Z3', 54.004, 1e4)
        rows.append((p, r2, r3))
    with open(os.path.join(ZM.HERE, 'out', 'fixed_hyb_v3.csv'), 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['a', 'b', 'c', 'sigma_star', 'Z2_status', 'Z2_thr', 'Z3_status', 'Z3_thr'])
        for p, r2, r3 in rows:
            w.writerow([str(p[0]), str(p[1]), str(p[2]), str(p[3]), r2[0], r2[1], r3[0], r3[1]])
    for name, idx in (('Z2', 1), ('Z3', 2)):
        t = [(r[idx][1], r[0]) for r in rows if r[idx][0] == 'thr']
        f = [r[0] for r in rows if r[idx][0] == 'fails']
        print(f"{name}: {len(t)} pieces with finite threshold, {len(f)} failing at the strong end")
        if t:
            v, p = min(t, key=lambda x: x[0])
            print(f"   min threshold {v:.6f} on L = [{float(p[0]):.3f}, {float(p[1]):.3f}]")
            for Lc in (7219, 7500, 8000, 10000, 20000, 1e5, 1e6, 1e7):
                u = [x for x in t if float(x[1][0]) >= Lc]
                if u:
                    v, p = min(u, key=lambda x: x[0])
                    print(f"   L >= {Lc:g}: min {v:.4f} at L = {float(p[0]):.1f}")
