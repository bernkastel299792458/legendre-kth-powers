"""Task 3.1(a): per-piece ZFR thresholds with the certificates' OWN parameters (pieces, M, c, sigma*).
For each family (see common.family_model) and each certificate piece, bisect for the weakest constant
that keeps that piece's rigorous delta < 1.  The global fixed-certificate threshold is the min over pieces;
it is then confirmed by one full rigorous pass at a value rounded to the safe side.
Usage: python -I fixed_thresholds.py FAMILY LO HI      (writes out/fixed_FAMILY.csv)"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
import time
from math import floor
import common as C
import zfr_model as ZM

if __name__ == '__main__':
    fam, lo, hi = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
    os.makedirs(os.path.join(C.ZM.HERE, 'out'), exist_ok=True)
    t = time.time()
    jobs = [('S', p) for p in C.load_smooth()] + [('H', p) for p in C.load_hyb()]
    res = C.bisect_all(jobs, fam, lo, hi, rel=1e-6)
    out = os.path.join(ZM.HERE, 'out', f'fixed_{fam}.csv')
    with open(out, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['kind', 'a', 'b', 'L_a', 'L_b', 'params', 'status', 'thr_ok', 'thr_fail'])
        for kind, piece, r in res:
            st = r[0]
            ok_, fail_ = (r[1], r[2]) if st == 'thr' else ((r[1], '') if st == 'beyond' else ('', r[1]))
            w.writerow([kind, str(piece[0]), str(piece[1]), f"{float(piece[0]):.6f}", f"{float(piece[1]):.6f}",
                        ' '.join(str(x) for x in piece[2:]), st, ok_, fail_])
    thr = [(r[1], kind, piece) for kind, piece, r in res if r[0] == 'thr']
    fails = [(kind, piece) for kind, piece, r in res if r[0] == 'fails']
    print(f"family {fam}: {len(res)} pieces, {len(thr)} with finite threshold in [{lo},{hi}], "
          f"{len(fails)} failing already at the strong end, time {time.time()-t:.0f}s")
    if thr:
        thr.sort(key=lambda x: x[0])
        for v, kind, piece in thr[:8]:
            print(f"  {kind} L=[{float(piece[0]):.4f},{float(piece[1]):.4f}] params={piece[2:]}  threshold ~ {v:.7f}")
        # rigorous confirmation at the safe side (6 decimals, rounded towards the strong end)
        xs = floor(thr[0][0] * 1e6) / 1e6
        res2 = C.eval_all(C.family_model(fam, f"{xs:.6f}"), jobs)
        okall = all(r[3] for r in res2)
        wd = max(res2, key=lambda r: r[2])
        print(f"  CONFIRM {fam} = {xs:.6f}: all {len(res2)} pieces rigorously delta<1: {okall}; "
              f"max delta {wd[2]:.7f} at L={float(wd[1][0]):.4f} ({wd[0]})")
