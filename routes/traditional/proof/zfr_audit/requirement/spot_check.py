"""Main-thread spot check of fork B's key claims (independent of repair.py / reopt.py):
 (a) each claimed cover: exact contiguity [L1, 1e8] from the CSV alone, and a fresh re-evaluation under the model
     of the 40 pieces with the largest recorded delta (all must be rigorously < 1);
 (b) the failure claims: under Z2 = 19.90 / 20.08, Prop S pieces of width 1/256 near the reported binding
     heights, with every M in 2..6, all have delta >= 1; for 19.90 also width 1/4096 with M in 2..8.
     19.854687 (fork B's fail value, found with M <= 4) is printed for information only.

Usage: python -I spot_check.py
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
from fractions import Fraction as F
import common as C
import zfr_model as ZM
import priority_z2 as PZ

OUT = os.path.join(ZM.HERE, 'out')


def read_cover(fn):
    rows = list(csv.DictReader(open(os.path.join(OUT, fn))))
    pcs = []
    for r in rows:
        a, b = F(r['a']), F(r['b'])
        if r['method'] == 'S':
            pcs.append(('S', (a, b, int(r['M_or_c'])), float(r['delta_upper'])))
        else:
            pcs.append(('H', (a, b, F(r['M_or_c']), F(r['sigma_star'])), float(r['delta_upper'])))
    return pcs


def check_cover(name, fn, model, top=40):
    pcs = read_cover(fn)
    iv = sorted((p[1][0], p[1][1]) for p in pcs)
    contig = iv[0][0] == ZM.L1 and iv[-1][1] == ZM.L3 and all(iv[i][1] == iv[i + 1][0] for i in range(len(iv) - 1))
    worst = sorted(pcs, key=lambda p: -p[2])[:top]
    res = C.eval_all(model, [(k, p) for k, p, d in worst])
    ok = all(r[3] for r in res)
    mx = max(r[2] for r in res)
    print(f"[cover] {name}: pieces={len(pcs)} contiguous={contig} recorded_max={worst[0][2]:.9f} "
          f"re-eval top{top}: all<1={ok} max={mx:.9f}", flush=True)
    return contig and ok


def check_fail(name, model, Ls, width=F(1, 256), Ms=range(2, 7)):
    jobs = []
    for L in Ls:
        a = F(L)
        for M in Ms:
            jobs.append(('S', (a, a + width, M)))
    res = C.eval_all(model, jobs)
    best = {}
    for kind, p, d, ok in res:
        best[p[0]] = min(best.get(p[0], 9.0), d)
    allfail = all(not r[3] for r in res)
    print(f"[fail ] {name}: min over M={min(Ms)}..{max(Ms)} of delta at width {width}: " +
          ", ".join(f"L={float(k):.0f}: {v:.5f}" for k, v in sorted(best.items())) + f"  -> all >= 1: {allfail}",
          flush=True)
    return allfail


if __name__ == '__main__':
    good = True
    good &= check_cover('Z2=19.853906', 'cover_Z2_19.853906.csv', ZM.ZModel(Z2="19.853906"))
    good &= check_cover('Z1=4.90875', 'cover_Z1_4.908750.csv', ZM.ZModel(Z1="4.90875"))
    good &= check_cover('PROF_opt', 'cover_PROF_opt.csv', PZ.MODELS['PROF_opt'])
    good &= check_fail('Z2=19.90', ZM.ZModel(Z2="19.90"), [3960, 4000, 4050, 4200, 4250])
    good &= check_fail('Z2=20.08', ZM.ZModel(Z2="20.08"), [3960, 4100, 4300])
    good &= check_fail('Z2=19.90 (narrow)', ZM.ZModel(Z2="19.90"), [3960, 3961, 4250], width=F(1, 4096), Ms=range(2, 9))
    # informative only (not counted): fork B's fail value 19.854687 used M <= 4; with M <= 6 some heights recover
    check_fail('Z2=19.854687 [info]', ZM.ZModel(Z2="19.854687"), [4213, 4214, 4215])
    print("SPOT CHECK", "PASSED" if good else "HAS FAILURES")
