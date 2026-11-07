"""Sampled scan (exploration, not a proof) for the smallest k with the v5 machinery.
Usage: python scan5.py KLO KHI [CS=1] [ROWS=path.csv[;path2.csv]] [ROWS_KEEP_ORIG=1] [BANDS=path.csv] [Z1=..] [Z2=..] [TAG=..]"""
import sys
import os
from fractions import Fraction as F
from math import exp, log
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prio  # noqa: E402,F401  (idle priority)
import phi5  # noqa: E402
import rig5  # noqa: E402
import rigorous_smooth as RS  # noqa: E402
import rigorous_hyb as RH  # noqa: E402
import tail  # noqa: E402
import tail5  # noqa: E402
from rigorous_hyb import A  # noqa: E402

KLO, KHI = int(sys.argv[1]), int(sys.argv[2])
import cfg5  # noqa: E402
P = cfg5.parse(sys.argv[3:])
MS = [int(m) for m in P['MS'].split(',')]


def setup():
    cfg5.setup(P)


CONSTS = None


def init():
    global CONSTS
    setup()
    CONSTS = {M: RS.weight_constants(M) for M in MS}


def s_job(args):
    k, a = args
    ds = []
    for M in MS:
        try:
            d = RS.rig_delta_smooth(k, a, a + F(1, 64), M, CONSTS[M])[0]
            if d is not None:
                ds.append(d)
        except Exception:
            pass
    return float(a), (min(ds) if ds else 9e9)


def h_job(args):
    k, a = args
    b = a + max(F(1, 64), F(int(a)) / 4000)
    best = 9e9
    cands = []
    try:
        c, _ = RH.pick_c(k, float(a), float(b))
        cands.append(c)
    except Exception:
        pass
    cands += [1.01, 1.03, 1.1, 1.3]
    for c in cands:
        for s in (F(985, 1000), F(99, 100)):
            try:
                d, _ = rig5.rig_delta5(k, a, b, RH.to_frac(c), s)
                if d is not None:
                    best = min(best, d)
            except Exception:
                pass
        if best < 1:
            break
    return float(a), best


def run_k(pool, k):
    L1 = RH.prop33_ceiling_lower(k)
    sgrid, a = [], F(L1)
    SMAX = int(P.get('SMAX', '30000'))
    while a < SMAX:
        sgrid.append((k, a))
        a += F(25) if a < 3500 else F(100) if a < 10000 else F(500) if a < 50000 else F(2500)
    hgrid = [(k, F(int(exp(log(2000) + i * (log(1e10) - log(2000)) / 90)))) for i in range(91)]
    S = pool.map(s_job, sgrid, chunksize=4)
    H = pool.map(h_job, hgrid, chunksize=1)
    s_fail = next((L for L, d in S if d >= 1), None)
    h_fail = max((L for L, d in H if d >= 1), default=None)
    h_from = min((L for L, d in H if h_fail is None or L > h_fail), default=None)
    ok = h_from is not None and h_from <= (s_fail if s_fail is not None else SMAX) and \
        cfg5.tail_check(P, 10 ** 10, k)
    wsn = max(((L, d) for L, d in S if h_from is None or L <= h_from), key=lambda r: r[1], default=(None, 0))
    print(f'  [{P["TAG"]}] k={k}: {"CLOSES" if ok else "fails"}; L1={float(L1):.0f}; first S fail={s_fail}; '
          f'H ok from {h_from}; worst S={wsn[1]:.3f} at L={wsn[0]}', flush=True)
    return ok


if __name__ == '__main__':
    with Pool(prio.NPROC, initializer=init) as pool:
        lo, hi = KLO, KHI
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if run_k(pool, mid):
                hi = mid
            else:
                lo = mid
        print(f'RESULT [{P["TAG"]}] min k (samples) = {hi}', flush=True)
