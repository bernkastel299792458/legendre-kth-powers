"""Generate a full v5 certificate chain for one k (parallel, chunked).
Usage: python make_chain5.py K OUTTAG [L2MIN=..] [config keys as in cfg5.py]
Output: certs/<OUTTAG>_S.csv, certs/<OUTTAG>_H.csv, certs/<OUTTAG>.json (config + input hashes), certs/<OUTTAG>.log"""
import sys
import os
import csv
from fractions import Fraction as F
from math import exp, log
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prio  # noqa: E402,F401  (idle priority)
import cfg5  # noqa: E402
import rig5  # noqa: E402
import rigorous_smooth as RS  # noqa: E402
import rigorous_hyb as RH  # noqa: E402
import tail  # noqa: E402
import tail5  # noqa: E402
from flint import arb  # noqa: E402

K = int(sys.argv[1])
OUT = sys.argv[2]
P = cfg5.parse(sys.argv[3:])
L2MIN = F(P.pop('L2MIN', '0'))
L3 = F(int(float(P['L3'])))
MS = [int(m) for m in P['MS'].split(',')]
os.makedirs('certs', exist_ok=True)
LOG = open(f'certs/{OUT}.log', 'w', encoding='utf-8')


def say(*a):
    m = ' '.join(str(x) for x in a)
    print(m, flush=True)
    LOG.write(m + '\n')
    LOG.flush()


CONSTS = None


def init():
    global CONSTS
    cfg5.setup(P)
    CONSTS = {M: RS.weight_constants(M) for M in MS}


CGRID = [1.002, 1.005, 1.01, 1.02, 1.03, 1.05, 1.08, 1.12, 1.2, 1.3, 1.5, 2.0]


def _ev(a, top, c):
    """Best (delta, c, s, row) over sigma_star for one c (exact rig5 bound), or None."""
    if not (1 < c < K / 10):
        return None
    cf, best = RH.to_frac(c), None
    for s in (F(985, 1000), F(99, 100)):
        try:
            d, det = rig5.rig_delta5(K, a, top, cf, s)
        except Exception:
            d = None
        if d is not None and (best is None or d < best[0]):
            best = (d, cf, s, det['row'])
    return best


def _search_c(a, top, c_prev):
    """Choose c by minimising the rigorous rig5 delta: coarse grid (plus c_prev), then local refinement."""
    pool = [x for x in [_ev(a, top, c) for c in sorted(set(CGRID + ([c_prev] if c_prev else [])))] if x]
    if not pool:
        return None
    best = min(pool, key=lambda x: x[0])
    step = 0.25
    for _ in range(4):
        c0 = float(best[1])
        for c in ((c0 - 1) * (1 + step) + 1, (c0 - 1) * (1 - step) + 1):
            x = _ev(a, top, c)
            if x and x[0] < best[0]:
                best = x
        step /= 2
    return best


def h_chunk(args):
    """Cover [lo, hi] downward with Prop. H pieces; return (L0 reached, pieces).
    v2 (2026-11-07): c is chosen by minimising the rig5 delta itself (the v4 pick_c optimised a different,
    v4-only bound and produced deltas ~0.99999 where c = 1.03 gives 0.35).  Soundness is unchanged:
    every piece is accepted only if rig5 certifies delta < 1, and check5 recomputes every piece."""
    lo, hi = args
    top, w, pieces, c_prev = F(hi), F(1, 4), [], None
    while top > lo:
        a = max(top - w, F(lo))
        got = _ev(a, top, c_prev) if c_prev else None
        if got is None or got[0] >= 0.5:
            alt = _search_c(a, top, c_prev)
            if alt and (got is None or alt[0] < got[0]):
                got = alt
        if got is not None and got[0] < 1:
            d, cf, s, row = got
            pieces.append((a, top, cf, s, d, row))
            top, c_prev = a, float(cf)
            if d < 0.5:
                w = min(w * 2, F(int(float(a) / 200) + 1))
            elif d > 0.9:
                w = max(w / 2, F(1, 256))
        else:
            if w <= F(1, 256):
                return top, pieces
            w /= 2
    return top, pieces


def s_chunk(args):
    lo, hi = args
    a, w, pieces = F(lo), F(1, 16), []
    while a < hi:
        b = min(a + w, F(hi))
        best = None
        for M in MS:
            d, _ = RS.rig_delta_smooth(K, a, b, M, CONSTS[M])
            if d is not None and (best is None or d < best[1]):
                best = (M, d)
        if best and best[1] < 1 and (best[1] < 0.985 or (b - a) <= F(1, 64)):
            pieces.append((a, b, best[0], best[1]))
            a = b
            w = F(4) if best[1] < 0.8 else F(1) if best[1] < 0.9 else F(1, 4) if best[1] < 0.95 else F(1, 16)
        else:
            if w <= F(1, 1024):
                return None, (float(a), best)
            w /= 2
    return pieces, None


if __name__ == '__main__':
    cfg5.setup(P)
    cfg5.dump(P, f'certs/{OUT}.json')
    L1 = RH.prop33_ceiling_lower(K)
    D1, D2 = arb(39097000), arb(251949000000)
    num1 = K * (D1 - 1) - (arb(600) / K).exp()
    num2 = K * (D2 - 1) - (arb(L1.numerator) / L1.denominator / K).exp()
    U1 = K * (K * D1 * (1 - 1 / D1) ** 2).log()
    assert num1.lower() > 0 and num2.lower() > 0 and U1.lower() >= 600
    say(f'[{OUT}] k={K} L1={L1} ({float(L1):.3f}); numeric facts OK')
    assert cfg5.tail_check(P, L3, K), 'Lemma T failed'
    say(f'[{OUT}] Lemma T verified for L >= {L3}')
    with Pool(prio.NPROC, initializer=init) as pool:
        # H: chunks with log-spaced boundaries from 2500 to L3, processed top-down inside each chunk
        H0 = max(2500.0, float(L2MIN))  # no point covering below L2MIN with H
        edges = sorted({F(int(exp(log(H0) + i * (log(float(L3)) - log(H0)) / 60))) for i in range(61)} | {L3})
        edges = [e for e in edges if e <= L3]
        res = pool.map(h_chunk, list(zip(edges[:-1], edges[1:])), chunksize=1)
        # the H range is the longest suffix of fully covered chunks
        Hpieces, L0H = [], L3
        for (lo, hi), (reached, pcs) in reversed(list(zip(zip(edges[:-1], edges[1:]), res))):
            if reached > lo:
                Hpieces += pcs
                L0H = reached
                break
            Hpieces += pcs
            L0H = lo
        bounds = sorted(p[0] for p in Hpieces)
        L2 = next(a for a in bounds if a >= max(L0H, L2MIN))
        Hsub = sorted([p for p in Hpieces if p[0] >= L2], key=lambda p: p[0])
        say(f'[{OUT}] H: covered down to {float(L0H):.3f}; using [{L2}, {L3}], {len(Hsub)} pieces, '
            f'max delta {max(p[4] for p in Hsub):.6f}')
        # S: chunks of length 50 from L1 to L2
        sedges = [L1] + [F(int(x)) for x in range(int(L1) + 50, int(L2), 50)] + [L2]
        sedges = sorted(set(sedges))
        sres = pool.map(s_chunk, list(zip(sedges[:-1], sedges[1:])), chunksize=1)
    fails = [r[1] for r in sres if r[0] is None]
    if fails:
        say(f'[{OUT}] S FAILED at {fails[:5]}')
        sys.exit(1)
    Spieces = [p for r in sres for p in r[0]]
    with open(f'certs/{OUT}_S.csv', 'w', newline='') as f:
        wr = csv.writer(f)
        wr.writerow(['k', 'a', 'b', 'M', 'delta_upper'])
        for a, b, M, d in Spieces:
            wr.writerow([K, str(a), str(b), M, f'{d:.7g}'])
    with open(f'certs/{OUT}_H.csv', 'w', newline='') as f:
        wr = csv.writer(f)
        wr.writerow(['k', 'a', 'b', 'c', 'sigma_star', 'delta_upper', 'row'])
        for a, b, c, s, d, row in Hsub:
            wr.writerow([K, str(a), str(b), str(c), str(s), f'{d:.7g}', row])
    say(f'[{OUT}] S: {len(Spieces)} pieces cover [{L1}, {L2}], max delta {max(p[3] for p in Spieces):.6f}')
    say(f'[{OUT}] CHAIN GENERATED k={K}: L1={L1}, L2={L2}, L3={L3}')
