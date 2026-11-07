"""Exploration (not a proof): smallest k whose sampled max delta < 1 when Bellotti's C is scaled.
Usage: python cscan.py F SCOPE KLO KHI   (SCOPE = all | low (rows with log T1 <= 80) | mid (46.2..70))
Prints, for each k tried by bisection, the worst sampled S and H values and where they occur."""
import sys, os
CODE = r'D:\UGit\AI4Math\legendre_k67\proof\code'
sys.path.insert(0, CODE)
from fractions import Fraction as F
from math import exp, log
from multiprocessing import Pool
import rigorous_smooth as RS
import rigorous_hyb as RH
import bound
import tail
from rigorous_smooth import A

FAC, SCOPE = sys.argv[1], sys.argv[2]
KLO, KHI = int(sys.argv[3]), int(sys.argv[4])
JYF = sys.argv[5] if len(sys.argv) > 5 else '1'


def in_scope(t0, t1):
    t0, t1 = float(t0), float(t1)
    if SCOPE == 'all':
        return True
    if SCOPE == 'low':
        return t1 <= 80.0001
    if SCOPE == 'mid':
        return t0 >= 46.1999 and t1 <= 70.0001
    a, b = (float(x) for x in SCOPE.split('-'))
    return t0 >= a - 1e-3 and t1 <= b + 1e-3


def setup():
    ZS = os.environ.get('ZSET', 'bty_pub'); RS.CFG['zfr'] = ZS; RS.CFG['full_table'] = True
    RH.HYB_CFG['zfr'] = ZS
    f = A(FAC); ff = float(FAC)
    RS.LOW_ROWS[:] = [(T0, T1, s0, C * f if in_scope(T0.mid(), T1.mid()) else C, B) for (T0, T1, s0, C, B) in RS.LOW_ROWS]
    RS.HIGH_ROWS[:] = [(T0, T1, s0, C * f if in_scope(T0.mid(), T1.mid()) else C, B) for (T0, T1, s0, C, B) in RS.HIGH_ROWS]
    RH.ROWS[:] = [(T0, T1, s0, C * f if in_scope(T0.mid(), T1.mid()) else C, B) for (T0, T1, s0, C, B) in RH.ROWS]
    bound.BELLOTTI_HIGH[:] = [(a, b, s, C * ff if in_scope(a, b) else C, B) for (a, b, s, C, B) in bound.BELLOTTI_HIGH]
    bound.BELLOTTI = bound.BELLOTTI_HIGH
    j = A(JYF)
    RH.B1, RH.B3 = RH.B1 * j, RH.B3 * j
    RS.B1, RS.B3 = RS.B1 * j, RS.B3 * j


CONSTS = None


def init():
    global CONSTS
    setup()
    CONSTS = {M: RS.weight_constants(M) for M in (2, 3)}


def s_job(args):
    k, a = args
    ds = [RS.rig_delta_smooth(k, a, a + F(1, 64), M, CONSTS[M])[0] for M in (2, 3)]
    ds = [d for d in ds if d is not None]
    return float(a), (min(ds) if ds else 9e9)


def h_job(args):
    k, a = args
    b = a + max(F(1, 64), F(int(a)) / 4000)
    best = 9e9
    try:
        c, sc = RH.pick_c(k, float(a), float(b))
        if sc < 5:
            for s in (F(985, 1000), F(99, 100)):
                d, _ = RH.rig_delta(k, a, b, RH.to_frac(c), s)
                if d is not None:
                    best = min(best, d)
    except Exception:
        pass
    return float(a), best


def run_k(pool, k):
    L1 = RH.prop33_ceiling_lower(k)
    sgrid = []
    a = F(L1)
    while a < 30000:
        sgrid.append((k, a)); a += F(25) if a < 10000 else F(250)
    hgrid = [(k, F(int(exp(log(2000) + i * (log(1e8) - log(2000)) / 80)))) for i in range(81)]
    S = pool.map(s_job, sgrid, chunksize=4)
    H = pool.map(h_job, hgrid, chunksize=1)
    s_fail = next((L for L, d in S if d >= 1), None)          # first S failure
    h_fail = max((L for L, d in H if d >= 1), default=None)    # last H failure
    h_from = min((L for L, d in H if h_fail is None or L > h_fail), default=None)  # H closes on samples >= h_from
    s_end = s_fail if s_fail is not None else 30000
    ok_split = h_from is not None and h_from <= s_end
    tail_ok = tail.check(F(10 ** 8), k=k, verbose=False)
    wsn = max(((L, d) for L, d in S if h_from is None or L <= h_from), key=lambda r: r[1], default=(None, 0))
    ok = ok_split and tail_ok
    print(f'  f={FAC} scope={SCOPE} JY={JYF} k={k}: {"CLOSES" if ok else "fails"}; L1={float(L1):.0f}; '
          f'first S fail={s_fail}; H closes from {h_from}; worst S below that={wsn[1]:.3f} at L={wsn[0]}; tail={tail_ok}', flush=True)
    return ok


if __name__ == '__main__':
    with Pool(15, initializer=init) as pool:
        lo, hi = KLO, KHI          # invariant: hi closes (assumed), lo fails (assumed)
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if run_k(pool, mid):
                hi = mid
            else:
                lo = mid
        print(f'RESULT f={FAC} scope={SCOPE} JY={JYF}: smallest k closing (samples) = {hi}', flush=True)
