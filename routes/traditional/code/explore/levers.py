"""Exploration (not a proof): smallest k whose *sampled* max delta < 1 under modified inputs.
Usage: python levers.py KLO KHI key=value ...
keys: Z1 Z2 Z3 (zero-free constants; default 4.896 21.233 54.004), CF (Bellotti C factor), CBAND (a-b rows to scale),
      BF (Bellotti B factor), JY (factor on 17.418/2.231), CS (1 = add Chourasiya-Simonic Cor. 1 as option in Lemma 5),
      HR (RH verification height), MS (comma list of M, default 2,3), L3 (tail start, default 1e10), TAG (label)"""
import sys, os
CODE = r'D:\UGit\AI4Math\legendre_k67\proof\code'
sys.path.insert(0, CODE)
from fractions import Fraction as F
from math import exp, log
from multiprocessing import Pool
from flint import arb
import rigorous_smooth as RS
import rigorous_hyb as RH
import bound
import tail
from rigorous_smooth import A

KLO, KHI = int(sys.argv[1]), int(sys.argv[2])
P = dict(Z1='4.896', Z2='21.233', Z3='54.004', CF='1', CBAND='all', BF='1', JY='1', CS='0', HR='3000175332800',
         MS='2,3', L3='10000000000', TAG='')
for a in sys.argv[3:]:
    k_, v_ = a.split('=', 1); P[k_] = v_
MS = [int(m) for m in P['MS'].split(',')]
L3 = F(int(float(P['L3'])))


def in_band(t0, t1):
    if P['CBAND'] == 'all':
        return True
    a, b = (float(x) for x in P['CBAND'].split('-'))
    return t0 >= a - 1e-3 and t1 <= b + 1e-3


ORIG_PHI = RS.Phi_upper
CS_B1, CS_B2, CS_B3 = A("46.06"), A("4.897"), A("86.84")


def phi_cs(va, vb, L):
    """Chourasiya-Simonic (arXiv:2507.15184v2, Cor. 1, sigma in [0.96875,1], T >= 3e12):
    N(s,T) <= 46.06 T^{3(1-s)/(2-s)} (log T)^{(7-5s)/(2-s)} + 4.897 log^2 T + 86.84 log T.
    Options: (d1) trivial below s_c, CS on [s_c, 1-eta]; (d2) CS on [s_c, s*], Bellotti row on [s*, 1-eta]."""
    v = va.union(vb)
    eta = RS.eta_low_at(vb)
    lam_c = L - 3 * v
    out = []
    if not RS.certainly_le(arb(1), lam_c):
        return out
    for sc in (F(31, 32), F(49, 50)):
        s = arb(sc.numerator) / sc.denominator
        p = (7 - 5 * s) / (2 - s)
        triv = v.exp() * v / (2 * RS.PI) * (-(1 - s) * L).exp()
        cs_full = CS_B1 * v ** p * (L / lam_c) * (-eta * lam_c).exp() + (CS_B2 * v ** 2 + CS_B3 * v) * (-eta * L).exp()
        out.append((triv + cs_full).upper())
        # (d2) with Bellotti rows on [s*, 1-eta]
        vals, ok, inter = [], True, []
        for T0, T1, s0, C, B in RS.rows():
            if RS.certainly_le(T1, va) or RS.certainly_le(vb, T0):
                continue
            inter.append((T0, T1))
            lamB = L - B * v
            best_row = None
            if RS.certainly_le(arb(1), lamB):
                for sf in sorted({s0, s0 + F(1, 1000), s0 + F(3, 1000), F(995, 1000)}):
                    ss = arb(sf.numerator) / sf.denominator
                    if sf >= s0 and sf >= sc and RS.certainly_le(ss, 1 - eta):
                        part = CS_B1 * v ** p * (L / lam_c) * (-(1 - ss) * lam_c).exp() \
                            + (CS_B2 * v ** 2 + CS_B3 * v) * (-(1 - ss) * L).exp()
                        cand = (triv + part + C * (L / lamB) * (-eta * lamB).exp()).upper()
                        if best_row is None or float(cand) < float(best_row):
                            best_row = cand
            if best_row is None:
                ok = False; break
            vals.append(best_row)
        if ok and vals and any(RS.certainly_le(T0, va) for T0, T1 in inter) and any(RS.certainly_le(vb, T1) for T0, T1 in inter):
            m = vals[0]
            for x in vals[1:]:
                m = m.max(x)
            out.append(m.upper())
    return out


def phi_new(va, vb, L):
    best = ORIG_PHI(va, vb, L)
    for c in phi_cs(va, vb, L):
        if float(c) < float(best):
            best = c
    return best


def setup():
    z = (A(P['Z1']), A(P['Z2']), A(P['Z3']))
    RS.ZFR['lev'] = z; RH.ZSETS['lev'] = z
    RS.CFG['zfr'] = 'lev'; RS.CFG['full_table'] = True; RH.HYB_CFG['zfr'] = 'lev'
    cf, bf = A(P['CF']), A(P['BF'])
    sc = lambda T0, T1, C: C * cf if in_band(float(T0.mid()), float(T1.mid())) else C
    RS.LOW_ROWS[:] = [(T0, T1, s0, sc(T0, T1, C), B * bf) for (T0, T1, s0, C, B) in RS.LOW_ROWS]
    RS.HIGH_ROWS[:] = [(T0, T1, s0, sc(T0, T1, C), B * bf) for (T0, T1, s0, C, B) in RS.HIGH_ROWS]
    RH.ROWS[:] = [(T0, T1, s0, sc(T0, T1, C), B * bf) for (T0, T1, s0, C, B) in RH.ROWS]
    ff, bb = float(P['CF']), float(P['BF'])
    bound.BELLOTTI_HIGH[:] = [(a, b, s, C * ff if in_band(a, b) else C, B * bb) for (a, b, s, C, B) in bound.BELLOTTI_HIGH]
    bound.BELLOTTI = bound.BELLOTTI_HIGH
    j = A(P['JY'])
    RH.B1, RH.B3 = RH.B1 * j, RH.B3 * j
    RS.B1, RS.B3 = RS.B1 * j, RS.B3 * j
    hr = A(P['HR'])
    RH.HR, RH.LOG_HR = hr, hr.log()
    RS.HR, RS.LOG_HR = hr, hr.log()
    if P['CS'] == '1':
        RS.Phi_upper = phi_new


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
    for c0 in (None, 1.01, 1.05, 1.2):
        try:
            if c0 is None:
                c, sc = RH.pick_c(k, float(a), float(b))
            else:
                c = c0
            for s in (F(985, 1000), F(99, 100)):
                d, _ = RH.rig_delta(k, a, b, RH.to_frac(c), s)
                if d is not None:
                    best = min(best, d)
        except Exception:
            pass
        if best < 1:
            break
    return float(a), best


def tail_ok(k):
    try:
        return tail.check(L3, k=k, verbose=False, Z3=P['Z3'])
    except Exception:
        return False


def run_k(pool, k):
    L1 = RH.prop33_ceiling_lower(k)
    sgrid, a = [], F(L1)
    while a < 30000:
        sgrid.append((k, a)); a += F(25) if a < 10000 else F(250)
    top = float(L3)
    hgrid = [(k, F(int(exp(log(2000) + i * (log(top) - log(2000)) / 90)))) for i in range(91)]
    S = pool.map(s_job, sgrid, chunksize=4)
    H = pool.map(h_job, hgrid, chunksize=1)
    s_fail = next((L for L, d in S if d >= 1), None)
    h_fail = max((L for L, d in H if d >= 1), default=None)
    h_from = min((L for L, d in H if h_fail is None or L > h_fail), default=None)
    s_end = s_fail if s_fail is not None else 30000
    ok = h_from is not None and h_from <= s_end and tail_ok(k)
    wsn = max(((L, d) for L, d in S if h_from is None or L <= h_from), key=lambda r: r[1], default=(None, 0))
    print(f'  [{P["TAG"]}] k={k}: {"CLOSES" if ok else "fails"}; L1={float(L1):.0f}; first S fail={s_fail}; '
          f'H ok from {h_from}; worst S={wsn[1]:.3f} at L={wsn[0]}', flush=True)
    return ok


if __name__ == '__main__':
    with Pool(15, initializer=init) as pool:
        lo, hi = KLO, KHI
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if run_k(pool, mid):
                hi = mid
            else:
                lo = mid
        print(f'RESULT [{P["TAG"]}] {dict((k, v) for k, v in P.items() if k != "TAG")}: min k (samples) = {hi}', flush=True)
