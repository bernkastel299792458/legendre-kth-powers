"""Sensitivity of the archived k = 70 (bty_pub) and k = 74 (pub) certificates (manuscript §11).

Every archived certificate piece is re-evaluated with the same endpoints, under one modified input.
The evaluation uses Arb and the non-pure smooth delta; for S pieces both M = 2 and M = 3 are tried.
The cases are:
  Z1=<v>  The classical zero-free constant is replaced by v. Only S pieces are re-evaluated: H starts at
          log(2T) > 137, where the Littlewood region already dominates the classical one.
  C=<f>   All C entries of Bellotti's Table 2 are multiplied by f.
  JY=<f>  The Johnston-Yang constants 17.418 / 2.231 are multiplied by f.

This is a sensitivity analysis, not part of the proof. A failing piece could still be repaired by
re-optimising the chain, so the tolerances found here are lower bounds for what the method tolerates.

Usage: python sensitivity.py              (all cases; the output is saved as ../certificates/sensitivity_output.txt)
       python sensitivity.py K SET CASE"""
import sys
import os
import csv
import subprocess
from fractions import Fraction as F
from multiprocessing import Pool

CODE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, CODE)
import rigorous_smooth as RS  # noqa: E402
import rigorous_hyb as RH  # noqa: E402
from rigorous_smooth import A  # noqa: E402

CERT = os.path.join(CODE, '..', 'certificates')
ALL = [('70', 'bty_pub', c) for c in ['base', 'Z1=4.95', 'Z1=4.98', 'Z1=4.99', 'Z1=5.0', 'Z1=5.1', 'Z1=5.558691',
                                       'C=1.05', 'C=1.1', 'C=1.2', 'JY=1.5']] + \
      [('74', 'pub', c) for c in ['base', 'C=1.05', 'C=1.1', 'C=1.2', 'JY=1.5']]

K = SET = CASE = None
CONSTS = None


def setup():
    z1, z2, z3 = RS.ZFR[SET]
    if CASE.startswith('Z1='):
        z1 = A(CASE[3:])
    RS.ZFR['sens'] = (z1, z2, z3)
    RH.ZSETS['sens'] = (z1, z2, z3)
    RS.CFG['zfr'] = 'sens'
    RS.CFG['full_table'] = True
    RH.HYB_CFG['zfr'] = 'sens'
    if CASE.startswith('C='):
        f = A(CASE[2:])
        RS.LOW_ROWS[:] = [(T0, T1, s0, C * f, B) for (T0, T1, s0, C, B) in RS.LOW_ROWS]
        RS.HIGH_ROWS[:] = [(T0, T1, s0, C * f, B) for (T0, T1, s0, C, B) in RS.HIGH_ROWS]
        RH.ROWS[:] = [(T0, T1, s0, C * f, B) for (T0, T1, s0, C, B) in RH.ROWS]
    if CASE.startswith('JY='):
        f = A(CASE[3:])
        RH.B1, RH.B3 = RH.B1 * f, RH.B3 * f
        RS.B1, RS.B3 = RS.B1 * f, RS.B3 * f


def init(k, zset, case):
    global K, SET, CASE, CONSTS
    K, SET, CASE = k, zset, case
    setup()
    CONSTS = {M: RS.weight_constants(M) for M in (2, 3)}


def s_job(row):
    a, b = F(row['a']), F(row['b'])
    ds = [RS.rig_delta_smooth(K, a, b, M, CONSTS[M])[0] for M in (2, 3)]
    ds = [d for d in ds if d is not None]
    return float(a), (min(ds) if ds else float('inf'))


def h_job(row):
    a, b, c, s = F(row['a']), F(row['b']), F(row['c']), F(row['sigma_star'])
    d, _ = RH.rig_delta(K, a, b, c, s)
    return float(a), (d if d is not None else float('inf'))


def one(k, zset, case):
    tag = f'k{k}_{zset}'
    S = list(csv.DictReader(open(os.path.join(CERT, f'cert_smooth_v3_{tag}.csv'))))
    H = list(csv.DictReader(open(os.path.join(CERT, f'cert_hyb_v3_{tag}.csv'))))
    with Pool(max(1, (os.cpu_count() or 2) - 1), initializer=init, initargs=(k, zset, case)) as p:
        rs = p.map(s_job, S, chunksize=8)
        rh = [] if case.startswith('Z1=') else p.map(h_job, H, chunksize=8)
    ws = max(rs, key=lambda r: r[1])
    nf = sum(1 for r in rs if r[1] >= 1)
    line = f'k={k} {zset:8s} {case:12s} S: max delta {ws[1]:.4f} at L={ws[0]:.1f}, {nf}/{len(rs)} pieces >= 1'
    if rh:
        wh = max(rh, key=lambda r: r[1])
        nh = sum(1 for r in rh if r[1] >= 1)
        line += f' | H: max delta {wh[1]:.4f} at L={wh[0]:.1f}, {nh}/{len(rh)} pieces >= 1'
    else:
        line += ' | H: unaffected'
    print(line, flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 1:
        for args in ALL:
            subprocess.run([sys.executable, '-B', os.path.abspath(__file__)] + list(args), check=True)
    else:
        one(int(sys.argv[1]), sys.argv[2], sys.argv[3])
