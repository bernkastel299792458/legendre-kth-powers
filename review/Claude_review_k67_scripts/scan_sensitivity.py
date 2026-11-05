"""Pointwise margin and sensitivity of delta_S in the bottleneck region, plus the
'no thesis constant' scan. Reproduces report §4 M1/M2 tables and Appendix A.3/A.4.

Each job resets the module state before applying its perturbation (an earlier draft of this scan
mutated module globals inside worker processes; those numbers were discarded).
Run:  python -B scan_sensitivity.py     (about 5 minutes with 16 processes)"""
import sys
sys.dont_write_bytecode = True
import os, time, collections
from pathlib import Path
from multiprocessing import Pool

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

TAGS = ('base', 'Z1x1.005', 'Z1x1.01', 'Bx1.005', 'Bx1.01', 'Cx1.05')


def job(args):
    L, M, zs, tag = args
    import indep_check as I
    from mpmath import mpf
    I.mp.dps = 30
    if not hasattr(I, '_ORIG'):
        I._ORIG = (dict(I.Z), list(I.ROWS))
    I.Z = dict(I._ORIG[0]); I.ROWS = list(I._ORIG[1])       # reset state for every job
    if tag.startswith('Z1x'):                                # scale the classical zero-free constant (4.896)
        z = I.Z[zs]; I.Z[zs] = (z[0] * mpf(tag[3:]), z[1], z[2])
    if tag.startswith('Bx'):                                 # scale every Bellotti B
        f = mpf(tag[2:]); I.ROWS = [(a, b, c, C, B * f) for a, b, c, C, B in I.ROWS]
    if tag.startswith('Cx'):                                 # scale every Bellotti C
        f = mpf(tag[2:]); I.ROWS = [(a, b, c, C * f, B) for a, b, c, C, B in I.ROWS]
    return (L, M, zs, tag, float(I.deltaS(mpf(L), M, zs)))


if __name__ == '__main__':
    jobs = [(L, M, 'lw', t) for L in range(3550, 3951, 50) for M in (2, 3) for t in TAGS]
    jobs += [(L, 4, 'lw', 'base') for L in (3700, 3750, 3800)]
    jobs += [(L, M, 'nothesis', 'base') for L in (3900, 4000, 4500, 5000, 5500, 6000, 6500, 7000) for M in (2, 3)]
    t0 = time.time()
    with Pool(min(16, os.cpu_count() or 1)) as p:
        res = p.map(job, jobs, chunksize=1)
    tab = collections.defaultdict(dict)
    for L, M, zs, tag, d in res:
        tab[(zs, L)][(tag, M)] = d
    print("constants 'lw' (4.896, 19.62, 54.004); entry = min over M in {2,3}  (M=2 / M=3)")
    print('L     ' + ' '.join(f'{t:>22s}' for t in TAGS))
    for (zs, L) in sorted(x for x in tab if x[0] == 'lw'):
        row = tab[(zs, L)]
        print(L, ' ', ' '.join(f'{min(row[(t, 2)], row[(t, 3)]):7.4f} ({row[(t, 2)]:.3f}/{row[(t, 3)]:.3f}) ' for t in TAGS))
    print('M=4 base:', {L: round(tab[('lw', L)][('base', 4)], 4) for L in (3700, 3750, 3800)})
    print("constants 'nothesis' (4.896, 21.233, 53.989): L, M=2, M=3, min")
    for (zs, L) in sorted(x for x in tab if x[0] == 'nothesis'):
        row = tab[(zs, L)]
        print(L, f"{row[('base', 2)]:.4f} {row[('base', 3)]:.4f} {min(row[('base', 2)], row[('base', 3)]):.4f}")
    print(f'time {time.time() - t0:.0f}s')
