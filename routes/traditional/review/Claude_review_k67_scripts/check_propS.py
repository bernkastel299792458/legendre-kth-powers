"""Prop. S spot checks: pointwise delta_S at both ends and the midpoint of selected pieces of
proof/certificates/cert_smooth_full_k67_lw_jy.csv (the 4 worst pieces + 3 others), same M as the piece.
Reproduces report Appendix A.2.
Run:  python -B check_propS.py     (about 2 minutes, single process)"""
import sys
sys.dont_write_bytecode = True
import csv
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import indep_check as I
from indep_check import mp, mpf, Rj, deltaS

I.mp.dps = 30
cert = list(csv.DictReader(open(ROOT / 'proof' / 'certificates' / 'cert_smooth_full_k67_lw_jy.csv')))
segs = sorted(cert, key=lambda r: -float(r['delta_upper']))[:4] + [cert[0], cert[300], cert[-1]]
Rc = {2: Rj(2), 3: Rj(3)}
bad = 0
for r in segs:
    a, b, M = Fr(r['a']), Fr(r['b']), int(r['M'])
    vals = [deltaS(mpf(Lq.numerator) / Lq.denominator, M, 'lw', R=Rc[M]) for Lq in (a, (a + b) / 2, b)]
    ok = max(vals) <= mpf(r['delta_upper'])
    bad += not ok
    print(f"S piece [{float(a):.4f},{float(b):.4f}] M={M} cert={r['delta_upper']} "
          f"pointwise(a,mid,b)={[mp.nstr(v, 7) for v in vals]} {'OK' if ok else '**EXCEEDS**'}", flush=True)
print('Prop. S spot checks:', 'all pointwise values <= certificate' if bad == 0 else f'{bad} pieces exceed')
