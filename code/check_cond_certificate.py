"""复核条件证书（Theorem B）：python check_cond_certificate.py ../results/cert_cond_k67.csv"""
import csv
import sys
from fractions import Fraction
from rigorous_hyb import rig_delta

rows = list(csv.DictReader(open(sys.argv[1])))
k, z = int(rows[0]['k']), Fraction(rows[0]['z'])
segs = sorted((Fraction(r['a']), Fraction(r['b']), Fraction(r['c']), Fraction(r['sigma_star']), r['mode']) for r in rows)
worst, umax = 0.0, Fraction(0)
for i, (a, b, c, s, m) in enumerate(segs):
    if i:
        assert segs[i - 1][1] == a, f"gap at {a}"
    d, det = rig_delta(k, a, b, c, s, mode=m, z_hyp=z)
    assert d is not None and d < 1, (a, b, d, det)
    worst = max(worst, d)
    umax = max(umax, c * b / k)
print(f"k={k}: conditional certificate OK (z={float(z)}). Covers [{float(segs[0][0])}, {float(segs[-1][1]):.6f}]; "
      f"{len(segs)} pieces; max delta_upper={worst:.7f}; hypothesis needed for H_R<|t|<=e^{float(umax):.4f}")
