"""独立复核证书：重新用 arb 计算每一段的 δ 上界，并检查各段首尾相接、无缝覆盖 [L0, L_end]。
用法：python check_certificate.py [--zfr thesis|lw|lw_ref] CERT.csv"""
import csv
import sys
from fractions import Fraction
from rigorous_hyb import rig_delta

import rigorous_hyb as RH
args = sys.argv[1:]
if '--zfr' in args:
    i = args.index('--zfr'); RH.HYB_CFG['zfr'] = args[i + 1]; del args[i:i + 2]
EXPECT = None
if '--expect-range' in args:
    i = args.index('--expect-range'); EXPECT = (Fraction(args[i + 1]), Fraction(args[i + 2])); del args[i:i + 3]
rows = list(csv.DictReader(open(args[0])))
k = int(rows[0]['k'])
segs = sorted((Fraction(r['a']), Fraction(r['b']), Fraction(r['c']), Fraction(r['sigma_star'])) for r in rows)
if EXPECT is not None:
    assert segs[0][0] == EXPECT[0], f"first endpoint {segs[0][0]} != expected {EXPECT[0]}"
    assert segs[-1][1] == EXPECT[1], f"last endpoint {segs[-1][1]} != expected {EXPECT[1]}"
worst = 0.0
for i, (a, b, c, s) in enumerate(segs):
    assert a < b
    if i > 0:
        assert segs[i - 1][1] == a, f"gap/overlap at {a}"
    d, det = rig_delta(k, a, b, c, s)
    assert d is not None and d < 1, (a, b, d, det)
    worst = max(worst, d)
print(f"[zfr={RH.HYB_CFG['zfr']}, KLN=JY(17.418,2.231), sigma1=0.98] k={k}: certificate OK. {len(segs)} pieces cover [{float(segs[0][0]):.6f}, {float(segs[-1][1])}] exactly; "
      f"max delta_upper = {worst:.7f}")
