"""复核光滑化证书链：各段重新严格计算并检查首尾相接。
python check_smooth_chain.py [--zfr thesis|lw|...] [--pure-arb] [--expect-range A B] [--old-table] FILE1 FILE2 ...
--expect-range A B：断言证书恰好从 A 开始、到 B 结束（有理数，如 2089605/1024）。
默认：zfr = thesis，使用 Bellotti 完整表。"""
import csv
import sys
from fractions import Fraction
import rigorous_smooth as RS

args = sys.argv[1:]
if '--zfr' in args:
    i = args.index('--zfr'); RS.CFG['zfr'] = args[i + 1]; del args[i:i + 2]
EXPECT = None
if '--expect-range' in args:
    i = args.index('--expect-range'); EXPECT = (Fraction(args[i + 1]), Fraction(args[i + 2])); del args[i:i + 3]
PURE = False
if '--pure-arb' in args:
    args.remove('--pure-arb'); PURE = True
if '--old-table' in args:
    args.remove('--old-table'); RS.CFG['full_table'] = False
segs = []
for fn in args:
    for r in csv.DictReader(open(fn)):
        segs.append((Fraction(r['a']), Fraction(r['b']), int(r['M']), int(r['k'])))
segs.sort()
if EXPECT is not None:
    assert segs[0][0] == EXPECT[0], f"first endpoint {segs[0][0]} != expected {EXPECT[0]}"
    assert segs[-1][1] == EXPECT[1], f"last endpoint {segs[-1][1]} != expected {EXPECT[1]}"
consts = {}
worst = 0
for i, (a, b, M, k) in enumerate(segs):
    if i:
        assert segs[i - 1][1] == a, f"gap/overlap at {float(a)}"
    if M not in consts:
        consts[M] = RS.weight_constants(M)
    if PURE:
        d, det = RS.rig_delta_smooth_pure(k, a, b, M, consts[M])
        assert d is not None and (1 - d).lower() > 0, (float(a), float(b), M, d)   # 严格判断 d < 1
        d = float(d)
    else:
        d, det = RS.rig_delta_smooth(k, a, b, M, consts[M])
        assert d is not None and d < 1, (float(a), float(b), M, d)
    worst = max(worst, d)
print(f"[zfr={RS.CFG['zfr']}, full_table={RS.CFG['full_table']}, pure_arb={PURE}] chain OK: {len(segs)} pieces cover [{float(segs[0][0]):.6f}, {float(segs[-1][1]):.6f}] exactly; "
      f"M used = {sorted(consts)}; max delta_upper = {worst:.6f}")
