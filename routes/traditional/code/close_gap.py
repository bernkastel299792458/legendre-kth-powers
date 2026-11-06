"""用光滑化 + Bellotti 完整表，严格覆盖 k 的缺口 [Prop 3.3 上限, L0(k)]。
用法：python close_gap.py K ZFR [HYB_CERT] [TAG]"""
import sys
import csv
from fractions import Fraction
import rigorous_hyb as RH
import rigorous_smooth as RS

k = int(sys.argv[1])
RS.CFG['zfr'] = sys.argv[2] if len(sys.argv) > 2 else 'thesis'
RS.CFG['full_table'] = True
hyb_file = sys.argv[3] if len(sys.argv) > 3 else f'../results/cert_hyb_k{k}.csv'
tag = sys.argv[4] if len(sys.argv) > 4 else ''
cert = list(csv.DictReader(open(hyb_file)))
L0 = min(Fraction(r['a']) for r in cert)
a0 = RH.prop33_ceiling_lower(k)
Ms = [3, 4, 2, 6, 8]
consts = {M: RS.weight_constants(M) for M in Ms}
pieces, a, w = [], a0, Fraction(1, 4)
fail = None
while a < L0:
    b = min(a + w, L0)
    got = None
    for M in Ms:
        d, det = RS.rig_delta_smooth(k, a, b, M, consts[M])
        if d is not None and d < 1:
            got = (a, b, M, d)
            break
    if got:
        pieces.append(got)
        a = b
        if got[3] < 0.9:
            w = min(w * 2, Fraction(4))
    else:
        if w <= Fraction(1, 256):
            fail = a
            break
        w /= 2
out = f'../results/cert_smooth_full_k{k}_{RS.CFG["zfr"]}{tag}.csv'
with open(out, 'w', newline='') as f:
    wr = csv.writer(f)
    wr.writerow(['k', 'a', 'b', 'M', 'delta_upper'])
    for p in pieces:
        wr.writerow([k, str(p[0]), str(p[1]), p[2], f'{p[3]:.6g}'])
top = pieces[-1][1] if pieces else a0
print(f"k={k} [{RS.CFG['zfr']}]: covered [{float(a0):.4f}, {float(top):.4f}] of window up to L0={float(L0):.4f}; "
      f"{len(pieces)} pieces; max delta={max((p[3] for p in pieces), default=None)}; "
      f"{'CLOSED' if fail is None else 'stuck at ' + str(float(fail))}", flush=True)
