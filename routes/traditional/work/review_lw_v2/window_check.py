"""Compare the v2 window constant Z_w of cert_v2.make_zw with an exact high-precision recomputation (indep_v2.zw_exact)
on the cells nearest every band edge (first/last 40 initial cells of each band, at leaf width h0/2^k) plus the
middle cell.  A violation = code's Z_w smaller than the exact window maximum."""
import os, sys, json, math
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.abspath(os.path.join(HERE, '..', 'phase1_littlewood'))
sys.path.insert(0, SRC)
sys.path.insert(0, HERE)
from flint import arb
import cert_v2 as C2
import indep_v2 as I
from mpmath import mpf

d = json.load(open(os.path.join(SRC, 'profile_v2.json')))
prof = [[float(a), float(b), str(Z)] for a, b, Z, ln in d['bands']]
zw, above = C2.make_zw(float(d['V1']))
viol = 0
n = 0
strict_more = 0
for i, (a, b, Z) in enumerate(prof):
    h0 = 0.004 * max(1.0, a / 100) * (0.5 if a >= 300 else 1.0)
    m = max(1, math.ceil((b - a) / h0 - 1e-9))
    js = sorted(set(list(range(0, min(40, m))) + list(range(max(0, m - 40), m)) + [m // 2]))
    for j in js:
        va = a + (b - a) * j / m if j else a
        vb = a + (b - a) * (j + 1) / m if j + 1 < m else b
        zc = zw(prof, va, vb, float(d['V0']), float(d['V1']))
        ze = mpf(I.zw_exact(va, vb))
        zcm = mpf(zc.upper().str(40, radius=False))
        n += 1
        if zcm < ze:
            viol += 1
            print('VIOLATION', i, va, vb, zc, ze)
        elif zcm > ze + mpf('1e-12'):
            strict_more += 1
print(f"cells compared: {n}; violations (code Zw < exact): {viol}; code strictly larger (conservative over-inclusion): {strict_more}")
print("above V1 constant used:", above.str(25), " exact min(21.233, Z_VK(V1)) =", I.ZABOVE)
