"""Check that the v-ball built in zl_core.cell_terms covers the closed cell [va, vb] for v2-sized cells,
and that the arb window inputs behave (exploration of 'float leaks')."""
import os, sys, json, math
SRC = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase1_littlewood'))
sys.path.insert(0, SRC)
from flint import arb, ctx
import zl_core  # sets ctx.prec = 128

d = json.load(open(os.path.join(SRC, 'profile_v2.json')))
bad = 0
tested = 0
for i, (a, b, Z, ln) in enumerate(d['bands']):
    a, b = float(a), float(b)
    h0 = 0.004 * max(1.0, a / 100) * (0.5 if a >= 300 else 1.0)
    m = max(1, math.ceil((b - a) / h0 - 1e-9))
    for j in [0, 1, m // 2, m - 1]:
        for depth in [0, 3, 7]:
            va = a + (b - a) * j / m if j else a
            vb = a + (b - a) * (j + 1) / m if j + 1 < m else b
            w = (vb - va) / 2 ** depth
            for s in [0, 2 ** depth - 1]:
                ca, cb = va + s * w, va + (s + 1) * w
                A_, B_ = arb(ca), arb(cb)
                v = (A_ + B_) / 2
                v = arb(v.mid(), ((B_ - A_) / 2).upper() * (1 + arb('1e-30')).upper())
                tested += 1
                if not (v.contains(A_) and v.contains(B_)):
                    bad += 1
                    print('NOT COVERED', i, ca, cb, v)
print(f"tested {tested} cells (incl. bisected); not covered: {bad}")
# exactness of float edges: consecutive initial-cell edges are shared, bisection midpoints shared by construction
print("float(28.73) - 28.73 =", float(arb(28.73) - arb('28.73')))
