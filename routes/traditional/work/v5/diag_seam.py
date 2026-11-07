"""Diagnostic (float, not a proof): where does delta_S come from at a given (k, L)?
Prints the largest contributions (S'_i - S'_{i-1}) * g_i by height cell, and which option wins there.
Usage: python diag_seam.py K L M [config keys]"""
import sys
import os
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cfg5  # noqa: E402
import phi5  # noqa: E402
import rigorous_smooth as RS  # noqa: E402
from flint import arb  # noqa: E402

K, L0, M = int(sys.argv[1]), F(sys.argv[2]), int(sys.argv[3])
P = cfg5.parse(sys.argv[4:])
cfg5.setup(P)
R_up, ratio = RS.weight_constants(M)
k = arb(K)
L = phi5.af(L0).union(phi5.af(L0 + F(1, 64)))
eps = k * (-L / k).exp()
v0 = L / k - k.log()
logA = [arb(R_up[j]).log() + j * (1 + eps).log() + j * v0 for j in range(M + 1)]


def g_up(v):
    return min(1.0, min(float((logA[j] - j * v).exp().upper()) for j in range(1, M + 1)))


vstart = F(int(max(float(RS.LOG_HR.lower()), min(float((logA[j] / j).lower()) for j in range(1, M + 1)) - 0.5) * 64), 64)
Vf = float(v0.mid()) + 30
rows, va, Sprev = [], vstart, 0.0
while float(va) < Vf:
    off = float(va) - float(v0.mid())
    dv = F(1, 64) if off < 12 else (F(1, 16) if off < 25 else F(1, 4))
    vb = va + dv
    pts = phi5.split_points(va, vb)
    S, win = 0.0, None
    for a_, b_ in zip(pts[:-1], pts[1:]):
        eta = phi5.eta_piece(a_, b_)
        opts = phi5.opt_options(a_, b_, L, eta)
        i = min(range(len(opts)), key=lambda j: float(opts[j]))
        if float(opts[i]) > S:
            S, win = float(opts[i]), i
    Sp = max(Sprev, S)
    contrib = (Sp - Sprev) * g_up(phi5.af(va))
    rows.append((contrib, float(va), S, win, float(phi5.eta_piece(va, vb))))
    Sprev = Sp
    va = vb
tot = sum(r[0] for r in rows)
print(f'k={K} L={float(L0)} M={M}: v0 = log(x/h) = {float(v0.mid()):.3f}; zero part 2*sum = {2 * tot:.4f}')
for c, v, S, win, eta in sorted(rows, reverse=True)[:12]:
    print(f'  v={v:8.4f}  contrib={2 * c:.4e}  Phi={S:.3e}  option#{win}  eta={eta:.5f}  g={g_up(phi5.af(F(v))):.3e}')
# share by height band
bands = {}
for c, v, *_ in rows:
    b = int(v)
    bands[b] = bands.get(b, 0) + 2 * c
print('  by integer v:', {b: round(x, 4) for b, x in sorted(bands.items()) if x > 1e-3})
