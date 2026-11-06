"""Hypothetical log-free density N(s,T) <= C T^{B(1-s)} for s >= 0.985, log T in [log HR, U).
Find the largest C (for given B) closing the k=67 gap L in [2041, 7100]; Bellotti's real rows used above U."""
import bound
from bound import delta, LOG_HR
from math import inf
k = 67
BASE = list(bound.BELLOTTI)
Ls = list(range(2041, 7101, 25))

def optc(L, **kw):
    best = (inf, None)
    cs = [1 + i * 2e-3 for i in range(1, 300)]
    for step in (2e-3, 2e-4, 2e-5):
        d, c = min((delta(L, c / k, k, **kw), c) for c in cs)
        best = min(best, (d, c))
        cs = [c + j * step / 10 for j in range(-10, 11) if c + j * step / 10 > 1]
    return best

def worst(C, B, U):
    rows = [(LOG_HR, U, 0.985, C, B)]
    for T0, T1, s0, C0, B0 in BASE:
        if T1 > U:
            rows.append((max(T0, U), T1, s0, C0, B0))
    bound.BELLOTTI = rows
    w, wl = 0, None
    for L in Ls:
        d = min(min(optc(L, mode='HYB', sstar=s)[0] for s in (0.985, 0.99)), optc(L, mode='KLN')[0])
        if d > w:
            w, wl = d, L
        if d >= 1:
            break
    bound.BELLOTTI = BASE
    return w, wl

U = 120
for B in (4.0, 5.216, 6.0, 8.0):
    lo, hi = 1.0, 1e9
    for _ in range(40):
        mid = (lo * hi) ** 0.5
        w, _ = worst(mid, B, U)
        lo, hi = (mid, hi) if w < 1 else (lo, mid)
    w, wl = worst(lo, B, U)
    print(f"U={U}, B={B:5.3f}: need C <= {lo:.3e}   (worst delta {w:.3f} at L={wl})", flush=True)
