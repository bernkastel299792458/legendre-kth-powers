"""Optimistic model of smoothing: truncation error -> 0 (theta free, c -> 1+).
(1) delta over the window with existing zero information (KLN / HYB);
(2) Z needed per L under ideal truncation."""
import bound
from bound import delta
from math import inf
k = 67
bound.truncation_constants = lambda th: (0.0, 0.8) if th < 0.1 else None

def optc(L, mode, Z=None, ss=(0.985,)):
    best = (inf, None)
    for s in ss:
        cs = [1 + i * 2e-3 for i in range(1, 300)]
        for step in (2e-3, 2e-4, 2e-5):
            d, c = min((delta(L, c / k, k, mode=mode, Z=Z, sstar=s), c) for c in cs)
            if d < best[0]: best = (d, c)
            cs = [c + j * step / 10 for j in range(-10, 11) if c + j * step / 10 > 1]
    return best

print("(1) ideal truncation, existing zero info")
first_ok = None
for L in list(range(2041, 7001, 100)):
    d = min(optc(L, 'KLN')[0], optc(L, 'HYB', ss=(0.985, 0.99))[0])
    print(f"  L={L}: delta={d:.3f}")
print("(2) ideal truncation: Z needed")
for L in (2041, 2500, 3000, 3500, 4000, 4500, 5000, 5500, 6000):
    lo, hi = 1.0, 40.0
    for _ in range(35):
        z = (lo + hi) / 2
        d = min(optc(L, 'KLN', Z=z)[0], optc(L, 'HYB', Z=z)[0])
        lo, hi = (z, hi) if d < 1 else (lo, z)
    d, c = optc(L, 'KLN', Z=lo)
    print(f"  L={L}: Z_needed={lo:.3f}  u={c*L/k:.1f}")
