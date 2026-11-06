"""If a Bellotti-type log-free bound N(s,T) <= C T^{B(1-s)} (s >= 0.985) held for log T in [log HR, 80),
what (B, C) would close the k=67 window [2041, 7000] (together with HYB for u >= 80)?"""
import bound
from bound import delta, LOG_HR
from math import inf
k = 67
BASE = list(bound.BELLOTTI)
Ls = list(range(2041, 7001, 50)) + [7000]

def optc(L, **kw):
    best = (inf, None)
    cs = [1 + i * 2e-3 for i in range(1, 300)]
    for step in (2e-3, 2e-4, 2e-5):
        d, c = min((delta(L, c / k, k, **kw), c) for c in cs)
        best = min(best, (d, c))
        cs = [c + j * step / 10 for j in range(-10, 11) if c + j * step / 10 > 1]
    return best

def window_ok(C, B, sstars=(0.985, 0.99, 0.995)):
    bound.BELLOTTI = [(LOG_HR, 80, 0.985, C, B)] + BASE
    worst = 0
    for L in Ls:
        d = min(min(optc(L, mode='HYB', sstar=s)[0] for s in sstars), optc(L, mode='KLN')[0])
        worst = max(worst, d)
        if d >= 1:
            break
    bound.BELLOTTI = BASE
    return worst < 1, worst

print("baseline: extend Bellotti row (80-90) down to log HR:", window_ok(3.7065573e5, 5.216))
for B in (4.0, 5.216, 6.0, 7.0, 8.0):
    lo, hi = 1.0, 1e12
    for _ in range(45):
        mid = (lo * hi) ** 0.5
        ok, _ = window_ok(mid, B)
        lo, hi = (mid, hi) if ok else (lo, mid)
    print(f"B={B:5.3f}: window closes iff C <~ {lo:.3e}")
