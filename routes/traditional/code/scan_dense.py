"""Dense scan of HYB for k=67: find threshold L* and check delta<1 on [L*, 240000] (grid only)."""
import csv, sys
from bound import delta
from math import inf
k = int(sys.argv[1]) if len(sys.argv) > 1 else 67

def optc(L, mode='HYB', sstars=(0.985, 0.99)):
    best = (inf, None, None)
    for s in sstars:
        cs = [1 + i * 2e-3 for i in range(1, 300)]
        for step in (2e-3, 2e-4, 2e-5):
            d, c = min((delta(L, c / k, k, mode=mode, sstar=s), c) for c in cs)
            if d < best[0]:
                best = (d, c, s)
            cs = [c + j * step / 10 for j in range(-10, 11) if c + j * step / 10 > 1]
    return best

grid = list(range(6500, 12000, 5)) + list(range(12000, 60000, 50)) + list(range(60000, 240001, 500))
rows, fails = [], []
for L in grid:
    d, c, s = optc(L)
    rows.append((L, d, c, s))
    if d >= 1:
        fails.append(L)
with open(f'../results/k{k}_hyb_scan.csv', 'w', newline='') as f:
    w = csv.writer(f); w.writerow(['L', 'delta', 'c', 'sstar']); w.writerows(rows)
last_fail = max(fails) if fails else None
print('last failing grid L:', last_fail)
print('max delta above it:', max(d for L, d, c, s in rows if last_fail is None or L > last_fail))
