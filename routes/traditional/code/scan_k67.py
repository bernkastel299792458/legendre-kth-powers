"""对 k=67 在 L ∈ [2040, 240000] 上比较 KLN / BEL / HYB 三种模式的最优 δ。"""
import sys
from bound import delta, terms, chl_ceiling
from math import inf

k = int(sys.argv[1]) if len(sys.argv) > 1 else 67

def opt(L, mode, sstars=(0.985,)):
    best = (inf, None, None)
    for s in sstars:
        # 粗网格 + 细化
        cs = [1 + i * 2e-3 for i in range(1, 400)]
        for step in (2e-3, 2e-4, 2e-5):
            vals = [(delta(L, c / k, k, mode=mode, sstar=s), c) for c in cs]
            d, c = min(vals)
            cs = [c + j * step / 10 for j in range(-10, 11) if c + j * step / 10 > 1]
        if d < best[0]:
            best = (d, c, s)
    return best

print(f"k={k}, 下段上限 L ≤ {chl_ceiling(k):.1f}")
Ls = [2041, 2100, 2200, 2400, 2600, 2800, 3000, 3500, 4000, 4500, 5000, 5360, 5400, 5500, 6000,
      7000, 8000, 10000, 15000, 20000, 30000, 50000, 80000, 120000, 160000, 238050]
SS = (0.985, 0.988, 0.99, 0.992, 0.994, 0.996, 0.998)
print(f"{'L':>8} {'KLN':>10} {'BEL':>10} {'HYB':>10}  HYB(c, σ*)   u=θL")
for L in Ls:
    dk = opt(L, 'KLN')[0]
    db = opt(L, 'BEL')[0]
    dh, ch, sh = opt(L, 'HYB', SS)
    u = ch * L / k if ch else float('nan')
    print(f"{L:>8} {dk:>10.4g} {db:>10.4g} {dh:>10.4g}  ({ch}, {sh})  {u:.1f}")
