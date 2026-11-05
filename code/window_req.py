"""k=67 剩余窗口 [2041, ~7000] 的量化需求。"""
import bound
from bound import delta, terms
from math import inf, log
k = 67
Ls = [2041, 2500, 3000, 3500, 4000, 4500, 5000, 5500, 6000, 6500, 7000]

def optc(L, **kw):
    best = (inf, None)
    cs = [1 + i * 2e-3 for i in range(1, 300)]
    for step in (2e-3, 2e-4, 2e-5):
        d, c = min((delta(L, c / k, k, **kw), c) for c in cs)
        if d < best[0]:
            best = (d, c)
        cs = [c + j * step / 10 for j in range(-10, 11) if c + j * step / 10 > 1]
    return best

# (1) 需要的固定 Littlewood 常数 Z（仅在 HR < t ≤ e^u 内使用），KLN 与 HYB 取优
print("(1) 窗口内每个 L 需要的零点自由区域常数 Z（当前已知 19.62；classical 等效 4.862·loglog t）")
for L in Ls:
    lo, hi = 1.0, 40.0
    for _ in range(40):
        z = (lo + hi) / 2
        d = min(optc(L, mode='KLN', Z=z)[0], optc(L, mode='HYB', Z=z)[0])
        lo, hi = (z, hi) if d < 1 else (lo, z)
    d, c = optc(L, mode='KLN', Z=lo)
    print(f"  L={L:5d}  Z_needed={lo:7.3f}   (KLN 最优 c={c:.4f}, u={c*L/k:.1f})")

# (2) 截断误差理想化为 0 后 KLN 还差多少
print("(2) 若截断误差 = 0 且 c→1（理想截断），KLN δ：")
orig = bound.truncation_constants
bound.truncation_constants = lambda th: (0.0, 0.8) if th < 0.1 else None
for L in Ls:
    d, c = optc(L, mode='KLN')
    print(f"  L={L:5d}  δ={d:.3f}  c={c:.4f}")
bound.truncation_constants = orig
