"""用 Lee 的 c 值检查 bound.py 是否复现 Lee Table 3 的阈值。"""
import bound
bound.KLN_MODE = "lee"   # 复现 Lee 时使用他的常数
from bound import delta
cases = [  # (k, mode, xA, c)
    (86, 'KLN', 2010, 1.22924), (90, 'KLN', 1997, 1.29478),
    (85, 'KLN', 6162, 1.08141), (85, 'BEL', 5587, 1.21712),
    (70, 'KLN', 580009, 1.01001), (70, 'BEL', 15951, 1.03001),
    (67, 'KLN', 37420887, 1.01001), (67, 'BEL', 238050, 1.00301),
]
for k, mode, xa, c in cases:
    d_at = delta(xa, c / k, k, mode=mode)
    d_below = delta(xa - 1, c / k, k, mode=mode)
    print(f"k={k:3d} {mode}  L={xa:>9}  c={c}  delta(L)={d_at:.6f}  delta(L-1)={d_below:.6f}")
