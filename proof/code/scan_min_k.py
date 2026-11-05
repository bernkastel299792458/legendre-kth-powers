"""对保守的零点自由区域常数组，严格抽样扫描各 k 在命题 S 窗口 [L_low(k), 7300] 上的最大 δ（逐点取 M ∈ {2,3} 中较小者）。
用法：python scan_min_k.py SET k1 k2
SET: bty_pub = (4.896, 21.233, 54.004)；pub = (5.558691, 21.233, 54.004)；r2008 = (4.896, 20.08, 54.004)（修复后的估计，仅作参考）"""
import sys
from fractions import Fraction as F
from multiprocessing import Pool
import rigorous_smooth as RS
from rigorous_smooth import A
import rigorous_hyb as RH

SETS = {'bty_pub': ("4.896", "21.233", "54.004"), 'pub': ("5.558691", "21.233", "54.004"),
        'r2008': ("4.896", "20.08", "54.004"), 'r1990': ("4.896", "19.90", "54.004")}


def job(args):
    name, k = args
    z = SETS[name]
    RS.ZFR[name] = tuple(A(s) for s in z)
    RS.CFG['zfr'] = name
    RS.CFG['full_table'] = True
    C = {M: RS.weight_constants(M) for M in (2, 3)}
    lo = RH.prop33_ceiling_lower(k)
    worst, wl = 0.0, None
    L = lo
    while L < 7300:
        a = F(L)
        d = min(RS.rig_delta_smooth(k, a, a + F(1, 64), M, C[M])[0] for M in (2, 3))
        if d > worst:
            worst, wl = d, float(a)
        L += F(25)
    return name, k, float(lo), worst, wl


if __name__ == '__main__':
    name = sys.argv[1]
    k1, k2 = int(sys.argv[2]), int(sys.argv[3])
    with Pool(8) as p:
        for name_, k, lo, w, wl in sorted(p.map(job, [(name, k) for k in range(k1, k2 + 1)]), key=lambda r: r[1]):
            print(f"{name_:8s} k={k:3d}  window [{lo:.1f}, 7300]  max delta_S (samples) = {w:.4f} at L={wl}  "
                  f"{'closes (samples)' if w < 1 else 'FAILS'}", flush=True)
