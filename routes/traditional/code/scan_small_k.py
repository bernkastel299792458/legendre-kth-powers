"""
浮点探索（非严格）：在"光滑化 + 拼接密度 + Bellotti 完整表"之下，对较小的 k 估计
  L_low(k)：下段（Lee Prop 3.3 / Cully-Hugill–Lee）能覆盖到的上限，k·log(kΔ(1−1/Δ)^2)
  L0(k)  ：解析起点 = 最后一个 δ_s ≥ 1 的 L（往上直到 1e15 都 < 1）
  以及窗口 (L_low, L0) 内的最大 δ_s。
与 smooth.delta_smooth 相同的上界，只是 v 积分只在 g 开始下降之后的 60 个单位内进行（之前 g ≡ 1，没有贡献），
因此能处理很大的 L。尾部用格子末端的值粗略估计。
"""
import sys
from math import log, exp, inf
import numpy as np
import bound
import smooth as S
from bound import LOG_HR, chl_ceiling

bound.use_full_bellotti(True)
CONSTS = {M: S.weight_constants(M) for M in (3, 4, 6, 8)}


def delta_fast(L, k, M, s1, dv=0.05, span=60.0, zfix=None):
    R, ratio_max = CONSTS[M]
    eps = k * exp(-L / k)
    v0 = L / k - log(k)
    logA = [log(R[j]) + j * log(1 + eps) + j * v0 for j in range(M + 1)]
    vstart = max(LOG_HR, min(logA[j] / j for j in range(1, M + 1)) - 0.5)
    vend = max(vstart, v0) + span
    total, v = 0.0, vstart
    last_phi = 0.0
    while v < vend:
        vm = v + dv / 2
        vals = [logA[j] - j * vm for j in range(M + 1)]
        j = int(np.argmin(vals))
        if j > 0:
            ph = S.Phi(vm, L, s1=s1, Zfix=zfix)
            total += ph * j * exp(vals[j]) * dv
            last_phi = ph
        v += dv
    vals = [logA[j] - j * vend for j in range(M + 1)]
    total += last_phi * exp(min(vals)) * 2  # 尾部粗估
    low = 2 * bound.HR * LOG_HR / (2 * 3.141592653589793) * exp(-L / 2)
    e_pp = ratio_max * ((1 + 1.93378e-8) * (1 + eps) ** 0.5 - 0.999) / k * exp(L * (1 / k - 0.5))
    return 2 * total + low + e_pp


def best_delta(L, k):
    s1 = 0.675 if k >= 4 else 0.61   # k=3 时需要 1−σ1 > 1/3
    return min(delta_fast(L, k, M, s1) for M in CONSTS)


def scan(k, Lmax=1e15, ratio=1.03):
    lo = chl_ceiling(k)
    L, last_fail, worst, wl = lo, None, 0.0, None
    while L < Lmax:
        d = best_delta(L, k)
        if d >= 1:
            last_fail = L
        if d > worst:
            worst, wl = d, L
        L *= ratio
    return lo, last_fail, worst, wl


if __name__ == '__main__':
    ks = [int(a) for a in sys.argv[1:]] or [67, 66, 65, 64, 60, 55, 50, 45, 40, 35, 30, 25, 20, 15, 12, 11, 10, 8, 6, 5, 4, 3]
    for k in ks:
        lo, lf, worst, wl = scan(k)
        L0 = lf if lf else lo
        print(f"{k}\t{lo:.1f}\t{L0:.4g}\t{worst:.3g}\t{wl:.4g}", flush=True)
