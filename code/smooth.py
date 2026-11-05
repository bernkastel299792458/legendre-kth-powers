"""
光滑化显式公式的上界（float 探索版）。推导见 docs/smoothing.md。

取权 φ(y) = y^M (1−y)^M（y∈[0,1]，其余为 0），F(t) = φ((t−x)/h)。显式公式
  Σ Λ(n)F(n) = ∫F − Σ_ρ F̂(ρ) − ∫ F(t)/(t^3−t) dt,  F̂(s) = ∫ F(t) t^{s−1} dt
对 F ∈ C^1、紧支于 (1,∞) 成立，并且零点和绝对收敛。每个零点有
  |F̂(ρ)|/(h∫φ) ≤ x^{β−1} g(|γ|),  g(t) = min_{0≤j≤M} R_j (1+ε)^j (x/(h t))^j,  R_j = ‖φ^{(j)}‖_1/∫φ。
于是
  δ_s = 2∫_{H_R}^∞ Φ(t)(−g'(t))dt + 2N(H_R)x^{−1/2} + (maxφ/∫φ)(E_pp + 1/(x^3−x)),
其中 Φ(t) ≥ Σ_{H_R<γ≤t} x^{β−1} 是由密度估计和零点自由区域得到的上界。δ_s < 1 ⇒ (x, x+h) 中有素数。
"""
from math import log, pi, sqrt, inf
from math import exp as _exp


def exp(x):
    return _exp(x) if x < 700 else inf
import numpy as np
from numpy.polynomial import polynomial as P
import bound
from bound import LOG_HR, Z_eff

B1, B3 = 17.418, 2.231   # Johnston–Yang (2023) Table 3，σ ∈ [0.98, 1)


def weight_constants(M):
    """φ = y^M(1−y)^M：返回 (R_0..R_M, maxφ/∫φ)。"""
    c = P.polypow([0, 1], M)
    c = P.polymul(c, P.polypow([1, -1], M))
    integ = P.polyval(1, P.polyint(c)) - P.polyval(0, P.polyint(c))
    ys = np.linspace(0, 1, 200001)
    R = []
    d = c.copy()
    for j in range(M + 1):
        vals = np.abs(P.polyval(ys, d))
        l1 = np.trapezoid(vals, ys)
        R.append(l1 / integ)
        d = P.polyder(d)
    maxphi = 0.25 ** M
    return R, maxphi / integ


def eta_known(v):
    """已知零点自由区域在高度 e^v 处的宽度（与 Lee 的 Z_eff 一致，含 Ford）。"""
    return log(v) / (Z_eff(v) * v)


def Phi(v, L, s1=0.98, sstars=(0.985, 0.99, 0.995), Zfix=None):
    """Φ(e^v) 的上界：Σ_{H_R<γ≤e^v} x^{β−1}（不含 ±γ 的因子 2）。在若干合法选项中取最小。"""
    eta = eta_known(v) if Zfix is None else log(v) / (min(Zfix, Z_eff(v)) * v)
    triv = exp(v + log(v) - log(2 * pi) - (1 - s1) * L)
    lam = L - 8 * v / 3 - 2 * log(v)
    best = exp(v) * v / (2 * pi)  # 平凡上界 N(t)
    if lam > 1:
        top = 1 - eta
        kln = B1 * v ** 3 * L / lam * exp(-eta * lam) + B3 * v ** 2 * exp(-eta * L)
        best = min(best, triv + kln)
        row = bound.bellotti(v)
        if row is not None:
            C, B, s0 = row
            lamB = L - B * v
            if lamB > 1:
                for ss in sorted(set(list(sstars) + [s0, s0 + 0.001, s0 + 0.003])):
                    if ss >= s0 and ss < top:
                        k1 = B1 * v ** 3 * L / lam * exp(-(1 - ss) * lam) + B3 * v ** 2 * exp(-(1 - ss) * L)
                        bel = C * L / lamB * exp(-eta * lamB)
                        best = min(best, triv + k1 + bel)
    return best


def delta_smooth(L, k, M=4, consts=None, Zfix=None, dv=0.02, vmax_extra=60):
    R, ratio_max = consts if consts else weight_constants(M)
    eps = k * exp(-L / k)
    v0 = L / k - log(k)                     # log(x/h)
    # g(e^v) = min_j R_j (1+ε)^j e^{j(v0 − v)}；log A_j = log R_j + j log(1+ε) + j v0
    logA = [log(R[j]) + j * log1p_(eps) + j * v0 for j in range(M + 1)]

    def g_and_slope(v):
        vals = [logA[j] - j * v for j in range(M + 1)]
        j = int(np.argmin(vals))
        return exp(vals[j]), j  # −d/dv g = j·g

    total = 0.0
    v = LOG_HR
    vend = v0 + vmax_extra
    while v < vend:
        vm = v + dv / 2
        gval, j = g_and_slope(vm)
        if j > 0:
            total += Phi(vm, L, Zfix=Zfix) * j * gval * dv
        v += dv
    # 尾项 v > vend：Φ ≤ e^v v/(2π)，−dg = M A_M e^{−Mv}；M ≥ 2，可以显式积分（这里给一个上界）
    gval, j = g_and_slope(vend)
    tail = j * gval * exp(vend) * vend / (2 * pi) / max(j - 1, 1e-9) * 2
    zeros = 2 * (total + tail)
    low = 2 * (HR_N()) * exp(-L / 2)
    pp = ratio_max * bound.terms(L, 1.5 / k, k, mode='KLN')['pp2'] if False else 0.0
    e_pp = ratio_max * ((1 + 1.93378e-8) * sqrt(1 + eps) - 0.999) / k * exp(L * (1 / k - 0.5))
    return zeros + low + e_pp


def log1p_(x):
    return log(1 + x)


def HR_N():
    return bound.HR * LOG_HR / (2 * pi)


if __name__ == '__main__':
    k = 67
    for M in (2, 3, 4, 6, 8):
        print('M', M, 'R_j', [round(r, 3) for r in weight_constants(M)[0]])
