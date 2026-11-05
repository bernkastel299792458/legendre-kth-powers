"""
KLN (2018) Lemma 3.2 (3.3) 在小 T 情形的严格（arb）验证。

KLN 声称：对所有 T > 0，max_{|t|≤T} |ζ(1/2+it)| ≤ a1 T^{1/6} log T + a2，其中 a1 = 0.63，a2 = 2.851。
  * T ≥ 3：由 Hiary–Patel–Yang（JNT 256, 2024）Thm 1.1 的 |ζ(1/2+it)| ≤ 0.618 t^{1/6} log t（t ≥ 3）推出，
    并且 [0,3] 上的值 ≤ RHS(3) ≈ 3.68。
  * 0 < T < 3：RHS(T) 在 T > 0 上的最小值在 T = e^{-6} 处，等于 a2 − 6 a1/e ≈ 1.4604157；
    因此只需验证 max_{t∈[0,3]} |ζ(1/2+it)| ≤ a2 − 6 a1/e。（|ζ(1/2+it)| 关于 t 对称。）
KLN 原文对 [0,3] 用的是界 1.461，它略大于 1.4604157，所以原文的论证在这一点上有缺口；
真实最大值 |ζ(1/2)| ≈ 1.4603545 补上了这个缺口（余量约 6·10⁻⁵）。此项由 Claude 评审指出，这里给出严格验证。
KLN 常数经由 Cully-Hugill–Lee 区间估计进入本项目的 (I8)。
"""
import sys
from flint import arb, acb, ctx

ctx.prec = 128
a1, a2 = arb("0.63"), arb("2.851")
target = a2 - 6 * a1 / arb(1).exp()           # 最小值 RHS(e^{-6})
# 验证 RHS 在 T = e^{-6} 处取最小：导数 T^{-5/6}((1/6)log T + 1)，T<e^{-6} 时为负，T>e^{-6} 时为正。
half = arb(1) / 2


def zabs_upper(t0, t1):
    """|ζ(1/2 + i t)| 在 t ∈ [t0, t1] 上的严格上界。"""
    t = arb((t0 + t1) / 2, (t1 - t0) / 2)
    z = acb(half, t).zeta()
    return abs(z).upper()


stack = [(0.0, 3.0)]
n_eval, worst = 0, arb(0)
while stack:
    t0, t1 = stack.pop()
    ub = zabs_upper(t0, t1)
    n_eval += 1
    if (target - ub).lower() > 0:
        if float(ub) > float(worst):
            worst = ub
        continue
    if t1 - t0 < 1e-12:
        print(f"FAILED near t = {t0}: upper bound {ub} vs target {target}")
        sys.exit(1)
    m = (t0 + t1) / 2
    stack += [(t0, m), (m, t1)]
zeta_half = acb(half, 0).zeta()
print(f"target = a2 - 6 a1/e = {target}")
print(f"|zeta(1/2)| = {abs(zeta_half)}")
print(f"max over [0,3] of |zeta(1/2+it)| <= {worst}  ({n_eval} ball evaluations)")
print("KLN LEMMA 3.2 SMALL-T CASE VERIFIED")
sys.exit(0)
