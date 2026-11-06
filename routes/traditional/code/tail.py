"""
尾部引理（Lemma T）的严格检查：k = 67，对所有 log x = L ≥ L∞ 证明 (3.2)。不依赖 Lee 的 Prop 3.2。

只用以下输入：
  * 命题 H 的 KLN-only 形式（σ ∈ [σ1, 1−η] 全部用 Johnston–Yang 修正后的 KLN 估计，σ1 = 0.98）；
  * Vinogradov–Korobov 零点自由区域：σ ≥ 1 − 1/(Z3 (log t)^{2/3}(log log t)^{1/3})，t ≥ 3，Z3 = 54.004。
    Bellotti 2024 (JMAA 536) 证明了 Z3 = 53.989，因此较弱的 54.004 也成立；这是已正式发表的结果，不依赖博士论文。
  * Cully-Hugill–Johnston II 的显式公式（M = 1.26，log 幂次 4/5）、(3.4)、N(T) ≤ T log T/(2π)、H_R。

固定 μ = c/67。对 L ≥ L∞，δ_H(L) ≤ U(L)，其中 U 是下面四个显式控制函数之和：
  U_triv(L) = (μL/π) e^{−aL},                       a = 1 − σ1 − μ
  U_K(L)    = (2B1/a2)(μL)^3 e^{−a2 w(L)} + 2B3 (μL)^2 e^{−w(L)},
              w(L) = L·η(μL)，η(u) = 1/(Z3 u^{2/3} (log u)^{1/3})，
              a2 = 1 − 8μ/3 − 2 log(μL∞)/L∞（因 2 log(μL)/L 在 L ≥ L∞ 上递减，λ ≥ a2 L）
  U_tr(L)   = (2M/67) c_tr L^{4/5} e^{−bL},          b = μ − 1/67，
              c_tr = (1+ε∞)(1+ε∞/L∞)^{4/5} + 1，ε∞ = 67 e^{−L∞/67}
  U_pp(L)   = (α1 √(1+ε∞) − 0.999)/67 · e^{−(1/2−1/67)L} + (α2 (1+ε∞)^{1/3} − 0.885)/67 · e^{−(2/3−1/67)L}

各控制函数在 [L∞, ∞) 上递减的充分条件（都只需在 L∞ 处检查，理由见 manuscript §8 Lemma T 的证明）：
  (C1) a L∞ > 1；
  (C2) log(μL∞) > 1，且 w(L∞)(1 − 1/log(μL∞)) ≥ 9/a2；（w·(1−1/log) 递增）
  (C3) b L∞ > 4/5；
  (C4) a2 > 0。
命题 H 在所有 L ≥ L∞ 上的前提：
  (P1) L∞ ≥ 1000；(P2) 1/67 < μ < 1/10；(P3) T = e^{μL}/2 ≥ max(H_R, 51, L^2)，在 L∞ 处检查并且 μ > 2/L∞（于是 μL − 2 log L 递增）；
  (P4) 4T + 2 < e^{L/10}，在 L∞ 处检查并且 μ < 1/10（于是 L/10 − μL 递增）；
  (P5) λ ≥ 1。
"""
from fractions import Fraction
from flint import arb, ctx

ctx.prec = 200
A = lambda s: arb(s)


def af(fr):
    fr = Fraction(fr)
    return arb(fr.numerator) / fr.denominator


def check(L_inf=Fraction(10 ** 10), c=Fraction(101, 100), Z3="54.004", verbose=True, k=67):
    K = arb(k)
    mu = af(c) / K
    s1 = arb(49) / 50
    B1, B3 = A("17.418"), A("2.231")
    M = A("1.26")
    a1, a2c = 1 + A("1.93378e-8"), 1 + A("1.936e-8")
    HR = A("3000175332800")
    z3 = A(Z3)
    L = af(L_inf)
    u = mu * L
    lu = u.log()
    a = 1 - s1 - mu
    a2 = 1 - 8 * mu / 3 - 2 * lu / L
    b = mu - 1 / K
    eps = K * (-L / K).exp()
    eta = 1 / (z3 * u ** (arb(2) / 3) * lu ** (arb(1) / 3))
    w = L * eta
    T = (mu * L).exp() / 2
    lam = L * (1 - 8 * mu / 3) - 2 * lu
    conds = {
        'C1: a*Linf > 1': (a * L - 1),
        'C2a: log(mu*Linf) > 1': (lu - 1),
        'C2b: w(1-1/log u) >= 9/a2': (w * (1 - 1 / lu) - 9 / a2),
        'C3: b*Linf > 4/5': (b * L - arb(4) / 5),
        'C4: a2 > 0': a2,
        'P1: Linf >= 1000': L - 1000,
        'P2a: mu > 1/k': mu - 1 / K,
        'P2b: mu < 1/10': arb(1) / 10 - mu,
        'P3a: T >= H_R': T - HR,
        'P3b: T > 51': T - 51,
        'P3c: T > L^2': T - L * L,
        'P3d: mu > 2/Linf': mu - 2 / L,
        'P4: 4T+2 < e^{L/10}': (L / 10).exp() - 4 * T - 2,
        'P5: lambda >= 1': lam - 1,
    }
    ok = all(v.lower() > 0 for v in conds.values())
    U_triv = u / arb.pi() * (-a * L).exp()
    U_K = 2 * B1 / a2 * u ** 3 * (-a2 * w).exp() + 2 * B3 * u ** 2 * (-w).exp()
    c_tr = (1 + eps) * (1 + eps / L) ** (arb(4) / 5) + 1
    U_tr = 2 * M / K * c_tr * L ** (arb(4) / 5) * (-b * L).exp()
    U_pp = (a1 * (1 + eps).sqrt() - A("0.999")) / K * (-(arb(1) / 2 - 1 / K) * L).exp() \
        + (a2c * (1 + eps) ** (arb(1) / 3) - A("0.885")) / K * (-(arb(2) / 3 - 1 / K) * L).exp()
    U = U_triv + U_K + U_tr + U_pp
    ok = ok and U.upper() < 1
    if verbose:
        print(f"Lemma T check: k = {k}, L_inf = {L_inf}, c = {c}, Z3 = {Z3}")
        for kname, v in conds.items():
            print(f"  {kname:28s} margin lower bound = {float(v.lower()):.6g}  {'OK' if v.lower() > 0 else 'FAIL'}")
        print(f"  U_triv <= {float(U_triv.upper()):.3e}, U_K <= {float(U_K.upper()):.3e}, "
              f"U_tr <= {float(U_tr.upper()):.3e}, U_pp <= {float(U_pp.upper()):.3e}")
        print(f"  U(L_inf) <= {float(U.upper()):.3e}  ->  {'LEMMA T VERIFIED' if ok else 'FAILED'}")
    return ok


if __name__ == '__main__':
    import sys
    Linf = Fraction(sys.argv[1]) if len(sys.argv) > 1 else Fraction(10 ** 8)
    kk = int(sys.argv[2]) if len(sys.argv) > 2 else 67
    sys.exit(0 if check(Linf, k=kk) else 1)
