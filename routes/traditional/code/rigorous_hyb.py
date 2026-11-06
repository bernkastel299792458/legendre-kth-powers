"""
用 arb 球算术严格验证"拼接版"Prop 3.1（见 docs/HYB_theorem.md 的 Proposition H）。

对每一段 L = log x ∈ [a, b] 固定参数 (θ = c/k, σ*, σ1)，在整段上（不只是在网格点上）
严格地给 δ 一个上界。δ_upper < 1 ⇒ 对该段所有 x 有 θ(x+h) − θ(x) > 0。

输入常数全部与 Lee (2026) 相同：Yang 的零点自由区域、KLN/Johnston–Yang 与 Bellotti 的密度估计、
Cully-Hugill–Johnston II 的显式公式、Platt–Trudgian 的 H_R，以及 (3.4) 中 ψ−θ 的界。

用法：
    python rigorous_hyb.py K L_END [L_STOP]
从 L_END 向下逐段验证，直到某段在最小宽度下仍无法验证为止；输出证书 CSV。
"""
import csv
import sys
from fractions import Fraction
from flint import arb, ctx

import bound  # float 版，只用来挑参数

ctx.prec = 160

# ---------- 常数（全部以十进制字符串读入，arb 自动给出包含真值的球） ----------
A = lambda s: arb(s)
HR = A("3000175332800")
LOG_HR = HR.log()
LOG2 = arb(2).log()
Z1, Z2, Z3 = A("4.862"), A("19.62"), A("51.34")
# 零点自由区域常数组（经典 Z1 / Littlewood Z2 / Vinogradov–Korobov Z3，t ≥ 3）：
#   'thesis'   : Yang 博士论文 Thm 1.1–1.3（4.862, 19.62, 51.34），即 Lee (2.2)；
#   'lw'       : 4.896（Bellotti–Trudgian–Yang arXiv:2603.21490 Thm 1，不依赖博士论文）
#                + 19.62（博士论文）+ 54.004（Bellotti arXiv:2306.10680；期刊版 53.989 更强，故 54.004 也成立）；
#   'lw_ref'   : 5.558691（MTY 2024，已发表）+ 19.62（博士论文）+ 54.004；
#   'published': 5.558691 + 21.233（Yang 2024，已发表）+ 54.004。
ZSETS = {'thesis': (A("4.862"), A("19.62"), A("51.34")),
         'lw': (A("4.896"), A("19.62"), A("54.004")),
         'lw_ref': (A("5.558691"), A("19.62"), A("54.004")),
         'published': (A("5.558691"), A("21.233"), A("54.004")),
         # 不用 19.62 的保守组：
         'bty_pub': (A("4.896"), A("21.233"), A("54.004")),   # BTY（arXiv，已由 zfr_audit 核实）+ 已发表
         'pub': (A("5.558691"), A("21.233"), A("54.004")),    # 全部已发表
         'r2008': (A("4.896"), A("20.08"), A("54.004"))}      # 19.62 修复后的网格估计（未证明，仅作参考）
HYB_CFG = {'zfr': 'thesis'}
# 高度方向的小余量（log 尺度）：用于端点约定的极限论证
PAD = arb(2) ** -40
# KLN 型密度估计：Johnston–Yang (2023, JMAA 527) Lemma 2.6 + Table 3（H0 = H_R，Hiary 界已修正），
# 对 σ ∈ [0.98, 1)：C1(σ) ≤ 17.418（σ→1 极限行，C1 递增），C2(σ) ≤ 2.231（σ = 0.98 行，C2 递减）。
# （Lee (2.7) 的 17.253 / 5.663 来自 KLN 2018，依赖 Hiary 的不可靠界，这里不再使用。）
B1, B3 = A("17.418"), A("2.231")
KLN_SIGMA_MIN = Fraction(49, 50)
M_CHJ, POW = A("1.26"), arb(4) / 5
ALPHA1 = 1 + A("1.93378e-8")
ALPHA2 = 1 + A("1.936e-8")
PI = arb.pi()

# Bellotti (2025) via Lee Table 2：(log T0, log T1, σ0, C, B)
BELLOTTI = [
    ("80", "90", "0.985", "370655.73", "5.216"),
    ("90", "100", "0.985", "425721.47", "4.831"),
    ("100", "110", "0.985", "488901.14", "4.513"),
    ("110", "120", "0.985", "545744.21", "4.264"),
    ("120", "130", "0.985", "629490.27", "4.032"),
    ("130", "140", "0.985", "694045.43", "3.855"),
    ("140", "150", "0.985", "771373.78", "3.696"),
    ("150", "160", "0.985", "825913.07", "3.572"),
    ("160", "170.2", "0.985", "909966.07", "3.448"),
    ("170.2", "500", "0.985", "1.12e6", "3.337"),
    ("500", "1000", "0.985", "6.23e6", "2.152"),
    ("1000", "1500", "0.985", "2.12e7", "1.820"),
    ("1500", "2000", "0.985", "6.47e7", "1.684"),
    ("2000", "2500", "0.985", "1.73e8", "1.610"),
    ("2500", "3000", "0.985", "2.56e8", "1.577"),
    ("3000", "481958", "0.985", "5.76e8", "1.551"),
    ("481958", "6.7e12", "0.985", "1.62e11", "1.448"),
]
ROWS = [tuple(A(s) for s in r) for r in BELLOTTI]


def certainly_le(x, y):
    return (y - x).lower() >= 0


def eta_lower(U, z_hyp=None):
    """U = 上端的 log(2T)（精确 arb）。返回 η 的严格下界：
    η_known(t) = max(1/(Z1 log t), loglog t/(Z2 log t), 1/(Z3 (log t)^{2/3}(loglog t)^{1/3}))，
    三者都在 log t > e 时单调递减，所以对所有 |t| ≤ e^U，零点自由区域宽度 ≥ η_known(e^U)。"""
    z1, z2, z3 = ZSETS[HYB_CFG['zfr']]
    lu = U.log()
    e1 = 1 / (z1 * U)
    e2 = lu / (z2 * U)
    e3 = 1 / (z3 * U ** (arb(2) / 3) * lu ** (arb(1) / 3))
    cands = [e1.lower(), e2.lower(), e3.lower()]
    if z_hyp is not None:  # 假设：H_R < |t| <= e^U 内无零点于 σ >= 1 - loglog t/(z log t)（该函数也单调递减）
        cands.append((lu / (arb(z_hyp.numerator) / z_hyp.denominator * U)).lower())
    return max(cands, key=float)


def rig_delta(k, a, b, c, sstar, s1=Fraction(49, 50), mode='HYB', z_hyp=None):
    """a, b, c, sstar, s1 为 Fraction（精确）。返回 (δ 上界 float, 细节 dict) 或 (None, 原因)。"""
    K = arb(k)
    La, Lb = arb(a.numerator) / a.denominator, arb(b.numerator) / b.denominator
    L = La.union(Lb)
    th = arb(c.numerator) / c.denominator / K
    s_star = arb(sstar.numerator) / sstar.denominator
    s_1 = arb(s1.numerator) / s1.denominator
    # ---- 前提条件 ----
    if not (c > 1 and c / k < Fraction(1, 10)):
        return None, "theta range"
    if a < 1000:
        return None, "x >= e^1000"
    if not (s1 >= KLN_SIGMA_MIN and sstar >= Fraction(985, 1000) and sstar >= s1 and sstar < 1):
        return None, "sigma params"
    ua, ub = th * La, th * Lb
    u = ua.union(ub)
    if not certainly_le(LOG_HR + LOG2, ua):  # T = x^θ/2 ≥ H_R
        return None, "T >= H_R"
    row = None
    for T0, T1, s0, C, B in ROWS:
        # 严格包含：log(2T) + PAD ≤ log T1。这样存在 T⁺ > 2T 使 (2T, T⁺] 中没有零点纵坐标、
        # 且 T⁺ 仍在同一行内（端点约定，见手稿 §2；GPT 评审 4.3、Claude 评审次要问题 3）
        if certainly_le(T0, ua) and certainly_le(ub + PAD, T1):
            row = (T0, T1, s0, C, B)
            break
    if mode == 'HYB' and row is None:
        return None, "Bellotti row"
    if mode == 'KLN':
        row = (arb(0), arb(0), arb(0), arb(0), arb(0))  # 不使用 Bellotti
    T0, T1, s0, C, B = row
    if sstar < Fraction(985, 1000):  # Bellotti 表中所有行 σ0 = 0.985
        return None, "sigma0"
    # CHJ II Thm 1.3（原文条件）：max{51, (log x)^2} < T < (x^{1/10} − 2)/4，其中 T = x^μ/2 = e^u/2。
    # （Lee (3.3) 把下界误写成 max{51, log x} < 2T；这里检查原文中更强的条件。）
    T_lo = ua.exp() / 2
    T_hi = ub.exp() / 2
    if not (certainly_le(arb(51), T_lo) and certainly_le(Lb * Lb, T_lo)):
        return None, "T lower (CHJ II: T > max{51, log^2 x})"
    if not certainly_le(4 * T_hi + 2, (La / 10).exp()):
        return None, "T upper (CHJ II: T < (x^{1/10}-2)/4)"
    lamK = L * (1 - 8 * th / 3) - 2 * u.log()
    lamB = L * (1 - B * th)
    if not (certainly_le(arb(1), lamK) and certainly_le(arb(1), lamB)):
        return None, "lambda >= 1"
    eta = eta_lower((ub + PAD).upper(), z_hyp)   # 在略高于 2T 的高度 e^{u+PAD} 处取零点自由宽度
    # ---- 各项 ----
    E_triv = u / PI * (-(1 - s_1 - th) * L).exp()
    if mode == 'HYB':
        # [σ1, σ*] 用 KLN，[σ*, 1−η] 用 Bellotti
        E_kln = 2 * B1 * u ** 3 * (L / lamK) * (-(1 - s_star) * lamK).exp() \
            + 2 * B3 * u ** 2 * (-(1 - s_star) * L).exp()
        E_bel = 2 * C * (L / lamB) * (-eta * lamB).exp()
    elif mode == 'KLN':
        # [σ1, 1−η] 全部用 KLN（Lee 的 option 2，略去负项）
        E_kln = 2 * B1 * u ** 3 * (L / lamK) * (-eta * lamK).exp() + 2 * B3 * u ** 2 * (-eta * L).exp()
        E_bel = arb(0)
    else:
        raise ValueError(mode)
    eps = K * (-L / K).exp()
    E_tr = 2 * M_CHJ / K * ((1 + eps) * (L + eps) ** POW + L ** POW) * (-(th - 1 / K) * L).exp()
    E_pp = (ALPHA1 * (1 + eps).sqrt() - A("0.999")) / K * ((1 / K - arb(1) / 2) * L).exp() \
        + (ALPHA2 * (1 + eps) ** (arb(1) / 3) - A("0.885")) / K * ((1 / K - arb(2) / 3) * L).exp()
    tot = E_triv + E_kln + E_bel + E_tr + E_pp
    det = dict(triv=float(E_triv.upper()), kln=float(E_kln.upper()), bel=float(E_bel.upper()),
               trunc=float(E_tr.upper()), pp=float(E_pp.upper()), row=float(T0.mid()))
    return float(tot.upper()), det


def prop33_ceiling_lower(k, Delta="2.51949e11"):
    """Lee Prop 3.3：(3.2) 对 4e18 <= x <= exp(k log(kΔ(1-1/Δ)^2)) 成立。返回该上限 log 值的严格下界（分母 1024）。"""
    D = A(Delta)
    val = arb(k) * (arb(k) * D * (1 - 1 / D) ** 2).log()
    lo = float(val.lower())
    from math import floor
    f = Fraction(floor(lo * 1024) - 1, 1024)
    assert certainly_le(arb(f.numerator) / f.denominator, val)
    return f


# ---------- 参数选择（float，仅作启发） ----------
def _fd(L, c, k, s):
    return bound.delta(L, c / k, k, mode='HYB', sstar=s)


def pick_c(k, a, b, c0=None, s=0.985):
    """在 [a,b] 两端 float δ 的最大值上优化 c，并保证 u 段不跨越 Bellotti 行的边界。"""
    def score(c):
        lo, hi = c * a / k, c * b / k
        for T0, T1, *_ in bound.BELLOTTI:
            if T0 <= lo and hi <= T1:
                return max(_fd(a, c, k, s), _fd(b, c, k, s))
        return float('inf')

    cands = []
    if c0 is not None:
        cands += [c0 * (1 + j * 2e-4) for j in range(-25, 26)]
    cands += [1 + i * 2e-3 for i in range(1, 300)]
    # 也尝试让 u 段恰好贴住某个行边界的两侧
    for T0, T1, *_ in bound.BELLOTTI:
        for edge in (T0, T1):
            cands += [edge * k / b * (1 - 1e-9), edge * k / a * (1 + 1e-9)]
    cands = [c for c in cands if 1 < c < k / 10]
    best = min(cands, key=score)
    for step in (1e-4, 1e-5, 1e-6):
        for _ in range(60):
            nb = min((best + step, best - step), key=score)
            if score(nb) < score(best):
                best = nb
            else:
                break
    return best, score(best)


def to_frac(c, den=10**9):
    return Fraction(round(c * den), den)


def verify_down(k, L_end, L_stop=1000, w0=1.0, minw=Fraction(1, 64), out=None, verbose=True):
    """从 L_end 往下覆盖。返回 (L0, pieces)，表示 [L0, L_end] 已严格验证。"""
    top = Fraction(L_end)
    w = Fraction(w0)
    c_prev = None
    pieces = []
    while top > L_stop:
        a = max(top - w, Fraction(L_stop))
        c_f, sc = pick_c(k, float(a), float(top), c_prev)
        ok = False
        if sc < 1:
            for sstar in (Fraction(985, 1000), Fraction(99, 100)):
                d, det = rig_delta(k, a, top, to_frac(c_f), sstar)
                if d is not None and d < 1:
                    ok = True
                    break
        if ok:
            pieces.append((a, top, to_frac(c_f), sstar, d, det))
            top = a
            c_prev = c_f
            # 余量大时放宽段宽，上限为 L/200
            if d < 0.5:
                w = min(w * 2, Fraction(int(float(a) / 200) + 1))
        else:
            if w <= minw:
                break
            w = w / 2
    if out:
        with open(out, 'w', newline='') as f:
            wr = csv.writer(f)
            wr.writerow(['k', 'a', 'b', 'c', 'sigma_star', 'delta_upper', 'triv', 'kln', 'bel', 'trunc', 'pp', 'bellotti_row_T0'])
            for a, b, c, s, d, det in pieces:
                wr.writerow([k, str(a), str(b), str(c), str(s), f"{d:.6g}", f"{det['triv']:.3g}", f"{det['kln']:.3g}",
                             f"{det['bel']:.3g}", f"{det['trunc']:.3g}", f"{det['pp']:.3g}", det['row']])
    L0 = top
    if verbose:
        print(f"k={k}: verified [{float(L0):.4f}, {L_end}] with {len(pieces)} pieces; max delta_upper = "
              f"{max(p[4] for p in pieces):.6f}")
    return L0, pieces


if __name__ == '__main__':
    k = int(sys.argv[1])
    L_end = int(sys.argv[2])
    L_stop = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
    verify_down(k, L_end, L_stop, out=f'../results/cert_hyb_k{k}.csv')
