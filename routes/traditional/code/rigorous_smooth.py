"""
光滑化上界 δ_s 的严格（arb）验证。推导见 docs/smoothing.md。

对一段 L ∈ [a,b]（精确有理端点），权 φ_M(y) = y^M(1−y)^M：
  δ_s ≤ 2·[ Σ_i (S'_i − S'_{i−1}) ĝ_i + tail ] + 2N(H_R) x^{−1/2} + (maxφ/∫φ)(E_pp + 1/(x^3−x))
其中 v 轴（v = log t）被切成格子 [v_i, v_{i+1}]，S_i 是 Φ(e^v) 在格子上的严格上界，
S'_i = max_{l≤i} S_l（单调化），ĝ_i 是 g(e^{v_i}) 的严格上界。这一步来自 Abel 求和：
  ∫Φ(−dg) ≤ Σ S_i (g_i − g_{i+1}) ≤ Σ (S'_i − S'_{i−1}) g_i，
它避免了球与球相减带来的依赖误差。尾部 v ≥ V 用 Φ ≤ N(t) ≤ t log t/(2π) 和 g = A_M t^{−M} 显式积分。
用法：python rigorous_smooth.py K up|down L_START L_LIMIT [M]
"""
import sys
import csv
from fractions import Fraction
from math import comb, floor
from flint import arb, ctx
import rigorous_hyb as R
from rigorous_hyb import A, HR, LOG_HR, Z1, Z2, Z3, B1, B3, ALPHA1, ALPHA2, PI, ROWS, certainly_le

ctx.prec = 128


def af(fr):
    """Fraction -> 精确 arb。"""
    fr = Fraction(fr)
    return arb(fr.numerator) / fr.denominator


# ---------- 权函数常数（严格） ----------
def poly_phi(M):
    """φ_M 的整数系数（升幂）。"""
    c = [0] * (2 * M + 1)
    for i in range(M + 1):
        c[M + i] = comb(M, i) * (-1) ** i
    return c


def deriv(c):
    return [i * c[i] for i in range(1, len(c))]


def horner(c, y):
    r = arb(0)
    for a in reversed(c):
        r = r * y + a
    return r


def weight_constants(M, N=4096):
    """返回 (R_up[0..M], ratio_max)：R_j 的严格上界、maxφ/∫φ（精确）。"""
    integ = Fraction(1)
    # ∫_0^1 y^M (1−y)^M dy = (M!)^2/(2M+1)!
    from math import factorial
    integ = Fraction(factorial(M) ** 2, factorial(2 * M + 1))
    I = arb(integ.numerator) / integ.denominator
    R_up = []
    c = poly_phi(M)
    for j in range(M + 1):
        s = arb(0)
        # 小格 [i/N,(i+1)/N]，中点 m 精确。多项式在 m 处的泰勒展开是精确的：
        # |p(m+t)| ≤ Σ_i |p^{(i)}(m)|/i! · r^i，r = 1/(2N)。
        ders = [c]
        while len(ders[-1]) > 1:
            ders.append(deriv(ders[-1]))
        from math import factorial as fct
        r = arb(1) / (2 * N)
        for i in range(N):
            m = arb((2 * i + 1) / (2 * N))
            bnd = arb(0)
            for q, dq in enumerate(ders):
                bnd += abs(horner(dq, m)) * r ** q / fct(q)
            s += arb(bnd.upper())
        R_up.append((s / N / I).upper())
        c = deriv(c)
    ratio_max = (arb(1) / 4 ** M) / I
    return R_up, ratio_max


# ---------- 输入选择 ----------
# 零点自由区域常数：'thesis' = Yang 博士论文（Lee 2026 所用）；'published' = 已发表版本
#   MTY 2024: 5.558691（经典）；Yang 2024 JMAA: 21.233（Littlewood）；Bellotti 2024 JMAA: 53.989（KV）
ZFR = {'thesis': (A("4.862"), A("19.62"), A("51.34")),
       'published': (A("5.558691"), A("21.233"), A("53.989")),
       # 不依赖博士论文：Bellotti–Trudgian–Yang 2026 (arXiv:2603.21490) Thm 1 的 4.896（t ≥ 3）
       # + Yang 2024 JMAA 的 21.233 + Bellotti 2024 JMAA 的 53.989
       'nothesis': (A("4.896"), A("21.233"), A("53.989")),
       # 只用博士论文中的 Littlewood 常数 19.62
       'littlewood_thesis': (A("4.896"), A("19.62"), A("53.989")),
       'lw': (A("4.896"), A("19.62"), A("54.004")),
       'lw_ref': (A("5.558691"), A("19.62"), A("54.004")),
       'bty_pub': (A("4.896"), A("21.233"), A("54.004")),
       'pub': (A("5.558691"), A("21.233"), A("54.004")),
       'r2008': (A("4.896"), A("20.08"), A("54.004"))}
CFG = {'zfr': 'thesis', 'full_table': True}

# Bellotti (2024/2025) Table 2 中 log T < 80 的行：(log T0, log T1, σ0, C, B)，σ0 用精确十进制
LOW_ROWS_SRC = [
    ("LOG3E12", "29", "0.9927", "37341.72", "14.160"), ("29", "30", "0.9927", "37564.18", "14.084"),
    ("30", "31", "0.9925", "40014.59", "13.588"), ("31", "32", "0.9923", "42840.01", "13.108"),
    ("32", "33", "0.9921", "46015.02", "12.647"), ("33", "34", "0.9919", "49270.71", "12.226"),
    ("34", "35", "0.9918", "52249.66", "11.856"), ("35", "36", "0.9916", "55524.80", "11.505"),
    ("36", "37", "0.9914", "59715.72", "11.134"), ("37", "38", "0.9912", "64228.93", "10.782"),
    ("38", "39", "0.9910", "68446.65", "10.475"), ("39", "40", "0.9909", "71907.32", "10.217"),
    ("40", "41", "0.9907", "76267.80", "9.951"), ("41", "42", "0.9906", "80004.48", "9.720"),
    ("42", "43", "0.9905", "83811.09", "9.501"), ("43", "44", "0.9903", "89209.33", "9.259"),
    ("44", "45", "0.9901", "95233.68", "9.020"), ("45", "46.2", "0.9900", "99227.30", "8.843"),
    ("46.2", "50", "0.9899", "104761.04", "8.634"), ("50", "60", "0.9892", "128806.85", "7.936"),
    ("60", "70", "0.9876", "194323.75", "6.661"), ("70", "80", "0.9860", "278045.07", "5.809"),
]


def _row(src):
    T0 = arb(3000000000000).log() if src[0] == "LOG3E12" else A(src[0])
    return (T0, A(src[1]), Fraction(src[2]), A(src[3]), A(src[4]))


LOW_ROWS = [_row(r) for r in LOW_ROWS_SRC]
HIGH_ROWS = [(T0, T1, Fraction(985, 1000), C, B) for (T0, T1, s0, C, B) in ROWS]


def rows():
    return (LOW_ROWS + HIGH_ROWS) if CFG['full_table'] else HIGH_ROWS


# ---------- η 与 Φ ----------
def eta_low_at(Vb):
    """高度 e^{Vb} 处已知零点自由宽度的严格下界（三种区域，均单调递减）。"""
    z1, z2, z3 = ZFR[CFG['zfr']]
    lu = Vb.log()
    e = [1 / (z1 * Vb), lu / (z2 * Vb), 1 / (z3 * Vb ** (arb(2) / 3) * lu ** (arb(1) / 3))]
    return max((x.lower() for x in e), key=float)


S1 = arb(49) / 50   # KLN（Johnston–Yang 修正值）只在 σ ≥ 0.98 上使用；β < 0.98 的零点用平凡估计
SSTARS = [arb(985) / 1000, arb(99) / 100, arb(995) / 1000]


def Phi_upper(va, vb, L):
    """sup_{v∈[va,vb]} Φ(e^v) 的严格上界（va, vb 为精确 arb；L 为球）。"""
    v = va.union(vb)
    eta = eta_low_at(vb)
    best = (v.exp() * v / (2 * PI)).upper()      # Φ ≤ N(t)
    triv = v.exp() * v / (2 * PI) * (-(1 - S1) * L).exp()
    lam = L - 8 * v / 3 - 2 * v.log()
    if certainly_le(arb(1), lam):
        kln = B1 * v ** 3 * (L / lam) * (-eta * lam).exp() + B3 * v ** 2 * (-eta * L).exp()
        cand = (triv + kln).upper()
        if float(cand) < float(best):
            best = cand
        # 与格子相交的每一行：在格子上求该行 HYB 界的上界；格子内每个 v 至少被其中一行覆盖，
        # 因此"各行界的最大值"对整个格子有效（若某行的界不可用，则该组合作废）。
        hyb_vals = []
        usable = True
        inter = []
        for T0, T1, s0, C, B in rows():
            # 只有"确定不相交"才跳过（arb 的确定性比较；包含多余的行只会让最大值变大，仍然合法）
            if certainly_le(T1, va) or certainly_le(vb, T0):
                continue  # 不相交
            inter.append((T0, T1))
            lamB = L - B * v
            best_row = None
            if certainly_le(arb(1), lamB):
                top = 1 - eta
                cands = sorted({s0, s0 + Fraction(1, 1000), s0 + Fraction(3, 1000), Fraction(995, 1000)})
                for sf in cands:
                    ss = af(sf)
                    if sf >= s0 and certainly_le(ss, top):
                        k1 = B1 * v ** 3 * (L / lam) * (-(1 - ss) * lam).exp() + B3 * v ** 2 * (-(1 - ss) * L).exp()
                        cand = (triv + k1 + C * (L / lamB) * (-eta * lamB).exp()).upper()
                        if best_row is None or float(cand) < float(best_row):
                            best_row = cand   # 任一候选都是合法上界；用 float 只是为了挑选
            if best_row is None:
                usable = False
                break
            hyb_vals.append(best_row)
        # 覆盖检查：相交各行的并必须包含整个格子
        if usable and hyb_vals:
            # 表行首尾相接（相邻行的 T1 与 T0 用同一个十进制串），所以只需确定：
            # 某个相交行的 T0 ≤ va，且某个相交行的 T1 ≥ vb（arb 的确定性比较）
            covered = any(certainly_le(T0, va) for T0, T1 in inter) and any(certainly_le(vb, T1) for T0, T1 in inter)
            if covered:
                m = hyb_vals[0]
                for hv in hyb_vals[1:]:
                    m = m.max(hv)         # arb 的严格最大值
                m = m.upper()
                if float(m) < float(best):
                    best = m
    return best


def rig_delta_smooth(k, a, b, M, consts):
    R_up, ratio_max = consts
    K = arb(k)
    La, Lb = af(a), af(b)
    L = La.union(Lb)
    if a < 300:
        return None, "log x >= 300"
    eps = K * (-L / K).exp()
    v0 = L / K - K.log()                        # log(x/h)
    logA = [arb(R_up[j]).log() + j * (1 + eps).log() + j * v0 for j in range(M + 1)]

    def g_up(v):  # g(e^v) 的严格上界：min_j 上界
        return min((float((logA[j] - j * v).upper()) for j in range(M + 1)))

    # 起点：g 开始小于 1 之前的格子没有贡献；取 max(log H_R, 保守起点)
    vstart_f = max(float(LOG_HR.lower()), min(float((logA[j] / j).lower()) for j in range(1, M + 1)) - 0.5)
    # 起点：不超过 max(log H_R, g ≡ 1 区域的右端) 的 1/64 格点。
    # 若起点低于 log H_R：该处真实的 Φ₀ = 0，用上界只会让结果变大，仍然合法；
    # 若起点高于 log H_R：起点 < min_j log(A_j)/j，[log H_R, 起点] 上 g ≡ 1，没有贡献。
    # （旧版在起点低于 log H_R 时改用 LOG_HR.upper()，漏掉了 [log H_R, LOG_HR.upper()] 这一小段；
    #  GPT 评审 4.2、Claude 评审次要问题 1。）
    vstart = af(Fraction(floor(vstart_f * 64), 64))
    # 终点 V：要求 j = M 在 V 处已是最小项
    Vf = max(float(((logA[M] - logA[j]) / (M - j)).upper()) for j in range(M)) + 1.0
    Vf = max(Vf, float(v0.upper()) + 30, (float(logA[M].upper()) + 60) / (M - 1))  # 尾部 A_M e^{-(M-1)V} 要足够小
    from math import exp, log
    total = 0.0
    Sprev = 0.0
    va = vstart
    while float(va) < Vf:
        off = float(va) - float(v0.mid())
        dv = Fraction(1, 64) if off < 12 else (Fraction(1, 16) if off < 25 else Fraction(1, 4))
        vb = va + af(dv)
        S = float(Phi_upper(va, vb, L))
        Sp = max(Sprev, S)
        gi = exp(min(0.0, g_up(va)))           # g ≤ 1
        total += (Sp - Sprev) * gi
        Sprev = Sp
        va = vb
    # 尾部：∫_V^∞ (e^v v/2π) M A_M e^{−Mv} dv = (M A_M/2π) e^{−(M−1)V} (V/(M−1) + 1/(M−1)^2)
    V = va
    AM = logA[M].exp()
    tail = (M * AM / (2 * PI) * (-(M - 1) * V).exp() * (V / (M - 1) + arb(1) / (M - 1) ** 2)).upper()
    # 浮点累加的舍入：每一项都是非负上界，再整体乘 (1 + 1e-12) 作为保险
    zeros = 2 * (total * (1 + 1e-12) + float(tail))
    low = float((2 * HR * LOG_HR / (2 * PI) * (-L / 2).exp()).upper())
    e_pp = (ratio_max * ((ALPHA1 * (1 + eps).sqrt() - A("0.999")) / K * ((1 / K - arb(1) / 2) * L).exp()
                         + (ALPHA2 * (1 + eps) ** (arb(1) / 3) - A("0.885")) / K * ((1 / K - arb(2) / 3) * L).exp()
                         + 1 / ((3 * L).exp() - L.exp()))).upper()
    d = zeros + low + float(e_pp)
    return d * (1 + 1e-12), dict(zeros=zeros, low=low, pp=float(e_pp))


def rig_delta_smooth_pure(k, a, b, M, consts):
    """与 rig_delta_smooth 相同的上界，但全程用 arb 累加（不经过 IEEE double）。
    S_i 取 Phi_upper 的精确上端点；S'_i 为精确最大值；ĝ_i 取各 j 项上界中的最小者（截断于 1）。"""
    R_up, ratio_max = consts
    K = arb(k)
    La, Lb = af(a), af(b)
    L = La.union(Lb)
    if a < 300:
        return None, "log x >= 300"
    eps = K * (-L / K).exp()
    v0 = L / K - K.log()
    logA = [arb(R_up[j]).log() + j * (1 + eps).log() + j * v0 for j in range(M + 1)]

    def g_up(v):
        best = arb(1)
        for j in range(1, M + 1):
            t = (logA[j] - j * v).exp().upper()
            if float(t) < float(best):
                best = t
        return best

    vstart_f = max(float(LOG_HR.lower()), min(float((logA[j] / j).lower()) for j in range(1, M + 1)) - 0.5)
    # 起点：不超过 max(log H_R, g ≡ 1 区域的右端) 的 1/64 格点。
    # 若起点低于 log H_R：该处真实的 Φ₀ = 0，用上界只会让结果变大，仍然合法；
    # 若起点高于 log H_R：起点 < min_j log(A_j)/j，[log H_R, 起点] 上 g ≡ 1，没有贡献。
    # （旧版在起点低于 log H_R 时改用 LOG_HR.upper()，漏掉了 [log H_R, LOG_HR.upper()] 这一小段；
    #  GPT 评审 4.2、Claude 评审次要问题 1。）
    vstart = af(Fraction(floor(vstart_f * 64), 64))
    Vf = max(float(((logA[M] - logA[j]) / (M - j)).upper()) for j in range(M)) + 1.0
    Vf = max(Vf, float(v0.upper()) + 30, (float(logA[M].upper()) + 60) / (M - 1))
    total = arb(0)
    Sprev = arb(0)
    va = vstart
    while float(va) < Vf:
        off = float(va) - float(v0.mid())
        dv = Fraction(1, 64) if off < 12 else (Fraction(1, 16) if off < 25 else Fraction(1, 4))
        vb = va + af(dv)
        S = arb(Phi_upper(va, vb, L)).upper()
        Sp = Sprev.max(S).upper()
        total += ((Sp - Sprev) * g_up(va)).upper()
        Sprev = Sp
        va = vb
    V = va
    AM = logA[M].exp()
    tail = (M * AM / (2 * PI) * (-(M - 1) * V).exp() * (V / (M - 1) + arb(1) / (M - 1) ** 2)).upper()
    zeros = 2 * (total + tail)
    low = 2 * HR * LOG_HR / (2 * PI) * (-L / 2).exp()
    e_pp = (ratio_max * ((ALPHA1 * (1 + eps).sqrt() - A("0.999")) / K * ((1 / K - arb(1) / 2) * L).exp()
                         + (ALPHA2 * (1 + eps) ** (arb(1) / 3) - A("0.885")) / K * ((1 / K - arb(2) / 3) * L).exp()
                         + 1 / ((3 * L).exp() - L.exp())))
    d = (zeros + low + e_pp).upper()
    return d, dict(zeros=float(zeros.upper()), low=float(low.upper()), pp=float(e_pp.upper()))


def run(k, direction, L_start, L_limit, M=4, w0=Fraction(1, 4), minw=Fraction(1, 64)):
    consts = weight_constants(M)
    pieces = []
    cur = Fraction(L_start)
    w = w0
    while (cur < L_limit) if direction == 'up' else (cur > L_limit):
        if direction == 'up':
            a, b = cur, min(cur + w, Fraction(L_limit))
        else:
            a, b = max(cur - w, Fraction(L_limit)), cur
        d, det = rig_delta_smooth(k, a, b, M, consts)
        if d is not None and d < 1:
            pieces.append((a, b, M, d))
            cur = b if direction == 'up' else a
            if d < 0.7:
                w = min(w * 2, Fraction(4))
        else:
            if w <= minw:
                break
            w /= 2
    tag = f"{float(Fraction(L_start)):.4f}".replace('.', 'p')
    with open(f'../results/cert_smooth_k{k}_{direction}_M{M}_from{tag}.csv', 'w', newline='') as f:
        wr = csv.writer(f)
        wr.writerow(['k', 'a', 'b', 'M', 'delta_upper'])
        for a, b, m, d in pieces:
            wr.writerow([k, str(a), str(b), m, f'{d:.6g}'])
    lo = min(p[0] for p in pieces) if pieces else None
    hi = max(p[1] for p in pieces) if pieces else None
    print(f"k={k} {direction}: verified [{float(lo) if lo else None}, {float(hi) if hi else None}] "
          f"with {len(pieces)} pieces (M={M})", flush=True)
    return lo, hi


if __name__ == '__main__':
    k = int(sys.argv[1]); direction = sys.argv[2]
    L_start = Fraction(sys.argv[3]); L_limit = Fraction(sys.argv[4])
    M = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    run(k, direction, L_start, L_limit, M)
