"""
Lee (2026) Prop. 3.1 的上界，重写为 float 版本以便快速扫描参数，并加入改进选项。

变量约定（与 Lee 代码一致）：
    L     = log x
    theta = θ，取 2T = x^θ，于是 u = log(2T) = θL
    s1    = σ1，β < σ1 的零点用平凡估计
返回 δ：若 δ < 1，则 θ(x+h) − θ(x) > (1−δ)h > 0，其中 h = k x^{1−1/k}。

mode:
    'KLN'  : Lee 的 option 2（KLN/Johnston–Yang 密度估计，σ1 默认 0.675）
    'BEL'  : Lee 的 option 1（Bellotti log-free 密度估计，σ1 = 0.985）
    'HYB'  : 新增。σ∈[σ1, σ*] 用 KLN，σ∈[σ*, 1−η] 用 Bellotti（要求 σ* ≥ 0.985）

这只是数值探索工具，没有用区间算术，不能直接当作严格证明。
"""
from math import log, pi, sqrt, inf
from math import exp as _exp


def exp(x):
    return _exp(min(x, 700.0))

# KLN 型密度估计 N(σ,T) ≤ B1 (log T)^{5−2σ} T^{8(1−σ)/3} + B3 (log T)^2 的常数与适用的最小 σ：
#   'lee'：Lee (2026) (2.7) 引用的 17.253 / 5.663，σ > 0.6（来自 KLN 2018，依赖 Hiary 的不可靠界）；
#   'jy' ：Johnston–Yang (2023) Table 3 的修正值，σ ∈ [0.98, 1)：C1 ≤ 17.418（σ→1 极限），C2 ≤ 2.231（σ=0.98）。
KLN_CONST = {'lee': (17.253, 5.663, 0.675), 'jy': (17.418, 2.231, 0.98)}
KLN_MODE = 'jy'

HR = 3000175332800.0
LOG_HR = log(HR)

# Bellotti (2025) Table：(log T0, log T1, σ0, C, B)，N(σ,T) ≤ C T^{B(1−σ)}，T0 ≤ T ≤ T1，σ0 ≤ σ < 1
# Bellotti (2024, arXiv:2405.12545) Table 2 中 log T < 80 的行（Lee 2026 没有引用这些行）
BELLOTTI_LOW = [
    (28.729, 29, 0.9927, 37341.72, 14.160),
    (29, 30, 0.9927, 37564.18, 14.084),
    (30, 31, 0.9925, 40014.59, 13.588),
    (31, 32, 0.9923, 42840.01, 13.108),
    (32, 33, 0.9921, 46015.02, 12.647),
    (33, 34, 0.9919, 49270.71, 12.226),
    (34, 35, 0.9918, 52249.66, 11.856),
    (35, 36, 0.9916, 55524.80, 11.505),
    (36, 37, 0.9914, 59715.72, 11.134),
    (37, 38, 0.9912, 64228.93, 10.782),
    (38, 39, 0.9910, 68446.65, 10.475),
    (39, 40, 0.9909, 71907.32, 10.217),
    (40, 41, 0.9907, 76267.80, 9.951),
    (41, 42, 0.9906, 80004.48, 9.720),
    (42, 43, 0.9905, 83811.09, 9.501),
    (43, 44, 0.9903, 89209.33, 9.259),
    (44, 45, 0.9901, 95233.68, 9.020),
    (45, 46.2, 0.9900, 99227.30, 8.843),
    (46.2, 50, 0.9899, 104761.04, 8.634),
    (50, 60, 0.9892, 128806.85, 7.936),
    (60, 70, 0.9876, 194323.75, 6.661),
    (70, 80, 0.9860, 278045.07, 5.809),
]
BELLOTTI_HIGH = [
    (80, 90, 0.985, 3.7065573e5, 5.216),
    (90, 100, 0.985, 4.2572147e5, 4.831),
    (100, 110, 0.985, 4.8890114e5, 4.513),
    (110, 120, 0.985, 5.4574421e5, 4.264),
    (120, 130, 0.985, 6.2949027e5, 4.032),
    (130, 140, 0.985, 6.9404543e5, 3.855),
    (140, 150, 0.985, 7.7137378e5, 3.696),
    (150, 160, 0.985, 8.2591307e5, 3.572),
    (160, 170.2, 0.985, 9.0996607e5, 3.448),
    (170.2, 500, 0.985, 1.12e6, 3.337),
    (500, 1000, 0.985, 6.23e6, 2.152),
    (1000, 1500, 0.985, 2.12e7, 1.820),
    (1500, 2000, 0.985, 6.47e7, 1.684),
    (2000, 2500, 0.985, 1.73e8, 1.610),
    (2500, 3000, 0.985, 2.56e8, 1.577),
    (3000, 481958, 0.985, 5.76e8, 1.551),
    (481958, 6.7e12, 0.985, 1.62e11, 1.448),
]
BELLOTTI = BELLOTTI_HIGH  # 默认与 Lee 相同；use_full_bellotti() 切换到完整表


def use_full_bellotti(on=True):
    global BELLOTTI
    BELLOTTI = BELLOTTI_LOW + BELLOTTI_HIGH if on else BELLOTTI_HIGH


def bellotti(u):
    for T0, T1, s0, C, B in BELLOTTI:
        if T0 <= u < T1:
            return C, B, s0
    return None


def ford_R(u):
    """Ford (2002) Thm 3 的 R(t)，u = log t。"""
    J = u / 6 + log(u) + log(0.618)
    return (J + 0.685 + 0.155 * log(u)) / (u * (0.04962 - 0.0196 / (J + 1.15)))


def Z_eff(u, Z1=4.862, Z2=19.62, Z3=51.34, fixed=None):
    """Littlewood 形式 σ ≥ 1 − loglog t/(Z log t) 的等效常数，与 Lee 代码 Z_ve 相同。"""
    if fixed is not None:
        return fixed
    return min(min(ford_R(u), Z1) * log(u), Z2, Z3 * log(u) ** (4 / 3) / u ** (1 / 3))


def truncation_constants(theta):
    """Cully-Hugill–Johnston II 显式公式误差：返回 (M, 1−log 幂次)。"""
    if theta < 1 / 85:
        return 6.391, 0.1
    if theta < 0.1:
        return 1.26, 0.8
    return None


def terms(L, theta, k, mode='KLN', s1=None, sstar=0.985, Z=None, zkw=None):
    """返回各项的字典，便于定位瓶颈。"""
    zkw = zkw or {}
    u = theta * L
    if Z is None:
        Z = Z_eff(u, **zkw)
    eta = log(u) / (Z * u)  # 零点自由区域宽度 η(2T)
    tc = truncation_constants(theta)
    if tc is None or u <= max(log(51), log(L)):
        return None
    M, p = tc
    e = k * exp(-L / k)  # h/x
    out = {}
    if mode in ('KLN', 'HYB') and u < LOG_HR:
        return None  # KLN 估计要求 T ≥ H_R
    if mode == 'KLN':
        s1 = KLN_CONST[KLN_MODE][2] if s1 is None else s1
    elif mode in ('BEL', 'HYB'):
        if bellotti(u) is None:
            return None
        s1 = (0.985 if mode == 'BEL' else KLN_CONST[KLN_MODE][2]) if s1 is None else s1
    # (a) β < σ1 的零点：平凡估计（含 ±γ 因子 2）
    out['trivial'] = u * exp(L * (s1 + theta - 1)) / pi
    top = 1 - eta
    # KLN：N(σ,Y) ≤ 17.253 (log Y)^3 (Y^{8/3}(log Y)^2)^{1−σ} + 5.663 (log Y)^2
    B1, B3 = KLN_CONST[KLN_MODE][:2]
    B2, B4 = 3, 2
    lnf_K = (3 - 8 * theta) / 3 * L - 2 * log(u)

    def kln_part(a, b):
        if b <= a:
            return 0.0
        main = 2 * B1 * u ** B2 * L / lnf_K * (exp(-(1 - b) * lnf_K) - exp(-(1 - a) * lnf_K))
        sec = 2 * B3 * u ** B4 * (exp(-(1 - b) * L) - exp(-(1 - a) * L))
        return main + sec

    def bel_part(a, b):
        C, B, s0 = bellotti(u)
        a = max(a, s0)
        if b <= a:
            return 0.0
        lnf_B = L * (1 - B * theta)
        if lnf_B <= 0:
            return inf
        return 2 * C * L / lnf_B * (exp(-(1 - b) * lnf_B) - exp(-(1 - a) * lnf_B))

    if mode == 'KLN':
        out['density'] = kln_part(s1, top)
    elif mode == 'BEL':
        out['density'] = bel_part(s1, top)
    else:  # HYB
        sstar = min(max(sstar, bellotti(u)[2]), top)
        out['density'] = kln_part(s1, sstar) + bel_part(sstar, top)
    # (c) 截断误差
    out['trunc'] = 2 * M / k * ((1 + e) * (L + e) ** p + L ** p) * exp(-L * (theta - 1 / k))
    # (d) 素数幂（ψ → θ 的转换）
    a1, a2 = 1 + 1.93378e-8, 1 + 1.936e-8
    out['pp2'] = (a1 * sqrt(1 + e) - 0.999) / k * exp(L * (1 / k - 1 / 2))
    out['pp3'] = (a2 * (1 + e) ** (1 / 3) - 0.885) / k * exp(L * (1 / k - 2 / 3))
    out['total'] = sum(out.values())
    out['u'], out['Z'], out['theta'] = u, Z, theta
    return out


def delta(L, theta, k, **kw):
    t = terms(L, theta, k, **kw)
    return inf if t is None else t['total']


def best(L, k, cgrid=None, **kw):
    """在 c = kθ 的网格上取最优，返回 (δ, c, terms)。"""
    if cgrid is None:
        cgrid = [1 + i * 1e-4 for i in range(1, 6001)]  # c ∈ (1, 1.6]
    bd, bc = inf, None
    for c in cgrid:
        d = delta(L, c / k, k, **kw)
        if d < bd:
            bd, bc = d, c
    return bd, bc, (terms(L, bc / k, k, **kw) if bc else None)


def chl_ceiling(k, Delta=2.51949e11):
    """Lee Prop 3.3：下段覆盖到 log x ≤ k log(kΔ(1−1/Δ)^2)。"""
    return k * log(k * Delta * (1 - 1 / Delta) ** 2)
