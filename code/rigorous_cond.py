"""严格版"最小零点自由区域"（改进 Lee 的 Theorem 1.4）。
假设在 H_R < |t| <= T_k 内 ζ 无零点于 σ >= 1 − loglog|t|/(z log|t|)。在这个假设下，
严格覆盖窗口 [Lee Prop 3.3 的上限, L0(k)]（L0 由 HYB 证书给出），并报告所需的 (z, log T_k)。
用法：python rigorous_cond.py K"""
import sys
import csv
from fractions import Fraction
import bound
import rigorous_hyb as R

def fdelta(L, c, k, mode, z, s=0.985):
    u = c * L / k
    if u <= 3:
        return float('inf')
    Z = min(z, bound.Z_eff(u))
    return bound.delta(L, c / k, k, mode=mode, Z=Z, sstar=s)

def pick(k, a, b, mode, z, c0=None):
    def score(c):
        if mode == 'HYB':
            lo, hi = c * a / k, c * b / k
            if not any(T0 <= lo and hi <= T1 for T0, T1, *_ in bound.BELLOTTI):
                return float('inf')
        return max(fdelta(a, c, k, mode, z), fdelta(b, c, k, mode, z))
    cands = ([c0 * (1 + j * 5e-4) for j in range(-20, 21)] if c0 else []) + [1 + i * 2e-3 for i in range(1, 400)]
    cands = [c for c in cands if 1 < c < k / 10]
    best = min(cands, key=score)
    for step in (1e-4, 1e-5, 1e-6):
        for _ in range(80):
            nb = min((best + step, best - step), key=score)
            if score(nb) < score(best):
                best = nb
            else:
                break
    return best, score(best)

def pick_low_u(k, a, b, mode, z, target=0.995):
    """在 δ_float < target 的 c 中取最小的（u = cL/k 最小，即所需高度最低）。"""
    def score(c):
        if mode == 'HYB':
            lo, hi = c * a / k, c * b / k
            if not any(T0 <= lo and hi <= T1 for T0, T1, *_ in bound.BELLOTTI):
                return float('inf')
        return max(fdelta(a, c, k, mode, z), fdelta(b, c, k, mode, z))
    c = 1.0
    for step in (1e-2, 1e-3, 1e-4, 1e-5):
        while c + step < k / 10 and score(c + step) >= target:
            c += step
            if c > 1.6:
                return None
    c += 1e-5
    return c if score(c) < target else None


def cover(k, z, a0, b0, minw=Fraction(1, 64), low_u=False):
    a, w, pieces, c_prev = a0, Fraction(1), [], None
    while a < b0:
        b = min(a + w, b0)
        got = None
        for mode in ('KLN', 'HYB'):
            if low_u:
                c_b, sb = pick(k, float(a), float(b), mode, float(z), c_prev)
                if sb >= 1:
                    continue
                tgt = 0.995 if sb < 0.99 else 1 - (1 - sb) / 2
                c_f = pick_low_u(k, float(a), float(b), mode, float(z), target=tgt) or c_b
            else:
                c_f, sc = pick(k, float(a), float(b), mode, float(z), c_prev)
                if sc >= 1:
                    continue
            for s in (Fraction(985, 1000), Fraction(99, 100)):
                d, det = R.rig_delta(k, a, b, R.to_frac(c_f), s, mode=mode, z_hyp=z)
                if d is not None and d < 1:
                    cand = (a, b, R.to_frac(c_f), s, d, mode)
                    key = (cand[2] * b) if low_u else d   # low_u：选所需高度最低者
                    if got is None or key < ((got[2] * b) if low_u else got[4]):
                        got = cand
        if got:
            pieces.append(got)
            a, c_prev = b, c_f
            if got[4] < 0.5:
                w = min(w * 2, Fraction(64))
        else:
            if w <= minw:
                return None, a
            w /= 2
    return pieces, None

if __name__ == '__main__':
    k = int(sys.argv[1])
    cert = list(csv.DictReader(open(f'../results/cert_hyb_k{k}.csv')))
    L0 = min(Fraction(r['a']) for r in cert)
    a0 = R.prop33_ceiling_lower(k)  # Lee Prop 3.3 上限的严格下界（取到 1/1024）
    lo, hi = Fraction(10), Fraction(20)   # z 越大假设越弱；求最大可行 z
    best = None
    for _ in range(14):
        mid = Fraction(round(float(lo + hi) / 2 * 1000), 1000)
        pieces, fail = cover(k, mid, a0, L0)
        if pieces:
            lo, best = mid, pieces
        else:
            hi = mid
        if hi - lo <= Fraction(1, 1000):
            break
    z = lo
    # 第二阶段：固定 z，在 δ < 1 的前提下让所需高度尽量低
    p2, _ = cover(k, z, a0, L0, low_u=True)
    pieces = p2 if p2 and max(float(p[2] * p[1] / k) for p in p2) < max(float(p[2] * p[1] / k) for p in best) else best
    logT = max(float(p[2] * p[1] / k) for p in pieces)  # u 的上端 = θ b
    with open(f'../results/cert_cond_k{k}.csv', 'w', newline='') as f:
        wr = csv.writer(f)
        wr.writerow(['k', 'z', 'a', 'b', 'c', 'sigma_star', 'mode', 'delta_upper'])
        for a, b, c, s, d, m in pieces:
            wr.writerow([k, str(z), str(a), str(b), str(c), str(s), m, f'{d:.6g}'])
    print(f"k={k}: window [{float(a0)}, {float(L0):.4f}] closes under zero-free region with z = {float(z):.3f} "
          f"for H_R < |t| <= e^{logT:.3f}  ({len(pieces)} pieces)")
