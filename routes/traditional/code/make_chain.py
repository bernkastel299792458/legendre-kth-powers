"""对给定 k 和零点自由区域常数组，生成完整的 k 证书链（v3 方法）：
  下段 [log 4e18, L1(k)]：CHL 两对 (Δ, x0) + 数值事实
  命题 S [L1(k), L2]：光滑化证书（每段 M ∈ {2,3} 取优，δ 越接近 1 段越细）
  命题 H [L2, 1e8]：尖锐截断证书（从 1e8 向下生成，L2 取 H 证书中 ≥ max(L0_H, L2_min) 的第一个分点）
  尾部 [1e8, ∞)：Lemma T（tail.check，k 作为参数）
用法：python make_chain.py K ZSET [L2_MIN]"""
import sys
import csv
from fractions import Fraction
from math import floor
from flint import arb
import rigorous_hyb as RH
import rigorous_smooth as RS
import tail

k = int(sys.argv[1]); z = sys.argv[2]
L2_min = Fraction(sys.argv[3]) if len(sys.argv) > 3 else Fraction(7300)
tag = f'k{k}_{z}'
RH.HYB_CFG['zfr'] = z
RS.CFG['zfr'] = z
RS.CFG['full_table'] = True
log = open(f'../results/chain_{tag}.log', 'w', encoding='utf-8')


def say(*a):
    msg = ' '.join(str(x) for x in a)
    print(msg, flush=True); log.write(msg + '\n'); log.flush()


# --- 下段：L1(k) 与数值事实 ---
L1 = RH.prop33_ceiling_lower(k)
D1, D2 = arb(39097000), arb(251949000000)
num1 = k * (D1 - 1) - (arb(600) / k).exp()
num2 = k * (D2 - 1) - (arb(L1.numerator) / L1.denominator / k).exp()
U1 = k * (k * D1 * (1 - 1 / D1) ** 2).log()      # 第一对覆盖到的 log x 上限（须 ≥ 600）
say(f'[{tag}] L1 = {L1} ({float(L1):.4f}); num1 margin = {float(num1.lower()):.4g}; num2 margin = {float(num2.lower()):.4g}; '
    f'first pair reaches log x <= {float(U1.lower()):.2f} (need >= 600)')
assert num1.lower() > 0 and num2.lower() > 0 and U1.lower() >= 600

# --- 尾部 ---
assert tail.check(Fraction(10 ** 8), k=k, verbose=False), 'Lemma T failed'
say(f'[{tag}] Lemma T verified for L >= 1e8')

# --- 命题 H：从 1e8 往下 ---
L0H, piecesH = RH.verify_down(k, 10 ** 8, 3000, out=f'../results/cert_hyb_full_{tag}.csv', verbose=False)
bounds = sorted(p[0] for p in piecesH)
L2 = next(a for a in bounds if a >= max(L0H, L2_min))
subH = sorted([p for p in piecesH if p[0] >= L2], key=lambda p: p[0])
with open(f'../results/cert_hyb_v3_{tag}.csv', 'w', newline='') as f:
    wr = csv.writer(f)
    wr.writerow(['k', 'a', 'b', 'c', 'sigma_star', 'delta_upper', 'triv', 'kln', 'bel', 'trunc', 'pp', 'bellotti_row_T0'])
    for a, b, c, s, d, det in subH:
        wr.writerow([k, str(a), str(b), str(c), str(s), f'{d:.7g}', f"{det['triv']:.3g}", f"{det['kln']:.3g}",
                     f"{det['bel']:.3g}", f"{det['trunc']:.3g}", f"{det['pp']:.3g}", det['row']])
say(f'[{tag}] H: verified down to L0_H = {float(L0H):.4f}; using [{L2}, 1e8], {len(subH)} pieces, '
    f'max delta = {max(p[4] for p in subH):.6f}')

# --- 命题 S：[L1, L2] ---
consts = {M: RS.weight_constants(M) for M in (2, 3)}


def next_w(d):
    return Fraction(4) if d < 0.8 else Fraction(1) if d < 0.9 else Fraction(1, 4) if d < 0.95 else Fraction(1, 16)


pieces, a, w = [], L1, Fraction(1, 16)
while a < L2:
    b = min(a + w, L2)
    best = None
    for M in (2, 3):
        d, _ = RS.rig_delta_smooth(k, a, b, M, consts[M])
        if d is not None and (best is None or d < best[1]):
            best = (M, d)
    if best and (best[1] < 0.985 or (b - a) <= Fraction(1, 64)) and best[1] < 1:
        pieces.append((a, b, best[0], best[1])); a = b; w = next_w(best[1])
    else:
        if w <= Fraction(1, 256):
            say(f'[{tag}] S FAILED at L = {float(a)}: {best}')
            sys.exit(1)
        w /= 2
with open(f'../results/cert_smooth_v3_{tag}.csv', 'w', newline='') as f:
    wr = csv.writer(f)
    wr.writerow(['k', 'a', 'b', 'M', 'delta_upper'])
    for p in pieces:
        wr.writerow([k, str(p[0]), str(p[1]), p[2], f'{p[3]:.7g}'])
say(f'[{tag}] S: {len(pieces)} pieces cover [{L1}, {L2}], max delta (float-accum) = {max(p[3] for p in pieces):.6f}')
say(f'[{tag}] CHAIN GENERATED: L1 = {L1}, L2 = {L2}, L3 = 1e8')
