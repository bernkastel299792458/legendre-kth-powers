"""v3：生成命题 S 的证书，覆盖 [L1, L2]，L1 = 2089605/1024，L2 = 7219（与 HYB 证书重叠后的新分界点）。
改进（按 Claude 评审 5.7、5.8）：每段在 M ∈ {2, 3} 中取 δ 上界较小者；δ 越接近 1，段宽越小，
使严格上界贴近逐点值；覆盖范围延伸到 7219，从而不再需要 HYB 证书在 6990 附近余量极小的那些段。
生成时用 float 累加版（rig_delta_smooth）挑参数，验收用 check_smooth_chain.py --pure-arb。
用法：python close_gap_v3.py ZFR"""
import sys
import csv
from fractions import Fraction
import rigorous_smooth as RS

z = sys.argv[1]
RS.CFG['zfr'] = z
RS.CFG['full_table'] = True
k = 67
a0, L2 = Fraction(2089605, 1024), Fraction(7219)
Ms = (2, 3)
consts = {M: RS.weight_constants(M) for M in Ms}


def next_w(d):
    if d < 0.8:
        return Fraction(4)
    if d < 0.9:
        return Fraction(1)
    if d < 0.95:
        return Fraction(1, 4)
    return Fraction(1, 16)


pieces, a, w = [], a0, Fraction(1, 16)
while a < L2:
    b = min(a + w, L2)
    best = None
    for M in Ms:
        d, _ = RS.rig_delta_smooth(k, a, b, M, consts[M])
        if d is not None and (best is None or d < best[1]):
            best = (M, d)
    if best and (best[1] < 0.985 or (b - a) <= Fraction(1, 64)) and best[1] < 1:
        pieces.append((a, b, best[0], best[1]))
        a = b
        w = next_w(best[1])
    else:
        if w <= Fraction(1, 256):
            print('FAILED at', float(a), best)
            sys.exit(1)
        w /= 2
out = f'../results/cert_smooth_v3_k67_{z}.csv'
with open(out, 'w', newline='') as f:
    wr = csv.writer(f)
    wr.writerow(['k', 'a', 'b', 'M', 'delta_upper'])
    for p in pieces:
        wr.writerow([k, str(p[0]), str(p[1]), p[2], f'{p[3]:.7g}'])
print(f"[{z}] {len(pieces)} pieces cover [{float(a0)}, {float(L2)}]; max delta (float-accum) = "
      f"{max(p[3] for p in pieces):.6f}; M=2 pieces: {sum(1 for p in pieces if p[2] == 2)}")
