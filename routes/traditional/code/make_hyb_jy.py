"""用 Johnston–Yang 修正后的 KLN 常数（σ1 = 0.98）重新生成 k = 67 的 HYB 证书，从 L = 10^8 往下。
用法：python make_hyb_jy.py thesis|lw"""
import sys
import rigorous_hyb as R
z = sys.argv[1]
R.HYB_CFG['zfr'] = z
L0, pieces = R.verify_down(67, 10 ** 8, 3000, out=f'../results/cert_hyb_jy_k67_{z}.csv')
print(z, float(L0), L0, len(pieces))
