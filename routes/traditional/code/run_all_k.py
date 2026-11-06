"""对 k = 65…85，从 Lee 的 KLN 阈值 xA 向下严格验证 HYB，得到严格阈值 L0(k)。"""
import sys
from multiprocessing import Pool
import rigorous_hyb as R
from bound import chl_ceiling

XA = {85: 6162, 84: 6828, 83: 7546, 82: 8450, 81: 9685, 80: 10986, 79: 12799, 78: 15286, 77: 18427,
      76: 23736, 75: 29735, 74: 43186, 73: 58051, 72: 96051, 71: 212515, 70: 580009, 69: 2133517,
      68: 12318302, 67: 37420887, 66: 39361821, 65: 41432145}
XB = {85: 5587, 84: 5587, 83: 5587, 82: 5587, 81: 5588, 80: 5588, 79: 5588, 78: 5589, 77: 5592, 76: 5601,
      75: 5880, 74: 6561, 73: 7554, 72: 9036, 71: 11620, 70: 15951, 69: 23148, 68: 43001, 67: 238050}

def job(k):
    L0, pieces = R.verify_down(k, XA[k], 3000, out=f'../results/cert_hyb_k{k}.csv', verbose=False)
    return k, float(L0), len(pieces), max(p[4] for p in pieces)

if __name__ == '__main__':
    ks = list(range(85, 64, -1))
    with Pool(8) as p:
        res = sorted(p.map(job, ks), reverse=True)
    with open('../results/rigorous_thresholds.md', 'w', encoding='utf-8') as f:
        f.write('| k | lower side ceiling (Lee Prop 3.3) | Lee best (xB or xA) | rigorous HYB threshold L0 | pieces |\n|---|---|---|---|---|\n')
        for k, L0, n, mx in res:
            lee = XB.get(k, XA[k])
            f.write(f'| {k} | {chl_ceiling(k):.1f} | {lee} | {L0:.2f} | {n} |\n')
            print(k, f'{chl_ceiling(k):.1f}', lee, f'{L0:.2f}', n, f'{mx:.6f}', flush=True)
