from multiprocessing import Pool
import scan_small_k as Q
KS = [67, 66, 65, 64, 60, 55, 50, 45, 40, 35, 30, 25, 20, 15, 12, 11, 10, 8, 6, 5, 4, 3]
def job(k):
    lo, lf, worst, wl = Q.scan(k)
    return k, lo, (lf if lf else lo), worst, wl
if __name__ == '__main__':
    with Pool(8) as p:
        res = p.map(job, KS)
    with open('../results/small_k_scan.tsv', 'w') as f:
        f.write('k\tL_low\tL0\tmax_delta_in_window\tat_L\n')
        for r in res:
            f.write('\t'.join(str(x) for x in r) + '\n')
            print(*[f'{x:.4g}' if isinstance(x, float) else x for x in r], flush=True)
