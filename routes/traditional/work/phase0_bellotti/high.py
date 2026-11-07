"""High-height rows (500 < log T <= 2e6) -> rows_high.csv.   python high.py
Geometric rows (ratio ~1.25), rigorous sup over each row with the high-L evaluation (belarb.piece_hl).
Per row: re-optimised (OPT_IMPR_H) with lam* and lam=1, B = B_her and B_edge; plus corrected-faithful rows
(her Table 4 parameters for the containing row, OPT_CORR_H, lam=1).
Zero-free regions: Littlewood 21.233 (Yang JMAA 2024) and Korobov-Vinogradov (Bellotti JMAA 2024):
re-optimised rows use 54.004 (conservative); corrected-faithful rows use her input 53.989 for L >= 481958.
"""
import sys, os, math, csv, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal
import numpy as np
from scipy.optimize import minimize
from flint import arb
import belarb as B
from beltables import rows as her_rows
from reopt import optimise, params_from_p, make_row, start_points, fobj
from frontier import ceil_sig, FIELDS

HERE = os.path.dirname(os.path.abspath(__file__))
ZFR_H = ('lw21.233', 'kv54.004')

def grid():
    E = []
    al = [500, 625, 800, 1000, 1250, 1500, 1750, 2000, 2250, 2500, 2750, 3000]     # aligned with her rows
    E += [(str(al[i]), str(al[i + 1])) for i in range(len(al) - 1)]
    for a, b in ((3000, 481958), (481958, 2000000)):
        n = max(1, round(math.log(b / a) / math.log(1.25)))
        r = (b / a) ** (1 / n)
        pts = [a] + [int(round(a * r ** i)) for i in range(1, n)] + [b]
        E += [(str(pts[i]), str(pts[i + 1])) for i in range(n)]
    return E

def her_row_containing(L0, L1):
    m = (float(L0) + float(L1)) / 2
    for r in her_rows(include_kv=True):
        if float(r['L0'] if r['L0'] != 'LOG3E12' else 28.7) <= m <= float(r['L1']):
            return r
    raise ValueError(m)

def optimise_edge(L0, L1, a0, zfr, opt, lam_free, starts):
    f0 = fobj(L0, L1, a0, None, zfr, opt, lam_free)
    Z0 = 1 / B.nuL(zfr, float(L0), B.FLT)
    f = lambda p: f0(p) + 2 * math.exp(p[-1]) / Z0
    best = None
    for s0 in starts:
        r = minimize(f, np.array(s0), method='Nelder-Mead', options=dict(maxiter=3000, xatol=1e-7, fatol=1e-9))
        r = minimize(f, r.x, method='Nelder-Mead', options=dict(maxiter=3000, xatol=1e-8, fatol=1e-10))
        if best is None or r.fun < best.fun:
            best = r
    return best

def run_reopt(L0, L1, hr, Blab, lamf):
    opt = B.OPT_IMPR_H
    a0 = '0.985'
    if Blab == 'B_edge':
        r = optimise_edge(L0, L1, a0, ZFR_H, opt, lamf, start_points(hr, lamf, x_free=True))
        if r is None or r.fun >= 1e8:
            return None
        xs = str(Decimal(repr(math.exp(r.x[-1]))).quantize(Decimal('0.00001')))
        st = [list(r.x[:-1])] + start_points(hr, lamf)[:2]
    else:
        xs = str(Decimal(hr['Bpr']) / 2)
        st = start_points(hr, lamf)
    r2 = optimise(L0, L1, a0, xs, ZFR_H, opt, lam_free=lamf, starts=st)
    if r2 is None or r2.fun >= 1e8:
        return None
    u, v, w, _, lam = params_from_p(r2.x, xs, lamf)
    row = dict(L0=L0, L1=L1, a0=a0, u=f"{u:.7f}", x=xs, v=f"{v:.7f}", w=f"{w:.8f}",
               lam=(str(Decimal(repr(lam)).quantize(Decimal('0.001'))) if lamf else '1'), zfr=ZFR_H)
    return row, opt

def finish(row, opt, status, label):
    pa = B.row_bound(row, opt, B.ARB)
    Cu = float(pa['C'].upper())
    hyp = B.check_hypotheses(row, opt)
    bad = [h[0] for h in hyp if (not h[1]) and not h[0].startswith('[paper only]') and not h[0].startswith('(4.9)')]
    mono = [h for h in hyp if h[0].startswith('(4.9)')][0][1]
    return dict(row=row, opt='IMPRH' if opt is B.OPT_IMPR_H else 'CORRH', ok=(not bad) and math.isfinite(Cu), bad=bad,
                mono=mono, C=Cu, Cclaim=ceil_sig(Cu), B=str(2 * Decimal(row['x'])), status=status, label=label,
                c1=float(pa['c1'].mid()), c5=float(pa['c5'].mid()), J1=pa.get('J1'))

def main(k=0, n=1):
    res = []
    t0 = time.time()
    for gi, (L0, L1) in enumerate(grid()):
        if gi % n != k:
            continue
        hr = her_row_containing(L0, L1)
        # corrected-faithful (her parameters)
        zf = ('lw21.233', 'kv53.989') if float(L1) > 481958 else ('lw21.233',)
        row = dict(L0=L0, L1=L1, a0=hr['a0'], u=hr['u'], x=hr['x'], v=hr['v'], w=hr['w'], lam='1', zfr=zf)
        res.append(finish(row, B.OPT_CORR_H, 'refereed', f"her params of row ({hr['L0']},{hr['L1']}]"))
        for lamf in (True, False):
            for Blab in ('B_her', 'B_edge'):
                o = run_reopt(L0, L1, hr, Blab, lamf)
                if o is None:
                    print('infeasible', L0, L1, Blab, lamf); continue
                res.append(finish(o[0], o[1], 'refereed', Blab))
        q = res[-1]
        print(f"{L0:>8}-{L1:<8} done ({time.time()-t0:.0f}s): " +
              "  ".join(f"[{p['label'][:6]} lam={p['row']['lam']} B={float(p['B']):.4f} C={p['Cclaim']} ok={p['ok']}]" for p in res[-5:]), flush=True)
    for q in res:
        q['gi'] = [gi for gi, iv in enumerate(grid()) if iv == (q['row']['L0'], q['row']['L1'])][0]
    json.dump([dict(q, row=dict(q['row'], zfr=list(q['row']['zfr']))) for q in res],
              open(os.path.join(HERE, f'high_raw_{k}.json'), 'w'), indent=1)
    print(f"shard {k} done {time.time()-t0:.0f}s")

def write(n):
    res = []
    for k in range(n):
        res += json.load(open(os.path.join(HERE, f'high_raw_{k}.json')))
    res.sort(key=lambda q: q['gi'])
    json.dump(res, open(os.path.join(HERE, 'high_raw.json'), 'w'), indent=1)
    t0 = time.time()
    with open(os.path.join(HERE, 'rows_high.csv'), 'w', newline='') as f:
        wr = csv.DictWriter(f, fieldnames=FIELDS)
        wr.writeheader()
        n = 0
        for q in res:
            if not q['ok']:
                print('NOT OK', q['row'], q['bad']); continue
            n += 1
            row = q['row']
            if q['opt'] == 'CORRH':
                note = (f"opt=CORRH; lam=1; corrected Bellotti argument with {q['label']}; high-L evaluation; "
                        "N(s,T)=#{beta>=s, 0<gamma<=T}")
            else:
                note = (f"opt=IMPRH; lam={row['lam']}; Bopt={q['label']}; "
                        + ("own modification: box height lam*delta; " if row['lam'] != '1' else "box height delta as in Bellotti; ")
                        + "corrected counting + improvements; high-L evaluation; N(s,T)=#{beta>=s, 0<gamma<=T}")
            if not q['mono']:
                note += "; (4.9) monotonicity factor K>1 used"
            wr.writerow(dict(id=f"HI{n:04d}", logT0=row['L0'], logT1=row['L1'], alpha0=row['a0'], C=q['Cclaim'], B=q['B'],
                             u=row['u'], x=row['x'], v=row['v'], w=row['w'], zfr_input='+'.join(row['zfr']),
                             status=q['status'], notes=note))
    print(f"wrote {n} rows, {time.time()-t0:.0f}s")

if __name__ == '__main__':
    # python high.py shard k n ; python high.py write n
    if sys.argv[1] == 'shard':
        main(int(sys.argv[2]), int(sys.argv[3]))
    else:
        write(int(sys.argv[2]))
