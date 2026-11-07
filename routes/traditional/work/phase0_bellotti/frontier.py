"""Task 4 driver: frontier of re-optimised rows (float optimiser -> rounding -> rigorous Arb bound + hypothesis checks).
Run:  python frontier.py            (all tasks, 12 worker processes; ~10-20 min)
      python frontier.py 20         (first 20 tasks only)
Outputs: rows_reopt.csv (box height lam*delta optimised), rows_reopt_lam1.csv (Bellotti's box height), frontier_raw.json
"""
import sys, os, math, csv, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal, ROUND_CEILING
from flint import arb
import belarb as B
from beltables import rows as her_rows
from reopt import (ZFR_REF, ZFR_PRE, optimise, params_from_p, make_row, her_row_for, start_points, fobj)
import numpy as np
from scipy.optimize import minimize

def optimise_edge(L0, L1, a0, zfr, opt, lam_free, starts):
    """x free: minimise log C + 2x/Z(T0)  (= log of the bound C T^{B nu(T0)} at the edge of the zero-free region)."""
    f0 = fobj(L0, L1, a0, None, zfr, opt, lam_free)
    Lf = math.log(3e12) if L0 == 'LOG3E12' else float(L0)
    Z0 = 1 / (B.nu(zfr, Lf, B.FLT) * Lf)
    f = lambda p: f0(p) + 2 * math.exp(p[-1]) / Z0
    best = None
    for s0 in starts:
        r = minimize(f, np.array(s0), method='Nelder-Mead', options=dict(maxiter=3000, xatol=1e-7, fatol=1e-9))
        r = minimize(f, r.x, method='Nelder-Mead', options=dict(maxiter=3000, xatol=1e-8, fatol=1e-10))
        if best is None or r.fun < best.fun:
            best = r
    return best

HERE = os.path.dirname(os.path.abspath(__file__))

def ceil_sig(xv, sig=6):
    x = Decimal(repr(float(xv))) * (1 + Decimal('1e-12'))
    e = x.adjusted() - sig + 1
    q = Decimal(1).scaleb(e)
    return format((x / q).to_integral_value(rounding=ROUND_CEILING) * q, 'f')

def intervals():
    I = [('LOG3E12', '29')] + [(str(a), str(a + 1)) for a in range(29, 80)]
    I += [(str(a), str(a + 2)) for a in range(80, 110, 2)]
    I += [(str(a), str(a + 4)) for a in range(110, 166, 4)] + [('166', '170.2')]
    I += [('170.2', '180'), ('180', '200'), ('200', '250'), ('250', '300'), ('300', '400'), ('400', '500')]
    return I

def her_row_mid(L0, L1):
    a = 28.7297 if L0 == 'LOG3E12' else float(L0)
    return her_row_for((a + float(L1)) / 2)

def tasks_all():
    T = []
    for (L0, L1) in intervals():
        hr = her_row_mid(L0, L1)
        a0s = [hr['a0']]
        if Decimal(hr['a0']) > Decimal('0.985'):
            a0s.append('0.985')
        if float(L1) <= 110:
            a0s.append('0.98')
        zfrs = [('refereed', ZFR_REF)]
        if (28.73 if L0 == 'LOG3E12' else float(L0)) < 73:
            zfrs.append(('audited preprint', ZFR_PRE))
        Bh = Decimal(hr['Bpr'])
        for st, zfr in zfrs:
            for a0 in a0s:
                for lab, Bv in (('B_her', Bh), ('B_her-1', Bh - 1), ('B_her+1', Bh + 1), ('B_her+2', Bh + 2), ('B_edge', None)):
                    T.append(dict(L0=L0, L1=L1, a0=a0, zfr=zfr, status=st, Blab=lab, B=None if Bv is None else str(Bv),
                                  lam_free=True, hr=hr['L0']))
            for lab, Bv in (('B_her', Bh), ('B_edge', None)):      # Bellotti's box height (lam = 1)
                T.append(dict(L0=L0, L1=L1, a0=hr['a0'], zfr=zfr, status=st, Blab=lab, B=None if Bv is None else str(Bv),
                              lam_free=False, hr=hr['L0']))
    return T

def run_task(t):
    try:
        return _run_task(t)
    except Exception as e:
        import traceback
        return dict(t, ok=False, err=repr(e) + traceback.format_exc()[-300:])

def _run_task(t):
    t0 = time.time()
    hr = [r for r in her_rows() if r['L0'] == t['hr']][0]
    opt = B.OPT_IMPR
    L0, L1, a0, zfr = t['L0'], t['L1'], t['a0'], t['zfr']
    lamf = t['lam_free']
    if t['B'] is None:
        st = start_points(hr, lamf, x_free=True)
        r = optimise_edge(L0, L1, a0, zfr, opt, lamf, st)
        if r is None or r.fun >= 1e8:
            return dict(t, ok=False, err='infeasible (x free)')
        xopt = min(math.exp(r.x[-1]), 3 * float(hr['x']))
        xs = str(Decimal(repr(xopt)).quantize(Decimal('0.0001')))
        Bs = str(2 * Decimal(xs))
        st2 = [list(r.x[:-1])] + start_points(hr, lamf)[:2]
    else:
        Bs = t['B']; xs = str(Decimal(Bs) / 2)
        st2 = start_points(hr, lamf)
        sc = float(xs) / float(hr['x'])
        if sc < 1:      # smaller B: rescale u, w with x (v/u kept) so that the start is feasible
            st2 = [[p[0] + math.log(sc * f), p[1], p[2] + math.log(sc * f)] + p[3:] for p in st2[:3] for f in (1.0, 0.95, 0.9)]
    r2 = optimise(L0, L1, a0, xs, zfr, opt, lam_free=lamf, starts=st2)
    if r2 is None or r2.fun >= 1e8:
        return dict(t, ok=False, err='infeasible', B=Bs)
    u, v, w, _, lam = params_from_p(r2.x, xs, lamf)
    row = make_row(L0, L1, a0, u, xs, v, w, (lam if lamf else '1'), zfr)
    if lamf:
        row['lam'] = str(Decimal(repr(lam)).quantize(Decimal('0.001')))
    pa = B.row_bound(row, opt, B.ARB)
    Cu = float(pa['C'].upper())
    hyp = B.check_hypotheses(row, opt)
    bad = [h[0] for h in hyp if (not h[1]) and not h[0].startswith('[paper only]') and not h[0].startswith('(4.9)')]
    mono = [h for h in hyp if h[0].startswith('(4.9)')][0][1]
    return dict(t, ok=(not bad) and math.isfinite(Cu), bad=bad, mono=mono, row=row, C=Cu, Cclaim=ceil_sig(Cu), B=Bs,
                Cfloat=math.exp(r2.fun), c1=float(pa['c1'].mid()), c5=float(pa['c5'].mid()), K=float(arb(pa['K']).mid()),
                secs=time.time() - t0)

FIELDS = ['id', 'logT0', 'logT1', 'alpha0', 'C', 'B', 'u', 'x', 'v', 'w', 'zfr_input', 'status', 'notes']

def write_csv(path, res, prefix):
    with open(path, 'w', newline='') as f:
        wr = csv.DictWriter(f, fieldnames=FIELDS)
        wr.writeheader()
        for i, q in enumerate(res):
            row = q['row']
            L0s = '28.7296' if row['L0'] == 'LOG3E12' else row['L0']
            notes = (f"lam={row['lam']}; opt=IMPR; Bopt={q['Blab']}; "
                     + ("own modification of Bellotti's argument: box height lam*delta (Bellotti lam=1); " if row['lam'] != '1'
                        else "box height delta as in Bellotti; ")
                     + "corrected counting + improvements; N(s,T)=#{beta>=s, 0<gamma<=T}"
                     + ("; computed on [log(3e12),29], N=0 for T<=3e12" if row['L0'] == 'LOG3E12' else '')
                     + ("; (4.9) monotonicity factor K>1 used on part of the row" if not q['mono'] else '')
                     + ("; alpha0 below Bellotti's stated range 0.985" if Decimal(row['a0']) < Decimal('0.985') else ''))
            wr.writerow(dict(id=f"{prefix}{i+1:04d}", logT0=L0s, logT1=row['L1'], alpha0=row['a0'],
                             C=q['Cclaim'], B=q['B'], u=row['u'], x=row['x'], v=row['v'], w=row['w'],
                             zfr_input='+'.join(row['zfr']), status=q['status'], notes=notes))

def _dump(res, path):
    dump = []
    for q in res:
        d = {k: v for k, v in q.items() if k != 'zfr'}
        d['zfr'] = list(q['zfr'])
        if 'row' in d:
            d['row'] = dict(d['row']); d['row']['zfr'] = list(d['row']['zfr'])
        dump.append(d)
    json.dump(dump, open(path, 'w'), indent=1, default=str)

def shard(k, n, only_failed=False):
    T = tasks_all()
    if only_failed:
        prev = json.load(open(os.path.join(HERE, 'frontier_raw.json')))
        failed = {q['task_index'] for q in prev if not q.get('ok')}
    res = []
    t0 = time.time()
    for i, t in enumerate(T):
        if i % n != k:
            continue
        if only_failed and i not in failed:
            continue
        q = run_task(t); q['task_index'] = i
        res.append(q)
        if len(res) % 20 == 0:
            print(f"shard {k}: {len(res)} done {time.time()-t0:.0f}s", flush=True)
    _dump(res, os.path.join(HERE, f'frontier_shard_{k}' + ('_retry' if only_failed else '') + '.json'))
    print(f"shard {k} finished {len(res)} in {time.time()-t0:.0f}s", flush=True)

def merge(n):
    res = []
    for k in range(n):
        res += json.load(open(os.path.join(HERE, f'frontier_shard_{k}.json')))
    retry = {}
    for k in range(n):
        p = os.path.join(HERE, f'frontier_shard_{k}_retry.json')
        if os.path.exists(p):
            for q in json.load(open(p)):
                retry[q['task_index']] = q
    res = [retry.get(q['task_index'], q) for q in res]
    res.sort(key=lambda q: q['task_index'])
    for q in res:
        q['zfr'] = tuple(q['zfr'])
        if 'row' in q:
            q['row']['zfr'] = tuple(q['row']['zfr'])
    _dump(res, os.path.join(HERE, 'frontier_raw.json'))
    good = [q for q in res if q.get('ok')]
    bad = [(q['L0'], q['L1'], q['a0'], q['Blab'], q['status'], q.get('err', q.get('bad'))) for q in res if not q.get('ok')]
    print(f"ok {len(good)} / {len(res)}; failures ({len(bad)}):")
    for b in bad[:80]:
        print("   ", str(b)[:300])
    write_csv(os.path.join(HERE, 'rows_reopt.csv'), [q for q in good if q['row']['lam'] != '1'], 'RO')
    write_csv(os.path.join(HERE, 'rows_reopt_lam1.csv'), [q for q in good if q['row']['lam'] == '1'], 'RL')

if __name__ == '__main__':
    # python frontier.py shard k n   |   python frontier.py merge n
    if sys.argv[1] == 'shard':
        shard(int(sys.argv[2]), int(sys.argv[3]), only_failed=(len(sys.argv) > 4 and sys.argv[4] == 'retry'))
    elif sys.argv[1] == 'merge':
        merge(int(sys.argv[2]))
