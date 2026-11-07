"""rows_reopt_v2.csv: corrected lam-box argument + Phase-2 Lemmas A (d4), B (box count), C (pair residue).
python v2.py probe | python v2.py shard k n | python v2.py write n
Lemma A/B rigorous bounds come from work/phase2_lemmas/improvements.py (own lemmas, Arb-verified, unreviewed).
"""
import sys, os, math, csv, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase2_lemmas'))
from decimal import Decimal, ROUND_CEILING
import numpy as np
from scipy.optimize import minimize
from flint import arb
import belarb as B
import improvements as P2
from flint import ctx as _ctx
_ctx.prec = 128          # Phase-2 modules set 100 bits on import; pin our working precision
B.patch_phase2_rounding()
from reopt import ZFR_REF, ZFR_PRE, her_row_for
from frontier import ceil_sig, FIELDS, intervals, her_row_mid

HERE = os.path.dirname(os.path.abspath(__file__))
LAMS = ('1', '8', '14', '18', '22')
BFRAC = (('B_her', Decimal('1')), ('B_her*0.85', Decimal('0.85')), ('B_her*0.72', Decimal('0.72')), ('B_her*0.62', Decimal('0.62')))

def lo_str(L0):
    return '28.7296' if L0 == 'LOG3E12' else L0

def nu_callable(zfr):
    return lambda L: B.nu(zfr, arb(L), B.ARB)

_cf = {}
def cf_steps(L0, L1):
    return 12 if float(L1) > 500 else None          # high rows: 12 L-pieces (geometric rows of ratio <= 1.25)

def cf_rig(a0, zfr, L0, L1, lam, weyl=False):
    key = (a0, zfr, L0, L1, lam, bool(weyl))
    if key not in _cf:
        try:
            kw = {'weyl': True} if weyl else {}
            if cf_steps(L0, L1):
                _cf[key] = P2._B.cf_upper(float(a0), nu_callable(zfr), float(lo_str(L0)), float(L1), hfac=lam,
                                          L_steps=cf_steps(L0, L1), **kw)[0]
            else:
                _cf[key] = P2.cf_upper(float(a0), nu_callable(zfr), float(lo_str(L0)), float(L1), hfac=lam, **kw)
        except AssertionError:          # Lemma B geometry (r < 1/2, box inside the disc) not satisfiable
            _cf[key] = None
        _ctx.prec = 128                 # lemmaB_weyl sets 100 bits when first imported
    return _cf[key]

def grid_starts(f, xx, L0, n_keep=4):
    """feasibility-seeking starts: coarse grid in (u, v/u, w), keep the best finite ones."""
    Lf0 = float(lo_str(L0))
    cand = []
    for u in np.geomspace(max(27.0 / Lf0, 0.2), max(1.0, 1.2 * xx), 10):
        for rv in (1.15, 1.35, 1.6, 2.0, 2.6):
            for w in (0.01, 0.03, 0.08, 0.2, 0.5):
                p = [math.log(u), math.log(rv - 1), math.log(w)]
                val = f(p)
                if val < 1e8:
                    cand.append((val, p))
    cand.sort(key=lambda t: t[0])
    return [p for _, p in cand[:n_keep]]

def eps_for(x, L0, L1):
    lX = float(x) * 0.5 * (float(lo_str(L0)) + float(L1))
    return f"{2.05 / lX:.5f}"

def d4_rig(u, v, x, L0, L1):
    return P2.d4_upper(u, v, x, float(lo_str(L0)), float(L1), eps_list=[eps_for(x, L0, L1)])

def d4_mod(u, v, x, L0, L1):
    return max(P2.d4_model(u, v, x, float(lo_str(L0))), P2.d4_model(u, v, x, float(L1)))

def fobj(L0, L1, a0, xfix, zfr, lam, lems, cfv, extra_row=None):
    Lf0 = float(lo_str(L0))
    def f(p):
        if max(abs(float(t)) for t in p) > 50:
            return 1e9
        u = math.exp(p[0]); v = u * (1 + math.exp(p[1])); w = math.exp(p[2])
        xx = xfix if xfix is not None else math.exp(p[3])
        if not (u < xx and w < 3):
            return 1e9
        row = dict(L0=L0, L1=L1, a0=a0, u=repr(u), x=repr(xx), v=repr(v), w=repr(w), lam=lam, zfr=zfr, lems=lems)
        if extra_row:
            row.update(extra_row)
        if 'lemA' in lems:
            if u * Lf0 < 26 or (v - u) * Lf0 < 14.5:
                return 1e9
            row['d4A'] = repr(d4_mod(u, v, xx, L0, L1))
        if 'lemB' in lems.split(',') or 'lemBW' in lems.split(','):
            row['cfB'] = repr(cfv)
        try:
            q = B.row_bound(row, B.OPT_V2, B.FLT, pts=(0.0, 0.5, 1.0))
        except (ValueError, OverflowError, ZeroDivisionError):
            return 1e9
        Cv = q['C']
        if not (Cv > 0) or Cv != Cv or Cv == float('inf'):
            return 1e9
        return math.log(Cv)
    return f

def starts(hr, xs=None, L0=None):
    u, v, w, xh = float(hr['u']), float(hr['v']), float(hr['w']), float(hr['x'])
    sc = (xs / xh) if xs else 1.0
    S = []
    for su in (1.0, 0.8, 0.6):
        for sw in (1.0, 1.5):
            uu = max(u * sc * su, 27.0 / float(lo_str(L0)) if L0 else 0)
            vv = max(v * sc * su, uu + 15.0 / float(lo_str(L0)) if L0 else 0)
            S.append([math.log(uu), math.log(vv / uu - 1), math.log(w * sc * sw)])
    return S

def run_opt(f, S, extra=None):
    best = None
    for s0 in S:
        s0 = list(s0) + ([extra] if extra is not None else [])
        r = minimize(f, np.array(s0), method='Nelder-Mead', options=dict(maxiter=2500, xatol=1e-7, fatol=1e-9))
        r = minimize(f, r.x, method='Nelder-Mead', options=dict(maxiter=2500, xatol=1e-8, fatol=1e-10))
        if best is None or r.fun < best.fun:
            best = r
    return best

def optimise(L0, L1, a0, zfr, lems, hr, Blab, Bfrac):
    """returns (row, float C) with the best lambda from LAMS."""
    best = None
    for lam in LAMS:
        cfv = None
        if 'lemB' in lems:
            cf = cf_rig(a0, zfr, L0, L1, lam)
            if cf is None:
                continue
            cfv = float(cf.upper())
        if Blab == 'B_edge':
            nL0 = B.nuL(zfr, float(lo_str(L0)), B.FLT)
            f0 = fobj(L0, L1, a0, None, zfr, lam, lems, cfv)
            f = lambda p: f0(p) + 2 * math.exp(p[3]) * nL0
            S = starts(hr, None, L0)[:3] + grid_starts(fobj(L0, L1, a0, float(hr['x']), zfr, lam, lems, cfv), float(hr['x']), L0, 3)
            r = run_opt(f, S, extra=math.log(float(hr['x'])))
            if r is None or r.fun >= 1e8:
                continue
            xs = str(Decimal(repr(math.exp(r.x[3]))).quantize(Decimal('0.0001')))
            f1 = fobj(L0, L1, a0, float(xs), zfr, lam, lems, cfv)
            r = run_opt(f1, [list(r.x[:3])])
        else:
            xs = str((Decimal(hr['Bpr']) * Bfrac / 2).quantize(Decimal('0.0001')))
            f1 = fobj(L0, L1, a0, float(xs), zfr, lam, lems, cfv)
            r = run_opt(f1, starts(hr, float(xs), L0)[:3] + grid_starts(f1, float(xs), L0, 4))
        if r is None or r.fun >= 1e8:
            continue
        val = r.fun + (2 * float(xs) * B.nuL(zfr, float(lo_str(L0)), B.FLT) if Blab == 'B_edge' else 0)
        if best is None or val < best[0]:
            u = math.exp(r.x[0]); v = u * (1 + math.exp(r.x[1])); w = math.exp(r.x[2])
            best = (val, dict(L0=L0, L1=L1, a0=a0, u=f"{u:.7f}", x=xs, v=f"{v:.7f}", w=f"{w:.8f}", lam=lam, zfr=zfr, lems=lems),
                    math.exp(r.fun))
    return best

def certify(row):
    t = time.time()
    lems = row['lems']
    if 'lemA' in lems:
        d4 = d4_rig(row['u'], row['v'], row['x'], row['L0'], row['L1'])
        row['d4A'] = ceil_sig(float(d4.upper()), 8)
        row['epsA'] = eps_for(row['x'], row['L0'], row['L1'])
    if 'lemB' in lems.split(',') or 'lemBW' in lems.split(','):
        cf = cf_rig(row['a0'], row['zfr'], row['L0'], row['L1'], row['lam'], weyl=('lemBW' in lems.split(',')))
        row['cfB'] = ceil_sig(float(cf.upper()), 8)
        if cf_steps(row['L0'], row['L1']):
            row['cfLsteps'] = str(cf_steps(row['L0'], row['L1']))
    pa = B.row_bound(row, B.OPT_V2, B.ARB)
    Cu = float(pa['C'].upper())
    hyp = B.check_hypotheses(row, B.OPT_V2)
    bad = [h[0] for h in hyp if (not h[1]) and not h[0].startswith('[paper only]') and not h[0].startswith('(4.9)')]
    mono = [h for h in hyp if h[0].startswith('(4.9)')][0][1]
    return dict(row=row, ok=(not bad) and math.isfinite(Cu), bad=bad, mono=mono, C=Cu, Cclaim=ceil_sig(Cu), B=str(2 * Decimal(row['x'])),
                c1=float(pa['c1'].mid()), c5=float(pa['c5'].mid()), d4=float(arb(pa['d4']).mid()), cf=float(arb(pa['cf']).mid()),
                Hn=float(arb(pa['Hn']).mid()), secs=time.time() - t)

def probe():
    for (L0, L1) in (('LOG3E12', '29'), ('70', '71'), ('100', '102')):
        hr = her_row_mid(L0, L1)
        for lems in ('lemA,lemB,lemC', 'lemB,lemC', 'lemC'):
            for Blab, fr in (('B_edge', None),) + BFRAC:
                t = time.time()
                b = optimise(L0, L1, hr['a0'], ZFR_REF, lems, hr, Blab, fr)
                if b is None:
                    print(L0, L1, lems, Blab, 'infeasible'); continue
                print(f"{L0}-{L1} {lems:15s} {Blab:10s} B={2*float(b[1]['x']):7.3f} lam={b[1]['lam']:>3} floatC={b[2]:10.4g} (C_pr {float(hr['Cpr']):.4g}) u={b[1]['u']} v={b[1]['v']} w={b[1]['w']} {time.time()-t:.1f}s", flush=True)

def tasks_for_interval(L0, L1):
    hr = her_row_mid(L0, L1)
    T = []
    a0s = [hr['a0'], '0.98'] if Decimal(hr['a0']) > Decimal('0.98') else [hr['a0']]
    zfrs = [('refereed', ZFR_REF)]
    if (28.73 if L0 == 'LOG3E12' else float(L0)) < 73:
        zfrs.append(('audited preprint', ZFR_PRE))
    for st, zfr in zfrs:
        for a0 in a0s:
            for Blab, fr in (('B_edge', None),) + BFRAC:
                if a0 != hr['a0'] and Blab not in ('B_edge', 'B_her'):
                    continue
                T.append((st, zfr, a0, 'lemA,lemB,lemC', Blab, fr))
            if a0 == hr['a0']:
                for lems in ('lemB,lemC', 'lemC'):
                    for Blab, fr in (('B_edge', None), ('B_her', Decimal('1'))):
                        T.append((st, zfr, a0, lems, Blab, fr))
    return hr, T

def shard(k, n):
    res = []
    t0 = time.time()
    for gi, (L0, L1) in enumerate(intervals()):
        if gi % n != k:
            continue
        if L0 != 'LOG3E12' and float(L0) >= 200:      # (200,500] is done by shard_mid (no Lemma A there)
            continue
        hr, T = tasks_for_interval(L0, L1)
        for (st, zfr, a0, lems, Blab, fr) in T:
            b = None
            try:
                b = optimise(L0, L1, a0, zfr, lems, hr, Blab, fr)
                if b is None:
                    res.append(dict(gi=gi, ok=False, err='infeasible', L0=L0, L1=L1, a0=a0, lems=lems, Blab=Blab, status=st)); continue
                q = certify(b[1])
                q.update(gi=gi, status=st, Blab=Blab, Cfloat=b[2])
                res.append(q)
            except Exception as e:
                import traceback
                res.append(dict(gi=gi, ok=False, err=repr(e) + traceback.format_exc()[-400:], L0=L0, L1=L1, a0=a0, lems=lems, Blab=Blab, status=st,
                                prow=(dict(b[1], zfr=list(b[1]['zfr'])) if b else None)))
        print(f"shard {k}: interval {L0}-{L1} done ({time.time()-t0:.0f}s, {len(res)} rows)", flush=True)
        json.dump([dict(q, row=dict(q['row'], zfr=list(q['row']['zfr']))) if 'row' in q else q for q in res],
                  open(os.path.join(HERE, f'v2_raw_{k}.json'), 'w'), indent=1, default=str)
    print(f"shard {k} finished {time.time()-t0:.0f}s", flush=True)

def shard_mid(k, n):
    """(200, 500]: Lemma A is too expensive there (block count ~ log T per 0.25-piece); rows with lemB+lemC and lemC only."""
    res = []
    t0 = time.time()
    ivs = [(gi, iv) for gi, iv in enumerate(intervals()) if float(iv[0] if iv[0] != 'LOG3E12' else 0) >= 200]
    for j, (gi, (L0, L1)) in enumerate(ivs):
        if j % n != k:
            continue
        hr = her_row_mid(L0, L1)
        for lems in ('lemB,lemC', 'lemC'):
            for Blab, fr in (('B_edge', None),) + BFRAC[:3]:
                try:
                    b = optimise(L0, L1, hr['a0'], ZFR_REF, lems, hr, Blab, fr)
                    if b is None:
                        res.append(dict(gi=gi, ok=False, err='infeasible', L0=L0, L1=L1, lems=lems, Blab=Blab)); continue
                    q = certify(b[1]); q.update(gi=gi, status='refereed', Blab=Blab, Cfloat=b[2])
                    res.append(q)
                except Exception as e:
                    import traceback
                    res.append(dict(gi=gi, ok=False, err=repr(e) + traceback.format_exc()[-300:], L0=L0, L1=L1, lems=lems, Blab=Blab))
        print(f"mid shard {k}: {L0}-{L1} done ({time.time()-t0:.0f}s)", flush=True)
    json.dump([dict(q, row=dict(q['row'], zfr=list(q['row']['zfr']))) if 'row' in q else q for q in res],
              open(os.path.join(HERE, f'v2_raw_mid{k}.json'), 'w'), indent=1, default=str)

def shard_high(k, n):
    import high
    res = []
    t0 = time.time()
    for gi, (L0, L1) in enumerate(high.grid()):
        if gi % n != k:
            continue
        hr = high.her_row_containing(L0, L1)
        for lems in ('lemB,lemC', 'lemC'):
            for Blab, fr in (('B_edge', None), ('B_her', Decimal('1')), ('B_her*0.85', Decimal('0.85'))):
                try:
                    b = optimise(L0, L1, '0.985', high.ZFR_H, lems, hr, Blab, fr)
                    if b is None:
                        res.append(dict(gi=gi, ok=False, err='infeasible', L0=L0, L1=L1, lems=lems, Blab=Blab)); continue
                    q = certify(b[1]); q.update(gi=gi, status='refereed', Blab=Blab, Cfloat=b[2])
                    res.append(q)
                except Exception as e:
                    import traceback
                    res.append(dict(gi=gi, ok=False, err=repr(e) + traceback.format_exc()[-300:], L0=L0, L1=L1, lems=lems, Blab=Blab))
        print(f"high shard {k}: {L0}-{L1} done ({time.time()-t0:.0f}s)", flush=True)
    json.dump([dict(q, row=dict(q['row'], zfr=list(q['row']['zfr']))) if 'row' in q else q for q in res],
              open(os.path.join(HERE, f'v2h_raw_{k}.json'), 'w'), indent=1, default=str)

def write(n, prefix='v2', out='rows_reopt_v2.csv', idp='V2'):
    res = []
    for k in range(n):
        res += json.load(open(os.path.join(HERE, f'{prefix}_raw_{k}.json')))
    if prefix == 'v2':
        import glob
        for fp in sorted(glob.glob(os.path.join(HERE, 'v2_raw_mid*.json'))):
            res += json.load(open(fp))
    res.sort(key=lambda q: (q['gi'], q.get('status', ''), q.get('row', {}).get('a0', ''), q.get('row', {}).get('lems', ''), float(q.get('B', 0) or 0)))
    json.dump(res, open(os.path.join(HERE, f'{prefix}_raw.json'), 'w'), indent=1, default=str)
    bad = [q for q in res if not q.get('ok')]
    print(f"{len(res)} results, {len(bad)} not ok")
    for q in bad[:40]:
        print('  ', q.get('L0'), q.get('L1'), q.get('a0'), q.get('lems'), q.get('Blab'), str(q.get('err', q.get('bad')))[:200])
    with open(os.path.join(HERE, out), 'w', newline='') as f:
        wr = csv.DictWriter(f, fieldnames=FIELDS)
        wr.writeheader()
        i = 0
        for q in res:
            if not q.get('ok'):
                continue
            i += 1
            row = dict(q['row'])
            # headroom: stored lemma constants 1e-6 high, claimed C 0.25% high (covers the (1+tol) slack of an
            # independent adaptive re-evaluation at another precision; C is increasing in d4A and cfB)
            if 'd4A' in row:
                row['d4A'] = ceil_sig(float(row['d4A']) * (1 + 1e-6), 8)
            if 'cfB' in row:
                row['cfB'] = ceil_sig(float(row['cfB']) * (1 + 1e-6), 8)
            q = dict(q, Cclaim=ceil_sig(float(q['C']) * (1 + 2.5e-3), 6))
            notes = (f"opt=V2; lems={row['lems']}; lam={row['lam']}; Bopt={q['Blab']}; "
                     + (f"d4A={row['d4A']}; epsA={row['epsA']}; " if 'lemA' in row['lems'] else '')
                     + (f"cfB={row['cfB']}; " if 'lemB' in row['lems'] else '')
                     + (f"cfLsteps={row['cfLsteps']}; " if 'cfLsteps' in row else '')
                     + "corrected lam-box argument + Phase-2 lemmas (own, unreviewed); N(s,T)=#{beta>=s, 0<gamma<=T}"
                     + ("; computed on [log(3e12),29]" if row['L0'] == 'LOG3E12' else '')
                     + ("; alpha0 below Bellotti's 0.985" if Decimal(row['a0']) < Decimal('0.985') else ''))
            wr.writerow(dict(id=f"{idp}{i:04d}", logT0=lo_str(row['L0']), logT1=row['L1'], alpha0=row['a0'], C=q['Cclaim'], B=q['B'],
                             u=row['u'], x=row['x'], v=row['v'], w=row['w'], zfr_input='+'.join(row['zfr']), status=q['status'], notes=notes))
    print(f"wrote {i} rows")

if __name__ == '__main__':
    if sys.argv[1] == 'probe':
        probe()
    elif sys.argv[1] == 'shard':
        shard(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == 'write':
        write(int(sys.argv[2]))
    elif sys.argv[1] == 'shard_mid':
        shard_mid(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == 'shard_high':
        shard_high(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == 'write_high':
        write(int(sys.argv[2]), prefix='v2h', out='rows_high_v2.csv', idp='H2')
