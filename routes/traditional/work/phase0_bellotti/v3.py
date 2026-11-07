"""rows_low_v3.csv: low heights with the local classical zero-free region (cl_local, our Theorem C, phase1_littlewood sec.12),
optimised for the seam figure of merit  M = log C + B/Z1(T0) + log(Ls/(Ls - B log T0)),  Ls = 1600.
python v3.py shard k n | python v3.py write n
"""
import sys, os, math, csv, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal
import numpy as np
from scipy.optimize import minimize
from flint import arb
import v2
from v2 import cf_rig, d4_mod, fobj, starts, grid_starts, run_opt, certify, LAMS, lo_str
from frontier import ceil_sig, FIELDS, her_row_mid
import belarb as B

HERE = os.path.dirname(os.path.abspath(__file__))
ZFR = ('cl_local',)
LS = 1600.0
A0S = ('0.99', '0.985', '0.98', '0.975', '0.97', '0.96')

def intervals():
    E = []
    def rng(a, b, h):
        x = Decimal(a)
        while x < Decimal(b):
            y = min(x + Decimal(h), Decimal(b))
            E.append((str(x), str(y)))
            x = y
    rng('28.8', '30', '0.1')
    E.insert(0, ('LOG3E12', '28.8'))
    rng('30', '33', '0.25'); rng('33', '40', '0.5'); rng('40', '60', '1')
    return E

def Z1_at(L0, zfr=None):
    Lf = float(lo_str(L0)) if L0 != 'LOG3E12' else math.log(3e12)
    return 1 / B.nuL(zfr or ZFR, Lf, B.FLT)

def merit(C, Bv, L0, zfr=None):
    v = math.log(3e12) if L0 == 'LOG3E12' else float(L0)
    if LS - Bv * v <= 0:
        return float('inf')
    return math.log(C) + Bv / Z1_at(L0, zfr) + math.log(LS / (LS - Bv * v))

EXTRA = {}          # extra row fields for the new lemma set (c1zeta=hpy)

def optimise(L0, L1, a0, lems, hr, Bfix=None, zfr=None):
    """Bfix None: x free, minimise the merit; else x = Bfix/2."""
    global ZFR
    if zfr is not None:
        ZFR = zfr
    ex = dict(EXTRA) if 'lemD' in lems else {}
    best = None
    v0 = math.log(3e12) if L0 == 'LOG3E12' else float(L0)
    Z1 = Z1_at(L0)
    for lam in LAMS:
        cfv = None
        if 'lemB' in lems.split(',') or 'lemBW' in lems.split(','):
            cf = cf_rig(a0, ZFR, L0, L1, lam, weyl=('lemBW' in lems.split(',')))
            if cf is None:
                continue
            cfv = float(cf.upper())
        if Bfix is None:
            f0 = fobj(L0, L1, a0, None, ZFR, lam, lems, cfv, ex)
            def f(p, f0=f0):
                xx = math.exp(p[3]) if abs(p[3]) < 50 else 1e9
                if LS - 2 * xx * v0 <= 0:
                    return 1e9
                return f0(p) + 2 * xx / Z1 + math.log(LS / (LS - 2 * xx * v0))
            S = starts(hr, None, L0)[:3] + grid_starts(fobj(L0, L1, a0, float(hr['x']), ZFR, lam, lems, cfv, ex), float(hr['x']), L0, 3)
            r = run_opt(f, S, extra=math.log(float(hr['x'])))
            if r is None or r.fun >= 1e8:
                continue
            xs = str(Decimal(repr(math.exp(r.x[3]))).quantize(Decimal('0.0001')))
            f1 = fobj(L0, L1, a0, float(xs), ZFR, lam, lems, cfv, ex)
            r = run_opt(f1, [list(r.x[:3])] + grid_starts(f1, float(xs), L0, 2))
        else:
            xs = str((Decimal(Bfix) / 2).quantize(Decimal('0.0001')))
            f1 = fobj(L0, L1, a0, float(xs), ZFR, lam, lems, cfv, ex)
            r = run_opt(f1, starts(hr, float(xs), L0)[:3] + grid_starts(f1, float(xs), L0, 4))
        if r is None or r.fun >= 1e8:
            continue
        m = merit(math.exp(r.fun), 2 * float(xs), L0)
        if best is None or m < best[0]:
            u = math.exp(r.x[0]); v = u * (1 + math.exp(r.x[1])); w = math.exp(r.x[2])
            best = (m, dict(L0=L0, L1=L1, a0=a0, u=f"{u:.7f}", x=xs, v=f"{v:.7f}", w=f"{w:.8f}", lam=lam, zfr=ZFR, lems=lems, **ex),
                    math.exp(r.fun))
    return best

def tasks(L0, L1):
    nu0 = B.nu(ZFR, math.log(3e12) if L0 == 'LOG3E12' else float(L0), B.FLT)
    a0s = [a for a in A0S if float(a) < 1 - nu0 - 1e-4]
    T = []
    for a0 in a0s:
        T.append((a0, 'lemA,lemB,lemC', 'merit'))
        T.append((a0, 'lemA,lemB,lemC', 'merit*0.85'))
        T.append((a0, 'lemA,lemB,lemC', 'merit*0.7'))
    for a0 in ('0.985', '0.98'):
        if a0 in a0s:
            T.append((a0, 'lemB,lemC', 'merit'))
            T.append((a0, 'lemC', 'merit'))
    return T

def shard(k, n):
    res = []
    t0 = time.time()
    for gi, (L0, L1) in enumerate(intervals()):
        if gi % n != k:
            continue
        hr = her_row_mid(L0, L1)
        Bstar = {}
        for (a0, lems, lab) in tasks(L0, L1):
            b = None
            try:
                if lab == 'merit':
                    b = optimise(L0, L1, a0, lems, hr)
                else:
                    if (a0, lems) not in Bstar:
                        continue
                    fac = Decimal(lab.split('*')[1])
                    b = optimise(L0, L1, a0, lems, hr, Bfix=str((Decimal(Bstar[(a0, lems)]) * fac).quantize(Decimal('0.0001'))))
                if b is None:
                    res.append(dict(gi=gi, ok=False, err='infeasible', L0=L0, L1=L1, a0=a0, lems=lems, Blab=lab)); continue
                if lab == 'merit':
                    Bstar[(a0, lems)] = str(2 * Decimal(b[1]['x']))
                q = certify(b[1])
                q.update(gi=gi, status='refereed', Blab=lab, Cfloat=b[2], merit=merit(q['C'], float(q['B']), L0), Z1=Z1_at(L0))
                res.append(q)
            except Exception as e:
                import traceback
                res.append(dict(gi=gi, ok=False, err=repr(e) + traceback.format_exc()[-400:], L0=L0, L1=L1, a0=a0, lems=lems, Blab=lab,
                                prow=(dict(b[1], zfr=list(b[1]['zfr'])) if b else None)))
        print(f"v3 shard {k}: {L0}-{L1} done ({time.time()-t0:.0f}s, {len(res)})", flush=True)
        json.dump([dict(q, row=dict(q['row'], zfr=list(q['row']['zfr']))) if 'row' in q else q for q in res],
                  open(os.path.join(HERE, f'v3_raw_{k}.json'), 'w'), indent=1, default=str)
    print(f"v3 shard {k} finished {time.time()-t0:.0f}s", flush=True)

NEWLEMS = 'lemA,lemBW,lemC,lemD'
ZFR_HI = ('cl5.558691', 'ford', 'lw21.233')       # above 60 (cl_local ends at 60): refereed regions

def intervals_b():
    E = list(intervals())
    for a in range(60, 80):
        E.append((str(a), str(a + 1)))
    for a in range(80, 110, 2):
        E.append((str(a), str(a + 2)))
    return E

def shard_b(k, n, lo, hi):
    """new lemma set (Lemmas A, B-W, C, D + Hiary-Patel-Yang in c1) on intervals_b()[lo:hi]."""
    global EXTRA
    EXTRA = {'c1zeta': 'hpy'}
    res = []
    t0 = time.time()
    I = intervals_b()
    for gi, (L0, L1) in enumerate(I):
        if not (lo <= gi < hi) or gi % n != k:
            continue
        zfr = ('cl_local',) if float(L1) < 59.5 else ZFR_HI    # cl_local ends at 60 (balls must stay below)
        hr = her_row_mid(L0, L1)
        nu0 = B.nu(zfr, math.log(3e12) if L0 == 'LOG3E12' else float(L0), B.FLT)
        a0s = [a for a in (A0S if float(L1) <= 33 else ('0.99', '0.98', '0.97')) if float(a) < 1 - nu0 - 1e-4]
        facs = ('merit', 'merit*0.85', 'merit*0.7', 'merit*0.55') if float(L1) <= 33 else ('merit', 'merit*0.85', 'merit*0.7')
        for a0 in a0s:
            Bstar = None
            for lab in facs:
                b = None
                try:
                    if lab == 'merit':
                        b = optimise(L0, L1, a0, NEWLEMS, hr, zfr=zfr)
                    else:
                        if Bstar is None:
                            continue
                        fac = Decimal(lab.split('*')[1])
                        b = optimise(L0, L1, a0, NEWLEMS, hr, Bfix=str((Decimal(Bstar) * fac).quantize(Decimal('0.0001'))), zfr=zfr)
                    if b is None:
                        res.append(dict(gi=gi, ok=False, err='infeasible', L0=L0, L1=L1, a0=a0, lems=NEWLEMS, Blab=lab)); continue
                    if lab == 'merit':
                        Bstar = str(2 * Decimal(b[1]['x']))
                    q = certify(b[1])
                    q.update(gi=gi, status='refereed', Blab=lab, Cfloat=b[2], merit=merit(q['C'], float(q['B']), L0), Z1=Z1_at(L0))
                    res.append(q)
                except Exception as e:
                    import traceback
                    res.append(dict(gi=gi, ok=False, err=repr(e) + traceback.format_exc()[-400:], L0=L0, L1=L1, a0=a0, lems=NEWLEMS, Blab=lab,
                                    prow=(dict(b[1], zfr=list(b[1]['zfr'])) if b else None)))
        print(f"v3b shard {k}: {L0}-{L1} done ({time.time()-t0:.0f}s, {len(res)})", flush=True)
        json.dump([dict(q, row=dict(q['row'], zfr=list(q['row']['zfr']))) if 'row' in q else q for q in res],
                  open(os.path.join(HERE, f'v3b_raw_{k}_{lo}.json'), 'w'), indent=1, default=str)
    print(f"v3b shard {k} finished {time.time()-t0:.0f}s", flush=True)


def write(n):
    res = []
    import glob
    for k in range(n):
        p = os.path.join(HERE, f'v3_raw_{k}.json')
        if os.path.exists(p):
            res += json.load(open(p))
    for p in sorted(glob.glob(os.path.join(HERE, 'v3b_raw_*.json'))):
        res += json.load(open(p))
    res.sort(key=lambda q: (q['gi'], q.get('row', {}).get('lems', q.get('lems', '')), -float(q.get('row', {}).get('a0', 0) or 0), q.get('Blab', '')))
    json.dump(res, open(os.path.join(HERE, 'v3_raw.json'), 'w'), indent=1, default=str)
    bad = [q for q in res if not q.get('ok')]
    print(f"{len(res)} results, {len(bad)} not ok")
    for q in bad[:30]:
        print('  ', q.get('L0'), q.get('L1'), q.get('a0'), q.get('lems'), q.get('Blab'), str(q.get('err', q.get('bad')))[:160])
    # joint sup over delta (count=joint) for the rows without Lemma B (Lemma B rows are joint already)
    extra = []
    for q in res:
        if q.get('ok') and 'lemB' not in q['row']['lems']:
            r2 = dict(q['row']); r2['zfr'] = tuple(r2['zfr']); r2['cnt'] = 'joint'
            p = B.row_bound(r2, B.OPT_V2, B.ARB)
            if bool(p['den'] > 0):
                extra.append(dict(q, row=dict(r2, zfr=list(r2['zfr'])), C=float(p['C'].upper()), Blab=q['Blab'] + '+joint'))
    res = res + extra
    res.sort(key=lambda q: (q['gi'], q.get('row', {}).get('lems', q.get('lems', '')), -float(q.get('row', {}).get('a0', 0) or 0), q.get('Blab', '')))
    with open(os.path.join(HERE, 'rows_low_v3.csv'), 'w', newline='') as f:
        wr = csv.DictWriter(f, fieldnames=FIELDS)
        wr.writeheader()
        i = 0
        for q in res:
            if not q.get('ok'):
                continue
            i += 1
            row = dict(q['row'])
            if 'd4A' in row:
                row['d4A'] = ceil_sig(float(row['d4A']) * (1 + 1e-6), 8)
            if 'cfB' in row:
                row['cfB'] = ceil_sig(float(row['cfB']) * (1 + 1e-6), 8)
            Ccl = ceil_sig(float(q['C']) * (1 + 2.5e-3), 6)
            notes = (f"opt=V2; lems={row['lems']}; lam={row['lam']}; Bopt={q['Blab']}; "
                     + ("count=joint; " if row.get('cnt') == 'joint' else '')
                     + ("c1zeta=hpy; " if row.get('c1zeta') == 'hpy' else '')
                     + ""
                     + (f"d4A={row['d4A']}; epsA={row['epsA']}; " if 'lemA' in row['lems'] else '')
                     + (f"cfB={row['cfB']}; " if 'lemB' in row['lems'] else '')
                     + f"Z1loc={q['Z1']:.4f}; merit={merit(float(Ccl), float(q['B']), row['L0'], tuple(row['zfr'])):.4f} (log C + B/Z1 + log(1600/(1600-B logT0))); "
                     + ("zfr cl_local = Theorem C (phase1_littlewood sec.12; own proof, refereed inputs); " if 'cl_local' in row['zfr'] else '')
                     + "corrected lam-box argument + Phase-2 lemmas (own); N(s,T)=#{beta>=s, 0<gamma<=T}"
                     + ("; computed on [log(3e12),28.8]" if row['L0'] == 'LOG3E12' else '')
                     + ("; alpha0 below Bellotti's 0.985" if Decimal(row['a0']) < Decimal('0.985') else ''))
            wr.writerow(dict(id=f"L3{i:04d}", logT0=lo_str(row['L0']), logT1=row['L1'], alpha0=row['a0'], C=Ccl, B=q['B'],
                             u=row['u'], x=row['x'], v=row['v'], w=row['w'], zfr_input='+'.join(row['zfr']), status='refereed', notes=notes))
    print(f"wrote {i} rows")

if __name__ == '__main__':
    if sys.argv[1] == 'shard':
        shard(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == 'write':
        write(int(sys.argv[2]))
    elif sys.argv[1] == 'shard_b':
        shard_b(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
