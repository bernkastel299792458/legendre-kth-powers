"""rows_mid_v4.csv: log T in [110, 600], lemma set lemA,lemBW,lemC,lemD + c1zeta=hpy,
zero-free region max(lw_local [Theorem Z v2], Littlewood 21.233, KV 54.004, Ford where valid).
Merit (edge of the zero-free region, L ~ 38 log T):  M = log C + B nu(T0) log T0 + log(38/(38 - B)).
python v4.py shard k n lo hi | python v4.py write
"""
import sys, os, math, csv, json, time, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal
import v3
from v2 import certify, lo_str
from frontier import ceil_sig, FIELDS, her_row_mid
import belarb as B

HERE = os.path.dirname(os.path.abspath(__file__))
ZFR_MID = ('lw_local', 'lw21.233', 'kv54.004', 'ford')
LEMS = 'lemA,lemBW,lemC,lemD'
A0S = ('0.99', '0.98', '0.97', '0.96')
KS = 38.0

def intervals():
    E = []
    for a, b, h in ((110, 200, 2), (200, 400, 5), (400, 600, 10)):
        x = a
        while x < b:
            E.append((str(x), str(x + h)))
            x += h
    return E

def merit(C, Bv, L0):
    v = float(L0)
    if Bv >= KS:
        return float('inf')
    return math.log(C) + Bv * B.nuL(ZFR_MID, v, B.FLT) + math.log(KS / (KS - Bv))

def shard(k, n, lo, hi):
    v3.EXTRA = {'c1zeta': 'hpy'}
    res = []
    t0 = time.time()
    for gi, (L0, L1) in enumerate(intervals()):
        if not (lo <= float(L1) <= hi) or gi % n != k:
            continue
        v3.LS = KS * float(L0)                      # v3.optimise uses log(LS/(LS - B v0)) = log(38/(38-B))
        hr = her_row_mid(L0, L1)
        for a0 in A0S:
            Bstar = None
            for lab in ('merit', 'merit*0.85', 'merit*0.7'):
                b = None
                try:
                    if lab == 'merit':
                        b = v3.optimise(L0, L1, a0, LEMS, hr, zfr=ZFR_MID)
                    else:
                        if Bstar is None:
                            continue
                        fac = Decimal(lab.split('*')[1])
                        b = v3.optimise(L0, L1, a0, LEMS, hr, Bfix=str((Decimal(Bstar) * fac).quantize(Decimal('0.0001'))), zfr=ZFR_MID)
                    if b is None:
                        res.append(dict(gi=gi, ok=False, err='infeasible', L0=L0, L1=L1, a0=a0, Blab=lab)); continue
                    if lab == 'merit':
                        Bstar = str(2 * Decimal(b[1]['x']))
                    q = certify(b[1])
                    q.update(gi=gi, status='refereed', Blab=lab, Cfloat=b[2], merit=merit(q['C'], float(q['B']), L0),
                             Zeff=1 / B.nuL(ZFR_MID, float(L0), B.FLT))
                    res.append(q)
                except Exception as e:
                    import traceback
                    res.append(dict(gi=gi, ok=False, err=repr(e) + traceback.format_exc()[-400:], L0=L0, L1=L1, a0=a0, Blab=lab,
                                    prow=(dict(b[1], zfr=list(b[1]['zfr'])) if b else None)))
        print(f"v4 shard {k}: {L0}-{L1} done ({time.time()-t0:.0f}s, {len(res)})", flush=True)
        json.dump([dict(q, row=dict(q['row'], zfr=list(q['row']['zfr']))) if 'row' in q else q for q in res],
                  open(os.path.join(HERE, f'v4_raw_{k}_{int(lo)}.json'), 'w'), indent=1, default=str)
    print(f"v4 shard {k} finished {time.time()-t0:.0f}s", flush=True)

def write():
    res = []
    for p in sorted(glob.glob(os.path.join(HERE, 'v4_raw_*.json'))):
        res += json.load(open(p))
    if not res:                                     # shard files cleaned up: rebuild from the merged file
        res = json.load(open(os.path.join(HERE, 'v4_raw.json')))
    res.sort(key=lambda q: (q['gi'], -float(q.get('row', {}).get('a0', q.get('a0', 0)) or 0), q.get('Blab', '')))
    json.dump(res, open(os.path.join(HERE, 'v4_raw.json'), 'w'), indent=1, default=str)
    bad = [q for q in res if not q.get('ok')]
    print(f"{len(res)} results, {len(bad)} not ok")
    for q in bad[:20]:
        print('  ', q.get('L0'), q.get('L1'), q.get('a0'), q.get('Blab'), str(q.get('err', q.get('bad')))[:200])
    with open(os.path.join(HERE, 'rows_mid_v4.csv'), 'w', newline='') as f:
        wr = csv.DictWriter(f, fieldnames=FIELDS)
        wr.writeheader()
        i = 0
        for q in res:
            if not q.get('ok'):
                continue
            i += 1
            row = dict(q['row'])
            row['d4A'] = ceil_sig(float(row['d4A']) * (1 + 1e-6), 8)
            row['cfB'] = ceil_sig(float(row['cfB']) * (1 + 1e-6), 8)
            Ccl = ceil_sig(float(q['C']) * (1 + 2.5e-3), 6)
            notes = (f"opt=V2; lems={row['lems']}; lam={row['lam']}; Bopt={q['Blab']}; c1zeta=hpy; "
                     f"d4A={row['d4A']}; epsA={row['epsA']}; cfB={row['cfB']}; "
                     f"Zeff={q['Zeff']:.4f}; merit={merit(float(Ccl), float(q['B']), row['L0']):.4f} "
                     "(log C + B nu(T0) log T0 + log(38/(38-B))); "
                     "zfr: lw_local = Theorem Z v2 (phase1_littlewood sec.11; own proof, refereed inputs, reviewed) "
                     "max Littlewood 21.233, KV 54.004, Ford; corrected lam-box argument + Phase-2 lemmas (own, reviewed); "
                     "N(s,T)=#{beta>=s, 0<gamma<=T}")
            wr.writerow(dict(id=f"M4{i:04d}", logT0=row['L0'], logT1=row['L1'], alpha0=row['a0'], C=Ccl, B=q['B'],
                             u=row['u'], x=row['x'], v=row['v'], w=row['w'], zfr_input='+'.join(row['zfr']), status='refereed', notes=notes))
    print(f"wrote {i} rows")

if __name__ == '__main__':
    if sys.argv[1] == 'shard':
        shard(int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5]))
    elif sys.argv[1] == 'write':
        write()
