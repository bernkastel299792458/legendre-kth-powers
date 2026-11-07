"""Task 5: independent re-check of every row of the rows_*.csv files in this folder, in pure Arb (python-flint).

For each row:
  * rebuild the parameters from the CSV (exact decimal strings); option set from the notes:
    'opt=IMPR' -> OPT_IMPR, 'opt=IMPRH' -> OPT_IMPR_H (high-L evaluation), both with lam from 'lam=...';
    'opt=CORRH' -> OPT_CORR_H (lam=1); 'opt=V2' -> OPT_V2 with the Phase-2 lemmas listed in 'lems=...'
       (lemA, lemB or lemBW [cf_upper(weyl=True)], lemC, lemD [mollifier on Re s=1/2 in c1]; 'c1zeta=hpy' uses
       min(Patel-Yang, Hiary-Patel-Yang) in c1; 'count=joint' takes the joint sup over delta):
       lemA / lemB constants are recomputed with work/phase2_lemmas/improvements.py (d4_upper, cf_upper) and must be
       <= the stored d4A / cfB (C is increasing in both); lemC needs 1 < U/L^2 < X (checked);
    otherwise the corrected-faithful set OPT_CORR (lam=1);
  * check every lemma hypothesis over the whole row in Arb (belarb.check_hypotheses);
  * recompute the rigorous upper bound of C by adaptive bisection over L in [max(logT0, log 3e12), logT1];
  * assert  C_claimed >= computed upper bound  and  B_claimed >= 2x  (exact decimal comparison);
  * assert status consistent with the zero-free-region input ('cl4.896' => 'audited preprint').
Rows whose status contains 'UNSURE' (sup over T not verifiable by this code) are reported and skipped.

Usage:  python verify_rows.py [file.csv ...] [-v] [--shard=k/n]     (default: all rows_*.csv here)
Exit code 0 iff every checked row passes.
"""
import sys, os, csv, math, glob, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal
from flint import arb, ctx
import belarb as B

ctx.prec = 128
HERE = os.path.dirname(os.path.abspath(__file__))
LOG3E12_DEC = Decimal('28.72963')   # < log(3e12) = 28.7296333...; rows starting below are computed from log(3e12)

def parse_notes(notes):
    d = {}
    for part in notes.split(';'):
        if '=' in part:
            k, v = part.split('=', 1)
            d[k.strip()] = v.strip()
    return d

def row_from_csv(rec):
    nd = parse_notes(rec['notes'])
    L0 = rec['logT0']
    if Decimal(L0) <= LOG3E12_DEC:
        L0 = 'LOG3E12'
    zfr = tuple(rec['zfr_input'].split('+'))
    tag = nd.get('opt', parse_notes(rec['notes'].split(';')[0] + ';').get('opt', ''))
    if tag == 'IMPR':
        opt = dict(B.OPT_IMPR); lam = nd.get('lam', '1')
    elif tag == 'IMPRH':
        opt = dict(B.OPT_IMPR_H); lam = nd.get('lam', '1')
    elif tag == 'CORRH':
        opt = dict(B.OPT_CORR_H); lam = '1'
    elif tag == 'V2':
        opt = dict(B.OPT_V2); lam = nd.get('lam', '1')
    else:
        opt = dict(B.OPT_CORR); lam = '1'
    row = dict(L0=L0, L1=rec['logT1'], a0=rec['alpha0'], u=rec['u'], x=rec['x'], v=rec['v'], w=rec['w'], lam=lam, zfr=zfr)
    if tag == 'V2':
        row['lems'] = nd.get('lems', '').replace('+', ',')
        if nd.get('count') == 'joint':
            row['cnt'] = 'joint'
        if nd.get('c1zeta') == 'hpy':
            row['c1zeta'] = 'hpy'
        for key in ('d4A', 'epsA', 'cfB', 'cfLsteps'):
            if key in nd:
                row[key] = nd[key]
    return row, opt

_P2 = None
def phase2():
    global _P2
    if _P2 is None:
        sys.path.insert(0, os.path.join(HERE, '..', 'phase2_lemmas'))
        import improvements
        import lemmaB_weyl, lemmaD_mollifier      # both set 100 bits on import; import now, then pin 128
        _P2 = improvements
        ctx.prec = 128
        B.patch_phase2_rounding()                 # review round 2 item 1: A_eta kept as an arb upper bound
        B.lemD_constants()
        ctx.prec = 128       # the Phase-2 modules set 100 bits on import; keep one precision for every row
    return _P2

def check_v2_constants(rec, row):
    """recompute the Phase-2 lemma constants rigorously and compare with the stored ones (C is increasing in both)."""
    msgs = []
    lems = row.get('lems', '')
    lo, hi = float(rec['logT0']), float(rec['logT1'])
    if 'lemA' in lems:
        try:
            d4 = phase2().d4_upper(row['u'], row['v'], row['x'], lo, hi, eps_list=[row['epsA']])
            if not bool(d4.upper() <= arb(row['d4A'])):
                msgs.append(f"Lemma A d4 {float(d4.upper()):.10g} > stored {row['d4A']}")
        except Exception as e:
            msgs.append(f"Lemma A not applicable: {e!r}")
    if 'lemB' in lems.split(',') or 'lemBW' in lems.split(','):
        try:
            zfr = row['zfr']
            weyl = 'lemBW' in lems.split(',')
            nuf = lambda L: B.nu(zfr, arb(L), B.ARB)
            kw = {'weyl': True} if weyl else {}
            if 'cfLsteps' in row:
                cf = phase2()._B.cf_upper(float(row['a0']), nuf, lo, hi, hfac=row['lam'], L_steps=int(row['cfLsteps']), **kw)[0]
            else:
                cf = phase2().cf_upper(float(row['a0']), nuf, lo, hi, hfac=row['lam'], **kw)
            ctx.prec = 128
            if not bool(cf.upper() <= arb(row['cfB'])):
                msgs.append(f"Lemma B cf {float(cf.upper()):.10g} > stored {row['cfB']}")
        except Exception as e:
            msgs.append(f"Lemma B not applicable: {e!r}")
    if 'lemC' in lems:
        # Lemma C(ii) needs 1 < Y = U/L^2 < X on the whole row
        u, x = arb(row['u']), arb(row['x'])
        L0 = arb(lo).max(B.LOG3E12_ARB); L1 = arb(hi)
        if not bool(u * L0 > 2 * L1.log()) or not bool(x > u):
            msgs.append("Lemma C needs 1 < U/L^2 < X")
    return msgs

def check_file(path, verbose=False, shard=None):
    nfail = nok = nskip = 0
    with open(path, newline='') as f:
        recs = list(csv.DictReader(f))
    if shard is not None:
        k, n = shard
        recs = [r for i, r in enumerate(recs) if i % n == k]
    for rec in recs:
        t0 = time.time()
        if 'UNSURE' in rec['status']:
            print(f"  SKIP {rec['id']}: status {rec['status']}")
            nskip += 1
            continue
        row, opt = row_from_csv(rec)
        msgs = []
        # B
        if Decimal(rec['B']) < 2 * Decimal(rec['x']):
            msgs.append(f"B_claimed {rec['B']} < 2x = {2*Decimal(rec['x'])}")
        # status vs inputs
        if 'cl4.896' in row['zfr'] and rec['status'] != 'audited preprint':
            msgs.append("uses 4.896 but status is not 'audited preprint'")
        if 'cl4.896' not in row['zfr'] and rec['status'] not in ('refereed',):
            msgs.append(f"status {rec['status']} but only refereed regions")
        if Decimal(rec['logT1']) <= Decimal(rec['logT0']):
            msgs.append("empty range")
        if opt.get('v2'):
            msgs += check_v2_constants(rec, row)
        # hypotheses
        hyp = B.check_hypotheses(row, opt)
        for name, ok, det in hyp:
            if ok or name.startswith('[paper only]'):
                continue
            if name.startswith('(4.9)') and opt.get('mono'):
                continue          # handled by the factor K in the bound
            msgs.append(f"hypothesis failed: {name} {det}")
        # C
        p = B.row_bound(row, opt, B.ARB)
        Cup = p['C'].upper()
        Ccl = arb(rec['C'])
        if not bool(Ccl >= Cup):
            msgs.append(f"C_claimed {rec['C']} < computed upper bound {float(Cup):.8g}")
        if msgs:
            nfail += 1
            print(f"  FAIL {rec['id']} [{rec['logT0']},{rec['logT1']}] a0={rec['alpha0']} B={rec['B']}: " + " | ".join(msgs))
        else:
            nok += 1
            if verbose:
                print(f"  ok   {rec['id']} [{rec['logT0']},{rec['logT1']}] a0={rec['alpha0']} B={rec['B']} C={rec['C']} >= {float(Cup):.8g}  ({time.time()-t0:.1f}s)")
    print(f"{os.path.basename(path)}: {nok} ok, {nfail} FAILED, {nskip} skipped")
    return nfail

def main():
    phase2()                 # import once, up front, so every row is checked at the same precision
    args = sys.argv[1:]
    shard = None
    for a in args:
        if a.startswith('--shard='):
            k, n = a.split('=')[1].split('/'); shard = (int(k), int(n))
    files = [a for a in args if not a.startswith('-')] or sorted(glob.glob(os.path.join(HERE, 'rows_*.csv')))
    verbose = '-v' in args
    tot = 0
    for fp in files:
        tot += check_file(fp, verbose, shard)
    print("ALL PASS" if tot == 0 else f"{tot} FAILURES")
    sys.exit(0 if tot == 0 else 1)

if __name__ == '__main__':
    main()
