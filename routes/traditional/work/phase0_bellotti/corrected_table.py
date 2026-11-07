"""Task 3: her Table 4 parameters + corrections (rigorous Arb, sup over the whole row) -> rows_corrected_faithful.csv
and the per-correction factor table (printed, and written to corrected_factors.txt).
Run: python corrected_table.py
"""
import sys, os, math, csv
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from decimal import Decimal, ROUND_CEILING
from flint import arb
import belarb as B
from beltables import rows

HERE = os.path.dirname(os.path.abspath(__file__))

def ceil_sig(xarb, sig=6):
    x = Decimal(str(float(arb(xarb).upper())))
    x = x * (1 + Decimal('1e-12'))
    e = x.adjusted() - sig + 1
    q = Decimal(1).scaleb(e)
    return format((x / q).to_integral_value(rounding=ROUND_CEILING) * q, 'f')

SINGLE = [('count', dict(count='fixed')), ('d4', dict(d4='rza')), ('d3only', dict(d4='paper')),
          ('c5:G(1/2)', dict(g5='fixed')), ('d2,(v+w)^4', dict(d2='fixed')), ('consts', dict(consts='verified')),
          ('T-range', dict(rng='full'))]

def main():
    out_rows = []
    lines = []
    hdr = f"{'row':>14} {'a0':>6} {'C_printed':>11} {'C_code':>11} " + " ".join(f"{n:>11}" for n, _ in SINGLE) + \
          f" {'mono':>6} {'ALL':>8} {'ALL+g3e12':>9}  {'C_corr':>11}"
    lines.append(hdr)
    for idx, r in enumerate(rows(include_kv=True)):
        wide = float(r['L1']) > 3000
        base = dict(B.OPT_PAPER)
        Cc = B.row_bound(r, base)['C']
        Cpr = float(r['Cpr'])
        fac = []
        for nm, o in SINGLE:
            opt = dict(base, **o)
            if wide and opt['rng'] == 'full':
                fac.append(float('nan')); continue
            fac.append(float(B.row_bound(r, opt)['C'].upper()) / float(Cc.mid()))
        # mono effect on top of the counting fix
        o1 = dict(base, count='fixed'); o2 = dict(o1, mono=True)
        mono = float(B.row_bound(r, o2)['C'].upper()) / float(B.row_bound(r, o1)['C'].upper())
        optc = dict(B.OPT_CORR_H) if wide else dict(B.OPT_CORR)     # wide rows: high-L evaluation (rigorous sup)
        pc = B.row_bound(r, optc)
        Ccorr = pc['C']
        pg = B.row_bound(r, dict(optc, gmin='3e12'))
        fa = float(Ccorr.upper()) / Cpr; fg = float(pg['C'].upper()) / Cpr
        lines.append(f"{r['L0']+'-'+r['L1']:>14} {r['a0']:>6} {Cpr:11.6g} {float(Cc.mid()):11.6g} " +
                     " ".join(f"{f:11.4f}" for f in fac) + f" {mono:6.4f} {fa:8.4f} {fg:9.4f}  {float(Ccorr.upper()):11.6g}")
        # hypotheses (rigorous, whole row) for the corrected computation
        if True:
            hyp = B.check_hypotheses(r, optc)
            bad = [h for h in hyp if not h[1] and not h[0].startswith('[paper only]') and not h[0].startswith('(4.9)')]
            mono_ok = [h for h in hyp if h[0].startswith('(4.9)')][0][1]
            paper_only = [h for h in hyp if h[0].startswith('[paper only]')][0][1]
            if bad:
                lines.append(f"{'':>14}   HYPOTHESIS FAILURES: {bad}")
        L0s = '28.7296' if r['L0'] == 'LOG3E12' else r['L0']
        notes = ("corrected Bellotti argument (REPORT.md sec.1-2): counting fix, d4 via RZA Cor1.2 only, |G(1/2+it)| bound fixed, "
                 "(v+w)^4 and Lemma 2.7 fixed, constants re-verified, sup over the whole row; gamma>0.447logT as in the paper; "
                 "N(s,T)=#{beta>=s,0<gamma<=T}")
        if r['L0'] == 'LOG3E12':
            notes += "; computed on [log(3e12),29]; N=0 for T<=3e12 (Platt-Trudgian)"
        if mono_ok is False:
            notes += "; x<Z/2 somewhere on the row: monotonicity factor K applied"
        if wide:
            notes = "opt=CORRH; " + notes + "; high-L evaluation (belarb.piece_hl), rigorous sup over the whole row"
        out_rows.append(dict(id=f"BELCORR{idx+1:02d}", logT0=L0s, logT1=r['L1'], alpha0=r['a0'],
                             C=ceil_sig(Ccorr.upper()), B=str(2 * Decimal(r['x'])), u=r['u'], x=r['x'], v=r['v'], w=r['w'],
                             zfr_input='+'.join(r['zfr']), status='refereed', notes=notes))
        print(lines[-1], flush=True)
    with open(os.path.join(HERE, 'rows_corrected_faithful.csv'), 'w', newline='') as f:
        wr = csv.DictWriter(f, fieldnames=['id', 'logT0', 'logT1', 'alpha0', 'C', 'B', 'u', 'x', 'v', 'w', 'zfr_input', 'status', 'notes'])
        wr.writeheader()
        for o in out_rows:
            wr.writerow(o)
    with open(os.path.join(HERE, 'corrected_factors.txt'), 'w') as f:
        f.write("Factors relative to her code (C_code); single corrections switched on one at a time on top of her code;\n"
                "'mono' = effect of the (4.9) monotonicity factor on top of the counting fix; ALL = all corrections (OPT_CORR) / C_printed;\n"
                "ALL+g3e12 = same with gamma > 3e12 instead of gamma > 0.447 log T in Lemma 3.4.\n\n")
        f.write("\n".join(lines) + "\n")

if __name__ == '__main__':
    main()
