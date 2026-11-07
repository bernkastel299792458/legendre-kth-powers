"""Task 2 validation: her code in Arb (all corrections OFF, her Table 4 parameters) vs her printed Table 2 (and 3,5,6).
Also cross-checks: (i) generic row_bound(OPT_PAPER) == faithful(); (ii) float model work/ref/belmodel.py.
Run:  python reproduce_table2.py      (about 1-2 min; the first call per alpha0 computes rigorous Gamma integrals)
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb
import belarb as B
from beltables import rows

def rel(a, b): return abs(a / b - 1)

def main():
    worst = 0.0; worst_row = None
    lines = []
    lines.append(f"{'row':>16} {'C_arb(her code)':>16} {'C_printed':>12} {'rel':>9} {'B':>7} {'Bpr':>7} | {'b1':>6} {'b2':>6} {'d4':>8} {'d5':>6} {'c1':>6} {'c2':>9} {'c3':>10} {'c4':>9} {'c5':>6}")
    for r in rows(include_kv=True):
        p = B.faithful(r)
        C = float(p['C'].mid()); rad = float(p['C'].rad())
        Cpr = float(r['Cpr'])
        e = rel(C, Cpr)
        Bv = 2 * float(r['x'])
        # printed precision: 2 decimals for C < 1e6, 3 significant digits otherwise
        tol = 0.005 / Cpr if Cpr < 1e6 else 0.005 * 10 ** math.floor(math.log10(Cpr)) / Cpr * 1.0
        tag = '' if e <= tol + 1e-12 else ('  <-- differs' )
        if e > worst:
            worst, worst_row = e, r['L0'] + '-' + r['L1']
        A = p['A']; d4 = float(p['d4'].mid()); d5 = float(p['d5'].mid())
        g = float(B.consts(r['a0'], r['L0'])['paper_G1'].mid())
        c2 = d5 / float(r['w']) * g * d4
        # c3, c4 as in her code
        nuT1 = float(B.nu(r['zfr'], arb(r['L1']), B.ARB).mid())
        c3 = 2 * c2 * math.log(1 / nuT1) * 1.12
        IS = float(B.consts(r['a0'], r['L0'])['IS'].mid())
        c4 = 2 * d5 / float(r['w']) * IS * d4 * 2.4
        lines.append(f"{r['L0']+'-'+r['L1']:>16} {C:16.4f} {Cpr:12.6g} {e:9.2e} {Bv:7.3f} {r['Bpr']:>7} | "
                     f"{float(p['b1'].mid()):6.3f} {float(p['b2'].mid()):6.3f} {d4:8.3f} {d5:6.3f} {float(p['c1'].mid()):6.3f} "
                     f"{c2:9.3f} {c3:10.3f} {c4:9.3f} {float(p['c5'].mid()):6.3f}{tag}  (ball rad {rad:.1e})")
        # consistency with the generic implementation
        q = B.row_bound(r, B.OPT_PAPER, B.ARB)
        assert abs(float(q['C'].mid()) - C) <= 1e-9 * C, (r['L0'], float(q['C'].mid()), C)
        if r['tab'] is not None:
            t = r['tab']
            for key, val in (('d4', d4), ('d5', d5), ('c1', float(p['c1'].mid())), ('c5', float(p['c5'].mid())),
                             ('b1', float(p['b1'].mid())), ('b2', float(p['b2'].mid())), ('c2', c2), ('c3', c3), ('c4', c4)):
                if abs(val - t[key]) > 0.0015 + 1e-6 * abs(t[key]) and rel(val, t[key]) > 2e-5:
                    lines.append(f"{'':>16}   table-{key} mismatch: computed {val:.4f} vs printed {t[key]}")
    print("\n".join(lines))
    print(f"\nmax relative discrepancy C_arb(her code) vs printed Table 2: {worst:.3e} (row {worst_row})")
    # float cross-check
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ref'))
    import belmodel
    print("\nbelmodel (float) cross-check on its 9 rows:")
    for R in belmodel.rows:
        o = belmodel.model(*R[:7])
        L0 = 'LOG3E12' if abs(R[0] - math.log(3e12)) < 1e-9 else ('%g' % R[0])
        rr = [r for r in rows() if r['L0'] == L0][0]
        Ca = float(B.faithful(rr)['C'].mid())
        print(f"  {L0:>8}: belmodel {o['C']:12.2f}   arb {Ca:12.2f}   rel {rel(o['C'], Ca):.2e}")

if __name__ == '__main__':
    main()
