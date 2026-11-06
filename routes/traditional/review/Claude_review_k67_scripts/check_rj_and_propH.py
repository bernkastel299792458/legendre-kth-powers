"""(1) Exact R_j versus the project's certified upper bounds R~_j (proof/code/rigorous_smooth.py).
(2) Prop. H spot checks: pointwise delta_H at both ends and the midpoint of selected certificate
    pieces (the 6 worst pieces + 2 others), using each piece's own c and sigma*.
Reproduces report Appendix A.1 and the R_j numbers in §3.6.
Run:  python -B check_rj_and_propH.py     (about 1 minute)"""
import sys
sys.dont_write_bytecode = True                     # do not write __pycache__ anywhere (proof/ stays read-only)
import csv
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]                             # legendre_k67/
sys.path.insert(0, str(HERE))
from indep_check import mp, mpf, Rj, deltaH

# (1) R_j: exact vs project code
sys.path.insert(1, str(ROOT / 'proof' / 'code'))
import rigorous_smooth as RS                       # needs python-flint 0.9.0
for M in (2, 3):
    R, ratio = Rj(M)
    Rup, rmax = RS.weight_constants(M)
    print(f'M={M}: exact R_j =', [mp.nstr(x, 10) for x in R], ' ratio =', mp.nstr(ratio, 10))
    print(f'      code R~_j  =', [str(x)[:14] for x in Rup], ' ratio =', str(rmax)[:20])
    assert all(float(u) >= float(r) for u, r in zip(Rup, R)), 'R~_j must be >= R_j'

# (2) Prop. H spot checks
cert = list(csv.DictReader(open(ROOT / 'proof' / 'certificates' / 'cert_hyb_jy_k67_lw.csv')))
segs = sorted(cert, key=lambda r: -float(r['delta_upper']))[:6] + [cert[0], cert[len(cert) // 2]]
bad = 0
for r in segs:
    a, b, c, s = Fr(r['a']), Fr(r['b']), Fr(r['c']), Fr(r['sigma_star'])
    mu = mpf(c.numerator) / c.denominator / 67
    vals = []
    for Lq in (a, (a + b) / 2, b):
        L = mpf(Lq.numerator) / Lq.denominator
        d, _ = deltaH(L, mu, mpf(s.numerator) / s.denominator, 'lw', eta_at=mu * mpf(b.numerator) / b.denominator)
        vals.append(d)
    ok = max(vals) <= mpf(r['delta_upper']) * (1 + mpf('1e-5'))   # certificate prints 6 significant digits
    bad += not ok
    print(f"H piece [{float(a):.4f},{float(b):.4f}] c={float(c):.9f} s*={float(s)} cert={r['delta_upper']} "
          f"pointwise(a,mid,b)={[mp.nstr(v, 8) for v in vals]} {'OK' if ok else '**EXCEEDS**'}")
print('Prop. H spot checks:', 'all pointwise values <= certificate' if bad == 0 else f'{bad} pieces exceed')
