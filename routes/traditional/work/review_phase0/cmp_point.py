import sys, csv
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); sys.path.insert(1, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase0_bellotti'))
import belarb as B
import indep_C as I
from flint import arb
recs = {r['id']: r for r in csv.DictReader(open(sys.argv[1]))}
I.DECOUPLED = (len(sys.argv) > 4 and sys.argv[4] == 'decoupled')
for rid in sys.argv[2].split(','):
    rec = recs[rid]; row = I.parse(rec)
    L = arb(sys.argv[3]) if sys.argv[3] != 'top' else arb(rec['logT1'])
    mine = I.C_point(row, L)
    brow = dict(L0=('LOG3E12' if float(rec['logT0']) < 28.73 else rec['logT0']), L1=rec['logT1'], a0=rec['alpha0'], u=rec['u'], x=rec['x'],
                v=rec['v'], w=rec['w'], lam=row['lam'], zfr=row['zfr'])
    theirs = B.piece(brow, B.OPT_IMPR, L, B.ARB, B.consts_N(brow, B.ARB))
    print(rid, 'L=', L)
    for k in ('Hn', 'K', 'J1', 'A', 'c1', 'c5', 'C'):
        a = mine[k]; b = theirs[k]
        fa = float(arb(a).mid()) if not isinstance(a, int) else a
        fb = float(arb(b).mid()) if not isinstance(b, int) else b
        print(f"   {k:4s} mine={fa:.9g}  phase0={fb:.9g}  ratio={fa/fb:.7f}")
    print(f"   nbar mine={float(mine['nbar'].mid()):.7g}  phase0 b1+b2Z={float((theirs['b1']+theirs['b2']*theirs['Z']).mid()):.7g}")
    print(f"   d4 {float(mine['d4'].mid()):.9g} {float(theirs['d4'].mid()):.9g}; d5 {float(mine['d5'].mid()):.9g} {float(theirs['d5'].mid()):.9g}")
