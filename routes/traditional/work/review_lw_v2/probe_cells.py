"""Probe zl_core.cell_terms ball widths at large heights (exploration, floats for display only)."""
import os, sys
SRC = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'phase1_littlewood'))
sys.path.insert(0, SRC)
from zl_core import *
import cert_profile as CP

CP.GT.check_increasing()
for (va, w, n, Z) in [(1000000.0, 9.88, 13, '12.202'), (1100000.0, 1.36, 13, '12.129'), (1100000.0, 0.68, 13, '12.129'),
                      (1100000.0, 10.89, 13, '12.129'), (1100000.0, 21.78, 13, '12.129'), (2400000.0, 1.48, 13, '11.937'),
                      (2400000.0, 0.74, 13, '11.937')]:
    r = cell_terms(arb(va), arb(va + w), arb(Z), arb(Z), n, detail=True)
    if r is None:
        print(va, w, n, 'None'); continue
    mu, PE, dd = r
    G = CP.GT.lower(mu)
    print(va, w, n, 'mu', mu.str(8), 'PE', PE.str(10), 'G', G.str(10), 'marg', (G - PE).str(5))
    for k in ('B', 'lam', 'y', 'eta', 'zero_err', 'Esum', 'loss351', 'nu', 'Cm1', 'J'):
        print('    ', k, dd[k].str(8))
