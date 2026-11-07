"""Exploration (not a certificate): local requirement Z(v) with Zw = Z, lines n = 3, 4."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl_core import *
import time
t0=time.time()
Gc = {}
def G(mu):
    key = round(float(mu.mid()), 4)
    if key not in Gc: Gc[key] = G_of_mu(arb(key) - arb('0.00005'))
    return Gc[key]
print("w0 =", W0, " kappa =", KAPPA_Q, " a =", A_SUM)
print("G(0.9645) =", G_of_mu(arb('0.96454')))
for v in [32, 35, 40, 45, 50, 56, 60, 65, 70, 75, 80, 90, 95.5, 100, 110, 120, 129, 140, 160, 190, 216, 230, 240]:
    out = []
    for n in (3, 4):
        lo, hi = 17.0, 23.0
        for it in range(30):
            Z = (lo + hi) / 2
            r = cell_terms(arb(v), arb(v) + arb('1e-6'), arb(Z), arb(Z), n)
            if r is None: lo = hi = float('nan'); break
            mu, PE = r
            if PE.upper() < G(mu).lower(): hi = Z
            else: lo = Z
        out.append(hi)
    r = cell_terms(arb(v), arb(v)+arb('1e-6'), arb(out[0]), arb(out[0]), 3, detail=True)
    d = r[2]
    print(f"v={v:6.1f}  Z(n=3)={out[0]:.4f}  Z(n=4)={out[1]:.4f}   lam={float(d['lam'].mid()):.4f} B*l={float((d['B']*ell(arb(v))).mid()):.4f} "
          f"zero/eta={float((d['zero_err']/d['eta']).mid()):.3f} E/eta={float((d['Esum']/d['eta']).mid()):.4f} mu={float(r[0].mid()):.5f}", flush=True)
print("time", time.time()-t0)
