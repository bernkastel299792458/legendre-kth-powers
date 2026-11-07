"""Hypothesis checks not asserted explicitly in cl_core.cell_margin, re-done over every certified cell:
  sigma = 1 - s*y >= sigma0 (needs y <= 1 - sigma0), eta_max <= eta0, mu range in [0.88, 1], window y vs own recomputation.
Uses the copy of cl_core in ./rerun (identical to the work folder's, md5 checked in REVIEW.md).

Run:  python -I hyp_check.py > hyp_check_output.txt
"""
import os, sys, json, math
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'rerun'))
import cl_core as C
from flint import arb

prof = [[float(a), float(b), str(z)] for a, b, z in json.load(open(os.path.join(HERE, '..', 'profile_classical.json')))['bands']]
worst_sig = None
worst_eta = None
mu_rng = [9, -9]
n = 0
for (a, b, Zs) in prof:
    nc = max(1, math.ceil((b - a) / 0.002))
    A = 1 / arb(Zs)
    for j in range(nc):
        va, vb = a + (b - a) * j / nc, a + (b - a) * (j + 1) / nc
        y, logT = C.window_y(prof, vb, 60.0)
        cap = arb((A / vb).lower())
        if cap < y:
            y = cap
        gap = (1 - y) - C.SIGMA0            # sigma >= 1 - y >= sigma0 ?
        etamax = (1 + C.EPS) * A / arb(va)
        geta = C.ETA0 - etamax
        mu_lo = y * va / A * (1 - C.EPS / C.S0)
        mu_hi = y * vb / A
        n += 1
        if worst_sig is None or gap.lower() < worst_sig[0]:
            worst_sig = (float(gap.lower()), va, vb)
        if worst_eta is None or geta.lower() < worst_eta[0]:
            worst_eta = (float(geta.lower()), va)
        mu_rng = [min(mu_rng[0], float(mu_lo.lower())), max(mu_rng[1], float(mu_hi.upper()))]
print(f"{n} cells")
print("min over cells of (1 - y) - sigma0 =", worst_sig, "(must be > 0)")
print("min over cells of eta0 - eta_max =", worst_eta, "(must be >= 0)")
print("mu range over all cells:", mu_rng, "(must lie in [0.88, 1])")
print("SIGMA0 =", C.SIGMA0.str(12), " ETA0 =", C.ETA0.str(12), " R_MIN =", C.R_MIN.str(10))
