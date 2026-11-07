"""
repair_margins.py -- robustness of Theorem R (informational, not part of the proof).

b4 = F(0+) = Tail0 + Bulk0 does not involve the eps-dependent terms T3..T6 at all; they only have to
keep F(eps) <= F(0+) for eps > 0.  For each T_i (and jointly) we compute, from point values of F on a
dense grid, the largest factor kappa_i such that F(eps) + (kappa_i - 1) T_i(eps) <= F(0+) for all grid
eps, i.e. how much T_i could be under-estimated before the supremum would move away from eps -> 0+.
(The certified b4 itself comes from the rigorous cell cover in repair_bound.py.)
Run (either variant): python -I repair_margins.py
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.dirname(HERE))
from repair_bound import certify
from rza_common import arb

if __name__ == "__main__":
    r = certify(verbose=False)
    F, F0 = r["F"], r["Tail0"] + r["Bulk0"]
    e0 = arb(r["rows"][-1][1])
    grid = [e0 * arb(2) ** (-k) for k in range(40, 0, -1)] + [e0 * i / 2000 for i in range(1, 2001)]
    names = {3: "T3 (ax1 term)", 4: "T4 (cross, sqrt part)", 5: "T5 (cross, log part)", 6: "T6 (square)"}
    kap = {i: (1e9, None) for i in list(names) + ["all"]}
    for e in grid:
        v, t = F(e, e)
        slack = F0 - v
        for i in names:
            Ti = t[i - 1]
            if bool(Ti > 0):
                k = float(((slack + Ti) / Ti).lower())
                if k < kap[i][0]:
                    kap[i] = (k, float(e.mid()))
        Ts = t[2] + t[3] + t[4] + t[5]
        k = float(((slack + Ts) / Ts).lower())
        if k < kap["all"][0]:
            kap["all"] = (k, float(e.mid()))
    vlast, tl = F(e0, e0)
    print("variant=%s  F(0+)=%s  F(eps0)=%s  margin at eps0=%s" % (r["variant"], F0.str(8), vlast.str(6), (F0 - vlast).str(4)))
    print("  terms at eps0: T1..T7 = " + ", ".join(x.str(4, radius=False) for x in tl))
    for i in list(names) + ["all"]:
        print("  %-24s kappa = %.3f (binding at eps = %.3g)" % (names.get(i, "T3..T6 jointly"), kap[i][0], kap[i][1]))
