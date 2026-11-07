# -*- coding: utf-8 -*-
"""
Recompute frak F_1(T0'', c, sigma, a, b) of Theorem 2 for every row of Table 3
(tab:ProofCorMain4thPM) of arXiv:2507.15184v2, and C_1(3e3) of the proof of
Corollary 2.  Compare with frak M_1(T0) of Table 2 and with 20.7225.
Run:  python -I f1_table.py  > f1_table_out.txt
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cs4_formulas import *

# Table 3 (l.397-405): T0'': c, sigma=(s1,(s2,s3),(s4,s5)), a, b
ROWS = {
    4:  (("-0.879", "0.1809"), ("0.3545", "0.7898", "0.4008", "0.5456", "0.3933"), ("0.339", "1.7553"), ("1.7215", "1.303")),
    5:  (("-0.938", "0.194"), ("0.368", "0.718", "0.435", "0.629", "0.3654"), ("1.99", "1.44"), ("1.33", "1.45")),
    6:  (("-0.9295", "0.1721"), ("0.4077", "0.6957", "0.3413", "0.5672", "0.4288"), ("1.6769", "1.5632"), ("1.6891", "1.6748")),
    7:  (("-0.9273", "0.2061"), ("0.4104", "0.6263", "0.3536", "0.5743", "0.41"), ("1.8473", "1.8288"), ("1.649", "1.9094")),
    8:  (("-0.9266", "0.1637"), ("0.3561", "0.7103", "0.3381", "0.5645", "0.4285"), ("0.6164", "1.9123"), ("1.0018", "1.9929")),
    9:  (("-0.834", "0.22985"), ("0.3964", "0.9479", "0.3927", "0.5846", "0.4235"), ("1.3609", "1.1367"), ("0.7112", "1.8455")),
    10: (("-0.8303", "0.1676"), ("0.3985", "0.668", "0.4088", "0.551", "0.386"), ("1.4356", "1.28"), ("1.5563", "1.6332")),
    15: (("-0.813", "0.221"), ("0.3464", "0.8268", "0.4263", "0.5698", "0.3511"), ("1.0851", "1.0245"), ("0.8137", "1.8276")),
    20: (("-0.875", "0.1936"), ("0.3785", "0.8615", "0.45", "0.619", "0.393"), ("0.1917", "1.525"), ("1.1358", "1.717")),
}
# Table 2 (l.184-192) frak M_1
M1_PAPER = {4: "59.300", 5: "48.801", 6: "43.230", 7: "39.720", 8: "37.550", 9: "36.211", 10: "34.842",
            15: "31.170", 20: "29.364"}


def run_row(T0, c, s, a, b, label):
    c1, c2 = Q(c[0]), Q(c[1])
    s1, s2, s3, s4, s5 = [Q(x) for x in s]
    a1, a2 = Q(a[0]), Q(a[1])
    b1, b2 = Q(b[0]), Q(b[1])
    conds = check_conditions(T0, c1, c2, s1, s2, s3, s4, s5, a1, a2, b1, b2)
    t = time.time()
    d = all_J(T0, c1, c2, s1, s2, s3, s4, s5, a1, a2, b1, b2)
    dt = time.time() - t
    print("=" * 78)
    print(label, " (%.1fs)" % dt)
    bad = [n for n, ok in conds if not ok]
    print("  conditions all satisfied:", not bad, ("  FAILED: %s" % bad) if bad else "")
    for k in ("J0", "J1", "J21", "G1", "G2", "G3", "G4", "G5", "G6", "J22", "J3", "J4", "J5", "J6", "mixed", "F1", "F2"):
        print("  %-6s = %s" % (k, d[k].str(12, radius=True)))
    return d


if __name__ == "__main__":
    import cs4_formulas as CF
    mode = sys.argv[1] if len(sys.argv) > 1 else "paper"
    CF.set_mode(mode == "corr")
    print("MODE =", mode, "(paper = constants exactly as printed; corr = exact D_k balls + CHT21 term 0.73x^{1/2}"
          " propagated into D4,D5,D6,D7; D6 constant =", CF.D6_CONST.str(10), ")")
    print("python-flint prec =", ctx.prec, " m0 =", M0.str(15))
    summary = []
    for n in sorted(ROWS):
        T0 = arb(10) ** n
        c, s, a, b = ROWS[n]
        d = run_row(T0, c, s, a, b, "T0'' = 1e%d" % n)
        m1 = Q(M1_PAPER[n])
        ok = d["F1"] < m1
        summary.append((n, d["F1"], m1, ok))
        print("  frak M1 (paper) = %s ;  F1 <= M1 rigorously: %s" % (M1_PAPER[n], ok))
    # C_1(3e3): parameters from l.372 (sigma not needed for F2/C1)
    print("=" * 78)
    T0p = arb(3000)
    c1, c2 = Q("-0.923364"), Q("0.161176")
    a1, a2 = Q("0.531241"), Q("1.52906")
    b1, b2 = Q("0.754804"), Q("1.68921")
    # dummy sigma (only enters F1, not F2 / C1); choose admissible values
    s1, s2, s3, s4, s5 = Q("0.4"), Q("0.7"), Q("0.4"), Q("0.55"), Q("0.4")
    conds = check_conditions(T0p, c1, c2, s1, s2, s3, s4, s5, a1, a2, b1, b2)
    bad = [nm for nm, ok in conds if not ok]
    print("T0' = 3e3 (C_1):  conditions (5),(6) etc. satisfied:", not bad, bad)
    d = {}
    d["J0"] = J0f(T0p, c1, c2, a1, a2, b1, b2)
    d["J1"] = J1(T0p)
    d["J3"] = (eta(T0p) + 2 * PI * M0) * D7(T0p)
    d["J4"] = eta(T0p) * D4(T0p, arb(-1)) + 2 * PI * M0 * D4(T0p, arb(-2))
    d["J5"] = g1f(T0p, Q("0.5"), c1, a1, a2)
    d["J6"] = g2f(T0p, Q("0.5"), c2, b1, b2)
    sq = d["J3"].sqrt() + d["J4"].sqrt() + d["J5"].sqrt() + d["J6"].sqrt()
    d["mixed"] = sq ** 2
    d["F2"] = d["J0"] + 2 * d["J1"] + d["mixed"]
    for k in ("J0", "J1", "J3", "J4", "J5", "J6", "F2"):
        print("  %-6s = %s" % (k, d[k].str(12, radius=True)))
    C1 = C1f(T0p, d)
    print("  C_1(3e3) = %s   (paper: 20.7225)   C1 <= 20.7225: %s" % (C1.str(12, radius=True), C1 < Q("20.7225")))
    print("=" * 78)
    print("SUMMARY  n | F1(1e^n) recomputed (upper end of ball) | frak M1 paper | F1 < M1")
    for n, f1, m1, ok in summary:
        print("  %2d | %s | %s | %s" % (n, (f1.mid() + f1.rad()).str(10), m1.str(8), ok))
