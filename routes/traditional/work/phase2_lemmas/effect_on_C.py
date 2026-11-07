"""Effect of Lemmas A, B, C on Bellotti's constant C, row by row, with HER parameters (u, v, x, w).

The lemma outputs (d4_new, cf_new, f2, f34) are rigorous Arb upper bounds; the assembly of C below
is a FLOAT model of Bellotti's formula
    C = (c2 + c3 + c4) * (b1 + b2/(nu(T0) log T0)) / (c1^2 - c5)
using her Table 6 values of c1..c5 (so it is an *effect estimate*, not a certified C).
Scalings:  Lemma A: c2,c3,c4,c5 *= d4_new/d4_old;  Lemma B: (b1 + b2 Z) -> cf_new;
           Lemma C: c2 *= f2, c3,c4 *= f34.
Usage: python effect_on_C.py   (needs results/d4_rows.json from run_d4_rows.py)"""
import json, math, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from flint import arb
from bellotti_rows import rows
from lemmaB_count import cf_upper, nu_of, f_up, f_down
from lemmaC_residue import residue_factors

d4res = {round(d["L0"], 6): d for d in json.load(open(os.path.join(HERE, "results", "d4_rows.json")))}
out = []
print(f"{'row':>16} {'C_tab':>10} {'A:d4':>7} {'B:cf':>7} {'C:res':>7} {'A':>6} {'B':>6} {'C':>6} {'A+B+C':>7} {'C_new':>9}")
for r in rows:
    if r["L1"] > 170.3:
        break
    L0, L1 = r["L0"], r["L1"]
    nm = "classical" if L1 <= 46.2 + 1e-9 else "ford"
    d = d4res[round(L0, 6)]
    s = d["d4_new"] / r["d4"]
    cf_new, det = cf_upper(r["alpha0"], nm, L0, L1)
    cf_new = f_up(cf_new)
    Z0 = 1 / f_down(nu_of(nm, arb(L0)) * arb(L0))
    cf_old = r["b1"] + r["b2"] * Z0
    f2, f34, kap = residue_factors(r["u"], r["x"], r["alpha0"], nm, L0, L1)
    f2 = f_up(f2); f34 = f_up(f34)
    c1, c2, c3, c4, c5 = r["c1"], r["c2"], r["c3"], r["c4"], r["c5"]
    def C(sA=1.0, cf=cf_old, g2=1.0, g34=1.0):
        return sA * (g2 * c2 + g34 * (c3 + c4)) * cf / (c1 * c1 - sA * c5)
    C0 = C()
    fa = C(sA=s) / C0; fb = C(cf=cf_new) / C0; fc = C(g2=f2, g34=f34) / C0
    fall = C(sA=s, cf=cf_new, g2=f2, g34=f34) / C0
    out.append(dict(L0=L0, L1=L1, C_table=r["C"], C_model=C0, d4_old=r["d4"], d4_new=d["d4_new"],
                    cf_old=cf_old, cf_new=cf_new, trig=dict(a0=str(det["a0"]), ak={k: str(v) for k, v in det["ak"].items()}, rho=str(det["rho"])),
                    f2=f2, f34=f34, kappa=f_up(kap), factor_A=fa, factor_B=fb, factor_C=fc, factor_ABC=fall,
                    C_new_estimate=r["C"] * fall))
    print(f"[{L0:6.2f},{L1:6.1f}] {r['C']:10.0f} {d['d4_new']:7.3f} {cf_new:7.3f} {f34:7.4f} {fa:6.4f} {fb:6.4f} {fc:6.4f} {fall:7.4f} {r['C']*fall:9.0f}")
json.dump(out, open(os.path.join(HERE, "results", "effect_rows.json"), "w"), indent=1)
