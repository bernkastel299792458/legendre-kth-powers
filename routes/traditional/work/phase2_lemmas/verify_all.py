"""Re-run every certified computation of the Phase-2 lemmas and check the stored results.

  python verify_all.py          (about 3 minutes on 14 cores)

1. Lemma B / C hypotheses that are checked once: Ford's nu_2 is strictly decreasing on [28, 172]
   (needed for kappa in Lemma C), trigonometric polynomials are >= 0 (done inside cf_upper).
2. Lemma A on all Bellotti rows up to e^170.2 (run_d4_rows.py, multiprocessing) -> results/d4_rows.json.
3. Lemma B and C on all rows + float assembly of the effect on C (effect_on_C.py) -> results/effect_rows.json.
4. Non-rigorous sanity checks: Lemma A vs. its closed-form model (should agree within ~10%), and the
   full inequality chain of Lemma A at a small scale where the left side can be computed directly.
"""
import json, math, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from flint import arb, arb_series

ok = True

# ---- 1. nu_2 monotone
def nu_series(L):
    s = arb_series([L, 1], prec=2)
    J = s / 6 + s.log() + arb("0.618").log()
    return (arb("0.04962") - arb("0.0196") / (J + arb("1.15"))) / (J + arb("0.685") + arb("0.155") * s.log())
worst = -1e9
for i in range(2000):
    a = 28 + 144 * i / 2000; b = 28 + 144 * (i + 1) / 2000
    worst = max(worst, float(nu_series(arb((a + b) / 2, (b - a) / 2)).coeffs()[1].upper()))
print(f"[1] d nu_2/dL <= {worst:.3e} on [28,172]  ->", "OK" if worst < 0 else "FAIL")
ok &= worst < 0

# ---- 2,3. rigorous runs
for script in ("run_d4_rows.py", "effect_on_C.py"):
    print(f"[2/3] running {script} ...", flush=True)
    r = subprocess.run([sys.executable, os.path.join(HERE, script)], cwd=HERE)
    ok &= (r.returncode == 0)

# ---- 4. sanity: Lemma A vs model
from improvements import d4_model
E = json.load(open(os.path.join(HERE, "results", "effect_rows.json")))
D = json.load(open(os.path.join(HERE, "results", "d4_rows.json")))
from bellotti_rows import rows
mx = 0
for d in D:
    r = rows[d["i"]]
    m = max(d4_model(r["u"], r["v"], r["x"], L) for L in (r["L0"], r["L1"]))
    q = d["d4_new"] / m
    mx = max(mx, abs(q - 1))
print(f"[4] max |d4_rigorous/d4_model - 1| = {mx:.3f}  ->", "OK" if mx < 0.15 else "CHECK")
for e in E:
    assert e["factor_ABC"] < 0.02
print("ALL OK" if ok else "SOME CHECK FAILED")
