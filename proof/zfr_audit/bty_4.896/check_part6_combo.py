"""Indicative: best classical constant from BTY's final step (corrected constants) when the iteration must run up
to the crossover with a weaker uniform Littlewood constant Z2, i.e. to log t = exp(Z2/Z1).  Same caveat as
check_part5 (eta0, sigma0 depend on A0 and are not recomputed).  Targets: the largest Z1 that closes k = 67 with uniform Z2 (19.90: 4.835; 20.08: 4.825; ../requirement/out/priority_combo.json) and the first failing value. Used by ../requirement/REPORT.md §4b.
Usage: python -I check_part6_combo.py"""
import contextlib, io, os
here = os.path.dirname(os.path.abspath(__file__))
import sys
sys.path.insert(0, here)
fn = os.path.join(here, 'check_part5_lemma15_final.py')
ns = {'__name__': 'part5', '__file__': fn}
with contextlib.redirect_stdout(io.StringIO()):
    try:
        exec(compile(open(fn, encoding='utf-8').read(), fn, 'exec'), ns)
    except SystemExit:      # part 5 ends with sys.exit(summary())
        pass
D, best_A0 = ns['D'], ns['best_A0']
for z2, z1 in [("19.90", "4.835"), ("19.90", "4.84"), ("20.08", "4.825"), ("20.08", "4.83")]:
    Ltop = (D(z2) / D(z1)).exp()
    bd, bc = best_A0(Ltop, False), best_A0(Ltop, True)
    print(f"Z2 = {z2}, target Z1 = {z1}: crossover log t = {float(Ltop):.4f}; best 1/A0 there: "
          f"decoupled {float(1 / bd):.5f}, coupled {float(1 / bc):.5f}  -> target reachable (coupled): "
          f"{float(1 / bc) <= float(z1)}")
