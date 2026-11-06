"""Main-thread follow-up to priority_z2.py: per-height Littlewood profiles built from the FULL grid of local
constants 1/A(t) in ../thesis_19.62/check_corrected_constant_output.txt (not only the 7 summary samples).

Between log t = 60 and 95.5 the thesis-lambda* local constant rises concavely (60: 19.415, 65: 19.644,
70: 19.807, 76.5: 19.947, 80: 19.997), so the linear interpolation used by PROF_lamstar_interp is optimistic.
Here each grid cell [v_i, v_{i+1}) gets max(value at v_i, value at v_{i+1}) + MARGIN (MARGIN covers variation
between grid points).  These local constants are a sensitivity guide, NOT a theorem (the thesis's induction uses
one A for all t >= H1); a "closes" result says only what a height-dependent version of the thesis would need.

Variants *_noLW: no Littlewood region below log t = 56.5 (Z2 = 1000 there), so heights [55, 56.5] rest on BTY's
4.896 alone and not on the thesis's unaudited Lemma 2.1 (finding F2).

Usage: python -I priority_grid.py [names...]     results -> out/priority_grid.json, covers -> out/cover_<name>.csv
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import json
import zfr_model as ZM
import priority_z2 as PZ

GRID = [56.5, 60.0, 65.0, 70.0, 76.5, 80.0, 90.0, 95.5, 100.0, 110.0, 120.0, 129.0, 140.0, 150.0, 160.0,
        170.0, 190.0, 216.0, 225.4]
LAMSTAR = [19.232, 19.415, 19.644, 19.807, 19.947, 19.997, 20.071, 20.079, 20.074, 20.035, 19.968, 19.894,
           19.792, 19.694, 19.593, 19.491, 19.290, 19.038, 19.088]
OPT = [19.232, 19.262, 19.304, 19.348, 19.407, 19.440, 19.533, 19.586, 19.629, 19.724, 19.819, 19.892,
       19.723, 19.583, 19.461, 19.357, 19.186, 19.023, 19.088]
TAIL = 19.09          # log t >= 225.4: the thesis output gives <= 19.088 and decreasing
MARGIN = 0.01


def profile(vals, below="19.62"):
    pr = [(0, below)]
    for i in range(len(GRID) - 1):
        pr.append((GRID[i], f"{max(vals[i], vals[i + 1]) + MARGIN:.3f}"))
    pr.append((GRID[-1], f"{max(vals[-1], TAIL) + MARGIN:.3f}"))
    return tuple(pr)


MODELS = {
    'GRID_lamstar': ZM.ZModel(z2prof=profile(LAMSTAR)),
    'GRID_opt': ZM.ZModel(z2prof=profile(OPT)),
    'GRID_lamstar_noLW': ZM.ZModel(z2prof=profile(LAMSTAR, below="1000")),
    'GRID_opt_noLW': ZM.ZModel(z2prof=profile(OPT, below="1000")),
}

if __name__ == '__main__':
    names = sys.argv[1:] or list(MODELS)
    jfn = os.path.join(ZM.HERE, 'out', 'priority_grid.json')
    allres = json.load(open(jfn)) if os.path.exists(jfn) else {}
    for n in names:
        res = PZ.test(n, MODELS[n])
        print(json.dumps(res), flush=True)
        allres[n] = res
        json.dump(allres, open(jfn, 'w'), indent=1)
