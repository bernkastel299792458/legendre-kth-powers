"""Main-thread follow-up: can a sharper classical constant compensate for a weaker uniform Littlewood constant?
BTY's method with corrected constants gives, indicatively (not proved), 1/A ~ 4.85 (decoupled) / 4.81 (coupled) when
run to log t = 55, and ~ 4.89 / 4.86 when run to 76.47 (../bty_4.896/REPORT.md §4).  With Z2 = 19.90 or 20.08 the
classical/Littlewood crossover exp(Z2/Z1) moves to log t ~ 60-63, between those two cases.

Usage: python -I priority_combo.py     results -> out/priority_combo.json
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import json
import zfr_model as ZM
import priority_z2 as PZ

MODELS = {f'Z1_{z1}_Z2_{z2}': ZM.ZModel(Z1=z1, Z2=z2)
          for z2 in ("19.90", "20.08") for z1 in ("4.87", "4.85", "4.83", "4.81")}
# refinement of the two thresholds
MODELS.update({f'Z1_{z1}_Z2_19.90': ZM.ZModel(Z1=z1, Z2="19.90") for z1 in ("4.835", "4.84", "4.845")})
MODELS.update({f'Z1_{z1}_Z2_20.08': ZM.ZModel(Z1=z1, Z2="20.08") for z1 in ("4.815", "4.82", "4.825")})

if __name__ == '__main__':
    names = sys.argv[1:] or list(MODELS)
    jfn = os.path.join(ZM.HERE, 'out', 'priority_combo.json')
    allres = json.load(open(jfn)) if os.path.exists(jfn) else {}
    for n in names:
        res = PZ.test(n, MODELS[n])
        print(json.dumps(res), flush=True)
        allres[n] = res
        json.dump(allres, open(jfn, 'w'), indent=1)
