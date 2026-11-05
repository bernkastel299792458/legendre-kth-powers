"""Band-localised requirement for the Littlewood constant (the form that matches a per-height
"local constant" profile): Z2 = z on the band (v_lo, v_hi] only, Z2 = 19.62 elsewhere, Z1 = 4.896,
Z3 = 54.004.  Bisect for the largest z with which repair() still closes the whole chain [L1, 1e8].
(The classical branch 1/(4.896 v) stays valid on the band, so it caps the damage near v ~ 55-60.)

Usage: python -I bands_z2.py [STEPS] [i:j]       (writes out/bands_z2.json, out/bands_z2.csv)"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
import json
import time
from fractions import Fraction
import zfr_model as ZM
import common as C
import repair as RP

RP.S_MAX_L = Fraction(12000)   # search restriction for speed: Prop. S is not tried at L >= 12000

EDGES = [Fraction(55), Fraction(58), Fraction(61), Fraction(64), Fraction(67), Fraction(70), Fraction(75),
         Fraction(80), Fraction(85), Fraction(90), Fraction(100), Fraction(110), Fraction(130), Fraction(170),
         Fraction(300), Fraction(1000), Fraction(10000), Fraction(100000), Fraction(677676)]

if __name__ == '__main__':
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    only = sys.argv[2] if len(sys.argv) > 2 else None
    bands = list(zip(EDGES[:-1], EDGES[1:]))
    idx = range(len(bands))
    if only:
        i0, i1 = (int(x) for x in only.split(':'))
        idx = range(i0, min(i1, len(bands)))
    jfn = os.path.join(ZM.HERE, 'out', 'bands_z2.json')
    old = json.load(open(jfn)) if os.path.exists(jfn) else {}
    for i in idx:
        vlo, vhi = bands[i]
        fam = f"z2band:{vlo}:{vhi}"
        t = time.time()
        cache = {}

        def closes(x):
            x = float(f"{x:.4f}")
            if x not in cache:
                cache[x] = RP.repair(C.family_model(fam, f"{x:.4f}"))
            return cache[x]['closes']

        if closes(30.0):
            z_ok, z_fail, where, status = 30.0, None, [], 'closes_at_30'
        else:
            g, b = (21.0, 30.0) if closes(21.0) else (19.62, 21.0)
            for _ in range(steps):
                m = float(f"{(g + b) / 2:.4f}")
                if m in (g, b):
                    break
                if closes(m):
                    g = m
                else:
                    b = m
            z_ok, z_fail, status = g, b, 'thr'
            rb = cache[float(f"{b:.4f}")]
            where = [(float(x), float(y)) for x, y in (rb['holes'] or rb['bad_ranges'])]
        row = dict(i=i, v_lo=float(vlo), v_hi=float(vhi), z2_ok=z_ok, z2_fail=z_fail, status=status,
                   binding_L=where[:3], seconds=round(time.time() - t))
        print(json.dumps(row), flush=True)
        old[str(i)] = row
        json.dump(old, open(jfn, 'w'), indent=1)
    allrows = [old[k] for k in sorted(old, key=int)]
    with open(os.path.join(ZM.HERE, 'out', 'bands_z2.csv'), 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['band', 'v_lo', 'v_hi', 'Z2_on_band_closes', 'Z2_on_band_fails', 'status', 'binding_L_ranges'])
        for r in allrows:
            w.writerow([r['i'], r['v_lo'], r['v_hi'], r['z2_ok'], r['z2_fail'], r['status'],
                        ';'.join(f"[{a:.2f},{b:.2f}]" for a, b in r['binding_L'])])
