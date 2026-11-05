"""Task 3.2: band-localised requirement curve.
For each height band (v_lo, v_hi] (v = log t) the pointwise zero-free width is multiplied by s <= 1
on that band only (the proof then sees the uniform width eta_unif, see zfr_model.py).  We bisect for
the smallest s for which repair() still closes the whole chain [L1, 1e8], and translate s into the
weakest admissible value of the constant that is active on the band (Z/s).

Usage: python -I bands.py [S_WEAK] [STEPS]       (writes out/bands.csv, out/bands.json)"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
import json
import time
from fractions import Fraction
from math import exp, log
import zfr_model as ZM
import reopt as RO
import common as C
import repair as RP
from fractions import Fraction as _F
RP.S_MAX_L = _F(12000)   # search restriction for speed: Prop. S is not tried at L >= 12000

V_HR = float(ZM.LOG_HR)                     # 28.7297...
V_C = exp(19.62 / 4.896)                    # classical/Littlewood crossover, ~55.006
# Littlewood/VK crossover for (19.62, 54.004)
def _cross():
    lo, hi = 1e3, 1e7
    f = lambda v: log(v) / (19.62 * v) - 1 / (54.004 * v ** (2 / 3) * log(v) ** (1 / 3))
    for _ in range(200):
        m = (lo * hi) ** 0.5
        (lo, hi) = (m, hi) if f(m) > 0 else (lo, m)
    return lo
V_VK = _cross()

# band edges (exact rationals; the two crossovers rounded to 1/1024 so every band has one active branch)
q = lambda x: Fraction(round(x * 1024), 1024)
EDGES = ([q(V_HR)] + [Fraction(x) for x in (31, 34, 37, 40, 43, 46, 49, 52)] + [q(V_C) + Fraction(1, 1024)]
         + [Fraction(x) for x in (58, 61, 64, 67, 70, 75, 80, 85, 90, 100, 110, 130, 170, 300, 1000, 10000, 100000)]
         + [q(V_VK)] + [Fraction(1600000)])


def active(vlo, vhi):
    vm = (vlo + vhi) / 2
    e1, e2, e3 = 1 / (4.896 * vm), log(vm) / (19.62 * vm), 1 / (54.004 * vm ** (2 / 3) * log(vm) ** (1 / 3))
    return ('Z1', 4.896) if e1 >= max(e2, e3) else (('Z2', 19.62) if e2 >= e3 else ('Z3', 54.004))


if __name__ == '__main__':
    s_weak = float(sys.argv[1]) if len(sys.argv) > 1 else 0.2
    steps = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    only = sys.argv[3] if len(sys.argv) > 3 else None      # optional "i:j" subset of band indices
    os.makedirs(os.path.join(ZM.HERE, 'out'), exist_ok=True)
    bands = list(zip(EDGES[:-1], EDGES[1:]))
    idx = range(len(bands))
    if only:
        i0, i1 = (int(x) for x in only.split(':'))
        idx = range(i0, min(i1, len(bands)))
    rows = []
    jfn = os.path.join(ZM.HERE, 'out', 'bands.json')
    old = json.load(open(jfn)) if os.path.exists(jfn) else {}
    for i in idx:
        vlo, vhi = bands[i]
        name, Z = active(float(vlo), float(vhi))
        fam = f"band:{vlo}:{vhi}"
        t = time.time()
        # bracket (s = s_weak, then 0.9), then bisect inside the bracket; each test is one repair()
        cache = {}

        def closes(x):
            x = float(f"{x:.6f}")
            if x not in cache:
                cache[x] = RP.repair(C.family_model(fam, f"{x:.6f}"))
            return cache[x]['closes']

        if closes(s_weak):
            s_ok, s_fail, where, status = s_weak, None, [], 'closes_at_weak'
        else:
            g, bb = (1.0, 0.9) if not closes(0.9) else (0.9, s_weak)
            for _ in range(steps):
                m = float(f"{(g + bb) / 2:.6f}")
                if m in (g, bb):
                    break
                if closes(m):
                    g = m
                else:
                    bb = m
            s_ok, s_fail, status = g, bb, 'thr'
            rb = cache[float(f"{bb:.6f}")]
            where = [(float(x), float(y)) for x, y in (rb['holes'] or rb['bad_ranges'])]
        row = dict(i=i, v_lo=float(vlo), v_hi=float(vhi), active=name, Z=Z, s_ok=s_ok, s_fail=s_fail,
                   Z_weakest_ok=(Z / s_ok if s_ok else None), status=status,
                   binding_L=where[:3], seconds=round(time.time() - t))
        print(json.dumps(row), flush=True)
        old[str(i)] = row
        json.dump(old, open(jfn, 'w'), indent=1)
    allrows = [old[k] for k in sorted(old, key=int)]
    with open(os.path.join(ZM.HERE, 'out', 'bands.csv'), 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['band', 'v_lo', 'v_hi', 'active_constant', 'proof_value', 's_ok', 's_fail',
                    'weakest_admissible_constant', 'status', 'binding_L_ranges'])
        for r in allrows:
            w.writerow([r['i'], f"{r['v_lo']:.4f}", f"{r['v_hi']:.4f}", r['active'], r['Z'], r['s_ok'], r['s_fail'],
                        '' if r['Z_weakest_ok'] is None else f"{r['Z_weakest_ok']:.4f}", r['status'],
                        ';'.join(f"[{a:.2f},{b:.2f}]" for a, b in r['binding_L'])])
