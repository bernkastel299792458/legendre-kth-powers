"""Task 3.1(b): re-optimised global thresholds.
Bisect a one-parameter family (common.family_model) for the weakest value at which repair() still
produces a complete rigorous cover of [L1, 1e8].  The cover found at the reported value is written
as a certificate-style CSV (out/cover_<family>_<value>.csv) so the claim can be re-checked.

Usage: python -I reopt.py FAMILY STRONG WEAK [STEPS]
  STRONG = value known to close (e.g. 4.896), WEAK = value expected to fail."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
import json
import time
from fractions import Fraction
import common as C
import zfr_model as ZM
import repair as RP


def write_cover(fn, pieces):
    with open(fn, 'w', newline='') as f:
        w = csv.writer(f)
        w.writerow(['method', 'a', 'b', 'M_or_c', 'sigma_star', 'delta_upper'])
        for kind, p, d in pieces:
            if kind == 'S':
                w.writerow(['S', str(p[0]), str(p[1]), p[2], '', '' if d is None else f'{d:.9g}'])
            else:
                w.writerow(['H', str(p[0]), str(p[1]), str(p[2]), str(p[3]), '' if d is None else f'{d:.9g}'])


def run(fam, strong, weak, steps=14, decreasing=False, tag=None, log=print):
    """Return dict with ok value, fail value, holes at fail value."""
    t = time.time()
    fmt = lambda x: f"{x:.6f}"
    r_strong = RP.repair(C.family_model(fam, fmt(strong)))
    if not r_strong['closes']:
        return dict(fam=fam, status='fails_at_strong', strong=strong, holes=[(float(a), float(b)) for a, b in r_strong['holes']])
    r_weak = RP.repair(C.family_model(fam, fmt(weak)))
    if r_weak['closes']:
        return dict(fam=fam, status='closes_at_weak', weak=weak, cover=r_weak)
    g, b, rg, rb = strong, weak, r_strong, r_weak
    for i in range(steps):
        m = (g + b) / 2
        m = float(fmt(m))
        if m in (g, b):
            break
        r = RP.repair(C.family_model(fam, fmt(m)))
        if r['closes']:
            g, rg = m, r
        else:
            b, rb = m, r
        log(f"    [{fam}] step {i}: ok={g} fail={b}  ({time.time()-t:.0f}s)")
    return dict(fam=fam, status='thr', ok=g, fail=b, cover=rg,
                holes_at_fail=[(float(x), float(y)) for x, y in rb['holes']],
                bad_at_fail=[(float(x), float(y)) for x, y in rb['bad_ranges']][:20])


def confirm(fam, val, pieces):
    """Full rigorous re-evaluation of a cover under the model, plus exact contiguity check."""
    model = C.family_model(fam, f"{val:.6f}")
    jobs = [(k, p) for k, p, d in pieces]
    res = C.eval_all(model, jobs)
    ok = all(r[3] for r in res)
    pcs = sorted(p for k, p in jobs)
    contig = pcs[0][0] == ZM.L1 and pcs[-1][1] == ZM.L3 and all(pcs[i][1] == pcs[i + 1][0] for i in range(len(pcs) - 1))
    w = max(res, key=lambda r: r[2])
    return dict(all_delta_lt_1=ok, contiguous_L1_to_1e8=contig, max_delta=w[2], max_at_L=float(w[1][0]), max_kind=w[0],
                pieces=[(r[0], r[1], r[2]) for r in res])


if __name__ == '__main__':
    fam, strong, weak = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
    steps = int(sys.argv[4]) if len(sys.argv) > 4 else 14
    os.makedirs(os.path.join(ZM.HERE, 'out'), exist_ok=True)
    res = run(fam, strong, weak, steps)
    summary = {k: v for k, v in res.items() if k != 'cover'}
    if 'cover' in res:
        val = res.get('ok', res.get('weak'))
        conf = confirm(fam, val, res['cover']['pieces'])
        pcs = conf.pop('pieces')
        summary['confirm'] = conf
        fn = os.path.join(ZM.HERE, 'out', f'cover_{fam}_{val:.6f}.csv')
        write_cover(fn, pcs)
        summary['cover_file'] = os.path.basename(fn)
        summary['cover_pieces'] = len(pcs)
        summary['cover_S_range'] = [float(min(p[0] for k, p, d in pcs if k == 'S')), float(max(p[1] for k, p, d in pcs if k == 'S'))]
        summary['cover_max_delta'] = max(d for k, p, d in pcs if d is not None)
    print(json.dumps(summary, indent=1))
    with open(os.path.join(ZM.HERE, 'out', f'reopt_{fam}.json'), 'w') as f:
        json.dump(summary, f, indent=1)
