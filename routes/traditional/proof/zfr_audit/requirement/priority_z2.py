"""Priority questions from the main thread (Littlewood constant of Yang's thesis may be ~19.90-20.08,
not 19.62).  With Z1 = 4.896, Z3 = 54.004 fixed:
  (1) does the k = 67 chain close with uniform Z2 = 19.90?  with Z2 = 20.08?
  (3) does it close with the per-height profiles supplied by the main thread (worse value per interval)?
Each "closes" claim is backed by a complete cover of [L1, 1e8] that is then RE-EVALUATED IN FULL under the
model (no pieces skipped), with exact contiguity check, and written to out/cover_<name>.csv.

Usage: python -I priority_z2.py [names...]   (default: all)"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import json
import time
import common as C
import zfr_model as ZM
import repair as RP
import reopt as RO

# Per-height local constants 1/A reported by the main thread (thesis method, grid estimates, not proofs):
#   log t :   60     80     95.5   129    160    216    >=225
#   lam*  :  19.42  20.00  20.08  19.89  19.59  19.04  <=19.09
#   opt.  :  19.26  19.44  19.59  19.89  19.46  19.02  <=19.09
# Piecewise-constant profile, worse (larger) endpoint value on each interval; on [55, 60] (below the first
# sample; there the thesis' 19.62 region rests on its unaudited Lemma 2.1) we keep 19.62, the larger value.
PROF_LAMSTAR = ((0, "19.62"), (60, "20.00"), (80, "20.08"), (129, "19.89"), (160, "19.59"), (216, "19.09"))
PROF_OPT = ((0, "19.62"), (60, "19.44"), (80, "19.59"), (95.5, "19.89"), (160, "19.46"), (216, "19.09"))

MODELS = {
    'U19.90': ZM.ZModel(Z2="19.90"),
    'U20.08': ZM.ZModel(Z2="20.08"),
    'PROF_lamstar': ZM.ZModel(z2prof=PROF_LAMSTAR),
    'PROF_opt': ZM.ZModel(z2prof=PROF_OPT),
    # sensitivity of PROF_opt to the unaudited part [55, 60]: drop the Littlewood region below v = 60
    # entirely (Z2 = 1000 there, i.e. only the classical 4.896 and VK regions are used below 60)
    'PROF_opt_noLW_below60': ZM.ZModel(z2prof=((0, "1000"),) + PROF_OPT[1:]),
    # same for the lambda* profile, to see whether it is [60, 80] that breaks it
    'PROF_lamstar_but_6080_opt': ZM.ZModel(z2prof=((0, "19.62"), (60, "19.44"), (80, "20.08"), (129, "19.89"),
                                                     (160, "19.59"), (216, "19.09"))),
    # lambda* profile with LINEAR INTERPOLATION between the samples 60 (19.42) and 80 (20.00), taken in
    # 2-unit pieces with the larger (right-end) value; elsewhere as PROF_LAMSTAR.  Hypothetical: the thesis
    # audit has not computed these intermediate values.
    'PROF_lamstar_interp': ZM.ZModel(z2prof=((0, "19.62"),) + tuple(
        (60 + 2 * i, f"{19.42 + 0.029 * (2 * i + 2):.3f}") for i in range(10)) + (
        (80, "20.08"), (129, "19.89"), (160, "19.59"), (216, "19.09"))),
}


def confirm_model(model, pieces):
    jobs = [(k, p) for k, p, d in pieces]
    res = C.eval_all(model, jobs)
    ok = all(r[3] for r in res)
    pcs = sorted(p for k, p in jobs)
    contig = pcs[0][0] == ZM.L1 and pcs[-1][1] == ZM.L3 and all(pcs[i][1] == pcs[i + 1][0] for i in range(len(pcs) - 1))
    w = max(res, key=lambda r: r[2])
    return dict(all_delta_lt_1=ok, contiguous_L1_to_1e8=contig, max_delta=w[2], max_at_L=float(w[1][0]),
                max_kind=w[0]), [(r[0], r[1], r[2]) for r in res]


def test(name, model):
    t = time.time()
    r = RP.repair(model)
    out = dict(name=name, model=repr(model), closes=r['closes'], n_failed_original=r['n_fail'],
               failed_ranges=[(float(a), float(b)) for a, b in r['bad_ranges']][:10],
               holes=[(float(a), float(b)) for a, b in r['holes']][:10])
    if r['closes']:
        conf, pcs = confirm_model(model, r['pieces'])
        out['confirm'] = conf
        S = [p for k, p, d in pcs if k == 'S']
        out['S_range'] = [float(min(p[0] for p in S)), float(max(p[1] for p in S))]
        fn = os.path.join(ZM.HERE, 'out', f'cover_{name}.csv')
        RO.write_cover(fn, pcs)
        out['cover_file'] = os.path.basename(fn)
        out['pieces'] = len(pcs)
    out['seconds'] = round(time.time() - t)
    return out


if __name__ == '__main__':
    names = sys.argv[1:] or list(MODELS)
    os.makedirs(os.path.join(ZM.HERE, 'out'), exist_ok=True)
    jfn = os.path.join(ZM.HERE, 'out', 'priority_z2.json')
    allres = json.load(open(jfn)) if os.path.exists(jfn) else {}
    for n in names:
        res = test(n, MODELS[n])
        print(json.dumps(res), flush=True)
        allres[n] = res
        json.dump(allres, open(jfn, 'w'), indent=1)
