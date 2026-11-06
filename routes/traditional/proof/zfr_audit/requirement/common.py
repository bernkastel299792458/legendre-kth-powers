"""Shared helpers: certificate loading, parallel evaluation, bisection."""
import csv
import os
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor

import zfr_model as ZM

NPROC = max(1, (os.cpu_count() or 2) - 1)


# Base certificates: the current (v3) ones when present, else the superseded v2 ones.  repair() fills any
# coverage gap between the base S and H certificates (e.g. [6989.94, 7219] for v2-S + v3-H).
SMOOTH_CANDIDATES = ['cert_smooth_v3_k67_lw.csv', os.path.join('superseded_v2', 'cert_smooth_full_k67_lw_jy.csv')]
HYB_CANDIDATES = ['cert_hyb_v3_k67_lw.csv', os.path.join('superseded_v2', 'cert_hyb_jy_k67_lw.csv')]
USED = {}


def _first(cands):
    for c in cands:
        fn = os.path.join(ZM.CERT, c)
        if os.path.exists(fn):
            return fn
    raise FileNotFoundError(cands)


def load_smooth():
    fn = _first(SMOOTH_CANDIDATES)
    USED['S'] = os.path.relpath(fn, ZM.CERT)
    rows = list(csv.DictReader(open(fn)))
    return sorted((Fraction(r['a']), Fraction(r['b']), int(r['M'])) for r in rows)


def load_hyb():
    fn = _first(HYB_CANDIDATES)
    USED['H'] = os.path.relpath(fn, ZM.CERT)
    rows = list(csv.DictReader(open(fn)))
    return sorted((Fraction(r['a']), Fraction(r['b']), Fraction(r['c']), Fraction(r['sigma_star'])) for r in rows)


def _eval_piece(args):
    kind, piece = args
    if kind == 'S':
        a, b, M = piece
        d = ZM.smooth_delta(a, b, M)
    else:
        a, b, c, s = piece
        d = ZM.hyb_delta(a, b, c, s)
    if isinstance(d, float):   # rig_delta (Prop. H) returns float(arb.upper()); same test as check_certificate.py
        return kind, piece, d, d < 1 - 1e-12
    return kind, piece, float(d), bool((1 - d).lower() > 0)   # rigorous "d < 1"


def eval_all(model, jobs, nproc=NPROC):
    """jobs: list of ('S', (a,b,M)) / ('H', (a,b,c,s)). Returns list of (kind, piece, delta, rigorously<1)."""
    with ProcessPoolExecutor(nproc, initializer=ZM.worker_init, initargs=(model.key(),)) as ex:
        return list(ex.map(_eval_piece, jobs, chunksize=4))


# ---------- one-parameter families of hypothetical ZFRs ----------
def family_model(fam, x):
    """fam: name; x: decimal string. Returns ZModel."""
    if fam == 'Z1':            # classical constant, others = proof's set
        return ZM.ZModel(Z1=x)
    if fam == 'Z2':            # Littlewood constant
        return ZM.ZModel(Z2=x)
    if fam == 'Z3':            # VK constant
        return ZM.ZModel(Z3=x)
    if fam == 'Z1_pubLW':      # classical constant needed if only the published Littlewood 21.233 (+53.989) is used
        return ZM.ZModel(Z1=x, Z2="21.233", Z3="53.989")
    if fam == 'Z2_pubC':       # Littlewood constant needed if only the published classical 5.558691 is used
        return ZM.ZModel(Z1="5.558691", Z2=x)
    if fam == 'optprof55':       # main thread's optimised-lambda profile, with Z2 = x on [55, 60)
        return ZM.ZModel(z2prof=((0, "19.62"), (55, x), (60, "19.44"), (80, "19.59"), (95.5, "19.89"),
                                 (160, "19.46"), (216, "19.09")))
    if fam.startswith('z2band:'):   # z2band:vlo:vhi ; x = Littlewood constant on (vlo, vhi], 19.62 elsewhere
        _, vlo, vhi = fam.split(':')
        return ZM.ZModel(z2prof=((0, "19.62"), (Fraction(vlo), x), (Fraction(vhi), "19.62")))
    if fam.startswith('band:'):  # band:vlo:vhi ; x = s
        _, vlo, vhi = fam.split(':')
        return ZM.ZModel(band=(Fraction(vlo), Fraction(vhi), Fraction(x)))
    raise ValueError(fam)


def piece_ok(kind, piece, model):
    ZM.install(model)
    return _eval_piece((kind, piece))


def _bisect_piece(args):
    """Largest x in [lo, hi] (increasing x = weaker ZFR) keeping this piece's delta < 1.
    For band families x = s and *decreasing* s is weaker; handled by `decreasing`."""
    kind, piece, fam, lo, hi, rel, decreasing = args
    def ok(x):
        return piece_ok(kind, piece, family_model(fam, f"{x:.12g}"))[3]
    weak, strong = (lo, hi) if decreasing else (hi, lo)   # weak end = weakest ZFR in range
    if ok(weak):
        return kind, piece, ('beyond', weak)
    if not ok(strong):
        return kind, piece, ('fails', strong)
    g, b = strong, weak    # g ok, b fails
    while abs(b - g) > rel * abs(g):
        m = (g + b) / 2
        if ok(m):
            g = m
        else:
            b = m
    return kind, piece, ('thr', g, b)


def bisect_all(jobs, fam, lo, hi, rel=1e-6, decreasing=False, nproc=NPROC):
    args = [(k, p, fam, lo, hi, rel, decreasing) for k, p in jobs]
    with ProcessPoolExecutor(nproc, initializer=ZM.worker_init, initargs=(ZM.ZModel().key(),)) as ex:
        return list(ex.map(_bisect_piece, args, chunksize=2))
