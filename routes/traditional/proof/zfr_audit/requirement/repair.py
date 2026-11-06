"""
Re-optimised closure test under a hypothetical ZFR ("repair").

Given a ZModel:
 1. evaluate every piece of the two existing certificates (Prop. S on [L1, L2], Prop. H on [L2, 1e8]);
    pieces the model cannot affect (by the conservative v-range test) are kept without re-evaluation;
 2. every failing range is re-covered with re-optimised pieces:
      - Prop. S: widths 4, 2, 1, ..., 1/1024 and M in {2, 3, 4};
      - Prop. H: c re-optimised (grid + Bellotti-row edges + local refinement, all with the rigorous
        evaluator), sigma* in {0.985, 0.99};
      - a range may be covered by either method (so the S/H junction can move);
 3. the model "closes" iff no hole remains.  The returned piece list is a complete rigorous cover of
    [L1, 1e8] under the model (Lemma 6 below L1 does not use any ZFR; Lemma T above 1e8 uses only Z3).

All deltas come from the certified code (pure-arb for Prop. S; rig_delta for Prop. H).
"""
from fractions import Fraction
from concurrent.futures import ProcessPoolExecutor

import zfr_model as ZM
import common as C

MIN_W_S = Fraction(1, 256)
MIN_W_H = Fraction(1, 1024)
M_LIST = (3, 2, 4)
SSTARS = (Fraction(985, 1000), Fraction(99, 100))


def _s_ok(a, b, M):
    d = ZM.smooth_delta(a, b, M)
    if isinstance(d, float):
        return False, d
    return bool((1 - d).lower() > 0), float(d)


def _h_ok(a, b, c, s):
    d = ZM.hyb_delta(a, b, c, s)
    return d < 1 - 1e-12, d


def best_hyb(a, b, c0=None):
    """Minimise the rigorous Prop. H delta over c (and sigma*) for the piece [a, b]."""
    k = ZM.K67
    a_f, b_f = float(a), float(b)

    def val(c):
        cf = Fraction(round(c * 10 ** 9), 10 ** 9)
        best = (float('inf'), None, None)
        for s in SSTARS:
            d = ZM.hyb_delta(a, b, cf, s)
            if d < best[0]:
                best = (d, cf, s)
        return best

    cands = [1 + i * 1e-3 for i in range(1, 1200)]
    if c0 is not None:
        cands += [c0 * (1 + j * 1e-4) for j in range(-30, 31)]
    for T0, T1, *_ in RowsF:
        for edge in (T0, T1):
            cands += [edge * k / b_f * (1 - 1e-9), edge * k / a_f * (1 + 1e-9)]
    cands = [c for c in cands if 1 < c < k / 10]
    best = min((val(c) + (c,) for c in cands), key=lambda t: t[0])
    cb = best[3]
    for step in (1e-4, 1e-5, 1e-6, 1e-7):
        for _ in range(80):
            nb = min((val(cb + step) + (cb + step,), val(cb - step) + (cb - step,)), key=lambda t: t[0])
            if nb[0] < best[0]:
                best, cb = nb, nb[3]
            else:
                break
    return best[:3]   # (delta, c Fraction, sigma*)


RowsF = [(float(r[0].mid()), float(r[1].mid())) for r in ZM.RH.ROWS]


S_MAX_L = None             # optional: do not attempt Prop. S at L >= S_MAX_L (search restriction only)
H_MIN_L = Fraction(6000)   # Prop. H is not attempted below this L (it never closes there, even with the
                           # unmodified ZFR its lowest reach is L = 6989.94); a search restriction only.


def cover(a, b, methods=('S', 'H'), w0=Fraction(4)):
    """Cover [a, b] bottom-up with re-optimised pieces. Returns (pieces, reached) where
    reached = b if fully covered, else the point where it got stuck (no method closes a piece of
    width MIN_W starting there)."""
    pieces = []
    cur = Fraction(a)
    w = Fraction(w0)
    c_prev = None
    m_order = list(M_LIST)
    while cur < b:
        top = min(cur + w, Fraction(b))
        got = None
        if 'S' in methods and (S_MAX_L is None or cur < S_MAX_L):
            for M in m_order:
                ok, d = _s_ok(cur, top, M)
                if ok:
                    got = ('S', (cur, top, M), d)
                    m_order.remove(M)
                    m_order.insert(0, M)       # try the last successful M first
                    break
        if got is None and 'H' in methods and cur >= H_MIN_L:
            d, c, s = best_hyb(cur, top, c_prev)
            if c is not None and d < 1 - 1e-12:
                got = ('H', (cur, top, c, s), d)
                c_prev = float(c)
        if got is not None:
            pieces.append(got)
            cur = top
            cap = Fraction(4) if got[0] == 'S' else max(Fraction(4), Fraction(int(float(cur) / 200) + 1))
            if got[2] < 0.95:
                w = min(w * 2, cap)
        else:
            if w <= MIN_W_S:
                return pieces, cur
            w /= 2
    return pieces, Fraction(b)


def _affected_S(model, p):
    a, b, M = p
    lo, hi = ZM.smooth_vrange(a, b, M)
    return model.affects(lo, hi)


def _affected_H(model, p):
    a, b, c, s = p
    u_hi = float(c) / ZM.K67 * float(b)
    return model.affects(u_hi * (1 - 1e-9), u_hi * (1 + 1e-9))


def _job(args):
    kind, payload = args
    if kind == 'eval':
        return C._eval_piece(payload)
    if kind == 'cover':
        a, b, methods = payload
        return cover(a, b, methods)
    raise ValueError(kind)


def merge_ranges(rs):
    rs = sorted(rs)
    out = []
    for a, b in rs:
        if out and out[-1][1] >= a:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def split(a, b, n):
    """Split [a, b] into n exact pieces at multiples of 1/1024 (for parallel covering)."""
    if n <= 1 or b - a < 8:
        return [(a, b)]
    pts = [a] + [Fraction(round((a + (b - a) * i / n) * 1024), 1024) for i in range(1, n)] + [b]
    pts = sorted(set(p for p in pts if a <= p <= b))
    return list(zip(pts[:-1], pts[1:]))


def repair(model, nproc=C.NPROC, verbose=False):
    """Returns dict(closes, pieces, holes, n_reeval, n_fail)."""
    S = C.load_smooth()
    H = C.load_hyb()
    jobs = []
    keep = []
    for p in S:
        (jobs if _affected_S(model, p) else keep).append(('S', p))
    for p in H:
        (jobs if _affected_H(model, p) else keep).append(('H', p))
    with ProcessPoolExecutor(nproc, initializer=ZM.worker_init, initargs=(model.key(),)) as ex:
        res = list(ex.map(_job, [('eval', j) for j in jobs], chunksize=4))
        good = [(k, p, None) for k, p in keep] + [(k, p, d) for k, p, d, ok in res if ok]
        bad = [(k, p) for k, p, d, ok in res if not ok]
        # coverage gaps of [L1, L3] left by the base certificates count as failing ranges too
        base = sorted([(p[0], p[1]) for p in S] + [(p[0], p[1]) for p in H])
        gaps, cur = [], ZM.L1
        for a_, b_ in base:
            if a_ > cur:
                gaps.append((cur, a_))
            cur = max(cur, b_)
        if cur < ZM.L3:
            gaps.append((cur, ZM.L3))
        assert all(base[i][1] <= base[i + 1][0] for i in range(len(base) - 1)), "overlapping base certificates"
        bad_ranges = merge_ranges([(p[0], p[1]) for k, p in bad] + gaps)
        # re-cover each failing range with both methods, in parallel sub-chunks
        tasks = []
        for a, b in bad_ranges:
            for x, y in split(a, b, max(1, min(nproc, int((b - a) / 16)))):
                tasks.append((x, y))
        covers = list(ex.map(_job, [('cover', (x, y, ('S', 'H'))) for x, y in tasks]))
    new_pieces, holes = [], []
    for (x, y), (pcs, reached) in zip(tasks, covers):
        new_pieces += pcs
        if reached < y:
            holes.append((reached, y))
    pieces = [(k, p, d) for k, p, d in good] + [(k, p, d) for k, p, d in new_pieces]
    pieces.sort(key=lambda t: t[1][0])
    # contiguity check of the final cover (only meaningful when there are no holes)
    contiguous = not holes and pieces[0][1][0] == ZM.L1 and pieces[-1][1][1] == ZM.L3 and all(
        pieces[i][1][1] == pieces[i + 1][1][0] for i in range(len(pieces) - 1))
    if verbose:
        print(f"  {model}: re-evaluated {len(jobs)}, failed {len(bad)} in {len(bad_ranges)} ranges, "
              f"holes {[(float(a), float(b)) for a, b in holes][:5]}")
    return dict(closes=contiguous, pieces=pieces, holes=holes, n_reeval=len(jobs), n_fail=len(bad),
                bad_ranges=bad_ranges, gaps=gaps, base=dict(C.USED))
