"""Independent pure-Arb re-check of a v5 chain.
Usage: python check5.py OUTTAG   (reads certs/OUTTAG.json for the configuration)
Checks: contiguity and exact endpoints L1 -> L2 -> L3, every S piece with rig_delta_smooth_pure (pure Arb),
every H piece with rig_delta5, Lemma T at L3, the CHL numeric facts, and input-file hashes."""
import sys
import os
import csv
import json
import hashlib
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prio  # noqa: E402,F401  (idle priority)
import cfg5  # noqa: E402
import rig5  # noqa: E402
import rigorous_smooth as RS  # noqa: E402
import rigorous_hyb as RH  # noqa: E402
import tail  # noqa: E402
import tail5  # noqa: E402
from flint import arb  # noqa: E402

OUT = sys.argv[1]
META = json.load(open(f'certs/{OUT}.json', encoding='utf-8'))
P = META['config']
CONSTS = None


def init():
    global CONSTS
    cfg5.setup(P)
    CONSTS = {M: RS.weight_constants(M) for M in (2, 3, 4, 5, 6)}


def chk_s(r):
    k, a, b, M = int(r['k']), F(r['a']), F(r['b']), int(r['M'])
    d, _ = RS.rig_delta_smooth_pure(k, a, b, M, CONSTS[M])
    return float(d.upper()) if d is not None else 9e9


def chk_h(r):
    k, a, b = int(r['k']), F(r['a']), F(r['b'])
    d, _ = rig5.rig_delta5(k, a, b, F(r['c']), F(r['sigma_star']))
    return d if d is not None else 9e9


def _local(f):
    """The sidecar records the code modules (phi5, rig5, cfg5, tail5) by absolute path on the machine that made it.
    Resolve such a path to the file of the same name next to this script; relative input paths are used as they are."""
    g = f.replace('\\', '/')
    if os.path.isabs(f) or (len(g) > 1 and g[1] == ':'):
        return os.path.join(os.path.dirname(os.path.abspath(__file__)), g.rsplit('/', 1)[-1])
    return f


if __name__ == '__main__':
    for f, h in META['sha256'].items():
        assert hashlib.sha256(open(_local(f), 'rb').read()).hexdigest() == h, f'input changed: {f}'
    S = list(csv.DictReader(open(f'certs/{OUT}_S.csv')))
    H = list(csv.DictReader(open(f'certs/{OUT}_H.csv')))
    K = int(S[0]['k'])
    L1 = RH.prop33_ceiling_lower(K)
    L3 = F(int(float(P['L3'])))
    assert F(S[0]['a']) == L1, 'S does not start at L1'
    for x, y in zip(S[:-1], S[1:]):
        assert F(x['b']) == F(y['a']), 'S gap'
    assert F(S[-1]['b']) == F(H[0]['a']), 'S/H junction'
    for x, y in zip(H[:-1], H[1:]):
        assert F(x['b']) == F(y['a']), 'H gap'
    assert F(H[-1]['b']) == L3, 'H does not end at L3'
    D1, D2 = arb(39097000), arb(251949000000)
    assert (K * (D1 - 1) - (arb(600) / K).exp()).lower() > 0
    assert (K * (D2 - 1) - (arb(L1.numerator) / L1.denominator / K).exp()).lower() > 0
    assert (K * (K * D1 * (1 - 1 / D1) ** 2).log()).lower() >= 600
    assert cfg5.tail_check(P, L3, K)
    with Pool(prio.NPROC, initializer=init) as pool:
        ds = pool.map(chk_s, S, chunksize=8)
        dh = pool.map(chk_h, H, chunksize=8)
    print(f'[{OUT}] k={K}: S {len(S)} pieces [{float(L1):.3f}, {float(F(S[-1]["b"])):.3f}] max delta (pure Arb) {max(ds):.6f}; '
          f'H {len(H)} pieces up to {L3}, max delta {max(dh):.6f}')
    ok = max(ds) < 1 and max(dh) < 1
    print(f'[{OUT}] ' + ('CHAIN VERIFIED' if ok else 'CHAIN FAILED'))
    sys.exit(0 if ok else 1)
