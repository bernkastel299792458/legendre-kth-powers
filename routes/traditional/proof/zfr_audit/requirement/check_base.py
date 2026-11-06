"""Sanity check: with the unmodified 'lw' ZFR the harness reproduces the certificates' max delta."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import time
import common as C
import zfr_model as ZM

if __name__ == '__main__':
    t = time.time()
    jobs = [('S', p) for p in C.load_smooth()] + [('H', p) for p in C.load_hyb()]
    res = C.eval_all(ZM.ZModel(), jobs)
    for kind in 'SH':
        r = [x for x in res if x[0] == kind]
        w = max(r, key=lambda x: x[2])
        print(kind, len(r), 'all rigorously < 1:', all(x[3] for x in r), 'max delta', w[2], 'at L =', float(w[1][0]))
    print('time', time.time() - t)
