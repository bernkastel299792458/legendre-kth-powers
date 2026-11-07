"""Driver: rigorous Lemma-A bound for d4 on every Bellotti row (her parameters u, v, x).
Writes results/d4_rows.json.  Usage:  python run_d4_rows.py [Lmax] [piece]"""
import json, math, os, sys, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bellotti_rows import rows
import lemmaA_d4 as A


def job(args):
    i, piece = args
    r = rows[i]
    t0 = time.time()
    # use the decimal strings as printed in the paper (exact decimal -> arb ball)
    u = repr(r["u"]); v = repr(r["v"]); x = repr(r["x"])
    b, det = A.d4_upper(u, v, x, r["L0"], r["L1"], piece=piece)
    return dict(i=i, L0=r["L0"], L1=r["L1"], u=u, v=v, x=x, d4_old=r["d4"], d4_new=A.f_up(b),
                pieces=det, seconds=time.time() - t0)


if __name__ == "__main__":
    Lmax = float(sys.argv[1]) if len(sys.argv) > 1 else 170.3
    piece = float(sys.argv[2]) if len(sys.argv) > 2 else 0.25
    idx = [i for i, r in enumerate(rows) if r["L1"] <= Lmax]
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    with Pool(min(14, len(idx))) as p:
        out = p.map(job, [(i, piece) for i in idx])
    out.sort(key=lambda d: d["i"])
    for d in out:
        print(f"[{d['L0']:7.2f},{d['L1']:6.1f}]  d4_old={d['d4_old']:8.3f}  d4_new<={d['d4_new']:7.4f}  "
              f"ratio={d['d4_new']/d['d4_old']:.4f}  ({d['seconds']:.0f}s)")
    json.dump(out, open(os.path.join(HERE, "results", "d4_rows.json"), "w"), indent=1)
