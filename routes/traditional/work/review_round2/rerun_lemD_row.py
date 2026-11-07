"""Referee re-run of the first Lemma-D demo row with Phase 0's NATIVE lemD integration (belarb.piece_v2 now has
'lemD' built in; phase2_lemmas/certify_lemmaD_demo.py no longer runs because its source patch target changed).
Also evaluates the same row WITHOUT lemD (SU with D2VW) to show where the gain comes from.
Run from review_round2:  python -B rerun_lemD_row.py"""
import sys, os, math, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'phase0_bellotti')); sys.path.insert(0, os.path.join(HERE, '..', 'phase2_lemmas'))
import belarb as B
import improvements as P2
from flint import arb, ctx

ZFR = ('cl4.896', 'ford', 'lw21.233')
cases = [('LOG3E12', '29', '0.9927', '2.244', '3.625', '0.600', '4.836', '18')]
for (L0, L1, a0, u, v, w, x, lam) in cases:
    t = time.time()
    Lf0 = 28.7296 if L0 == 'LOG3E12' else float(L0)
    d4 = P2.d4_upper(u, v, x, Lf0, float(L1))
    cf = P2.cf_upper(float(a0), lambda L: B.nu(ZFR, L, B.ARB), Lf0, float(L1), hfac=lam, weyl=True)
    ctx.prec = 128
    for lems in ('lemA,lemB,lemC,lemD', 'lemA,lemB,lemC'):
        row = dict(L0=L0, L1=L1, a0=a0, u=u, x=x, v=v, w=w, lam=lam, zfr=ZFR, lems=lems,
                   d4A=str(float(d4.upper()) * (1 + 1e-9)), cfB=str(float(cf.upper()) * (1 + 1e-9)))
        try:
            p = B.row_bound(row, B.OPT_V2, B.ARB)
            Cu = float(p['C'].upper())
            print(f"[{L0},{L1}] lems={lems}: C <= {Cu:.3f}  B={2*float(x):.3f}  C e^(B/4.62) = {Cu*math.exp(2*float(x)/4.62):.1f}"
                  f"  c1={float(p['c1'].mid()):.6f} SU={float(p['SU'].mid()):.3e} Mfac={float(p['Mfac'].mid()):.4e}"
                  f"  d4={float(d4.upper()):.4f} cf={float(cf.upper()):.4f} ({time.time()-t:.0f}s)", flush=True)
        except Exception as e:
            print(f"[{L0},{L1}] lems={lems}: FAILED ({type(e).__name__}: {e})", flush=True)
        # point value at the bottom, to see SU without lemD
        q = B.piece_v2(row, B.OPT_V2, B.LOG3E12_ARB, B.ARB, B.consts_N(row, B.ARB))
        print(f"    at log 3e12: c1={q['c1']}  SU={q['SU']}  S1t={q['S1t']}", flush=True)
