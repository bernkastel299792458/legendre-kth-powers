"""Demonstration (rigorous evaluation with Phase 0's Arb code + Phase-2 lemmas A, B(-W), C, D) of rows at low
heights with parameters from the float re-optimisation (explore/round2_combined.py).

Phase 0's belarb.piece_v2 is used unchanged except for ONE line: in c1, the factor D2VW multiplying (VW)^{1/2}
in SU (Bellotti (3.11)/(3.17), |M(1/2+it)| <= sum_{n<=VW} d^2(n) n^{-1/2}) is replaced by Lemma D's
K_D = 4 c^2 P* (1-(U/V)^{1/2})(1-W^{-1/2})/(Delta log W).  S1t (|M(1)|) keeps D2VW.
We do not modify Phase 0's files: the patched function is built at run time from the source text.
Usage: python certify_lemmaD_demo.py"""
import sys, os, math, inspect, time
HERE = os.path.dirname(os.path.abspath(__file__))
P0 = os.path.join(HERE, '..', 'phase0_bellotti')
sys.path.insert(0, P0); sys.path.insert(0, HERE)
import belarb as B
from flint import arb, ctx
import improvements as P2
import lemmaD_mollifier as LD
ctx.prec = 128

src = inspect.getsource(B.piece_v2)
old = "    SU = D2VW / (2 * pi) * (2 * I2c * N.exp((base + k) * L) + N.exp(lE312) + N.exp(lE313))"
assert src.count(old) == 1
new = ("    if row.get('lemD'):\n"
       "        _c = LD.certify_c(); _P = LD.certify_Pstar()\n"
       "        _c = N.c(str(_c.upper())) if N is B.FLT else _c; _P = N.c(str(_P.upper())) if N is B.FLT else _P\n"
       "        _D = (v - u) * L\n"
       "        KD = 4 * _c * _c * _P * (1 - N.exp(-_D / 2)) * (1 - N.exp(-wL / 2)) / (_D * wL)\n"
       "        SU = KD / (2 * pi) * (2 * I2c * N.exp((base + k) * L) + N.exp(lE312) + N.exp(lE313))\n"
       "    else:\n"
       "        SU = D2VW / (2 * pi) * (2 * I2c * N.exp((base + k) * L) + N.exp(lE312) + N.exp(lE313))")
src = src.replace(old, new).replace("def piece_v2(", "def piece_v2D(")
ns = dict(B.__dict__); ns['LD'] = LD; ns['B'] = B
exec(src, ns)
B.piece_v2 = ns['piece_v2D']

def certify(L0, L1, a0, u, v, w, x, lam, zfr, weyl=True):
    t = time.time()
    Lf0 = 28.7296 if L0 == 'LOG3E12' else float(L0)
    d4 = P2.d4_upper(u, v, x, Lf0, float(L1))
    cf = P2.cf_upper(float(a0), lambda L: B.nu(zfr, L, B.ARB), Lf0, float(L1), hfac=lam, weyl=weyl)
    row = dict(L0=L0, L1=L1, a0=a0, u=u, x=x, v=v, w=w, lam=lam, zfr=zfr, lems='lemA,lemB,lemC',
               d4A=str(float(d4.upper()) * (1 + 1e-9)), cfB=str(float(cf.upper()) * (1 + 1e-9)), lemD=True)
    p = B.row_bound(row, B.OPT_V2, B.ARB)
    hyp = B.check_hypotheses(row, B.OPT_V2)
    bad = [h[0] for h in hyp if (not h[1]) and not h[0].startswith('[paper only]') and not h[0].startswith('(4.9)')]
    Cu = float(p['C'].upper())
    return dict(C=Cu, B=2 * float(x), CeBZ=Cu * math.exp(2 * float(x) / 4.62), d4=float(d4.upper()), cf=float(cf.upper()),
                c1=float(p['c1'].mid()), c5=float(p['c5'].mid()), bad=bad, secs=time.time() - t)

if __name__ == '__main__':
    ZFR = ('cl4.896', 'ford', 'lw21.233')
    cases = [('LOG3E12', '29', '0.9927', '2.244', '3.625', '0.600', '4.836', '18'),
             ('35', '36', '0.9927', '2.084', '3.435', '0.580', '4.574', '18'),
             ('40', '41', '0.9927', '1.985', '3.323', '0.568', '4.419', '18')]
    for c in cases:
        r = certify(*c, ZFR)
        print(f"[{c[0]},{c[1]}] a0={c[2]} u={c[3]} v={c[4]} w={c[5]} x={c[6]} lam={c[7]}: C <= {r['C']:.3f}  B={r['B']:.3f}  "
              f"C*e^(B/4.62)={r['CeBZ']:.1f}  d4<={r['d4']:.4f} cf<={r['cf']:.4f} c1={r['c1']:.5f} c5={r['c5']:.5f} hyp_fail={r['bad']} ({r['secs']:.0f}s)", flush=True)
