"""FLOAT effect estimate (not rigorous): Phase-0 v2 evaluator + Lemma D (critical-line mollifier bound)
+ Lemma B-W (Weyl J-bound in Lemma B); objective C*e^{B/4.62}; re-optimised (u,v,w,x,lam)."""
import sys, math
import round2_model as R
import improvements as P2
import lemmaB_count as LB
import belarb as B
_cfw = {}
def cf_w(a0, zfr, L0, L1, lam):
    key = (a0, zfr, L0, L1, lam, R.CTX.get('weyl', False))
    if key not in _cfw:
        try:
            _cfw[key] = float(LB.cf_upper(float(a0), lambda L: B.nu(zfr, L, B.ARB), float(L0), float(L1), hfac=lam,
                                          weyl=R.CTX.get('weyl', False))[0].upper())
        except AssertionError:
            _cfw[key] = None
    return _cfw[key]
R.cf = cf_w
ZFR = ('cl4.896', 'ford', 'lw21.233') if len(sys.argv) < 2 or sys.argv[1] != 'ref' else ('cl5.558691', 'ford', 'lw21.233')
rows = sys.argv[2:] or ['LOG3E12:29', '35:36', '40:41']
for rs in rows:
    L0s, L1s = rs.split(':')
    a0s = ('0.9927',) if (L0s == 'LOG3E12' or float(L0s) < 46) else ('0.985',)
    for a0 in a0s:
        for lab, lemD, weyl in (('base', False, False), ('D', True, False), ('BW', False, True), ('D+BW', True, True)):
            R.CTX['weyl'] = weyl
            best = None
            for lam in ('1', '8', '14', '18', '22'):
                r = R.optimise(L0s, L1s, a0, ZFR, lam, lemD=lemD)
                if r and (best is None or r['obj'] < best['obj']):
                    best = r
            if best:
                print(f"[{L0s},{L1s}] a0={a0} {lab:5s} C={best['C']:9.2f} B={best['B']:7.3f} lam={best['lam']:>3} "
                      f"C*e^(B/4.62)={best['CeBZ']:10.1f}  u={best['u']:.3f} v={best['v']:.3f} w={best['w']:.3f} x={best['x']:.3f}", flush=True)
