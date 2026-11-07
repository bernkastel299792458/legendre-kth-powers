"""Task 4: re-optimisation (float optimiser on the corrected bound, then rigorous Arb evaluation).
Library + CLI.  python reopt.py explore | python reopt.py frontier
"""
import sys, os, math, csv, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.optimize import minimize
from decimal import Decimal, ROUND_CEILING
from flint import arb
import belarb as B
from beltables import rows as her_rows

HERE = os.path.dirname(os.path.abspath(__file__))
ZFR_REF = ('cl5.558691', 'ford', 'lw21.233')         # refereed: MTY 2024, Yang JMAA 2024 (1.4) [Ford+HPY], Yang JMAA 2024
ZFR_PRE = ('cl4.896', 'ford', 'lw21.233')            # + Bellotti-Trudgian-Yang arXiv:2603.21490 (audited preprint)

def fmt(xv, nd=7):
    return f"{xv:.{nd}f}"

def make_row(L0, L1, a0, u, x, v, w, lam, zfr):
    return dict(L0=L0, L1=L1, a0=a0, u=fmt(u), x=x if isinstance(x, str) else fmt(x), v=fmt(v), w=fmt(w),
                lam=lam if isinstance(lam, str) else ('1' if lam == 1 else fmt(lam, 4)), zfr=zfr)

def fobj(L0, L1, a0, x, zfr, opt, lam_free, lam_fixed='1'):
    """returns f(p) = log C (float) for p = (log u, log(v/u-1), log w [, log(lam-1)])."""
    def f(p):
        if max(abs(float(t)) for t in p) > 50:
            return 1e9
        u = math.exp(p[0]); v = u * (1 + math.exp(p[1])); w = math.exp(p[2])
        xx = x if x is not None else math.exp(p[-1])
        if lam_free:
            lam = 1 + math.exp(p[3])
            if lam > 30: return 1e9
        else:
            lam = float(lam_fixed)
        if not (u < xx and w < 5 and u > 1e-3):
            return 1e9
        row = dict(L0=L0, L1=L1, a0=a0, u=repr(u), x=repr(xx), v=repr(v), w=repr(w),
                   lam=(repr(lam) if lam_free else lam_fixed), zfr=zfr)
        try:
            p_ = B.row_bound(row, opt, B.FLT, pts=(0.0, 0.5, 1.0))
        except (ValueError, OverflowError, ZeroDivisionError):
            return 1e9
        Cv = p_['C']
        if not (Cv > 0) or Cv == float('inf') or Cv != Cv:
            return 1e9
        return math.log(Cv)
    return f

def optimise(L0, L1, a0, x, zfr, opt, lam_free=True, starts=None, lam_fixed='1', maxiter=4000):
    """x: decimal string (B fixed) or None (x free, then p[-1] = log x)."""
    f = fobj(L0, L1, a0, None if x is None else float(x), zfr, opt, lam_free, lam_fixed)
    best = None
    if starts is None:
        starts = []
    for s in starts:
        r = minimize(f, np.array(s), method='Nelder-Mead', options=dict(maxiter=maxiter, xatol=1e-7, fatol=1e-9))
        r = minimize(f, r.x, method='Nelder-Mead', options=dict(maxiter=maxiter, xatol=1e-8, fatol=1e-10))
        if best is None or r.fun < best.fun:
            best = r
    return best

def params_from_p(p, x, lam_free, lam_fixed='1'):
    u = math.exp(p[0]); v = u * (1 + math.exp(p[1])); w = math.exp(p[2])
    xx = float(x) if x is not None else math.exp(p[-1])
    lam = 1 + math.exp(p[3]) if lam_free else float(lam_fixed)
    return u, v, w, xx, lam

def her_row_for(Lmid):
    R = her_rows()
    for r in R:
        lo = 28.7297 if r['L0'] == 'LOG3E12' else float(r['L0'])
        if lo <= Lmid <= float(r['L1']):
            return r
    return R[-1]

def start_points(hr, lam_free, x_free=False):
    u, v, w = float(hr['u']), float(hr['v']), float(hr['w'])
    base = [math.log(u), math.log(v / u - 1), math.log(w)]
    S = []
    for su in (1.0, 0.9, 1.1):
        for sw in (1.0, 0.7, 1.4):
            p = [base[0] + math.log(su), base[1], base[2] + math.log(sw)]
            if lam_free:
                for lam in (3.0, 6.0):
                    S.append(p + [math.log(lam - 1)])
            else:
                S.append(list(p))
    if x_free:
        S = [s + [math.log(float(hr['x']))] for s in S]
    return S[:6] if lam_free else S[:5]

def explore():
    for (L0, L1) in (('LOG3E12', '29'), ('35', '36'), ('70', '71'), ('80', '82'), ('100', '102'), ('160', '164')):
        Lm = ((28.73 if L0 == "LOG3E12" else float(L0)) + float(L1)) / 2
        hr = her_row_for(Lm)
        a0 = hr['a0']; x = hr['x']
        Cpr = float(hr['Cpr'])
        out = [f"{L0}-{L1} her row {hr['L0']}-{hr['L1']} a0={a0} B={hr['Bpr']} C_pr={Cpr:.4g}"]
        for nm, opt, zfr, lamf in (('corr,lam=1,ref', B.OPT_CORR, ZFR_REF, False), ('impr,lam=1,ref', B.OPT_IMPR, ZFR_REF, False),
                                   ('impr,lam*,ref', B.OPT_IMPR, ZFR_REF, True), ('impr,lam*,pre', B.OPT_IMPR, ZFR_PRE, True)):
            t = time.time()
            r = optimise(L0, L1, a0, x, zfr, opt, lam_free=lamf, starts=start_points(hr, lamf))
            u, v, w, xx, lam = params_from_p(r.x, x, lamf)
            row = make_row(L0, L1, a0, u, x, v, w, lam, zfr)
            pa = B.row_bound(row, opt, B.ARB)
            out.append(f"   {nm:16s} float C={math.exp(r.fun):10.5g} arb C={float(pa['C'].upper()):10.5g} ratio/pr={float(pa['C'].upper())/Cpr:.3f}"
                       f"  u={u:.4f} v={v:.4f} w={w:.4f} lam={lam:.3f} c1={float(pa['c1'].mid()):.3f} c5={float(pa['c5'].mid()):.3f} ({time.time()-t:.1f}s)")
        print("\n".join(out), flush=True)

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'explore':
        explore()
