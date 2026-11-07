"""FLOAT exploration (not rigorous): effect of candidate round-2 lemmas on C*e^{B/Z1} at low heights,
using Phase 0's v2 evaluator (belarb.piece_v2, FLT mode) with monkeypatches.

variants:
  base   : Phase 0 v2 as is (lemA, lemB, lemC)
  lemD   : |M(1/2+it)| <= K_D (VW)^{1/2},  K_D = 4 c^2 P* (1-(U/V)^{1/2})(1-W^{-1/2})/(Delta log W)
           instead of D2VW (VW)^{1/2}, D2VW ~ sum_{n<=VW} d(n)^2/n  (Phase-0/Bellotti (3.11))
  smoothX: X-side smoothing of the weight over log-width H (item 4): detector X_eff = X e^{-H}
           (cost), band terms of the X-part multiplied by |nu_hat(a)| (gain)
"""
import sys, os, math, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
P0 = os.path.join(HERE, '..', '..', 'phase0_bellotti')
sys.path.insert(0, P0); sys.path.insert(0, os.path.join(HERE, '..'))
import numpy as np
from scipy.optimize import minimize
import belarb as B
import improvements as P2
from flint import ctx
ctx.prec = 128

Z1 = 4.62
CTX = {}
_orig_D2 = B._D2fixed
C2P = 4 * 1.32964 ** 2 * 1.47228

def D2_patched(lY, N):
    if CTX.get('lemD'):
        u, v, w, L = CTX['u'], CTX['v'], CTX['w'], CTX['L']
        D = (v - u) * L; lW = w * L
        return C2P * (1 - math.exp(-D / 2)) * (1 - math.exp(-lW / 2)) / (D * lW)
    return _orig_D2(lY, N)
B._D2fixed = D2_patched

# --- band-sum hook for X-side smoothing: per-pair b(d) multiplied by |nu_hat(d * lam * nu)| on the X part
_orig_Hn = B.Hn_general
_S = np.linspace(0, 1, 801)
_DENS = _S ** 3 * (1 - _S) ** 3; _DENS /= np.trapezoid(_DENS, _S)
_XI = np.linspace(0, 400, 40001)
_NH = np.array([abs(np.trapezoid(_DENS * np.exp(1j * xi * _S), _S)) for xi in _XI])
_NH = np.maximum.accumulate(_NH[::-1])[::-1]      # monotone (non-increasing) majorant
def nu_hat(a, H):
    """|hat nu(a)| for nu = H * Beta(4,4) (smooth bump on [0,H]); monotone majorant, float."""
    if H <= 0:
        return 1.0
    xi = a * H
    return float(_NH[min(len(_NH) - 1, int(xi / 0.01))]) if xi < 400 else float(_NH[-1])

def Hn_patched(a, b, J1, far, N):
    H = CTX.get('H')
    if H is None:
        return _orig_Hn(a, b, J1, far, N)
    lamnu = CTX['lam'] * CTX['nu']; epsY = CTX['epsY']
    half = 0.5
    def bb(d):   # per-pair numerator at normalised distance d (in box heights): X part damped, Y part not
        return b / (1 + epsY) * (min(1.0, nu_hat(d * lamnu, H) + 2 * CTX['delta'] * H / 2) + epsY)
    def m(d):
        return a if d == 0 else min(a, bb(d) / d)
    tot = a
    for j in range(1, J1 + 1):
        tot += m(j - 1) + m(j - half) if j > 1 else (a + bb(0.5) / 0.5 if False else m(0) + m(half))
    return tot + far
B.Hn_general = Hn_patched

_cf = {}
def cf(a0, zfr, L0, L1, lam):
    key = (a0, zfr, L0, L1, lam)
    if key not in _cf:
        try:
            _cf[key] = float(P2.cf_upper(float(a0), lambda L: B.nu(zfr, L, B.ARB), float(L0), float(L1), hfac=lam).upper())
        except AssertionError:
            _cf[key] = None
    return _cf[key]

def evalC(L0s, L1s, a0, u, v, w, x, lam, zfr, lemD=False, H=None):
    L0 = 28.7296 if L0s == 'LOG3E12' else float(L0s)
    cfv = cf(a0, zfr, L0, float(L1s), lam)
    if cfv is None:
        return float('inf')
    if u * L0 < 26 or (v - u) * L0 < 14.5 or not (u < x and w < 3):
        return float('inf')
    # X-side smoothing: detector sees X e^{-H} -> equivalent to x_det = x - H/L in c1 (approx: use L0)
    row = dict(L0=L0s, L1=L1s, a0=a0, u=repr(u), x=repr(x), v=repr(v), w=repr(w), lam=lam, zfr=zfr,
               lems='lemA,lemB,lemC', d4A=repr(max(P2.d4_model(u, v, x, L0), P2.d4_model(u, v, x, float(L1s)))), cfB=repr(cfv))
    worst = 0
    for f in (0.0, 0.5, 1.0):
        L = L0 + (float(L1s) - L0) * f
        CTX.update(lemD=lemD, u=u, v=v, w=w, L=L, H=H, lam=float(lam), nu=float(B.nuL(zfr, L, B.FLT)) / L,
                   delta=float(B.nuL(zfr, L, B.FLT)) / L, epsY=math.exp(-2 * (x - u) * B.nuL(zfr, L, B.FLT) - 4 * B.nuL(zfr, L, B.FLT) * math.log(L) / L))
        Cc = B.consts_N(row, B.FLT)
        if H is not None and H > 0:
            # detector with X_eff = X e^{-H}: evaluate c1 with x - H/L, rest with x
            rowd = dict(row, x=repr(x - H / L))
            pd = B.piece(rowd, B.OPT_V2, L, B.FLT, Cc)
            p = B.piece(row, B.OPT_V2, L, B.FLT, Cc)
            c1 = pd['c1']; den = c1 * c1 - p['c5']
            if c1 <= 0 or den <= 0:
                return float('inf')
            Cv = p['A'] * p['cf'] / den * (1 + 1e-12)
        else:
            p = B.piece(row, B.OPT_V2, L, B.FLT, Cc)
            if p['c1'] <= 0 or p['den'] <= 0:
                return float('inf')
            Cv = p['C']
        worst = max(worst, Cv)
    return worst

def optimise(L0s, L1s, a0, zfr, lam, lemD=False, H=None, start=None):
    def f(p):
        u = math.exp(p[0]); v = u * (1 + math.exp(p[1])); w = math.exp(p[2]); x = math.exp(p[3])
        try:
            Cv = evalC(L0s, L1s, a0, u, v, w, x, lam, zfr, lemD, H)
        except (ValueError, OverflowError, ZeroDivisionError):
            return 1e9
        if not (Cv < 1e300):
            return 1e9
        return math.log(Cv) + 2 * x / Z1
    best = None
    starts = [start] if start else []
    starts += [[math.log(2.5), math.log(0.7), math.log(0.72), math.log(7.08)],
               [math.log(2.0), math.log(0.6), math.log(0.6), math.log(6.0)],
               [math.log(1.6), math.log(0.5), math.log(0.45), math.log(4.8)],
               [math.log(2.2), math.log(0.9), math.log(0.9), math.log(6.0)]]
    for s in starts:
        if f(s) >= 1e8:
            continue
        r = minimize(f, np.array(s), method='Nelder-Mead', options=dict(maxiter=3000, xatol=1e-7, fatol=1e-9))
        r = minimize(f, r.x, method='Nelder-Mead', options=dict(maxiter=3000, xatol=1e-8, fatol=1e-10))
        if best is None or r.fun < best.fun:
            best = r
    if best is None:
        return None
    u = math.exp(best.x[0]); v = u * (1 + math.exp(best.x[1])); w = math.exp(best.x[2]); x = math.exp(best.x[3])
    C = evalC(L0s, L1s, a0, u, v, w, x, lam, zfr, lemD, H)
    return dict(obj=best.fun, C=C, B=2 * x, u=u, v=v, w=w, x=x, lam=lam, CeBZ=C * math.exp(2 * x / Z1))

if __name__ == '__main__':
    ZFR = ('cl4.896', 'ford', 'lw21.233')
    rowsel = [a for a in sys.argv[1:]] or ['LOG3E12:29', '35:36', '40:41']
    VARS = (dict(lemD=False), dict(lemD=True), dict(lemD=False, H=0.0), dict(lemD=False, H=3.0), dict(lemD=False, H=10.0), dict(lemD=True, H=0.0), dict(lemD=True, H=3.0), dict(lemD=True, H=10.0))
    for rs in rowsel:
        L0s, L1s = rs.split(':')
        for a0 in ('0.9927', '0.98'):
            for var in VARS:
                best = None
                for lam in ('1', '4', '8', '14', '18'):
                    r = optimise(L0s, L1s, a0, ZFR, lam, **var)
                    if r and (best is None or r['obj'] < best['obj']):
                        best = r
                if best:
                    print(f"[{L0s},{L1s}] a0={a0} {str(var):32s} C={best['C']:9.2f} B={best['B']:7.3f} lam={best['lam']:>3} "
                          f"C*e^(B/{Z1})={best['CeBZ']:10.1f}  u={best['u']:.3f} v={best['v']:.3f} w={best['w']:.3f}", flush=True)
