"""Referee spot-check of the local classical zero-free region (phase1_littlewood/zfr_classical_local.csv).
Independent float/mpmath implementation (from BTY's LaTeX definitions and REPORT §12, NOT importing cl_core):
  * window y from the CSV profile (own code), with T = 16 t + 1e10, MTY 5.558691 above log T > 60;
  * mu range [y v (1-2e-100)/A, y v/A] -> use mu_lo (G increasing);   eta = A/v (the coupled worst case);
  * L14 = a1 F(sigma-1+eta) + a1 F(sigma-eta) - a0 F(sigma-1), F by direct mpmath quadrature of BTY Def. 2;
  * Q = L14 - eta w0 C_UP - 1e-10 eta - 1e-7 - eta^3(P_ERR + Q_ERR v) - KC A  (C_UP, P_ERR, Q_ERR taken from
    cl_constants.json; they were re-derived independently by the first classical reviewer).
Also: eta-monotonicity scan of Q at fixed (mu, v) for eta in [A/(2v), A/v]; a_k >= 0; what Z the inequality
would allow if the window were "uniform Z everywhere" (sensitivity).  Floats: exploration only."""
import json, math, os, csv
import mpmath as mp
mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))
P1 = os.path.join(HERE, '..', 'phase1_littlewood')

th = mp.mpf('1.1338')
tan, cot, sec2 = mp.tan(th), 1 / mp.tan(th), 1 / mp.cos(th) ** 2
d = 2 * th * cot
def w(u):
    return sec2 * (sec2 * (th * cot - u / 2) * mp.cos(u * tan) + 2 * th * cot - u
                   + mp.sin(2 * th - u * tan) / mp.sin(2 * th) - 2 * (1 + mp.sin(th - u * tan) / mp.sin(th)))
w0 = w(0)
kap = [mp.mpf(1), mp.mpf(-851) / 859, mp.mpf(780) / 859, mp.mpf(-525) / 859, mp.mpf(171) / 859, mp.mpf(28) / 859, mp.mpf(-29) / 859]
c = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
a = [mp.mpf(sum(c[j] * c[j + k] for j in range(17 - k)) * (1 if k == 0 else 2)) / 14912370 for k in range(17)]
asum = sum(a[1:]); kaps = sum(kap)
KC = asum * kaps * w0 / 2
cons = json.load(open(os.path.join(P1, 'cl_constants.json')))
def num(s):
    s = s.strip('[]').split('+/-')[0]
    return mp.mpf(s)
C_UP, P_ERR, Q_ERR = num(cons['C_UP']), num(cons['P_ERR']), num(cons['Q_ERR'])
H = mp.mpf(3) * 10 ** 12; T0 = mp.mpf(10) ** 10; ZMTY = mp.mpf('5.558691')

prof = []
with open(os.path.join(P1, 'zfr_classical_local.csv')) as f:
    for row in csv.DictReader(f):
        prof.append((float(row['logt_lo']), float(row['logt_hi']), mp.mpf(row['Z1'])))

def window_y(v):
    logT = mp.log(16 * mp.e ** v + T0)
    cands = []
    for (lo, hi, Z) in prof:
        if lo < logT:
            cands.append(1 / Z / min(mp.mpf(hi), logT))
    if logT > 60:
        cands.append(1 / ZMTY / logT)
    return min(cands), logT

def F(z, eta, sigma):
    dd = 2 * sigma - 1
    def g(x):
        return mp.exp(-z * x / eta) * w(x) * sum(kap[m] * mp.exp(-dd * m * x / eta) for m in range(7))
    pts = [0, mp.mpf('1e-4'), mp.mpf('1e-3'), mp.mpf('1e-2'), mp.mpf('0.05'), mp.mpf('0.2'), mp.mpf('0.5'), d]
    return mp.quad(g, pts)

def Qval(eta, mu, v, A):
    sigma = 1 - mu * eta
    L14 = a[1] * F(sigma - 1 + eta, eta, sigma) + a[1] * F(sigma - eta, eta, sigma) - a[0] * F(sigma - 1, eta, sigma)
    rhs = eta * w0 * C_UP + mp.mpf('1e-10') * eta + mp.mpf('1e-7') + eta ** 3 * (P_ERR + Q_ERR * v) + KC * eta * v
    return L14 - rhs, L14

if __name__ == '__main__':
    print("a_k >= 0 for all k:", all(x >= 0 for x in a), " a0 =", float(a[0]), " a1 =", float(a[1]), " a =", float(asum))
    print("KC =", float(KC), " w(0) =", float(w0))
    bands = [0, 4, 7, 30, 31, 52, 66, 76, 77]
    print("\nSpot check of (CL) at band endpoints / middles (relative margin Q/(KC A)):")
    for bi in bands:
        lo, hi, Z = prof[bi]
        A = 1 / Z
        for v in (max(lo, float(mp.log(H))) + 1e-9, (lo + hi) / 2, hi):
            v = mp.mpf(v)
            y, logT = window_y(v)
            y = min(y, A / v)
            mu = y * v / A
            q, L14 = Qval(A / v, mu, v, A)
            print(f"  band ({lo},{hi}] Z={float(Z):.3f}  v={float(v):.4f}  logT={float(logT):.3f}  y*logT={float(y*logT):.5f}"
                  f"  mu={float(mu):.5f}  L14={float(L14):.7f}  Q/(KC A)={float(q/(KC*A)):.3e}", flush=True)
    print("\neta-monotonicity at fixed (mu, v) (band 0, v = 28.75):")
    lo, hi, Z = prof[0]; A = 1 / Z; v = mp.mpf('28.75')
    y, _ = window_y(v); mu = y * v / A
    prev = None
    for f in (0.5, 0.6, 0.7, 0.8, 0.9, 0.95, 1.0):
        q, _ = Qval(f * A / v, mu, v, A)
        print(f"  eta = {f:.2f} A/v: Q = {float(q):.6e}" + ("" if prev is None else f"   (dQ < 0: {q < prev})"))
        prev = q
    print("\nsensitivity: smallest Z at v = 28.75 if the window used the SAME Z everywhere up to log T (bisection):")
    def margin_uniform(Zt, v):
        A = 1 / Zt; logT = mp.log(16 * mp.e ** v + T0)
        y = min(A / logT, A / v); mu = y * v / A
        return Qval(A / v, mu, v, A)[0]
    lo_, hi_ = mp.mpf('4.55'), mp.mpf('4.70')
    for _ in range(20):
        mid = (lo_ + hi_) / 2
        if margin_uniform(mid, v) > 0: hi_ = mid
        else: lo_ = mid
    print(f"  Z_uniform(28.75) ~ {float(hi_):.4f}  (CSV, with the rising profile in the window: 4.614)")
