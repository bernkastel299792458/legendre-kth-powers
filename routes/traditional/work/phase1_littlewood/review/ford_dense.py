"""Dense check of Ford's |W0(z)| <= C(-1, r)|z|^-3 on the worst line Re z = -1 for the r actually used (nu = lambda/eta_max
ranges over ~ 80..290 in the certificate).  W0 by the (convergent, ratio ~ tan(theta)/|z|; used for |z| > 30, checked against quadrature at |z| = 90..300 to 1e-10) integration-by-parts series.
Run:  python -I ford_dense.py > ford_dense_output.txt"""
import mpmath as mp
mp.mp.dps = 25
th = mp.mpf('1.1272'); tn, sn, cs = mp.tan(th), mp.sin(th), mp.cos(th); d = 2 * th / tn
def w(u):
    s2 = 1 / cs ** 2
    return s2 * (s2 * (th / tn - u / 2) * mp.cos(u * tn) + 2 * th / tn - u + mp.sin(2 * th - u * tn) / mp.sin(2 * th) - 2 * (1 + mp.sin(th - u * tn) / sn))
w0 = w(0)
WD0 = [mp.diff(w, 0, j) for j in range(12)]; WDd = [mp.diff(w, d, j) for j in range(12)]
def W0(z):
    if abs(z) <= 30:
        m = max(4, int(abs(mp.im(z)) * d / 2) + 4)
        return mp.quad(lambda u: mp.exp(-z * u) * w(u), mp.linspace(0, d, m)) - w0 / z
    return sum((WD0[j] - mp.exp(-z * d) * WDd[j]) / z ** (j + 1) for j in range(1, 12)) - 0  # j = 0 term is w(0)/z, removed by W0
def C(nu, r):
    c0 = 1 / (sn * cs ** 3); c1 = (th - sn * cs) * tn ** 4; c2 = tn ** 3 * sn ** 2; c3 = (th - sn * cs) * tn ** 2
    return c0 * r * (c2 * (r + 1) ** 2 * (mp.exp(-2 * nu * th / tn) + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - tn ** 2) ** 2
for r in [80, 100, 140, 200, 282]:
    r = mp.mpf(r); Cr = C(-1, r); mx = (0, None)
    for j in range(4001):                       # |Im z| from ~r to 3r on Re z = -1, step ~ r/2000 (<< period 2 pi/d = 5.9)
        Y = mp.sqrt(r ** 2 - 1) + 2 * r * j / 4000
        z = mp.mpc(-1, Y)
        q = abs(W0(z)) * abs(z) ** 3 / Cr
        if q > mx[0]: mx = (q, Y)
    print(f"r = {r}: C(-1,r) = {mp.nstr(Cr, 8)}  max |z^3 W0|/C on Re z=-1, |z| in [r,3r]: {mp.nstr(mx[0], 6)} at Im z = {mp.nstr(mx[1], 6)}", flush=True)
