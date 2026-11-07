"""Ford's W0 bound |W0(z)| <= C(nu, r)|z|^-3 (thesis Lemma 2.3 with corrected c0) in the v2 regime of LARGE r:
zero sums use C(-1, nu) with nu = lambda/eta ~ 1.4e3 .. 7e3 (v1: <= 282); E-terms use C(x0/eta, x0/eta) ~ 1e6.
W0(z) = W(z) - w(0)/z is evaluated by the convergent integration-by-parts series
    W0(z) = sum_{j>=2} (w^(j)(0) - e^{-zd} w^(j)(d)) / z^{j+1}   (w(d) = w'(d) = w''(d) = w'(0) = 0),
with the derivatives of w computed in closed form (w is a trig/linear combination).  50 digits.
Also prints the identities c0*c3 = |w''(0)| and c0*c2 = w'''(0) (the bound is asymptotically tight)."""
import os
from mpmath import mp, mpf, mpc
mp.dps = 50
th = mpf('1.1272')
tn, sn, cs = mp.tan(th), mp.sin(th), mp.cos(th)
S = 1 / cs ** 2
d = 2 * th / tn
c0 = 1 / (sn * cs ** 3); c1 = (th - sn * cs) * tn ** 4; c2 = tn ** 3 * sn ** 2; c3 = (th - sn * cs) * tn ** 2


def C(nu, r):
    return c0 * r * (c2 * (r + 1) ** 2 * (mp.exp(-2 * nu * th / tn) + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - tn ** 2) ** 2


def wder(j, u):
    """j-th derivative of w(u) = S*( S*(a - u/2) cos(u tn) + 2a - u + sin(2th - u tn)/sin(2th) - 2 - 2 sin(th - u tn)/sin th )"""
    a = th / tn
    # derivative of (a - u/2) cos(u tn): Leibniz
    def cosd(k):  # k-th derivative of cos(u tn)
        return tn ** k * mp.cos(u * tn + k * mp.pi / 2)
    p1 = (a - u / 2) * cosd(j) + (j * (-mpf(1) / 2) * cosd(j - 1) if j >= 1 else 0)
    lin = (2 * a - u) if j == 0 else (-1 if j == 1 else 0)
    s2 = (-tn) ** j * mp.sin(2 * th - u * tn + j * mp.pi / 2) / mp.sin(2 * th)
    s1 = -2 * (-tn) ** j * mp.sin(th - u * tn + j * mp.pi / 2) / sn
    const = -2 if j == 0 else 0
    return S * (S * p1 + lin + s2 + s1 + const)


D0 = [wder(j, mpf(0)) for j in range(0, 400)]
DD = [wder(j, d) for j in range(0, 400)]
out = []
out.append(f"w(0)={mp.nstr(D0[0], 15)} w'(0)={mp.nstr(D0[1], 5)} w(d)={mp.nstr(DD[0], 5)} w'(d)={mp.nstr(DD[1], 5)} w''(d)={mp.nstr(DD[2], 5)}")
out.append(f"w''(0)={mp.nstr(D0[2], 20)}  c0*c3={mp.nstr(c0 * c3, 20)}   w'''(0)={mp.nstr(D0[3], 20)}  c0*c2={mp.nstr(c0 * c2, 20)}  w'''(d)={mp.nstr(DD[3], 20)}")


def W0(z):
    tot = mpc(0)
    ezd = mp.exp(-z * d)
    zp = z ** 3
    for j in range(2, 400):
        term = (D0[j] - ezd * DD[j]) / zp
        tot += term
        zp *= z
        if j > 20 and abs(term) < mpf(10) ** -45 * abs(tot):
            break
    return tot


# cross-check the series against direct quadrature at a moderate |z|
def w_direct(u):
    return S * (S * (th / tn - u / 2) * mp.cos(u * tn) + 2 * th / tn - u + mp.sin(2 * th - u * tn) / mp.sin(2 * th)
                - 2 * (1 + mp.sin(th - u * tn) / sn))


z = mpc(-1, 40)
Wq = mp.quad(lambda u: mp.exp(-z * u) * w_direct(u), mp.linspace(0, d, 41)) - D0[0] / z
out.append(f"series vs quadrature at z=-1+40i: {mp.nstr(W0(z), 15)} vs {mp.nstr(Wq, 15)}")

for nu, r in [(-1, 1400), (-1, 3000), (-1, 7000), (-1, 20000), (-1, 1e5)]:
    r = mpf(r)
    best = 0
    # |z| >= r with Re z >= -1: scan Re z in {-1, -0.5, 0, 1, 5, r/2^.5} and |z| in [r, r + 3 periods]
    period = 2 * mp.pi / d
    for x in [mpf(-1), mpf('-0.5'), mpf(0), mpf(1), mpf(5)]:
        y0 = mp.sqrt(r ** 2 - x ** 2)
        for q in range(0, 1201):
            y = y0 + period * 3 * q / 1200
            for sgn in (1, -1):
                zz = mpc(x, sgn * y)
                ratio = abs(zz) ** 3 * abs(W0(zz)) / C(mpf(nu), r)
                best = max(best, ratio)
    for ang in range(0, 91, 5):
        zz = r * mp.expjpi(mpf(ang) / 180)
        best = max(best, abs(zz) ** 3 * abs(W0(zz)) / C(mpf(nu), r))
    out.append(f"nu={nu}, r={mp.nstr(r, 6)}: max |z|^3|W0(z)|/C(nu,r) = {mp.nstr(best, 10)}  (predicted ~ 1 - 2.31/r = {mp.nstr(1 - mpf('2.31') / r, 10)})")
for rr in [1e5, 1e6, 3e6]:
    r = mpf(rr)
    best = 0
    for ang in range(0, 91, 3):
        zz = r * mp.expjpi(mpf(ang) / 180)
        if zz.real < r * mpf('0.999999'):
            continue
        best = max(best, abs(zz) ** 3 * abs(W0(zz)) / C(r, r))
    zz = mpc(r, 0)
    best = max(best, abs(zz) ** 3 * abs(W0(zz)) / C(r, r))
    for q in range(200):
        zz = mpc(r, r * mpf(q) / 50)
        best = max(best, abs(zz) ** 3 * abs(W0(zz)) / C(r, r))
    out.append(f"nu=r={mp.nstr(r, 6)} (E-terms, Re z >= r): max ratio = {mp.nstr(best, 10)}")
txt = "\n".join(out)
print(txt)
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ford_large_r_output.txt'), 'w').write(txt + "\n")
