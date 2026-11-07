"""Checks 3-5 of check_formulas.py run on their own (same code; split off because check 2 at complex s is slow).
Run:  python -I check_formulas_345.py > check_formulas_345_output.txt
"""

import mpmath as mp

mp.mp.dps = 20
th = mp.mpf('1.1272'); tn, sn, cs = mp.tan(th), mp.sin(th), mp.cos(th); d = 2 * th / tn


def w(u):
    s2 = 1 / cs ** 2
    return s2 * (s2 * (th / tn - u / 2) * mp.cos(u * tn) + 2 * th / tn - u
                 + mp.sin(2 * th - u * tn) / mp.sin(2 * th) - 2 * (1 + mp.sin(th - u * tn) / sn))


w0 = w(0)


WD0 = [mp.diff(w, 0, j) for j in range(8)]
WDd = [mp.diff(w, d, j) for j in range(8)]
assert abs(WD0[1]) < 1e-12 and abs(WDd[0]) < 1e-12 and abs(WDd[1]) < 1e-12 and abs(WDd[2]) < 1e-10


def W(z):
    z = mp.mpc(z)
    if abs(z) <= 150:
        m = max(4, int(abs(mp.im(z)) * d / 2) + 4)
        return mp.quad(lambda u: mp.exp(-z * u) * w(u), mp.linspace(0, d, m))
    # repeated integration by parts: W(z) = sum_j (w^(j)(0) - e^{-zd} w^(j)(d)) / z^(j+1)  (asymptotic, |z| > 150)
    return sum((WD0[j] - mp.exp(-z * d) * WDd[j]) / z ** (j + 1) for j in range(8))


def W0(z):
    return W(z) - w0 / z


for ztest in [mp.mpc(-1, 149.9), mp.mpc(2, 149.9)]:     # continuity of the two branches at |z| ~ 150
    zq = ztest; za = ztest * (150.01 / abs(ztest))
    print("W0 branch check:", mp.nstr(W0(zq) * zq ** 3, 10), mp.nstr(W0(za) * za ** 3, 10))


def Cford(nu, r):
    c0 = 1 / (sn * cs ** 3); c1 = (th - sn * cs) * tn ** 4; c2 = tn ** 3 * sn ** 2; c3 = (th - sn * cs) * tn ** 2
    return c0 * r * (c2 * (r + 1) ** 2 * (mp.exp(-2 * nu * th / tn) + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - tn ** 2) ** 2


# ---------------------------------------------------------------- 3. digamma bound
print("\n3. |Re psi(1/4 + iy/2)| <= log(|y|/2+4) + 10/3")
worst = mp.inf
for j in range(0, 20001):
    y = mp.mpf(j) / 100                       # y in [0, 200], step 0.01
    p = mp.re(mp.digamma(mp.mpc(0.25, y / 2)))
    worst = min(worst, mp.log(y / 2 + 4) + mp.mpf(10) / 3 - abs(p))
for e in range(3, 40):
    y = mp.mpf(10) ** e / 5
    p = mp.re(mp.digamma(mp.mpc(0.25, y / 2)))
    worst = min(worst, mp.log(y / 2 + 4) + mp.mpf(10) / 3 - abs(p))
print("  min slack over y in [0,200] (step 0.01) and y = 2*10^(3..39):", mp.nstr(worst, 6), "(attained at y = 0)")

# ---------------------------------------------------------------- 4. Ford W0 bound at the parameters used
print("\n4. |W0(z)||z|^3 / C(nu, r) at the parameters used (must be < 1)")
for (nu, r) in [(-1, 40), (-1, 60), (-1, 90), (-1, 160), (0, 60)]:
    nu, r = mp.mpf(nu), mp.mpf(r)
    C = Cford(nu, r)
    mx = 0
    # boundary and interior points of {Re z >= nu, |z| >= r}: Re z = nu line, circle |z| = r, and far points
    pts = [mp.mpc(nu, mp.sqrt(R ** 2 - nu ** 2)) for R in [r, r * 1.02, r * 1.1, r * 1.5, 2 * r, 5 * r]]
    pts += [r * mp.expj(phi) for phi in mp.linspace(-mp.acos(max(-1, nu / r)) + 1e-9, 0, 25)]
    for z in pts:
        if mp.re(z) < nu - 1e-12 or abs(z) < r - 1e-9:
            continue
        mx = max(mx, abs(W0(z)) * abs(z) ** 3 / C)
    print(f"  nu = {nu}, r = {r}: C = {mp.nstr(C, 8)}, max ratio = {mp.nstr(mx, 6)}")

# ---------------------------------------------------------------- 5. (3.42) on the half disc
print("\n5. (3.42): min over half-disc boundary of Re F*(z) / (eta^3/lam^3) vs -C(0, lam/eta)")
for (lam, eta) in [(mp.mpf('0.494'), mp.mpf('0.006')), (mp.mpf('0.27'), mp.mpf('0.0016'))]:
    nu = lam / eta
    def Fstar(z):
        return W(z / eta) + eta * w0 * (mp.pi / (2 * lam) * mp.cot(mp.pi * z / (2 * lam)) - 1 / z)
    mn = mp.inf
    for phi in mp.linspace(-mp.pi / 2 + 1e-6, mp.pi / 2 - 1e-6, 61):
        mn = min(mn, mp.re(Fstar(lam * mp.expj(phi))))
    for yv in mp.linspace(-lam, lam, 41):
        if abs(yv) > 1e-9:
            mn = min(mn, mp.re(Fstar(mp.mpc(0, yv))))
    print(f"  lam = {lam}, eta = {eta}: min Re F* = {mp.nstr(mn, 6)},  -C(0,nu) eta^3/lam^3 = {mp.nstr(-Cford(0, nu) * eta ** 3 / lam ** 3, 6)}")
