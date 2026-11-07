"""Numerical sanity checks (not proofs) of the analytic identities/bounds the certificate rests on, tested directly
against zeta (mpmath).  Independent of zl_core.py except where stated.

 1. Ford's two-line zero detector (thesis Lemma 3.3 / (3.4)) for f = zeta: fixes the 1/(4 lambda) factor and the
    2 lambda i u / pi scaling that the main term B = (1/2lambda)[...] relies on.
 2. Kadiri's explicit formula (thesis Lemma 2.6 / (3.3)) at a real and a complex point, with E(s) as defined in
    thesis Lemma 3.4 -- fixes the Gamma term (1/2)(psi(s/2+1) - log pi) used for the Q(sigma*) gain and the form of E.
 3. |Re psi(1/4 + i y/2)| <= log(|y|/2 + 4) + 10/3  (dense grid + large-y asymptotics).
 4. Ford's W0 bound |W0(z)| <= C(nu, r)|z|^-3 at the parameters actually used (nu = -1, r = lambda/eta ~ 40..160; and
    nu = r = x0/eta for the E-terms), by direct numerical Laplace transform.
 5. (3.42): Re F*(z) >= -C(0,nu) eta^3/lambda^3 on the half disc |z| <= lambda, Re z >= 0.
Run:  python -I check_formulas.py > check_formulas_output.txt
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


ZEROS = [mp.zetazero(n).imag for n in range(1, 401)]
print("first zero", mp.nstr(ZEROS[0], 10), " 400th:", mp.nstr(ZEROS[-1], 8))

# ---------------------------------------------------------------- 1. Ford's detector
print("\n1. Ford two-line detector for zeta (thesis (3.4))")
for (sig, t, lam) in [(0.9, 30, 0.45), (0.9, 30, 0.3), (0.95, 50, 0.41)]:
    sig, t, lam = mp.mpf(sig), mp.mpf(t), mp.mpf(lam)
    s = mp.mpc(sig, t)
    lhs = -mp.re(mp.zeta(s, derivative=1) / mp.zeta(s))
    zsum = 0
    for g in ZEROS:
        for gg in (g, -g):
            rho = mp.mpc(0.5, gg)
            if abs(mp.re(s - rho)) <= lam:
                zsum += mp.re(mp.cot(mp.pi * (s - rho) / (2 * lam)))
    pole = mp.re(mp.cot(mp.pi * (s - 1) / (2 * lam)))
    integ = mp.quad(lambda u: (mp.log(abs(mp.zeta(s - lam + 2 * lam * 1j * u / mp.pi)))
                               - mp.log(abs(mp.zeta(s + lam + 2 * lam * 1j * u / mp.pi)))) / mp.cosh(u) ** 2,
                    mp.linspace(-25, 25, 101))
    rhs = -mp.pi / (2 * lam) * zsum + mp.pi / (2 * lam) * pole + integ / (4 * lam)
    print(f"  s = {sig}+{t}i, lam = {lam}:  -Re zeta'/zeta = {mp.nstr(lhs, 12)}   RHS = {mp.nstr(rhs, 12)}   diff = {mp.nstr(lhs - rhs, 3)}")

# ---------------------------------------------------------------- 2. Kadiri explicit formula
print("\n2. Explicit formula (3.3)/(Lemma 2.6) with E(s) of Lemma 3.4, f(u) = eta w(eta u)")


def von_mangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0:
                m //= p
            return mp.log(p) if m == 1 else mp.mpf(0)
    return mp.mpf(0)


def explicit_check(s, eta):
    F = lambda z: W(z / eta)
    F0 = lambda z: W0(z / eta)
    N = int(mp.floor(mp.exp(d / eta)))
    lhs = mp.re(sum(von_mangoldt(n) * mp.mpf(n) ** (-s) * eta * w(eta * mp.log(n)) for n in range(2, N + 1)))
    zs = 0
    for g in ZEROS:
        for gg in (g, -g):
            zs += mp.re(F0(s - mp.mpc(0.5, gg)))
    # tail of sum Re F0(s-rho) beyond the 400th zero: F0(z) ~ w''(0) eta^3 / z^3 with w''(0) < 0; |tail| <~ 46 eta^3 sum gamma^-3
    G400 = ZEROS[-1]
    tail = 46 * eta ** 3 * 2 * mp.log(G400 / (2 * mp.pi)) / (4 * mp.pi * G400 ** 2)
    Eint = mp.quad(lambda y: F0(s - mp.mpc(0.5, y)) * mp.re(mp.digamma(mp.mpc(0.25, y / 2))),
                   [-mp.inf, -200, -50, -10, 0, 10, 50, 200, mp.inf] if mp.im(s) == 0 else
                   [-mp.inf, -200, -50, 0, mp.im(s) - 10, mp.im(s), mp.im(s) + 10, 200, mp.inf]) / (2 * mp.pi)
    E = mp.re(Eint) + mp.re(F0(s))
    main = -eta * w0 * mp.re(mp.zeta(s, derivative=1) / mp.zeta(s))
    rhs = main + mp.re(F0(s - 1)) - zs + E
    # Lemma 2.6 form at real s: f(0)(1/2)(psi(s/2+1) - log pi) + F(s-1) - sum Re F(s-rho) + E
    if mp.im(s) == 0:
        zsF = sum(mp.re(F(s - mp.mpc(0.5, gg))) for g in ZEROS for gg in (g, -g))
        tailF = eta * w0 * (s - 0.5) * 2 * mp.log(G400 / (2 * mp.pi)) / (2 * mp.pi * G400)
        rhs2 = eta * w0 * (mp.digamma(s / 2 + 1) - mp.log(mp.pi)) / 2 + F(s - 1) - zsF + E
        print(f"  s = {mp.nstr(s, 4)}, eta = {eta}: LHS = {mp.nstr(lhs, 12)}  (3.3) RHS = {mp.nstr(rhs, 12)} (tail <~ {mp.nstr(tail, 2)})"
              f"  Lemma 2.6 RHS = {mp.nstr(rhs2, 10)} (zero-sum tail ~ -{mp.nstr(tailF, 3)})  |E| = {mp.nstr(abs(E), 4)}")
    else:
        print(f"  s = {mp.nstr(s, 4)}, eta = {eta}: LHS = {mp.nstr(lhs, 12)}  (3.3) RHS = {mp.nstr(rhs, 12)}  diff = {mp.nstr(lhs - rhs, 3)}"
              f" (tail <~ {mp.nstr(tail, 2)})  |E| = {mp.nstr(abs(E), 4)}")


explicit_check(mp.mpf('0.9'), mp.mpf('0.3'))
explicit_check(mp.mpc('0.9', '30'), mp.mpf('0.3'))

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
