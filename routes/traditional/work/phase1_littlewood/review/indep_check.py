"""Independent re-implementation (mpmath, point evaluation) of the final inequality
       eta*Psi < G(mu)
of the height-dependent Littlewood argument, written from the thesis (Yang 2025, Ch. 3) and the review's own
re-derivation, NOT from zl_core.py.  Used only to cross-check zl_core.cell_terms; not itself rigorous.

Run:  python -I indep_check.py > indep_check_output.txt
"""
import os, sys, json
import mpmath as mp

mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))
PL = os.path.dirname(HERE)

# ---------------- polynomial (thesis §2.4: c_0..c_16, P = |sum c_j e^{ijx}|^2 / 14912370)
c = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
Dn = sum(x * x for x in c)
assert Dn == 14912370
a = [mp.mpf(sum(c[j] * c[j + k] for j in range(17 - k)) * (1 if k == 0 else 2)) / Dn for k in range(17)]

th = mp.mpf('1.1272')
tn, sn, cs = mp.tan(th), mp.sin(th), mp.cos(th)
d = 2 * th / tn


def w(u):
    s2 = 1 / cs ** 2
    return s2 * (s2 * (th / tn - u / 2) * mp.cos(u * tn) + 2 * th / tn - u
                 + mp.sin(2 * th - u * tn) / mp.sin(2 * th) - 2 * (1 + mp.sin(th - u * tn) / sn))


w0 = w(mp.mpf(0))


def G_quad(mu):
    return mp.quad(lambda u: mp.exp(mu * u) * (a[1] * mp.exp(-u) - a[0]) * w(u), [0, d / 2, d])


# moments c_n = int u^n (a1 e^-u - a0) w(u) du;  G(mu) = sum_n c_n mu^n / n!  (|u| <= 1.072, |mu| <= 1: 40 terms ample)
_CN = [mp.quad(lambda u, n=n: u ** n * (a[1] * mp.exp(-u) - a[0]) * w(u), [0, d / 2, d]) for n in range(40)]


def G(mu):
    return mp.fsum(_CN[n] * mp.mpf(mu) ** n / mp.factorial(n) for n in range(40))


assert abs(G(mp.mpf('0.93')) - G_quad(mp.mpf('0.93'))) < mp.mpf('1e-25')


def Cford(nu, r):
    c0 = 1 / (sn * cs ** 3)
    c1 = (th - sn * cs) * tn ** 4
    c2 = tn ** 3 * sn ** 2
    c3 = (th - sn * cs) * tn ** 2
    assert r > tn
    return c0 * r * (c2 * (r + 1) ** 2 * (mp.exp(-2 * nu * th / tn) + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - tn ** 2) ** 2


def R0(LT):
    return mp.mpf('0.137') * LT + mp.mpf('0.443') * mp.log(LT) + mp.mpf('1.588')


def Mstrip(LT):   # zeros with |gamma - T| <= 1
    return (LT - mp.log(2 * mp.pi)) / mp.pi + 2 * R0(LT) + mp.mpf('1e-9')


def Sfar(LT):     # sum_{|gamma-T|>1} |gamma-T|^-3
    return (LT - mp.log(2 * mp.pi)) / (2 * mp.pi) + 4 * R0(LT) + mp.mpf('1e-9')


LINES = {3: (mp.mpf(1) / 2, mp.mpf('0.618'), mp.mpf(1) / 6)}
for n in range(4, 7):
    LINES[n] = (1 - mp.mpf(n) / (2 ** n - 2), mp.mpf('1.546'), mp.mpf(1) / (2 ** n - 2))

T0 = mp.mpf(10) ** 10
KAPPA = (mp.log(mp.pi) - mp.digamma(mp.mpf(3) / 2)) / 2


def terms(v, Z, Zw, n):
    """All terms at the single height log t = v (s = 1 worst case), band constant Z, window constant Zw."""
    v = mp.mpf(v); Z = mp.mpf(Z); Zw = mp.mpf(Zw)
    ell = mp.log(v) / v
    LK = v + mp.log(16 + T0 * mp.exp(-v))
    ellK = mp.log(LK) / LK
    y = ellK / Zw
    sig = 1 - y
    sn_, X, Y = LINES[n]
    lam = sig - sn_
    if not (lam < 0.5 and lam > y and sig > 0.75):
        return None
    eta = ell / Z
    mu = y / eta
    # main term: (1/2lam)[sum_{k>=1} a_k (log X + Y log kt + log log kt) + a0 log zeta(sig+lam)], log zeta(1+x) <= g x - log x
    x = sig + lam - 1
    S = sum(a[k] * (mp.log(X) + Y * (v + mp.log(k)) + mp.log(v + mp.log(k))) for k in range(1, 17))
    B = (S + a[0] * (mp.euler * x - mp.log(x))) / (2 * lam)
    # zero sums
    nu = lam / eta
    J = (lam ** -3 + (2 * sig - 1 - lam) ** -3) / 2
    zs = sum(a[k] * (J * Mstrip(v + mp.log(k)) + Sfar(v + mp.log(k))) for k in range(1, 17))
    zero = Cford(-1, nu) * eta ** 3 * zs
    # E terms
    x0 = sig - mp.mpf(1) / 2
    CE = Cford(x0 / eta, x0 / eta)

    def Eb(LT):
        if LT is None:
            main = 2 / x0 ** 2 * (mp.log(4) + mp.mpf(10) / 3) + 2 / (8 * x0)
        else:
            T = mp.exp(LT)
            main = 2 / x0 ** 2 * (mp.log(T / 2 + 4) + mp.mpf(10) / 3) + 2 / (x0 * (T + 8))
        return CE / (2 * mp.pi) * eta ** 3 * main + CE * eta ** 3 / x0 ** 3
    Es = a[0] * Eb(None) + sum(a[k] * Eb(v + mp.log(k)) for k in range(1, 17))
    u = mp.pi * (eta - y) / (2 * lam)
    loss = a[1] * eta * w0 * mp.pi / (2 * lam) * (1 / u - mp.cot(u))   # exact value of the (3.51) loss
    Psi = eta * w0 * (B - a[0] * KAPPA) + zero + Es + loss + mp.mpf('1e-9') * eta
    return dict(Psi=Psi, G=G(mu), mu=mu, B=B, lam=lam, y=y, eta=eta, zero=zero, E=Es, loss=loss, nu=nu, c=B * ell)


# ---------------- window
prof = [(float(r.split(',')[0]), float(r.split(',')[1]), r.split(',')[2]) for r in open(os.path.join(PL, 'zfr_local.csv')).read().splitlines()[1:]]


def Zband(v):
    for a_, b_, Zs in prof:
        if a_ < v <= b_:
            return Zs
    raise ValueError(v)


def Zw_true(v):
    """max of the profile over heights log u in [log(t - T0), log(16 t + T0)], t = e^v (MTY below 30, 21.233 above 300)."""
    lo = v + float(mp.log(1 - T0 * mp.exp(-v)))
    hi = v + float(mp.log(16 + T0 * mp.exp(-v)))
    m = 0.0
    if lo <= 30:
        m = max(m, float(mp.mpf('5.558691') * mp.log(30)))
    if hi > 300:
        m = max(m, 21.233)
    for a_, b_, Zs in prof:
        if b_ > lo and a_ < hi:
            m = max(m, float(Zs))
    return m, lo, hi


if __name__ == '__main__':
    print("a_k > 0:", all(x > 0 for x in a), " a =", mp.nstr(sum(a[1:]), 12), " w(0) =", mp.nstr(w0, 12), " kappa =", mp.nstr(KAPPA, 10))
    print("G(0) =", mp.nstr(G(0), 12), " G(0.9) =", mp.nstr(G(mp.mpf('0.9')), 12))
    sys.path.insert(0, PL)
    from zl_core import cell_terms, arb, G_of_mu
    print("\n v        Z      Zw     n  margin=G-Psi (indep)   rel     | zl_core PsiEta upper     mu_low     (tiny cell)")
    for v in [30.0005, 31, 45, 60, 80, 95.5, 100, 129.9, 130, 130.3, 130.6, 131, 160, 216, 250, 296.9, 297.2, 297.5, 299, 300]:
        Z = Zband(v)
        Zw, lo, hi = Zw_true(v)
        best = None
        for n in (3, 4, 5):
            r = terms(v, Z, max(Zw, float(Z)), n)
            if r is None:
                continue
            marg = r['G'] - r['Psi']
            if best is None or marg > best[1]:
                best = (n, marg, r)
        n, marg, r = best
        ct = cell_terms(arb(v), arb(v) + arb('1e-9'), arb(Z), arb(max(Zw, float(Z))), n)
        print(f"{v:9.4f} {Z} {Zw:7.3f}  {n}  {mp.nstr(marg, 8):>14}  {mp.nstr(marg / r['G'], 3):>9}   | {ct[1].upper().str(10):>22}  {ct[0].str(8)}  indepPsi={mp.nstr(r['Psi'], 10)} mu={mp.nstr(r['mu'], 8)}")
    # dense scan of margins with point evaluation at band constant (independent, not rigorous)
    print("\nDense scan (every 0.05 in v; best n among 3,4,5): minimum relative margin per 10-unit block")
    worst = (1, None)
    blk = {}
    for iv in range(0, 5401):
        vv = max(30.0 + iv * 0.05, 30.000001)
        Z = Zband(vv); Zw, lo, hi = Zw_true(vv)
        best = None
        for n in (3, 4, 5):
            r = terms(vv, Z, max(Zw, float(Z)), n)
            if r is None:
                continue
            rel = (r['G'] - r['Psi']) / r['G']
            if best is None or rel > best[0]:
                best = (rel, n)
        key = int(vv // 10) * 10
        if key not in blk or best[0] < blk[key][0]:
            blk[key] = (best[0], vv, best[1])
        if best[0] < worst[0]:
            worst = (best[0], vv, best[1])
    for k in sorted(blk):
        print(f"  [{k},{k+10}):  min rel margin {mp.nstr(blk[k][0], 4)} at v={blk[k][1]:.2f} (n={blk[k][2]})")
    print("overall worst:", mp.nstr(worst[0], 4), "at v =", worst[1], "n =", worst[2])
