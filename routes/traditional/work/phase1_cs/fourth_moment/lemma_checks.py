# -*- coding: utf-8 -*-
"""
Checks of the auxiliary lemmas of Section 5 of arXiv:2507.15184v2.
Run: python -I lemma_checks.py > lemma_checks_out.txt
Parts marked [RIGOROUS] use Arb; parts marked [NUMERICAL] are float sanity checks.
"""
import os, sys, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, acb, acb_series, ctx
from cs4_formulas import Q, PI, GAM, E, M0, D1 as D1f, D2 as D2f, D3 as D3f, D4 as D4f
import numpy as np

ctx.prec = 128
L2 = arb(2).log()

print("=" * 78)
print("[RIGOROUS] 1. Coefficients D1..D4 of sum_{n<=x} d(n)^2 = x(D1 L^3+D2 L^2+D3 L+D4)+D0(x)")
print("   = residue at s=1 of zeta(s)^4/zeta(2s) x^s/s  (Ramanujan: sum d^2 n^-s = zeta^4/zeta(2s))")
N = 6
ctx.cap = N
# w*zeta(1+w) = 1 + sum_{n>=0} (-1)^n gamma_n w^{n+1}/n!
coef = [acb(1)] + [acb((-1) ** n) * acb.stieltjes(n) / math.factorial(n) for n in range(N - 1)]
wz = acb_series(coef)
z2 = acb_series.zeta(acb_series([2, 2]))       # zeta(2+2w)
h = wz ** 4 / z2 / acb_series([1, 1])            # (w zeta(1+w))^4 / zeta(2+2w) / (1+w)
hc = h.coeffs()
# residue = coefficient of w^3 in h(w) e^{wL}: sum_k L^k/k! h_{3-k}
Dex = [hc[0].real / 6, hc[1].real / 2, hc[2].real, hc[3].real]
for k, v in enumerate(Dex):
    print("   D%d = %s" % (k + 1, v.str(20, radius=True)))
print("   1/pi^2 = %s" % (1 / PI ** 2).str(20))
print("   CS (Lemma 11) intervals: 0.744341<D2<0.744342, 0.823265<D3<0.823266, 0.460323<D4<0.460324")
print("   in CS intervals:", (Dex[1] > Q("0.744341")) and (Dex[1] < Q("0.744342")),
      (Dex[2] > Q("0.823265")) and (Dex[2] < Q("0.823266")),
      (Dex[3] > Q("0.460323")) and (Dex[3] < Q("0.460324")))
print("   NB: CHT21 arXiv v1 (1911.07369v1) Thm 2 prints D2=0.745..., D3=0.824..., D4=0.461... and error")
print("       O*(9.73 x^{3/4} log x + 0.73 x^{1/2}); CS quote |D0(x)| <= 9.73 x^{3/4} log x only.")
D1x, D2x, D3x, D4x = Dex

print("=" * 78)
print("[RIGOROUS] 2. Lemma 13 (D6) constant 154: |c0| + int_2^oo |D0(u)|/u^2 du")
c0 = D4x + Q("0.5") - (D1x * L2 ** 4 / 4 + D2x * L2 ** 3 / 3 + D3x * L2 ** 2 / 2 + D4x * L2)
I973 = Q("9.73") * arb(2) ** (-Q("0.25")) * (4 * L2 + 16)
I073 = Q("0.73") * 2 / arb(2).sqrt()
print("   c0 = %s" % c0.str(10))
print("   9.73*int_2^oo u^{-5/4} log u du = %s" % I973.str(10))
print("   0.73*int_2^oo u^{-3/2} du       = %s" % I073.str(10))
print("   |c0| + 9.73-part            = %s  (<=154: %s)" % ((abs(c0) + I973).str(10), abs(c0) + I973 < 154))
print("   |c0| + 9.73-part + 0.73-part = %s  (<=154: %s)" % ((abs(c0) + I973 + I073).str(10), abs(c0) + I973 + I073 < 154))
print("   coefficient check D1+D2/3 = %s (paper 0.349436), D2+D3/2 = %s (1.155975), D3+D4 = %s (1.28359)"
      % ((D1x + D2x / 3).str(10), (D2x + D3x / 2).str(10), (D3x + D4x).str(10)))

print("=" * 78)
print("[RIGOROUS] 3. Lemma 14 (D7): exact lower-order coefficients vs paper (0.12441, 0.364, 0.3)")


def mi(i):
    f = lambda v, an: (2 * v * v - v) * (-2 * v).exp() * (v.log(analytic=an)) ** i if i > 0 else (2 * v * v - v) * (-2 * v).exp()
    val = acb.integral(f, 1, 80, rel_tol=2.0 ** -100).real
    # tail int_80^oo (2v^2) e^{-2v} (log v)^i <= int_80^oo 2 v^{2+i} e^{-2v} < 1e-60
    return val + arb(0, 1e-60)


m = [mi(i) for i in range(4)]
e2 = (-arb(2)).exp()
print("   m0 - e^-2 = %s  (expected 0.75 e^-2 = %s)" % ((m[0] - e2).str(12), (Q("0.75") * e2).str(12)))
cL3 = D1x * (m[0] - e2)
cL2 = 3 * D1x * m[1] + D2x * (m[0] - e2)
cL1 = 3 * D1x * m[2] + 2 * D2x * m[1] + D3x * (m[0] - e2)
cL0 = D1x * m[3] + D2x * m[2] + D3x * m[1] + D4x * (m[0] - e2)
print("   L^3: %s   (paper 3/(2e pi)^2 = %s)" % (cL3.str(10), (3 / (2 * E * PI) ** 2).str(10)))
print("   L^2: %s   (paper 0.12441)  ok: %s" % (cL2.str(10), cL2 < Q("0.12441")))
print("   L^1: %s   (paper 0.364)    ok: %s" % (cL1.str(10), cL1 < Q("0.364")))
print("   L^0: %s   (paper 0.3)      ok: %s" % (cL0.str(10), cL0 < Q("0.3")))
d0p = (Q("9.73") + Q("19.46") * Q("1.25")) * e2
print("   D0-part (9.73 + 19.46*1.25) e^-2 = %s (paper 4.61) ok: %s" % (d0p.str(10), d0p < Q("4.61")))
print("   extra 0.73 x^{1/2} part: 0.73*(1+2.5) e^-2 = %s  (-> + .../(sqrt(x0) log^3 x0))" % (Q("0.73") * Q("3.5") * e2).str(6))

print("=" * 78)
print("[RIGOROUS] 4. Lemma 12 sign conditions (interval subdivision of sigma)")


def Zfun(Zv, s, D):
    d1, d2, d3, d4 = D
    L = Zv.log()
    p = Zv ** (1 - s) if not isinstance(s, arb) else ((1 - s) * L).exp()
    return p * (d1 * L ** 3 / (1 - s) + (-3 * d1 / (1 - s) ** 2 + d2 / (1 - s)) * L ** 2
                + (6 * d1 / (1 - s) ** 3 - 2 * d2 / (1 - s) ** 2 + d3 / (1 - s)) * L
                + (-6 * d1 / (1 - s) ** 4 + 2 * d2 / (1 - s) ** 3 - d3 / (1 - s) ** 2 + d4 / (1 - s)))


Dball = (D1x, D2x, D3x, D4x)
nsub = 3000
ok_br = True
ok_const = True
worst_const = -1e9
for j in range(nsub):
    lo = -3 + 3 * j / nsub
    hi = -3 + 3 * (j + 1) / nsub
    s = arb((lo + hi) / 2, (hi - lo) / 2)
    b1 = -3 * s * D1x / (1 - s) ** 2 + D2x / (1 - s)
    b2 = 6 * s * D1x / (1 - s) ** 3 - 2 * s * D2x / (1 - s) ** 2 + D3x / (1 - s)
    b3 = -6 * s * D1x / (1 - s) ** 4 + 2 * s * D2x / (1 - s) ** 3 - s * D3x / (1 - s) ** 2 + D4x / (1 - s)
    if not (b1 > 0 and b2 > 0 and b3 > 0):
        ok_br = False
    # constant part: 1-2^{-s} - s Z(2,s) - 9.73|s| 2^{3/4-s} log2/(3/4-s) <= 0
    # f(s) = 1-2^{-s} + |s| Z(2,s) - 9.73|s| 2^{3/4-s} log2/(3/4-s);  1-2^{|s|} <= -|s| log 2, so
    # f(s)/|s| <= -log2 + Z(2,s) - 9.73 2^{3/4-s} log2/(3/4-s)   (checked <= 0 on each subinterval)
    cst = -L2 + Zfun(arb(2), s, Dball) - Q("9.73") * ((Q("0.75") - s) * L2).exp() * L2 / (Q("0.75") - s)
    up = float((cst.mid() + cst.rad()))
    worst_const = max(worst_const, up)
    if not (cst <= 0):
        ok_const = False
print("   sigma in [-3,0): inner brackets of (d2Aux) positive: %s" % ok_br)
print("   sigma in [-3,0): x-independent constant <= 0 (enough for '17.52'): %s (max upper end %.4g)" % (ok_const, worst_const))
print("   17.52 >= 9.73(1+3/3.75) = %s" % (Q("9.73") * (1 + Q(3) / Q("3.75"))).str(8))
ok42 = True
worst42 = -1e9
for j in range(nsub):
    lo = 1e-9 + (1 - 2e-9) * j / nsub
    hi = 1e-9 + (1 - 2e-9) * (j + 1) / nsub
    s = arb((lo + hi) / 2, (hi - lo) / 2)
    P2 = D1x * L2 ** 3 + D2x * L2 ** 2 + D3x * L2 + D4x
    # f(s) = 1-2^{-s} - s P(log2)/(1-s) - 9.73 s 2^{-1/4} log^2 2 ;  1-2^{-s} <= s log 2, so
    # f(s)/s <= log2 - P(log2)/(1-s) - 9.73 2^{-1/4} log^2 2  (checked <= 0 on each subinterval)
    cst = L2 - P2 / (1 - s) - Q("9.73") * arb(2) ** (-Q("0.25")) * L2 ** 2
    worst42 = max(worst42, float(cst.mid() + cst.rad()))
    if not (cst <= 0):
        ok42 = False
print("   sigma in (0,1): x-independent constant <= 0: %s (max upper end %.4g)" % (ok42, worst42))

print("=" * 78)
print("[NUMERICAL] 5. Divisor sums up to N (floats)")
Nmax = 5_000_000
t = time.time()
d = np.zeros(Nmax + 1, dtype=np.int64)
for k in range(1, Nmax + 1):
    d[k::k] += 1
print("   sieve d(n) n<=%d: %.1fs" % (Nmax, time.time() - t))
n = np.arange(1, Nmax + 1, dtype=np.float64)
dd = d[1:].astype(np.float64)
Dsum = np.cumsum(dd)
S2 = np.cumsum(dd * dd)
g = float(GAM.mid())
# Delta(x) at x=n (right value) and x->n- (left value = sum up to n-1)
logn = np.log(n)
main1 = n * logn + (2 * g - 1) * n
DeltaR = Dsum - main1
DeltaL = np.concatenate(([0.0], Dsum[:-1])) - main1
r = np.maximum(np.abs(DeltaR), np.abs(DeltaL)) / np.sqrt(n)
print("   max |Delta(x)|/sqrt(x), 1<=x<=N : %.4f  (CS use <=1; BBR12 Thm 1.1 gives 0.961 for x>=1)" % r.max())
Df = [float(v.mid()) for v in Dex]
mainS = n * (Df[0] * logn ** 3 + Df[1] * logn ** 2 + Df[2] * logn + Df[3])
D0R = S2 - mainS
D0L = np.concatenate(([0.0], S2[:-1])) - mainS
sel = n >= 2
rr = (np.maximum(np.abs(D0R), np.abs(D0L)) / (n ** 0.75 * logn))[sel]
print("   max |D0(x)|/(x^{3/4} log x), 2<=x<=N : %.4f  (CS: 9.73)" % rr.max())
for X in (10, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, Nmax):
    i = X - 1
    print("     x=%8d  D0(x)=%.4g   D0/(x^0.5)=%.4g" % (X, D0R[i], D0R[i] / X ** 0.5))
# Lemma 12 spot checks: sum_{n<=x} d^2 n^{-s} <= D4(x, s) x^{1-s} log^3 x
print("   Lemma 12 spot checks (ratio LHS/RHS must be <=1):")
for s in (-3.0, -2.0, -1.0, -0.2, 0.0, 0.3, 0.8, 0.95):
    worst = 0
    for X in (100, 1000, 10 ** 4, 10 ** 5, 10 ** 6, Nmax):
        lhs = float(np.sum(dd[:X] ** 2 * n[:X] ** (-s)))
        rhs = float((D4f(arb(X), Q(repr(s))) * arb(X) ** (1 - Q(repr(s))) * arb(X).log() ** 3).mid())
        worst = max(worst, lhs / rhs)
    print("     sigma=%5.2f  max ratio = %.4f" % (s, worst))
# Lemma 9 spot checks
print("   Lemma 9/10 spot checks:")
for s0 in (0.0, -0.5, -1.0):
    worst = 0
    for X in (100, 1000, 10 ** 4, 10 ** 5, 10 ** 6):
        for s in (s0, (s0 + 0.5) / 2, 0.5):
            lhs = float(np.sum(dd[:X] * n[:X] ** (-s)))
            rhs = float((D1f(arb(X), Q(repr(s0))) / (1 - Q(repr(s))) * arb(X) ** (1 - Q(repr(s))) * arb(X).log()).mid())
            worst = max(worst, lhs / rhs)
    print("     D1(x0,%4.1f): max ratio %.4f" % (s0, worst))
worst = 0
for X in (100, 1000, 10 ** 4, 10 ** 5):
    for s in (0.0, 0.5, 1.0):
        lhs = float(np.sum(dd[X:] * n[X:] ** (-s) * np.exp(-n[X:] / X)))
        rhs = float((D3f(arb(X)) * arb(X) ** (1 - Q(repr(s))) * arb(X).log()).mid())
        worst = max(worst, lhs / rhs)
print("     D3(x0) (Lemma 10, 2nd): max ratio %.4f" % worst)

print("=" * 78)
print("[NUMERICAL/RIGOROUS] 6. Lemma 16 (chi, Gamma) constants")


# Gamma ratio on a grid
worst = 0
for x in np.linspace(-1, 1, 21):
    for y in list(np.linspace(2, 50, 97)) + [100, 1000]:
        z = acb(x, y)
        r = abs(z.gamma()) / ((2 * PI).sqrt() * abs(z) ** (Q(repr(float(x))) - Q("0.5")) * (-PI * y / 2).exp())
        lr = abs(float(r.mid().log().mid())) * 2 * y * y   # must be <= 1
        worst = max(worst, lr)
print("   max |log ratio| * 2 y^2 over grid x in[-1,1], y in[2,1000]: %.4f (Lemma claims <= 1)" % worst)


# rigorous boundary maxima via ball evaluation (maximum modulus principle)
def bmax(fun, segs, nseg):
    mx = 0.0
    for (z0, z1) in segs:
        for k in range(nseg):
            a = z0 + (z1 - z0) * k / nseg
            b = z0 + (z1 - z0) * (k + 1) / nseg
            c = (a + b) / 2
            rad = abs(b - a) / 2
            ball = acb(arb(c.real, rad), arb(c.imag, rad))
            v = abs(fun(ball))
            mx = max(mx, float((v.mid() + v.rad()).mid()) * (1 + 1e-12))
    return mx


def chi_b(s):
    return ((s * acb(2 * PI).log()).exp() / (2 * s.gamma() * (acb(PI) * s / 2).cos()))


def zm1chi(s):
    # (s-1)chi(s) = -(2^s pi^{s-1} sin(pi s/2) Gamma(2-s))
    return -((s * acb(2).log()).exp() * ((s - 1) * acb(PI).log()).exp() * (acb(PI) * s / 2).sin() * (2 - s).gamma())


# NUMERICAL grid (boundary of the rectangles; max modulus principle).  Ball evaluation on boxes was
# too crude to be useful here; these constants only enter J0, which is negligible (see report).
def gridmax(fun, pts):
    return max(float(abs(fun(acb(x, y))).mid()) for (x, y) in pts)


tp = 2 * math.pi
pts1 = [(-0.5 + 0.5 * i / 200, yy) for i in range(201) for yy in (-100.0, 100.0)] +        [(xx, -100 + 200 * j / 8000) for j in range(8001) for xx in (-0.5, 0.0)]
m1 = gridmax(lambda z: (z * acb(2).log()).exp() * ((z - 1) * acb(PI).log()).exp() * (acb(PI) * z / 2).sin() * (1 - z).gamma(), pts1)
print("   [NUMERICAL] max |chi| on boundary grid of [-1/2,0]x[-100,100]: %.6f (claim 16)" % m1)
pts2 = [(0.5 + 0.5 * i / 400, yy) for i in range(401) for yy in (-tp, tp)] +        [(xx, -tp + 2 * tp * j / 4000) for j in range(4001) for xx in (0.5, 1.0)]
m2 = gridmax(zm1chi, pts2)
print("   [NUMERICAL] max |(z-1)chi(z)| on boundary grid of [1/2,1]x[-2pi,2pi]: %.6f (claim 6.31)" % m2)
pts3 = [(0.5 + 0.5 * i / 50, sgn * tp * (1 + k / 20)) for i in range(51) for k in range(400) for sgn in (1, -1)]
m3 = gridmax(lambda z: (z * acb(2).log()).exp() * ((z - 1) * acb(PI).log()).exp() * (acb(PI) * z / 2).sin() * (1 - z).gamma(), pts3)
print("   [NUMERICAL] max |chi| for x in [1/2,1], 2pi<=|y|<=42pi (grid): %.6f (claim 1.1)" % m3)
print("   1/log(1+1/n) <= n+1/2 (MV lemma), n=1..1e6:", all(1 / math.log1p(1 / k) <= k + 0.5 + 1e-12 for k in range(1, 10 ** 6)))
