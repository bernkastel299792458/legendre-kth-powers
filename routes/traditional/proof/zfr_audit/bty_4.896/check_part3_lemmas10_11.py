"""Part 3: Lemma 11 (f(u) >= kappa*eta*w(0) on [0,59]) and Lemma 10 (the
positive lower bound 0.1186 via the certified minima m_p of Table 1).
Run:  python -I check_part3_lemmas10_11.py      (about 1-3 minutes)"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Q
from flint import arb, arb_series
from bty_common import *          # noqa: F401,F403

print("=" * 78)
print("PART 3: Lemmas 10 and 11")
print("=" * 78)
w0 = w(arb(0))
kap = A(KAPPA_SUM)


def ball(lo, hi):
    lo, hi = arb(lo), arb(hi)
    return arb(((lo + hi) / 2).mid(), ((hi - lo) / 2).upper())


# ---------------------------------------------------------------- Lemma 11
# h(u) = w(eta0 u) S(u) - kappa w(0),  S(u) = sum kappa_m e^{-d_m u},
# d_m = (2 sigma0 - 1) m if kappa_m < 0, d_m = m otherwise.  h(0) = 0.
dm = [((2 * sigma0 - 1) * m if KAPPA[m] < 0 else arb(m)) for m in range(M + 1)]


def h_series(u, n=2):
    us = arb_series([u, 1], prec=n)
    S = sum(A(KAPPA[m]) * (-dm[m] * us).exp() for m in range(M + 1))
    return w(eta0 * us) * S - kap * w0


h0 = h_series(arb(0)).coeffs()
check("Lemma 11: h(0) = 0 exactly (so the claim is tight at u = 0)", h0[0].contains(0), str(h0[0]))
check("Lemma 11: h'(0) = -w(0) sum d_m kappa_m > 0", h0[1].lower() > 0, fmt(h0[1], 8))
u1 = D("0.5")
okd, n1 = True, 2000
for i in range(n1):
    c = h_series(ball(u1 * i / n1, u1 * (i + 1) / n1)).coeffs()
    okd &= c[1].lower() > 0
check("Lemma 11: h' > 0 on [0, 0.5] (interval arithmetic, 2000 cells) => h > 0 on (0, 0.5]", okd)
okv, n2, hmin = True, 20000, None
lo = u1
step = (arb(59) - u1) / n2
for i in range(n2):
    v = h_series(ball(lo + i * step, lo + (i + 1) * step)).coeffs()[0]
    okv &= v.lower() > 0
    hmin = v.lower() if hmin is None else min(hmin, v.lower())
check("Lemma 11: h > 0 on [0.5, 59] (interval arithmetic, 20000 cells)", okv, f"min lower bound = {float(hmin):.4e}")
h59 = h_series(arb(59)).coeffs()[0]
h60 = h_series(arb(60)).coeffs()[0]
check("Lemma 11: margin at u = 59 (and h(60) for reference)", None, f"h(59) = {fmt(h59, 6)}, h(60) = {fmt(h60, 6)}")

# ---------------------------------------------------------------- Lemma 10
# G_p(1, x) = sum_{m=1}^{Mp} p^{-m} P(m x),  P(x) = sum_k a_k cos(kx) >= 0.
# Monotonicity in sigma: dG_p/dsigma = -log p sum_m m p^{-m sigma} P(m x) <= 0 since P >= 0,
# so G_p(sigma, x) >= G_p(1, x) for sigma <= 1 -- no numerical check needed.
check("Lemma 10: dG_p/dsigma = -(log p) sum_m m p^{-m sigma} P(mx) <= 0 because P >= 0 "
      "(the paper's Mathematica check is unnecessary)", True)

AKa = [A(x) for x in AK]
ka_abs1 = sum(arb(k) * AKa[k] for k in range(K + 1))
ka_abs2 = sum(arb(k * k) * AKa[k] for k in range(K + 1))


def G(p, Mp, x):
    s = arb(0)
    for m in range(1, Mp + 1):
        s += sum(AKa[k] * (arb(k * m) * x).cos() for k in range(K + 1)) / arb(p) ** m
    return s


def Gd(p, Mp, x):
    s = arb(0)
    for m in range(1, Mp + 1):
        s -= sum(AKa[k] * arb(k * m) * (arb(k * m) * x).sin() for k in range(1, K + 1)) / arb(p) ** m
    return s


import math

_af = [float(x) for x in AK]


def Gf(p, Mp, x):
    return sum(p ** -m * sum(_af[k] * math.cos(k * m * x) for k in range(K + 1)) for m in range(1, Mp + 1))


def float_argmin(p, Mp, n=20000):
    xs = [math.pi * i / n for i in range(n + 1)]
    i = min(range(n + 1), key=lambda j: Gf(p, Mp, xs[j]))
    lo, hi = xs[max(i - 1, 0)], xs[min(i + 1, n)]
    for _ in range(100):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if Gf(p, Mp, m1) < Gf(p, Mp, m2):
            hi = m2
        else:
            lo = m1
    x = (lo + hi) / 2
    return x, Gf(p, Mp, x)


def certify_above(p, Mp, target, max_evals=400000):
    """Branch and bound: prove G_p(1, x) > target for all x in [0, pi] (G even, 2 pi-periodic).
    On [c-r, c+r]: G >= G(c) - |G'(c)| r - M2 r^2/2, M2 = sum m^2 p^-m sum k^2 a_k.
    Returns (ok, evals); gives up (ok=False) after max_evals cells."""
    M2 = sum(arb(m * m) / arb(p) ** m for m in range(1, Mp + 1)) * ka_abs2
    pi = arb.pi()
    nmin = 512
    stack = [(pi * i / nmin, pi * (i + 1) / nmin) for i in range(nmin)]
    evals = 0
    while stack:
        a_, b_ = stack.pop()
        c = (a_ + b_) / 2
        r = (b_ - a_) / 2
        lb = G(p, Mp, c) - abs(Gd(p, Mp, c)) * r - M2 * r * r / 2
        evals += 1
        if evals > max_evals:
            return False, evals
        if lb.lower() > target.upper():
            continue
        stack.append((a_, c))
        stack.append((c, b_))
    return True, evals


TABLE = {2: "0.23416332", 3: "0.05006283", 5: "0.00735709", 7: "0.00205251", 11: "0.00039742",
         13: "0.00022273", 17: "0.00009071", 19: "0.00006314", 23: "0.00003427", 29: "0.00001656",
         31: "0.00001346", 37: "7.8e-6", 41: "5.69e-6", 43: "4.91e-6", 47: "3.74e-6", 53: "2.59e-6",
         59: "1.87e-6", 61: "1.69e-6", 67: "1.27e-6", 71: "1.06e-6", 73: "9.7e-7", 79: "7.7e-7",
         83: "6.6e-7", 89: "5.3e-7", 97: "4.1e-7"}
ctx.prec = 120
sum_paper = arb(0)
sum_cert = arb(0)
for p, mps in TABLE.items():
    Mp = min(15, int((arb(59) / arb(p).log()).floor().unique_fmpz()))
    mp_val = D(mps)
    xs, gmin = float_argmin(p, Mp)
    g_at = G(p, Mp, D(repr(xs)))           # rigorous value at the float minimiser
    sum_paper += arb(p).log() * mp_val
    if lt(g_at, mp_val):
        check(f"Table 1, p = {p:2d}: m_p = {mps} is a lower bound for min_x G_p(1,x)", False,
              f"counterexample: G_{p}(1, {xs:.12f}) = {fmt(g_at, 12)} < m_p (rigorous point value)", issue=True)
        target = D(f"{gmin - 1e-9:.15e}")
        ok, ev = certify_above(p, Mp, target)
        check(f"           replacement certified lower bound for p = {p}", ok, f"G_{p}(1,x) > {fmt(target, 12)} ({ev} cells)")
        sum_cert += arb(p).log() * target
    else:
        ok, ev = certify_above(p, Mp, mp_val)
        note = f" (uses m <= {Mp}; the paper uses m <= 15 although p^m > e^59 for m > {Mp})" if Mp < 15 else ""
        check(f"Table 1, p = {p:2d}: G_p(1,x) > m_p = {mps} for all x{note}", ok,
              f"float min = {gmin:.12f}, {ev} cells")
        sum_cert += arb(p).log() * mp_val
    print("", flush=True)
check("Lemma 10: sum_{p<100} (log p) m_p > 0.23545 with the printed table", lt(D("0.23545"), sum_paper),
      fmt(sum_paper, 10))
check("Lemma 10: sum_{p<100} (log p) m_p > 0.23545 with the CERTIFIED values (p = 5 replaced)",
      lt(D("0.23545"), sum_cert), fmt(sum_cert, 10))
ctx.prec = 200
v = D("0.23545") * kap
check("Lemma 10: 0.23545 * kappa > 0.1186", lt(D("0.1186"), v), fmt(v, 8))
check("Lemma 10 NOTE: here 'f(0)' means eta*w(0) (the paper's f(0) = eta*w(0)*kappa is used "
      "inconsistently; the final step treats f(0) as eta*w(0)).  With f(0) := eta w(0) the chain "
      "Lemma 11 -> Lemma 10 is correct.", None)
sys.exit(summary())
