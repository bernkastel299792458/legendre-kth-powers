"""Part 2: Lemma 6 (sum over far zeros), Lemma 8 (error term), Lemma 9,
Lemma 12 (digamma main term), Lemma 13 (pole term).
Run:  python -I check_part2_lemmas6_8_9_12_13.py"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Q
from flint import arb, acb
from bty_common import *          # noqa: F401,F403

print("=" * 78)
print("PART 2: Lemmas 6, 8, 9, 12, 13")
print("=" * 78)
w0 = w(arb(0))
pi = arb.pi()
Kq = arb(K)

# ---------------------------------------------------------------- Lemma 6
v = 88 * eta0 * T0.log() / T0
check("Lemma 6 (26): 88 eta0 log(T0)/T0 < 1e-8 (Lehman Lemma 2: sum_{g>T0} g^-2 < log T0/T0)",
      lt(v, D("1e-8")), fmt(v, 6))
# (27): int_{T0}^inf phi(x) log(x/2pi) dx <= term1 + term2 + term3 (term4 dropped)
#   term1 <= (log t + T0/(K H) + log(K/2pi))/T0
#   term2 = log((kt+T0)/2pi)/(2kt+T0) <= value at kt = H (decreasing)
#   term3 = log(2kt+T0)/kt <= value at kt = H
t1_const = T0 / (Kq * H) + (Kq / (2 * pi)).log()          # coefficient of 1/T0 beyond log t
t2 = ((H + T0) / (2 * pi)).log() / (2 * H + T0)
t3 = (2 * H + T0).log() / H
t4 = -T0.log() / H                                          # the dropped (negative) term at kt = H
excess = t1_const + (t2 + t3) * T0                          # (27) claims this is <= 1
check("Lemma 6 (27): int phi log(x/2pi) < 1e-10 (log t + 1)?  The bound as derived gives "
      "1e-10 (log t + c) with c below", lt(excess, arb(1)),
      f"c = {fmt(excess, 8)}  (with the dropped term kept: c = {fmt(excess + t4 * T0, 8)}); "
      "harmless: corrected final bound checked next", issue=True)
excess_kept = excess + t4 * T0
# Since log t >= log H = 28.7, 1e-10 (log t + 1.08) <= 1.0028e-10 (log t + 1): harmless.
# Final bound of Lemma 6 for k != 0 using a corrected (27):
B27 = lambda L: (L + excess) / T0                            # >= true integral, L = log t
B28 = lambda L: (1 / T0 ** 2 + 1 / (2 * H + T0) ** 2) * (L + (Kq).log() + T0 / (Kq * H))
B29 = 1 / (2 * T0 ** 2) + 1 / ((2 * H) ** 2 * T0)            # >= int_{T0}^inf (x^-2 + (2H+x)^-2) dx/x
worst = arb(0)
for L in [logH, logH + 1, arb(40), arb(77), arb(200), arb(10) ** 4, arb(10) ** 8]:
    eta = A0 / L
    val = 44 * eta * (B27(L) / (2 * pi) + 4 * B28(L) + 2 * B29)
    worst = arb(max(worst.upper(), val.upper()))
# sup over L: eta*(L + c) = A0 (1 + c/L) is decreasing in L, so L = log H is the worst case
check("Lemma 6, k != 0: 44 eta [ (1/2pi) B27 + 4 B28 + 2 B29 ] < 1e-8 with corrected (27) "
      "(worst case t = H)", lt(worst, D("1e-8")), fmt(worst, 6))
v29 = B29
check("Lemma 6 (29): int_{T0}^inf (x^-2 + (2H+x)^-2) dx/x < 1e-10", lt(v29, D("1e-10")), fmt(v29, 4))
check("Lemma 6: sum over k of a_k * 1e-8 < 1e-7  (needed for (47))",
      lt(A(sum(AK)) * D("1e-8"), D("1e-7")), f"sum a_k = {float(sum(AK)):.6f}")
check("NOTE Lemma 6: the far-zero sum must be paired rho <-> 1-conj(rho) (not rho <-> conj(rho)) to "
      "apply (22); doing so gives -22 eta sum(...), so the printed -44 eta is conservative. "
      "(25): 'F(2s-1+beta0)' is a typo for F(s-1+beta0); (47) omits the factor a_1.", None)

# ---------------------------------------------------------------- Lemma 8
Cx = C_ford(x0 / eta0, x0 / eta0)
check("Lemma 8: C(x0/eta0, x0/eta0) < 52  [correct c0]", lt(Cx, arb(52)),
      f"{fmt(Cx, 8)}  (printed c0: {fmt(C_ford_printed(x0/eta0, x0/eta0), 6)})")


def U(y):
    """Upper bound (31) for |Re psi((1/2+iy)/2)| (Kadiri Lemma 3.6), y an arb (ball)."""
    y = abs(y)
    if lt(y, arb(1) / 2):
        return (arb(16) / (1 + 4 * y ** 2)).log() / 2 + 2 / (1 + 4 * y ** 2) + 2
    if not lt(y, arb(1) / 2) and (y - arb(1) / 2).lower() >= 0:
        return abs((y / 2).log() - 2 / (1 + 4 * y ** 2)) + 2 / (3 * y) + 1 / (8 * y ** 2)
    return None   # ball straddles 1/2


def ball(lo, hi):
    lo, hi = arb(lo), arb(hi)
    return arb(((lo + hi) / 2).mid(), ((hi - lo) / 2).upper())


def repsi(y):
    return acb(arb(1) / 4, arb(y) / 2).digamma().real


# (a) the digamma bound (31) itself, rigorously on [0, 1000], analytically beyond
ok31, worst_gap = True, None
grid = [D("0")]
y = D("0")
while lt(y, arb(1000)):
    step = D("0.005") if lt(y, arb(5)) else (D("0.05") if lt(y, arb(100)) else D("0.5"))
    y = y + step
    grid.append(y)
grid[-1] = arb(1000)
half = arb(1) / 2
for a_, b_ in zip(grid, grid[1:]):
    if lt(a_, half) and lt(half, b_):
        pieces = [(a_, half), (half, b_)]
    else:
        pieces = [(a_, b_)]
    for lo, hi in pieces:
        # Re psi(1/4 + iy/2) is increasing in y >= 0 (psi(z) = -gamma + sum 1/(n+1) - 1/(n+z) gives
        # Re psi(a+ib) = psi(a) + sum_n b^2/((n+a)((n+a)^2+b^2))), so on [lo,hi] |Re psi| is at most
        # the larger endpoint value.
        p_lo = repsi(lo)
        p_hi = repsi(hi)
        psi_abs = arb(max(abs(p_lo).upper(), abs(p_hi).upper()))
        yb = ball(lo, hi)
        u = U(yb)
        if u is None:   # closed interval ending at 1/2: take the smaller of both branches
            u = arb(min(((arb(16) / (1 + 4 * yb ** 2)).log() / 2 + 2 / (1 + 4 * yb ** 2) + 2).lower(),
                        (abs((yb / 2).log() - 2 / (1 + 4 * yb ** 2)) + 2 / (3 * yb) + 1 / (8 * yb ** 2)).lower()))
        gap = u.lower() - psi_abs.upper()
        if gap < 0:
            ok31 = False
        worst_gap = gap if worst_gap is None else min(worst_gap, gap)
check("Lemma 8 (31): |Re psi(1/4 + iy/2)| <= U(y) for 0 <= y <= 1000 (arb digamma on "
      f"{len(grid)} intervals)", ok31, f"min slack = {float(worst_gap):.3e}")
check("Lemma 8 (31) for y >= 1000: from Binet's formula |Re psi(1/4+iy/2) - log(y/2)| <= 0.8/y^2 "
      "while U(y) >= log(y/2) + 2/(3y) - 2/(1+4y^2); holds (hand argument, see REPORT)", None)

# (b) U(x) < log(100 - x) for x <= 2 (used for I_1) -- FALSE near 0
u0 = U(arb(0))
check("Lemma 8: claim 'U(x) < log(100 - x) for x <= 2' at x = 0", lt(u0, arb(100).log()),
      f"U(0) = {fmt(u0, 6)} > log 100 = {fmt(arb(100).log(), 6)}  (fails for |x| < ~0.33)", issue=True)
# corrected: U(x) <= 6 + log(1 + |x|) for all x  (check on a grid + asymptotics), then I_1 tiny
okU = all(lt(U(D(str(xx))), 6 + (1 + abs(D(str(xx)))).log()) for xx in
          [0, 0.1, 0.3, 0.49, 0.5, 0.7, 1, 2, 5, 10, 100, 1000, 10 ** 6])
I1c = (6 + (H).log() + 1) / H ** 2          # >= int_{H-2}^inf (6 + log(1+y))/y^3 dy, crude
check("Lemma 8: with U(x) <= 6 + log(1+|x|) instead, I_1 < 1e-10 still holds", okU and lt(I1c, D("1e-10")),
      fmt(I1c, 4))
# (c) U(x) <= log x for x >= 2: rigorous on [2, 1e4], asymptotic beyond (2/(3x)+1/(8x^2) < log 2)
okL = True
xx = arb(2)
while lt(xx, arb(10000)):
    st = D("0.01") if lt(xx, arb(10)) else D("1")
    bb = ball(xx, xx + st)
    if not lt(U(bb), bb.log()):
        # refine
        for j in range(10):
            b2 = ball(xx + st * j / 10, xx + st * (j + 1) / 10)
            okL &= lt(U(b2), b2.log())
    xx = xx + st
check("Lemma 8: U(x) <= log x for x in [2, 1e4] (intervals); beyond: U(x) <= log x - log 2 + "
      "2/(3x) + 1/(8x^2) < log x", okL)
# (d) the integral (32): int_R U(y)/(x0^2+y^2)^{3/2} dy < 24, rigorous upper Riemann sum


def upper_integral(f_ball, lo, hi, n):
    lo, hi = arb(lo), arb(hi)
    s = arb(0)
    st = (hi - lo) / n
    for i in range(n):
        s += f_ball(ball(lo + i * st, lo + (i + 1) * st)).upper() * st
    return s


def integrand(yb):
    u = U(yb)
    if u is None:
        u = arb(max(((arb(16) / (1 + 4 * yb ** 2)).log() / 2 + 2 / (1 + 4 * yb ** 2) + 2).upper(),
                    (abs((yb / 2).log() - 2 / (1 + 4 * yb ** 2)) + 2 / (3 * yb) + 1 / (8 * yb ** 2)).upper()))
    return u / (x0 ** 2 + yb ** 2) ** (arb(3) / 2)


Y = arb(10000)
Iup = 2 * (upper_integral(integrand, 0, D("0.5"), 4000) + upper_integral(integrand, D("0.5"), 3, 4000)
           + upper_integral(integrand, 3, 100, 4000) + upper_integral(integrand, 100, Y, 2000)
           + (2 * Y.log() + 1) / (4 * Y ** 2))          # tail: U(y) <= log y, int_Y^inf log y / y^3
check("Lemma 8 (32) AS STATED: int U(y)/(x0^2+y^2)^{3/2} dy < 24", lt(Iup, arb(24)),
      f"rigorous upper bound = {fmt(Iup, 8)}; the true value is about 34.577 (mpmath), so (32) is false", issue=True)


def upper_integral_psi(lo, hi, n):
    """Upper sum for int |Re psi(1/4+iy/2)| (x0^2+y^2)^{-3/2} dy on [lo,hi], 0 <= lo:
    |Re psi| <= max of endpoint values (monotone), weight decreasing in y."""
    lo, hi = arb(lo), arb(hi)
    s = arb(0)
    st = (hi - lo) / n
    prev = repsi(lo)
    for i in range(n):
        a_, b_ = lo + i * st, lo + (i + 1) * st
        cur = repsi(b_)
        m = arb(max(abs(prev).upper(), abs(cur).upper()))
        s += (m / (x0 ** 2 + a_ ** 2) ** (arb(3) / 2)).upper() * st
        prev = cur
    return s


Ipsi = 2 * (upper_integral_psi(0, 2, 8000) + upper_integral_psi(2, 30, 6000) + upper_integral_psi(30, 1000, 3000)
            + (2 * arb(1000).log() + 1) / (4 * arb(1000) ** 2))   # |Re psi| <= log y for y >= 1000
check("Lemma 8 (32) AS NEEDED for T1: int |Re psi((1/2+iy)/2)| (x0^2+y^2)^{-3/2} dy < 24 "
      "(rigorous upper sum, monotonicity of Re psi in |y|)", lt(Ipsi, arb(24)), f"upper bound = {fmt(Ipsi, 8)}")
T1_t0 = 52 / (2 * pi) * Iup
check("Lemma 8 (33): (52/2pi) * 24 < 199", lt(52 / (2 * pi) * 24, arb(199)), fmt(52 / (2 * pi) * 24, 8))
alpha = 52 / (2 * pi) * 2 / x0 ** 2
check("Lemma 8 (33), t >= H: (52/2pi)(2/x0^2) A0 < 14", lt(alpha * A0 + D("1e-6"), arb(14)),
      f"(52/2pi)(2/x0^2) = {fmt(alpha, 8)};  times A0 = {fmt(alpha * A0, 8)}")
Cs = C_ford(sigma0 / eta0, sigma0 / eta0)
check("Lemma 8 (34): C(s0/eta0, s0/eta0)/x0^3 < 424  [correct c0]", lt(Cs / x0 ** 3, arb(424)),
      f"{fmt(Cs / x0 ** 3, 8)} (dividing by sigma0^3 instead would give {fmt(Cs / sigma0 ** 3, 6)}; printed c0: {fmt(C_ford_printed(sigma0/eta0, sigma0/eta0)/x0**3, 6)})")
check("Lemma 8 ISSUE: in Lemma 15 it is applied at s = s_k + delta_m with Im s = kt (k <= 16), "
      "but its hypothesis eta <= A0/log(Im s) is only known with log t. Correct bound: "
      "T1 <= 14 eta^2 + alpha*log(k)*eta^3,  alpha = (52/2pi)(2/x0^2)", None, f"alpha = {fmt(alpha, 6)}")

# ---------------------------------------------------------------- Lemma 9
KA = A(KAPPA_ABS)
check("Lemma 9: 623 sum|kappa_m| < 2353", lt(623 * KA, arb(2353)), fmt(623 * KA, 7))
check("Lemma 9: 14 sum|kappa_m| < 53", lt(14 * KA, arb(53)), fmt(14 * KA, 7))
check("Lemma 9: 424 sum|kappa_m| < 1601", lt(424 * KA, arb(1601)), fmt(424 * KA, 7))
check("Lemma 9 typos: proof says 'apply Lemma 9' (should be Lemma 7) and "
      "'g(d)=g'(0)=g'(d)=g''(d)' (missing '=0')", None)
a0q, a_ = AK[0], sum(AK[1:])
e2 = A(a_) * 53
e3 = A(a_) * 1601 + A(a0q) * 2353
check("(48): sum_{k>=1} a_k 53 < 187 and a 1601 + a0 2353 < 8013 (as printed)",
      lt(e2, arb(187)) and lt(e3, arb(8013)), f"{fmt(e2, 7)}, {fmt(e3, 7)}")
sum_alogk = sum(A(AK[k]) * arb(k).log() for k in range(1, K + 1))
e3c = e3 + KA * alpha * sum_alogk
check("(48) corrected for the log k issue: eta^3 coefficient", None,
      f"{fmt(e3c, 7)}  (= printed {fmt(e3, 6)} + {fmt(KA * alpha * sum_alogk, 6)})")

# ---------------------------------------------------------------- Lemma 12
a = A(a_)
kap = A(KAPPA_SUM)
check("a = sum_{k>=1} a_k = 2919857/828465 (exact)", a_ == Q(2919857, 828465), str(a_))
check("a0 = 1, a1 = 865534/497079 (exact)", a0q == 1 and AK[1] == Q(865534, 497079), str(AK[1]))
check("all a_k >= 0", all(x >= 0 for x in AK), str([float(x) for x in AK]))
# the k >= 1 error term
x_hi = arb(M + 3) / 2
err = 1 / (2 * x_hi) * x_hi / (H / 2) ** 2 + 1 / (12 * 1 * (H / 2)) + x_hi ** 2 / (2 * (H / 2) ** 2)
check("Lemma 12: error terms of (36) < 1e-10 for 1 <= x <= (M+3)/2, y >= H/2", lt(err, D("1e-10")), fmt(err, 4))
# k = 0 term: (1/2) sum kappa_m psi(...) <= -0.041 with the monotone bounds
s38 = arb(0)
for m in range(M + 1):
    km = A(KAPPA[m])
    if KAPPA[m] > 0:
        s38 += km * (arb(m + 3) / 2).digamma()
    else:
        s38 += km * ((sigma0 + (2 * sigma0 - 1) * m) / 2 + 1).digamma()
s38 = s38 / 2
check("Lemma 12 (38): (1/2) sum kappa_m psi((s+delta_m)/2+1) <= -0.041", lt(s38, D("-0.041")), fmt(s38, 8))
const12 = a * kap / 2 * (-(2 * pi).log()) + kap / 2 * sum(A(AK[k]) * arb(k).log() for k in range(1, K + 1)) \
    - kap / 2 * pi.log() * A(a0q) + s38 + (a * kap / 2 + KA / 2 * a) * D("1e-10")
check("Lemma 12: total constant <= -1.568", lt(const12, D("-1.568")), fmt(const12, 8))
check("Lemma 12 NOTE: the O*(1e-10) error multiplies sum|kappa_m|, not kappa (included above)", None)

# ---------------------------------------------------------------- Lemma 13
C13 = C_ford(-1, D("1e10"))
check("Lemma 13: C(-1, 1e10) < 51  [correct c0]", lt(C13, arb(51)),
      f"{fmt(C13, 8)} (printed c0: {fmt(C_ford_printed(-1, D('1e10')), 6)})")
check("Lemma 13: H/eta0 > 1e10", lt(D("1e10"), H / eta0), fmt(H / eta0, 6))
v13 = w0 * M / H ** 2 + 51 / H ** 3
check("Lemma 13: w(0) M/H^2 + 51/H^3 < 1e-12 (per eta)", lt(v13, D("1e-12")), fmt(v13, 4))
check("Lemma 13: sum_k a_k * sum|kappa| * 1e-12 < 1e-10", lt(a * KA * D("1e-12"), D("1e-10")))

sys.exit(summary())
