"""Part 4: Lemma 14 (the key lower bound for a1 F(s-1+eta) + a1 F(s-eta) - a0 F(s-1)).
(i) recompute every constant of the printed proof; (ii) a corrected, fully valid
version of the same proof; (iii) a direct rigorous evaluation of the left side on a
grid, compared with the printed and corrected lower bounds.
Run:  python -I check_part4_lemma14.py       (a few minutes)"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Q
from flint import arb, acb
from bty_common import *          # noqa: F401,F403

print("=" * 78)
print("PART 4: Lemma 14")
print("=" * 78)
w0 = w(arb(0))
a0, a1 = A(AK[0]), A(AK[1])
kap = [A(k) for k in KAPPA]
two_s0 = 2 * sigma0 - 1

# ---------------------------------------------------------------- mu0, S1, S2
check("mu0 = (1 - sigma0)/eta0 - 1e-10 = 0.91198...", abs(mu0 - D("0.91198")) < D("1e-5"), fmt(mu0, 10))
S1 = sum(KAPPA[m] / m for m in range(1, M + 1))
S2 = sum(KAPPA[m] / m ** 2 for m in range(1, M + 1))
check("S1 = -0.689736127...", abs(A(S1) - D("-0.689736127")) < D("1e-9"), f"{S1} = {float(S1):.10f}")
check("S2 = -0.818779265...", abs(A(S2) - D("-0.818779265")) < D("1e-9"), f"{S2} = {float(S2):.10f}")
S1a, S2a = A(S1), A(S2)

# ---------------------------------------------------------------- the error constants 1126, 1188
def err_const(X, x1_of_m, valid):
    """sum_{m>=1} |kappa_m| ( X^2 w0 / ((2s0-1)^2 m^2 x1) + C/x1^3 ),
    C = C(x1, x1) as printed (valid=False) or C(x1/eta0, x1/eta0) (valid=True)."""
    s = arb(0)
    for m in range(1, M + 1):
        x1 = x1_of_m(m)
        C = C_ford(x1 / eta0, x1 / eta0) if valid else C_ford_noassert(x1, x1)
        s += abs(kap[m]) * (X ** 2 * w0 / (two_s0 ** 2 * m ** 2 * x1) + C / x1 ** 3)
    return s


def C_ford_noassert(nu, r):
    nu, r = arb(nu), arb(r)
    return fc0 * r * (fc2 * (r + 1) ** 2 * ((-2 * nu * theta * cot_t).exp() + 1)
                      + fc1 * r + fc3 * r ** 3) / (r ** 2 - tan_t ** 2) ** 2


Ea_pr = err_const(mu0, lambda m: two_s0 * m - mu0 * eta0, False)          # x = -mu, as printed
Eb_pr = err_const(1 - mu0, lambda m: two_s0 * m - (1 - mu0) * eta0, False)  # x = 1-mu, as printed
check("1126 (x=-mu, printed choices x0=mu0, x1=(2s0-1)m-mu0 eta0, C(x1,x1))", lt(Ea_pr, arb(1126)), fmt(Ea_pr, 8))
check("1188 (x=1-mu, printed choices)", lt(Eb_pr, arb(1188)), fmt(Eb_pr, 8))
check("ISSUE: C(x1,x1) needs x1 > tan(theta) = 2.14, false for m = 1, 2 (x1 ~ 0.98, 1.97); "
      "and for x = -mu one needs x0 = 1 (|x| = mu <= 1), not mu0.  Valid version below "
      "(uses C(x1/eta0, x1/eta0), since Re z = (delta_m + x eta)/eta >= x1/eta0).", None)
Ea = err_const(arb(1), lambda m: two_s0 * m - eta0, True)
Eb = err_const(1 - mu0, lambda m: two_s0 * m, True)
check("valid error constants (x=-mu: x0=1, x1=(2s0-1)m-eta0; x=1-mu: x0=1-mu0, x1=(2s0-1)m)", None,
      f"E_a = {fmt(Ea, 6)}, E_b = {fmt(Eb, 6)}  (printed 1126, 1188)")

# ---------------------------------------------------------------- (41)
c41_eta = w0 * (a1 - a0) * S1a / two_s0                      # S1 < 0: worst at sigma = sigma0
c41_eta2_printed = -w0 * ((a1 - a0) * mu0 + a1) * S2a        # printed: -((a1-a0)mu + a1) S2 / (2s-1)^2, worst mu=mu0, s->1
c41_eta2_correct = -w0 * (a1 - (a1 - a0) * 1) * S2a          # correct: -(a1 - (a1-a0)mu) S2/(2s-1)^2, worst mu = 1, s -> 1
check("(41) eta coefficient: w0 (a1-a0) S1/(2 s0 - 1) > -2.939", lt(arb(-2939) / 1000, c41_eta), fmt(c41_eta, 8))
check("(41) eta^2 coefficient as printed: -w0((a1-a0)mu0+a1) S2 >= 11", lt(arb(11), c41_eta2_printed),
      fmt(c41_eta2_printed, 8))
check("(41) eta^3 coefficient as printed: a0*1126 + a1*1188 <= 3193?", lt(a0 * 1126 + a1 * 1188, arb(3193)),
      f"{fmt(a0 * 1126 + a1 * 1188, 8)} (paper writes 3188 then 3193)", issue=True)
check("ISSUE (41): expansion W(d/eta + x) = w0 eta/d - x w0 eta^2/d^2 + E gives the eta^2 term "
      "-(a1(1-mu) + a0 mu) w0 S2/(2s-1)^2, not -((a1-a0)mu + a1) w0 S2/(2s-1)^2 (sign of mu). "
      "Correct worst-case coefficient (mu=1):", None, f"{fmt(c41_eta2_correct, 8)} instead of >= 11")

# ---------------------------------------------------------------- (42): c_n, c*, the exp remainder
lu = (a1 / a0).log()       # a1 e^{-u} - a0 changes sign at u = log(a1/a0)


def cint(n, absval=False, power=None):
    pw = n if power is None else power
    f = lambda u, an: u ** pw * (a1 * (-u).exp() - a0) * w(u)
    I1 = acb.integral(f, 0, lu).real
    I2 = acb.integral(f, lu, d_supp).real
    return (I1 - I2) if absval else (I1 + I2)


cn = [cint(n) for n in range(4)]
cstar = cint(3, absval=True)
c4star = cint(4, absval=True, power=4)
printed = ["0.8763706262", "0.1200272738", "0.0203537951", "0.0004382722"]
for n in range(4):
    check(f"c_{n} = {printed[n]}...", abs(cn[n] - D(printed[n])) < D("1e-10"), fmt(cn[n], 12))
check("c* = int u^3 |a1 e^-u - a0| w = 0.0190417514...", abs(cstar - D("0.0190417514")) < D("1e-10"), fmt(cstar, 12))
# exponential remainder: e^x - (1+x+x^2/2+x^3/6) < x^4/18 (printed) and < x^3/18 on [0, d]
xd = d_supp
r3 = (xd.exp() - (1 + xd + xd ** 2 / 2 + xd ** 3 / 6)) / xd ** 3
r4 = (xd.exp() - (1 + xd + xd ** 2 / 2 + xd ** 3 / 6)) / xd ** 4
check("e^x - T3(x) < x^4/18 on [0, d]  ((e^x-T3)/x^k is increasing, so check x = d)", lt(r4, arb(1) / 18), fmt(r4, 8))
check("e^x - T3(x) < x^3/18 on [0, d]  (what the bound with c* = int u^3|..|w actually needs)",
      lt(r3, arb(1) / 18), f"{fmt(r3, 8)} vs 1/18 = {fmt(arb(1)/18, 8)}")
cubic = cn[3] / 6 - cstar / 18
check("C1 cubic coefficient: c3/6 - c*/18 >= -0.00073 ?", lt(D("-0.00073"), cubic), fmt(cubic, 8), issue=True)
cubic4 = cn[3] / 6 - c4star / 18
check("C1 cubic coefficient with remainder (mu u)^4/18 <= mu^3 u^4/18: c3/6 - c4*/18 >= -0.00073",
      lt(D("-0.00073"), cubic4), f"{fmt(cubic4, 8)} (c4* = int u^4|a1e^-u - a0|w = {fmt(c4star, 10)})")
check("=> C1(x) = 0.87637 + 0.12002x + 0.01017x^2 - 0.00073x^3 is valid if c* is read with u^4 "
      "(and mu <= 1); with c* as printed (u^3) the cubic term should be -0.000985", None)
C1_ok = lt(D("0.87637"), cn[0]) and lt(D("0.12002"), cn[1]) and lt(D("0.01017"), cn[2] / 2)
check("C1 constant, linear, quadratic coefficients are rounded down correctly", C1_ok)

# ---------------------------------------------------------------- F(sigma - eta) part
dmin = [two_s0 * m for m in range(M + 1)]


def Tk(k, s):
    return sum(kap[m] / (1 + (2 * s - 1) * m) ** k for m in range(M + 1))


def Tkp(k, s):  # derivative in sigma
    return -2 * k * sum(arb(m) * kap[m] / (1 + (2 * s - 1) * m) ** (k + 1) for m in range(1, M + 1))


okT = True
for i in range(201):
    s = sigma0 + (1 - sigma0) * i / 200
    sb = s
    okT &= Tkp(1, sb).lower() > 0 and Tkp(2, sb).lower() > 0
# enclosure over the whole interval [sigma0, 1]
sb = arb(((sigma0 + 1) / 2).mid(), ((1 - sigma0) / 2).upper())
okT_ball = Tkp(1, sb).lower() > 0 and Tkp(2, sb).lower() > 0
check("T_1', T_2' > 0 on [sigma0, 1] (ball enclosure)", okT_ball,
      f"T1'(ball) = {Tkp(1, sb).str(5)}, T2'(ball) = {Tkp(2, sb).str(5)}")
check("T_2(sigma0) > 0 (needed to use (1+mu) >= 1+mu0)", Tk(2, sigma0).lower() > 0, fmt(Tk(2, sigma0), 8))
lin = a1 * w0 * Tk(1, sigma0)
quad = a1 * w0 * (1 + mu0) * Tk(2, sigma0)
CE = C_ford(sigma0 / eta0 - 1, sigma0 / eta0 - 1)
E1_printed = sum(abs(kap[m]) * (4 * w0 / ((1 + dmin[m]) * (1 + dmin[m] - (1 + mu0) * eta0)) + CE / (sigma0 - eta0) ** 3)
                 for m in range(M + 1))
E1_valid = sum(abs(kap[m]) * (4 * w0 / ((1 + dmin[m]) ** 2 * (1 + dmin[m] - 2 * eta0)) + CE / (sigma0 - eta0) ** 3)
               for m in range(M + 1))
check("a1 w0 T1(sigma0) > 6.848", lt(D("6.848"), lin), fmt(lin, 8))
check("a1 w0 (1+mu0) T2(sigma0) > 15", lt(arb(15), quad), fmt(quad, 8))
check("a1 sum|kappa_m| |E1| bound < 708 (printed form, '/m' typo dropped)", lt(a1 * E1_printed, arb(708)),
      f"{fmt(a1 * E1_printed, 8)}; valid form (1+d_m)^2, 1+d_m-2 eta0: {fmt(a1 * E1_valid, 8)}")
tot3 = 3193 + 708
check("Lemma 14 eta^3 total: 3193 + 708 = 3901 (paper writes 3897)", None, str(tot3))

# ---------------------------------------------------------------- corrected Lemma 14 constants
corr_eta = c41_eta + lin
corr_eta2 = c41_eta2_correct + quad
corr_eta3 = a0 * Ea + a1 * Eb + a1 * E1_valid
check("CORRECTED Lemma 14: LHS >= C1'(mu) + b1 eta + b2 eta^2 - b3 eta^3, C1' with cubic term "
      "c3/6 - c4*/18 (remainder (mu u)^4/18, mu <= 1)", None,
      f"b1 = {fmt(corr_eta, 7)}, b2 = {fmt(corr_eta2, 7)}, b3 = {fmt(corr_eta3, 7)}   (printed: 3.909, 26, 3897)")
# rigorous C1: remainder e^{mu u} - T3(mu u) <= (mu u)^4/18 <= mu^3 u^4/18 (mu <= 1); this is the
# better of the two valid choices (cubic4 = -0.000503 > cubic = -0.000985).
C1c = [cn[0], cn[1], cn[2] / 2, cubic4]


def C1_corr(x):
    return C1c[0] + C1c[1] * x + C1c[2] * x ** 2 + C1c[3] * x ** 3


def C1_printed(x):
    return D("0.87637") + D("0.12002") * x + D("0.01017") * x ** 2 - D("0.00073") * x ** 3


# ---------------------------------------------------------------- direct evaluation of the LHS
def Wreal(x):
    return acb.integral(lambda u, an: (-acb(x) * u).exp() * w(u), 0, d_supp).real


def Fval(z, sigma, eta):
    return sum(kap[m] * Wreal((z + (2 * sigma - 1) * m) / eta) for m in range(M + 1))


def LHS14(sigma, eta):
    return a1 * Fval(sigma - 1 + eta, sigma, eta) + a1 * Fval(sigma - eta, sigma, eta) - a0 * Fval(sigma - 1, sigma, eta)


worst_pr, worst_co = None, None
okP, okC = True, True
grid_eta = [eta0 * f for f in (D("0.3"), D("0.5"), D("0.75"), D("1"))]
grid_mu = [mu0, D("0.93"), D("0.96"), D("0.99"), arb(1)]
for eta in grid_eta:
    for mu in grid_mu:
        sigma = 1 - mu * eta
        if lt(sigma, sigma0):
            continue
        L = LHS14(sigma, eta)
        rp = C1_printed(mu) + D("3.909") * eta + 26 * eta ** 2 - 3897 * eta ** 3
        rc = C1_corr(mu) + corr_eta * eta + corr_eta2 * eta ** 2 - corr_eta3 * eta ** 3
        gp, gc = L - rp, L - rc
        okP &= gp.lower() > 0
        okC &= gc.lower() > 0
        worst_pr = gp.lower() if worst_pr is None else min(worst_pr, gp.lower())
        worst_co = gc.lower() if worst_co is None else min(worst_co, gc.lower())
check("Lemma 14 printed bound holds at all grid points (direct rigorous quadrature of the LHS)", okP,
      f"min(LHS - printed bound) = {float(worst_pr):.3e}")
check("Lemma 14 corrected bound holds at all grid points", okC, f"min(LHS - corrected bound) = {float(worst_co):.3e}")
# save for part 5
import json
# rigorous one-sided rounding: C1 coefficients and b1, b2 rounded down, b3 up (mu in [0,1], eta > 0)
out = {"C1c_lower": [x.lower().str(25, radius=False) for x in C1c],
       "b1_lower": corr_eta.lower().str(25, radius=False),
       "b2_lower": corr_eta2.lower().str(25, radius=False),
       "b3_upper": corr_eta3.upper().str(25, radius=False)}
json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lemma14_corrected.json"), "w"), indent=1)
sys.exit(summary())
