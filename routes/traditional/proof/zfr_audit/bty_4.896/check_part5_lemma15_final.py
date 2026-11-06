"""Part 5: Lemma 15 (iteration lemma), the final numerical contradiction, and
Theorem 1.  Needs lemma14_corrected.json written by check_part4_lemma14.py.
Run:  python -I check_part5_lemma15_final.py"""
import json
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb
from bty_common import *          # noqa: F401,F403

HERE = os.path.dirname(os.path.abspath(__file__))
print("=" * 78)
print("PART 5: Lemma 15 and the final contradiction")
print("=" * 78)
w0 = w(arb(0))
a = A(sum(AK[1:]))
kap = A(KAPPA_SUM)
Kc = a * kap * w0 / 2            # coefficient of eta*log t on the left
eps = arb(10) ** -100
Kq = arb(K)
logKterm = (Kq + T0 / H).log()    # log(Kt+T0) <= log t + log(K + T0/H)
check("a kappa w(0)/2 = 5.0391...", None, fmt(Kc, 12))
check("log(K + T0/H) <= 2.78 (used for mu > 1 - 2.78/log t)", lt(logKterm, D("2.78")), fmt(logKterm, 8))

# ---------------------------------------------------------------- printed constants
C2p = lambda e: D("13.47") * e - 161 * e ** 2 - 11896 * e ** 3
C1p = lambda x: D("0.87637") + D("0.12002") * x + D("0.01017") * x ** 2 - D("0.00073") * x ** 3
lin_p = D("3.909") + (D("0.1186") + D("1.568")) * w0 - D("1e-10")
check("C2 eta-coefficient: 3.909 + (0.1186+1.568) w(0) - 1e-10 >= 13.47", lt(D("13.47"), lin_p), fmt(lin_p, 8))
check("C2 eta^2: 26 - 187 = -161", True)
check("C2 eta^3: 3897 + 8013 = 11910 > 11896 (slip of 14 eta^3), compensated by the linear slack "
      "(3.909 + 1.6866 w0 - 13.47) eta >= 14 eta^3 for eta <= eta0",
      lt(arb(14) * eta0 ** 2, lin_p - D("13.47")), f"linear slack {fmt(lin_p - D('13.47'), 4)} vs 14 eta0^2 = {fmt(14*eta0**2, 4)}")

# the paper's symbolic step: C1(1 - 2.78/L) + C2(1/(6L)) - 1e-7 > 1.00582 + 1.86088/L - 4.4106/L^2 - 55.0584/L^3
def paper_poly(L):
    return D("1.00582") + D("1.86088") / L - D("4.4106") / L ** 2 - D("55.0584") / L ** 3


def paper_lhs(L):
    return C1p(1 - D("2.78") / L) + C2p(1 / (6 * L)) - D("1e-7")


okpoly = True
for i in range(0, 481):
    L = logH + (D("76.47") - logH) * i / 480
    okpoly &= lt(paper_poly(L), paper_lhs(L))
check("C1(1-2.78/L) + C2(1/(6L)) - 1e-7 > 1.00582 + 1.86088/L - 4.4106/L^2 - 55.0584/L^3 "
      "(grid of 481 points on [log H, 76.47])", okpoly)
L76 = D("76.47")
v76 = paper_poly(L76)
check("value at L = 76.47 is 1.02928...", abs(v76 - D("1.02928")) < D("1e-5"), fmt(v76, 10))
need = Kc * (A0 + eps)
check("PRINTED final step: 1.02928.../(a kappa w0/2) > A0 + eps with A0 = 1/4.896", lt(need, v76),
      f"1.02928.../5.0391 = {fmt(v76 / Kc, 10)} vs A0 = {fmt(A0, 10)};  margin = {fmt(v76 - need, 4)} "
      f"(relative {fmt((v76 - need) / need, 3)})")
check("(with the printed table value A0 = 1/4.8596 this step would FAIL: needs "
      + fmt(Kc / D("4.8596"), 8) + ")", None)

# ---------------------------------------------------------------- corrected constants
cj = json.load(open(os.path.join(HERE, "lemma14_corrected.json")))
tiny = D("1e-20")
C1c = [D(x) - tiny for x in cj["C1c_lower"]]
b1, b2, b3 = D(cj["b1_lower"]) - tiny, D(cj["b2_lower"]) - tiny, D(cj["b3_upper"]) + tiny
# (48) with the log k correction of Lemma 8 (see part 2): eta^2 187, eta^3 8396 (rounded up)
E2, E3 = arb(187), arb(8396)
# Lemma 10: 0.1186 (verified in part 3), Lemma 12: 1.568 (part 2), Lemma 13: 1e-10, Lemma 6: 1e-7
lin_c = b1 + (D("0.1186") + D("1.568")) * w0 - D("1e-10")


def Phi(eta, mu):
    """Lower bound for (a kappa w0/2) eta log t, from (44)-(48) and corrected Lemma 14."""
    return (C1c[0] + C1c[1] * mu + C1c[2] * mu ** 2 + C1c[3] * mu ** 3
            + lin_c * eta + (b2 - E2) * eta ** 2 - (b3 + E3) * eta ** 3 - D("1e-7"))


dphi = lin_c - 2 * (E2 - b2) * eta0 - 3 * (b3 + E3) * eta0 ** 2
check("corrected Phi is increasing in eta on [0, eta0] (so lower bounds for eta may be used)",
      dphi.lower() > 0, f"d Phi/d eta >= {fmt(dphi, 6)}")
dC1 = C1c[1] + 2 * C1c[2] * mu0 - 3 * abs(C1c[3])
check("corrected C1 increasing on [mu0, 1]", dC1.lower() > 0, fmt(dC1, 6))


def mu_low(L):
    return (1 - 6 * eps) * L / (L + logKterm)


def margin_decoupled(L):      # paper's route: eta > 1/(6L), A <= A0
    return Phi(1 / (6 * L), mu_low(L)) - Kc * (A0 + eps)


def margin_coupled(L, A0_=A0):   # eta >= A/L and worst case A = A0 (see REPORT)
    return Phi(A0_ / L, mu_low(L)) - Kc * (A0_ + eps)


dA = lin_c / logH - Kc
check("coupled route: d/dA [Phi(A/L, mu) - Kc (A+eps)] < 0 for L >= log H, so worst case is A = A0",
      dA.upper() < 0, fmt(dA, 6))

for L in [logH, D("40"), D("55.01"), D("60"), D("76.47")]:
    md, mc = margin_decoupled(L), margin_coupled(L)
    check(f"L = log t = {fmt(L, 6)}: margins (decoupled, coupled)", md.lower() > 0 and mc.lower() > 0,
          f"decoupled {fmt(md, 5)} (rel {fmt(md / (Kc * A0), 3)}), coupled {fmt(mc, 5)} (rel {fmt(mc / (Kc * A0), 3)})")


def largest_L(fn, lo, hi, it=60):
    lo, hi = arb(lo), arb(hi)
    if fn(hi).lower() > 0:
        return hi
    for _ in range(it):
        mid = (lo + hi) / 2
        if fn(mid).lower() > 0:
            lo = mid
        else:
            hi = mid
    return lo


Lmax_d = largest_L(margin_decoupled, D("76.47"), arb(10) ** 4)
Lmax_c = largest_L(margin_coupled, D("76.47"), arb(10) ** 6)
check("corrected constants, decoupled final step: Lemma 1 range extends to log t <=", None, fmt(Lmax_d, 8))
check("corrected constants, coupled final step: Lemma 1 range extends to log t <=", None, fmt(Lmax_c, 8))
# monotonicity in L of the margins (so checking the top of a range suffices)
okm = True
prev = None
for i in range(0, 1001):
    L = logH + (D("76.47") - logH) * i / 1000
    cur = margin_decoupled(L)
    if prev is not None:
        okm &= (prev - cur).lower() > -D("1e-15")
    prev = cur
check("margin (decoupled) is decreasing in L on [log H, 76.47] (grid of 1001 points)", okm)

# rigorous cover in L: evaluate the margins on L-balls covering [log H, Ltop]
def cover_ok(fn, lo, hi, n):
    lo, hi = arb(lo), arb(hi)
    worst = None
    for i in range(n):
        l_, h_ = lo + (hi - lo) * i / n, lo + (hi - lo) * (i + 1) / n
        Lb = arb(((l_ + h_) / 2).mid(), ((h_ - l_) / 2).upper())
        m = fn(Lb).lower()
        worst = m if worst is None else min(worst, m)
        if m <= 0:
            return False, worst
    return True, worst


for name, fn in [("decoupled (paper's route)", margin_decoupled), ("coupled", margin_coupled)]:
    for Ltop in [D("55.01"), D("76.47")]:
        ok_, wst = cover_ok(fn, logH, Ltop, 4000)
        check(f"corrected constants, {name}: contradiction for ALL log t in [log H, {fmt(Ltop, 5)}] "
              "(4000 L-balls)", ok_, f"min margin = {float(wst):.4e}")

# best constant at the top of the range we need
def best_A0(Ltop, coupled):
    lo, hi = D("0.15"), D("0.3")
    for _ in range(80):
        mid = (lo + hi) / 2
        ok = True
        # margins are decreasing in L, so test the top
        m = margin_coupled(Ltop, mid) if coupled else (Phi(1 / (6 * Ltop), mu_low(Ltop)) - Kc * (mid + eps))
        if m.lower() > 0:
            lo = mid
        else:
            hi = mid
    return lo


for Ltop in [D("55.01"), D("76.47")]:
    bd, bc = best_A0(Ltop, False), best_A0(Ltop, True)
    check(f"best classical constant 1/A0 provable this way for t <= exp({fmt(Ltop, 5)})", None,
          f"decoupled 1/A0 = {fmt(1 / bd, 6)}, coupled 1/A0 = {fmt(1 / bc, 6)}")
check("NOTE: for the coupled bound one also needs eta <= eta0 = A0/log H; at A = A0 and t >= H this holds. "
      "For other A the hypotheses of Lemmas 6, 8, 9 (eta <= A0/log t) need A + eps <= A0, i.e. the iteration "
      "should be run with A <= A0 - eps (cosmetic).", None)

# ---------------------------------------------------------------- Theorem 1 assembly
x21 = (D("21.233") / D("4.896")).exp()
x19 = (D("19.62") / D("4.896")).exp()
check("Littlewood 21.233 (Yang JMAA 2024) beats 1/(4.896 log t) iff log t >= exp(21.233/4.896)",
      lt(x21, D("76.47")), f"exp(21.233/4.896) = {fmt(x21, 8)} (paper: 76.463)")
check("with the thesis constant 19.62 the crossover is at log t = exp(19.62/4.896)", None, fmt(x19, 8))
check("t < H: RH verified (Platt-Trudgian) and 1 - 1/(4.896 log 3) > 1/2", lt(arb(1) / 2, 1 - 1 / (D("4.896") * arb(3).log())))
check("iteration start: an existing region with c > 1/6, e.g. Kadiri 2005: 1/5.69693 > 1/6",
      lt(arb(1) / 6, 1 / D("5.69693")))
sys.exit(summary())
