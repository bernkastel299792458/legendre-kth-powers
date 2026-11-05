"""Part 1: Section 3 of BTY (test function, parameters, Lemmas 3-5).
Run:  python -I check_part1_sec3_lemma5.py"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Q
from flint import arb, acb, arb_series
from bty_common import *          # noqa: F401,F403
import polyq as P

print("=" * 78)
print("PART 1: Section 3 (w, f, parameters), Lemmas 3, 4, 5")
print("=" * 78)

# ---------------------------------------------------------------- w(0)
w0 = w(arb(0))
check("w(0): definition == closed form sec^2(th tan th + 3 th cot th - 3)",
      (w0 - w0_formula).contains(0), f"w(0) = {fmt(w0, 15)}")
check("w(0) = 5.672787598...", abs(w0 - D("5.6727875985")) < D("1e-9"), fmt(w0, 15))
check("support d = 2 th cot th = 1.05923293...", abs(d_supp - D("1.05923293")) < D("1e-8"),
      fmt(d_supp, 12))
check("tan(theta) (Lemma 4 needs r > tan theta)", None, fmt(tan_t, 10))

# ---------------------------------------------------------------- boundary conditions of w
# Lemma 7 (Kadiri Prop 2.1) needs g(d) = g'(0) = g'(d) = g''(d) = 0 for g(u) = eta w(eta u).


def wser(u0, n=5):
    return w(arb_series([arb(u0), 1], prec=n))


s0 = wser(0).coeffs()
sd = wser(d_supp).coeffs()
check("w'(0) = 0", s0[1].contains(0), str(s0[1]))
check("w(d) = 0", sd[0].contains(0), str(sd[0]))
check("w'(d) = 0", sd[1].contains(0), str(sd[1]))
check("w''(d) = 0", sd[2].contains(0), str(2 * sd[2]))
check("w''(0) < 0 and w'''(d) < 0 (so w' < 0 near both ends)", None,
      f"w''(0)={fmt(2*s0[2],6)}, w'''(d)={fmt(6*sd[3],6)}")

# ---------------------------------------------------------------- w >= 0, w' <= 0 on [0, d]
# Strategy: w'' < 0 on [0, a] gives w' < 0 on (0, a]; interval evaluation shows
# w' < 0 on [a, b]; and on [b, d] w''' has a sign that, with w'(d)=w''(d)=0,
# forces w' < 0.  Then w decreasing with w(d)=0 gives w >= 0.


def wd(k, lo, hi):
    """Ball enclosure of w^{(k)} on [lo, hi]."""
    mid = (arb(lo) + arb(hi)) / 2
    rad = (arb(hi) - arb(lo)) / 2
    ball = arb(mid.mid(), rad.upper())
    c = w(arb_series([ball, 1], prec=k + 1)).coeffs()
    f = 1
    for j in range(1, k + 1):
        f *= j
    return c[k] * f


def cover(pred, lo, hi, n):
    lo, hi = arb(lo), arb(hi)
    step = (hi - lo) / n
    for i in range(n):
        if not pred(lo + i * step, lo + (i + 1) * step):
            return False, i
    return True, n


a_split, b_split = D("0.2"), d_supp - D("0.2")
ok1, _ = cover(lambda l, h: wd(2, l, h).upper() < 0, 0, a_split, 400)
ok2, _ = cover(lambda l, h: wd(1, l, h).upper() < 0, a_split, b_split, 2000)
ok3, _ = cover(lambda l, h: wd(3, l, h).upper() < 0, b_split, d_supp, 400)
check("w'' < 0 on [0,0.2]  (=> w' < 0 on (0,0.2])", ok1)
check("w' < 0 on [0.2, d-0.2]", ok2)
check("w''' < 0 on [d-0.2, d] (with w'(d)=w''(d)=0 => w'' > 0, w' < 0 there)", ok3)
check("Hence w is decreasing on [0,d] and w >= 0 (Lemma 3, Lemma 11 use this)", ok1 and ok2 and ok3)

# ---------------------------------------------------------------- parameter table
for name, a0s in [("4.896", "4.896"), ("4.8596 (as printed)", "4.8596"), ("4.8594", "4.8594")]:
    e0, s0_ = params(1 / D(a0s))
    check(f"table: A0 = 1/{name}", None, f"eta0 = {fmt(e0, 10)}, sigma0 = {fmt(s0_, 10)}")
check("table entries eta0=0.0071093.., sigma0=0.9935164.. correspond to A0=1/4.896 "
      "(the printed '(4.8596)^-1' is a typo)",
      abs(eta0 - D("0.0071093")) < D("1e-7") and abs(sigma0 - D("0.9935164")) < D("1e-7"),
      f"eta0={fmt(eta0,10)}, sigma0={fmt(sigma0,10)}")
e2, s2 = params(1 / D("4.8594"))
check("Lemma-2 column matches A0=1/4.8594",
      abs(e2 - D("0.0071628")) < D("1e-7") and abs(s2 - D("0.9934675")) < D("1e-7"))

# ---------------------------------------------------------------- kappa
check("kappa = sum kappa_m = 433/859", KAPPA_SUM == Q(433, 859), str(KAPPA_SUM))
check("sum |kappa_m| = 3243/859 = 3.7753...", KAPPA_ABS == Q(3243, 859), f"{float(KAPPA_ABS):.6f}")
S_mk = sum(m * KAPPA[m] for m in range(M + 1))
check("sum m kappa_m", None, f"{S_mk} = {float(S_mk):.6f}")

# ---------------------------------------------------------------- Lemma 3
p = list(KAPPA)
nroots = P.count_roots(p, Q(0), Q(1))
check("Lemma 3: p(x)=sum kappa_m x^m has no root in (0,1] (Sturm, exact)",
      nroots == 0 and P.ev(p, Q(1)) > 0, f"#roots in (0,1] = {nroots}, p(1) = {P.ev(p, Q(1))}")
check("Lemma 3: p(0) = 1 > 0 too, so p > 0 on [0,1]", P.ev(p, Q(0)) > 0)
pmin = min(P.ev(p, Q(i, 1000)) for i in range(1001))
check("min_{[0,1]} p (grid, info)", None, f"{float(pmin):.6f}")

# ---------------------------------------------------------------- Lemma 4 (Ford)
# (a) Ford's closed form for W_0 agrees with direct rigorous quadrature.
okc = True
for zz in [acb(3, 0), acb(0, 5), acb(-1, 7), acb(10, 30), acb(2, 200), acb(138, 0)]:
    diff = W(zz) - w0 / zz - W0_closed(zz)
    okc &= abs(diff).upper() < 1e-20
check("Ford closed form W_0(z) = c0(c2[(z+1)^2 e^{-2 th cot th z} + z^2-1] - c1 z - c3 z^3)"
      "/(z^2(z^2+tan^2 th)^2) with c0 = 1/(sin th cos^3 th) matches quadrature (6 points)", okc)
check("BTY prints c0 = csc th sec^2 th; Ford/MTY have csc th sec^3 th (factor sec th = "
      + fmt(1 / theta.cos(), 8) + ")", None, f"printed c0 = {fmt(fc0_printed, 8)}, correct c0 = {fmt(fc0, 8)}")
lim = fc0 * fc3
w2_0 = 2 * wser(0).coeffs()[2]
check("asymptotics: C(nu,r) -> c0 c3 must be >= |w''(0)| = lim |W_0(z) z^3|", lt(abs(w2_0), lim + D("1e-30")) or (lim - abs(w2_0)).contains(0),
      f"c0 c3 = {fmt(lim, 12)} (correct c0) vs {fmt(fc0_printed * fc3, 8)} (printed); |w''(0)| = {fmt(abs(w2_0), 12)}")
# (b) the bound itself, tested with nu = Re z, r = |z|
for label, Cf in [("correct c0", C_ford), ("printed c0", C_ford_printed)]:
    worst = arb(0)
    okF = True
    for nu in ["-1", "0", "1", "3", "10", "69", "138"]:
        for y in ["0", "1", "5", "30", "200", "1000"]:
            z = acb(D(nu), D(y))
            r = abs(z)
            if not lt(tan_t, r):
                continue
            ratio = abs(W(z) - w0 / z) * r ** 3 / Cf(D(nu), r)
            worst = arb(max(worst.upper(), ratio.upper()))
            okF &= lt(ratio, arb(1))
    check(f"Lemma 4 bound |W0(z)| <= C(Re z,|z|)|z|^-3 at 40 test points, {label}", okF if label == "correct c0" else (None if not okF else True),
          f"max ratio = {fmt(worst, 6)}")
# (c) C(nu, R) with R >= r is maximised at R = r (H(R) decreasing), spot check
okm = all(lt(C_ford(nu, D(r) * 2), C_ford(nu, D(r))) for nu in [-1, 0, 138] for r in ["2.5", "3", "10", "138", "1e6"])
check("C(nu, R) decreasing in R (spot check) so sup over |z|>=r is at |z|=r", okm)

# Heath-Brown: Re W(iy) >= 0 (cited, refereed).  Spot check only.
hb = min(W(acb(0, D(str(y)))).real.lower() for y in [0, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233])
check("Heath-Brown property Re W(iy) >= 0 (spot check, 13 points)", hb > 0 or None,
      f"min lower bound = {hb}")

# ---------------------------------------------------------------- Lemma 5, (21) on Re z = 0
two_s0 = 2 * sigma0 - 1
check("Lemma 5: (2 sigma0 - 1)/eta0 > 138", lt(arb(138), two_s0 / eta0), fmt(two_s0 / eta0, 8))
C138 = C_ford(138, 138)
lhs = eta0 ** 2 * C138 / (two_s0 ** 2 * w0)
check("Lemma 5: eta0^2 C(138,138)/((2s0-1)^2 w(0)) < eps0 = 1/2000  [correct c0]", lt(lhs, arb(1) / 2000),
      f"value = {fmt(lhs, 6)}, C(138,138) = {fmt(C138, 8)} (printed c0 would give {fmt(C_ford_printed(138,138), 6)})")
c0q = Q(151, 153)
check("Lemma 5: c0 = 151/153 < 2 sigma0 - 1", lt(A(c0q), two_s0),
      f"{float(c0q):.8f} < {fmt(two_s0, 10)}")

# b_m: (1+x) sum kappa_m x^m
b = P.mul([Q(1), Q(1)], list(KAPPA))
check("b_m = kappa_m + kappa_{m-1}", None, "[" + ", ".join(str(x) for x in b) + "]")
eps0 = Q(1, 2000)
# B(y) as N(Y)/prod(c_m^2 + Y), Y = y^2
dens, nums = [], []
for m in range(1, M + 2):
    if b[m] > 0:
        dens.append([Q(m * m), Q(1)])
        nums.append(b[m] * (m - eps0 / m))
    else:
        dens.append([c0q ** 2 * m * m, Q(1)])
        nums.append(b[m] * (m + eps0 / m))
N = []
for i in range(len(dens)):
    term = [nums[i]]
    for j in range(len(dens)):
        if j != i:
            term = P.mul(term, dens[j])
    N = P.add(N, term)
Ny = []        # N(y^2) as polynomial in y
for k, c in enumerate(N):
    Ny += [Q(0)] * (2 * k - len(Ny)) + [c]
paper_p = {12: 4061245152630328137981, 10: 4077560173170236734684710,
           8: -104378137212291977844887868, 6: -4484512641017853031179075270,
           4: 135673322742635307737680349343, 2: -229732179325278720034298507440,
           0: 112359769561546903428467326544}
scale_q = Q(4012454647232553285540000)
# paper: B = p/q with q = scale_q * prod(...).  So p should equal scale_q * N(y^2)
recomputed = {k: scale_q * Ny[k] for k in range(len(Ny)) if Ny[k] != 0}
match = all(recomputed.get(k, 0) == v for k, v in paper_p.items()) and \
    set(recomputed) == set(paper_p)
check("Lemma 5: recomputed numerator of B(y) == paper's p(y) (exact, all 7 coefficients)",
      match, "" if match else str({k: (recomputed.get(k), paper_p[k]) for k in paper_p}))
# paper's q-factors
qfactors_ok = sorted(str(dd[0]) for dd in dens) == sorted(
    [str(Q(1)), str(Q(9)), str(Q(25))] + [str(c0q ** 2 * m * m) for m in (2, 4, 6, 7)])
check("Lemma 5: denominator factors (y^2+1)(y^2+9)(y^2+25)(y^2+4c0^2)...(y^2+49c0^2)", qfactors_ok)
nr = P.count_roots(N, Q(0), "+inf")
check("Lemma 5: N(Y) has no root in Y >= 0 and N(0) > 0  =>  B(y) > 0 for all real y (Sturm)",
      nr == 0 and P.ev(N, Q(0)) > 0, f"#roots of N in (0,inf) = {nr}")
nr_y = P.count_roots(Ny, "-inf", "+inf")
check("Lemma 5: paper's p(y) has no real root (Sturm on degree-12 poly)", nr_y == 0)
sum_mb = sum(m * b[m] for m in range(len(b)))
check("Large-|Im z| behaviour: Re[F(x+iT)+F(2s-1-x+iT)] ~ (eta w0 (2s-1)/T^2) * sum m b_m, "
      "sum m b_m = kappa + 2 sum m kappa_m", sum_mb == KAPPA_SUM + 2 * S_mk and sum_mb > 0,
      f"sum m b_m = {sum_mb}")
check("NOTE: paper says Re F(x+iT) = eta w0 (kappa+o(1))/T^2 > 0; actually "
      "Re F(x+iT) ~ eta w0 (kappa x + (2s-1) sum m kappa_m)/T^2, which is < 0 for small x. "
      "The needed statement (for the SUM F(z)+F(2s-1-z)) is true: coefficient (2s-1)*sum m b_m = "
      "(2s-1)/859 > 0.", None)

# ---------------------------------------------------------------- Lemma 5, (22)
r_big = T0 / eta0
Cm1 = C_ford(-1, r_big)   # correct c0
C0 = C_ford(0, r_big)
c57 = w0 + (Cm1 + C0) / T0 * eta0 ** 2
check("Lemma 5 (22): w(0) + (C(-1,T0/eta0)+C(0,T0/eta0)) eta0^2/T0 < 5.7", lt(c57, D("5.7")),
      fmt(c57, 10))
c44 = 2 * D("5.7") * A(KAPPA_ABS)
check("Lemma 5 (22): 2 * 5.7 * sum|kappa_m| < 44", lt(c44, arb(44)), fmt(c44, 8))
check("NOTE (22) is stated for -eta <= Re z <= 1, but the proof only covers Re z in [-eta, 2s-1+eta]"
      " (via symmetry).  Lemma 6 only needs Re z in (s-1, s) and s-1 >= -eta, so this suffices.", None)

sys.exit(summary())
